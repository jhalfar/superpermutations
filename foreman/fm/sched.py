"""Foreman's scheduler and arm policy (one process; the only writer of foreman.db).

Policy, per case:
* population: the K shortest plans of the store (PBT: every run starts from a population member, mostly the best;
  a plan that stalls is left behind because new runs take the best plan).
* candidates: for each population plan and arm, the first (rung, variant) of the arm's ladder that is neither in the
  memo for that plan nor running.  So an arm climbs a rung only after every variant of the lower rung gave 0 on the
  plan (the stall), and nothing that gave 0 runs again on the same plan.  Rungs >= 2 run only on the best plan
  (successive-halving: the expensive rungs go to the front of the population only).
* choice: discounted UCB on letters gained per resource hour (cost = CPU thread-hours + 8 x GPU hours; every
  finished run of the case discounts older rewards by GAMMA, so rewards shrink near a fixed point); untried arms
  first, cheaper rungs preferred.
* fixed point: no candidate on any population plan and nothing running: every arm at its top rung gave 0.
Scheduler: tokens (threads <= cap, the GPU exclusive and only when nvidia-smi shows no other compute process, GB of
memory limits <= cap and below free RAM), pre-emption by suspend/resume when other processes use the cores foreman
would need, or when the file PAUSE exists next to foreman.py.
"""
import importlib
import json
import math
import os
import re
import shlex
import shutil
import subprocess
import time

from . import db, winproc
from .arms import ARMS
from .config import ROOT
from . import config
from .config import P, C
from .runner import Job, store_plan

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WORK = P("work")
GAMMA = 0.9
GPU_WEIGHT = 8.0
POP = 3
DEAD_K = 3          # a rung that gave 0 on its last DEAD_K distinct plans of a case is skipped on new plans


def now():
    return time.time()


def oom(note):
    """True if a run ended at its memory limit (peak committed memory = the limit): not searched, so no memo 0."""
    m = re.search(r"peak committed memory of the job ([\d.]+) GB \(limit ([\d.]+) GB\)", note or "")
    return bool(m) and float(m.group(1)) >= float(m.group(2)) - 0.05


class Scheduler:
    def __init__(self, cases, threads_cap=12, gb_cap=48, hours=24.0, reserve_gb=10, dry=False, floor=0, on_record=None):
        self.c = db.connect()
        self.cases = [db.case_row(self.c, n) for n in cases]
        self.threads_cap, self.gb_cap, self.reserve_gb = threads_cap, gb_cap, reserve_gb
        self.floor = min(floor, threads_cap)       # threads foreman keeps even when other jobs load the machine
        self.on_record = on_record if on_record is not None else C.get("on_record", "")
        self.t_stop = now() + hours * 3600
        self.jobs = {}                    # run id -> Job
        self.paused = None                # reason or None
        self.ncpu = os.cpu_count() or 8
        self.done_cases = set()
        self.dry = dry
        self.last_snap = 0.0
        self.gpu_checked = (0.0, False)
        self.load_hi_since = None
        self.other_ema = None
        self.eff_cap = 0                 # set by update_cap() before the first launch
        winproc.cpu_busy()

    # -- policy ------------------------------------------------------------------------------------------------
    def arm_values(self, case):
        """discounted (gain, cost hours, runs) per arm of a case from the finished runs, newest weighted most."""
        rows = self.c.execute("SELECT arm, gain, cpu_h, gpu_h FROM runs WHERE case_name=? AND status='done' "
                              "ORDER BY t_end", (case,)).fetchall()
        st = {a: [0.0, 0.0, 0.0] for a in ARMS}
        for k, r in enumerate(rows):
            w = GAMMA ** (len(rows) - 1 - k)
            s = st[r["arm"]]
            s[0] += w * max(0, r["gain"] or 0)
            s[1] += w * ((r["cpu_h"] or 0) + GPU_WEIGHT * (r["gpu_h"] or 0))
            s[2] += w
        return st

    def dead_rungs(self, case):
        """(arm, rung) pairs that gave 0 on each of their last DEAD_K distinct plans of the case: skipped on new plans
        (the final sweep before a fixed point ignores this)."""
        dead = set()
        rows = self.c.execute("SELECT arm, rung, plan_sha, gain FROM runs WHERE case_name=? AND status='done' "
                              "ORDER BY t_end DESC", (case["name"],)).fetchall()
        seen = {}
        for r in rows:
            k = (r["arm"], r["rung"])
            d = seen.setdefault(k, {})
            if len(d) < DEAD_K and r["plan_sha"] not in d:
                d[r["plan_sha"]] = r["gain"] or 0
        for k, d in seen.items():
            if len(d) >= DEAD_K and all(g == 0 for g in d.values()):
                dead.add(k)
        return dead

    def mkey(self, case_name, sha):
        """memo key of a plan: the plan's hash, or "case/hash" for a case with own_memo (a controlled comparison of
        two cases on the same plans must not share zeros)"""
        return case_name + "/" + sha if db.config(db.case_row(self.c, case_name)).get("own_memo") else sha

    def candidates(self, case, use_dead=True):
        """for each population plan and arm, the first free variant of every rung that is open: rung 0 always, rung r
        once rung r - 1 has started on this plan (running or in the memo) or is dead in the case.  So the rungs of an
        arm run side by side (ils12.sh's kmax 2 and kmax 3 lanes) instead of one after the other, and every new best
        plan does not start the ladder from the bottom again."""
        n = case["n"]
        pop = db.population(self.c, case["name"], POP if n <= 11 else (2 if n == 12 else 1),
                            extra_bases=2 if n <= 11 else 0,          # n >= 12: every job is expensive
                            explorers=db.config(case).get("explorers", 2))
        if not pop:
            return []
        running = {(j.plan["sha"], j.arm.name, j.rung, j.variant) for j in self.jobs.values()}
        cfg = db.config(case)
        arms = [a for a in ARMS.values() if a.applicable(n, cfg) and a.name in cfg.get("arms", ARMS.keys())]
        dead = self.dead_rungs(case) if use_dead else set()
        out = []
        for i, p in enumerate(pop):
            for a in arms:
                if a.per_base and self.c.execute(
                        "SELECT 1 FROM memo m JOIN plans p ON m.plan_sha IN (p.sha, p.case_name || '/' || p.sha) WHERE m.arm=? AND p.base=? AND "
                        "p.case_name=?", (a.name, p["base"], case["name"])).fetchone():
                    continue                    # a certificate of this base exists already
                top = len(a.ladder) - 1 if i == 0 else min(1, len(a.ladder) - 1)
                nv = len(a.variants) * (a.repeats if i == 0 else 1)
                prev_open = True
                for r in range(top + 1):
                    if not prev_open:
                        break
                    started = False
                    pick = None
                    for v in range(nv):
                        key = (p["sha"], a.name, r, v)
                        if key in running:
                            started = True
                        elif db.memo_get(self.c, self.mkey(case["name"], p["sha"]), a.name, r, v) is not None:
                            started = True
                        elif pick is None:
                            pick = v
                    if (a.name, r) in dead:
                        prev_open = True        # skip this rung, the next one is open
                        continue
                    if pick is not None:
                        out.append((i, p, a, r, pick))
                    prev_open = started
        if any(not c[2].plateau_escape for c in out):
            out = [c for c in out if not c[2].plateau_escape]     # escapes (ncr) only on a plateau
        return out

    def score(self, case, cand, st):
        i, p, a, r, v = cand
        g, cost, nrun = st[a.name]
        tot = sum(s[2] for s in st.values()) + 1
        rates = [s[0] / max(s[1], 1e-3) for s in st.values() if s[2] > 0]
        top = max(rates) if rates and max(rates) > 0 else 1.0
        if nrun < 1e-9:
            u = 10.0 - a.budget(case["n"], r) / 3600.0          # untried: cheapest first
        else:
            u = (g / max(cost, 1e-3)) / top + 0.5 * math.sqrt(math.log(tot) / nrun)
        return u + (0.3 if i == 0 else 0.0) - 0.05 * r

    # -- resources ---------------------------------------------------------------------------------------------
    def used(self):
        js = [j for j in self.jobs.values() if j.susp_since is None]
        return sum(j.threads for j in js), sum(j.gb for j in self.jobs.values()), any(j.arm.gpu for j in self.jobs.values())

    def gpu_free(self):
        """No other GPU job: under Windows (WDDM) nvidia-smi lists every desktop program as a compute app with
        memory [N/A], so the card counts as free when no known GPU search program of someone else runs
        (config gpu_exe) and utilization stays below 25 % with less than 10 GB used over three samples (desktop ~6 GB)."""
        ours = set()
        for j in self.jobs.values():
            if j.arm.gpu:                 # only a GPU arm's own job is "ours"; any other job's card use counts as busy
                ours.update(j.pids())
        for pid, (_, exe) in winproc.proc_table().items():
            if pid not in ours and any(k in exe.lower() for k in config.live("gpu_exe")):
                return False
        for _ in range(3):
            try:
                r = subprocess.run(["nvidia-smi", "--query-gpu=utilization.gpu,memory.used",
                                    "--format=csv,noheader,nounits"], capture_output=True, text=True, timeout=30)
                util, mem = (float(x) for x in r.stdout.split(",")[:2])
            except (OSError, ValueError, subprocess.TimeoutExpired):
                return False
            if util >= 25 or mem >= 10240:
                return False
            time.sleep(1)
        return True

    def fits(self, arm, n, rung):
        th, gb, gpu = self.used()
        need_th, need_gb = arm.threads(n, rung), arm.gb(n, rung)
        if th + need_th > self.eff_cap or gb + need_gb > self.gb_cap:
            return False
        tot, avail = winproc.mem_status()
        if avail - need_gb < self.reserve_gb:
            return False
        if arm.gpu:
            if gpu:
                return False
            if now() - self.gpu_checked[0] > 60:
                self.gpu_checked = (now(), self.gpu_free())
            if not self.gpu_checked[1]:
                return False
        free = shutil.disk_usage(os.path.dirname(WORK) if os.path.exists(os.path.dirname(WORK)) else ROOT).free / 2 ** 30
        return free > (60 if n >= 13 else 5)

    # -- pre-emption -------------------------------------------------------------------------------------------
    def update_cap(self):
        """adaptive thread cap: cores left by other processes (smoothed over about a minute) minus 2, at most the
        configured cap.  Other users' jobs come first, so foreman shrinks instead of competing."""
        busy = winproc.cpu_busy()
        ours = sum(j.threads for j in self.jobs.values() if j.susp_since is None)
        other = max(0.0, busy * self.ncpu - ours)
        self.other_ema = other if self.other_ema is None else 0.85 * self.other_ema + 0.15 * other
        self.eff_cap = int(max(self.floor, min(self.threads_cap, self.ncpu - self.other_ema - 2)))
        return self.eff_cap

    def fit_load(self):
        """suspend the newest jobs while foreman uses more than the cap (+2 slack for a minute); resume the oldest
        load-suspended job when it fits under the cap again."""
        cap = self.update_cap()
        act = [j for j in self.jobs.values() if j.susp_since is None]
        used = sum(j.threads for j in act)
        tot, avail = winproc.mem_status()
        if avail < 3 and act:               # memory pressure: free RAM below 3 GB, suspend the newest job
            j = max(act, key=lambda j: j.t0)
            j.suspend()
            j.load_susp = True
            self.ev(j.case, "pause", "run %d suspended: free RAM %.1f GB" % (j.id, avail))
            return
        if used > cap + 2:
            self.load_hi_since = self.load_hi_since or now()
            if now() - self.load_hi_since > 60:
                for j in sorted(act, key=lambda j: -j.t0):
                    if used <= cap:
                        break
                    j.suspend()
                    j.load_susp = True
                    used -= j.threads
                    self.ev(j.case, "pause", "run %d suspended: load (other %.1f cores, cap %d)" % (j.id, self.other_ema, cap))
                self.load_hi_since = None
            return
        self.load_hi_since = None
        for j in sorted((j for j in self.jobs.values() if getattr(j, "load_susp", False)), key=lambda j: j.t0):
            if used + j.threads <= cap and avail > 8:
                j.resume()
                j.load_susp = False
                used += j.threads
                self.ev(j.case, "resume", "run %d resumed (other %.1f cores, cap %d)" % (j.id, self.other_ema, cap))

    def preempt(self):
        reason = None
        if os.path.exists(os.path.join(HERE, "PAUSE")):
            reason = "PAUSE file"
        if reason and not self.paused:
            for j in self.jobs.values():
                j.suspend()
            self.ev(None, "pause", "suspended %d jobs: %s" % (len(self.jobs), reason))
        elif not reason and self.paused:
            for j in self.jobs.values():
                if not getattr(j, "load_susp", False):
                    j.resume()
            self.ev(None, "resume", "resumed jobs (%s over)" % self.paused)
        self.paused = reason
        if not reason:
            self.fit_load()

    # -- jobs --------------------------------------------------------------------------------------------------
    def ev(self, case, kind, text):
        db.event(self.c, case, kind, text)
        print(time.strftime("%m-%d %H:%M:%S"), case or "-", kind, text, flush=True)

    def launch(self, case, cand):
        i, p, a, r, v = cand
        cur = self.c.execute("INSERT INTO runs (case_name, plan_sha, arm, rung, variant, setting, threads, gpu, gb, "
                             "status, t_start, len_in) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
                             (case["name"], p["sha"], a.name, r, str(v), json.dumps(a.setting(r, v)),
                              a.threads(case["n"], r), int(a.gpu), a.gb(case["n"], r), "running", now(), p["length"]))
        rid = cur.lastrowid
        d = os.path.join(WORK, case["name"], "r%05d_%s%d_%d" % (rid, a.name, r, v))
        j = Job(rid, case["name"], case["n"], p["base"] or case["base"], p, a.name, r, v, 1000 + rid, d, db.config(case))
        if self.dry:
            self.c.execute("UPDATE runs SET status='dry', dir=? WHERE id=?", (d, rid))
            db.memo_put(self.c, self.mkey(case["name"], p["sha"]), a.name, r, str(v), rid, 0)
            self.ev(case["name"], "dry", "%s rung %d variant %d on %s (%d)" % (a.name, r, v, p["sha"][:10], p["length"]))
            return
        pid = j.start()
        self.c.execute("UPDATE runs SET dir=?, pid=? WHERE id=?", (d, pid, rid))
        self.jobs[rid] = j
        self.ev(case["name"], "start", "run %d %s rung %d variant %d %s on %s (%d)" %
                (rid, a.name, r, v, json.dumps(a.setting(r, v)), p["sha"][:10], p["length"]))

    def finish(self, j):
        case = next(cs for cs in self.cases if cs["name"] == j.case)
        if j.arm.certificate:
            self.certificate(case, j)
            return
        length, plan, word, note = j.result()
        if length is None and j.early == "plateau":          # killed on the plateau rule: no gain, a 0 for the memo
            length, plan, word, note = j.plan["length"], None, None, "plateau stop, no gain"
        wall = j.active_s()
        cpu_h = j.threads * wall / 3600
        gpu_h = wall / 3600 if j.arm.gpu else 0.0
        gain = (j.plan["length"] - length) if length is not None else 0
        gain = max(0, gain)
        out_sha = None
        best = db.best_plan(self.c, j.case)
        keep = False
        if gain > 0 and word and (j.arm.terminal or plan is None):
            keep = True                     # wide-model word: kept and reported, its plan is not reused
            self.ev(j.case, "terminal", "run %d %s: verified word %d (%d below its plan), plan not reusable: %s" %
                    (j.id, j.arm.name, length, gain, word))
            rb = db.config(case).get("report_below")
            if rb and length < rb:
                self.report_found(case, length, word, j.plan["sha"])
        elif gain > 0 and plan:
            out_sha = store_plan(self.c, j.case, j.n, j.base, plan, length, j.plan["sha"], j.arm.name, j.rung,
                                 str(j.variant), note)
            if length < best["length"]:
                keep = True
                self.new_best(case, j, length, word, out_sha, best["length"])
        elif j.arm.changes_base and plan and length is not None and length <= j.plan["length"] + j.arm.accept_slack:
            nb = j.new_base()               # same length on another base: a new population member, not a gain
            if nb:
                out_sha = store_plan(self.c, j.case, j.n, nb, plan, length, j.plan["sha"], j.arm.name, j.rung,
                                     str(j.variant), "rebased onto " + nb)
                self.ev(j.case, "rebase", "run %d: plan %d on base %s (plan %s)" % (j.id, length, nb, out_sha[:16]))
        elif (j.arm.accept_slack and not j.arm.changes_base and plan and length is not None
              and db.config(case).get("explorers", 2) > 0
              and j.plan["length"] <= length <= j.plan["length"] + j.arm.accept_slack):
            # late acceptance: a result a few letters above its start (or a different plan of equal length)
            # is kept as an explorer; db.population lets up to 2 explorers near the best into the population
            out_sha = store_plan(self.c, j.case, j.n, j.base, plan, length, j.plan["sha"], j.arm.name, j.rung,
                                 str(j.variant), "explorer (+%d)" % (length - j.plan["length"]))
            self.ev(j.case, "explorer", "run %d %s: plan %d kept as explorer (+%d, plan %s)" %
                    (j.id, j.arm.name, length, length - j.plan["length"], out_sha[:16]))
        status = "done" if length is not None else "failed"
        self.c.execute("UPDATE runs SET status=?, t_end=?, wall_s=?, susp_s=?, cpu_h=?, gpu_h=?, len_out=?, gain=?, "
                       "out_sha=?, early=?, note=? WHERE id=?",
                       (status, now(), wall, j.susp_s, cpu_h, gpu_h, length, gain, out_sha, int(bool(j.early)), note, j.id))
        # a run cut by STOP (not by the plateau rule) did not search its whole setting: no memo 0 for it
        if (status == "done" and not (j.early == "stop" and gain == 0)) or "delcheck FAILED" in note:
            db.memo_put(self.c, self.mkey(j.case, j.plan["sha"]), j.arm.name, j.rung, str(j.variant), j.id, gain)
        elif status == "failed" and j.early != "stop" and not oom(note):
            # a setting that failed twice on a plan (e.g. a tool that cannot read the plan's gap-1 cuts) counts as
            # searched with 0, otherwise it would be launched again and again
            nf = self.c.execute("SELECT COUNT(*) FROM runs WHERE plan_sha=? AND arm=? AND rung=? AND variant=? AND "
                                "status='failed' AND case_name=?", (j.plan["sha"], j.arm.name, j.rung, str(j.variant), j.case)).fetchone()[0]
            if nf >= 2:
                db.memo_put(self.c, self.mkey(j.case, j.plan["sha"]), j.arm.name, j.rung, str(j.variant), j.id, 0)
                note += " (failed twice: memo 0)"
        self.ev(j.case, "end", "run %d %s rung %d variant %d: %s -> %s, gain %d, %.0f s%s%s" %
                (j.id, j.arm.name, j.rung, j.variant, j.plan["length"], length, gain, wall,
                 " (stopped early)" if j.early else "", (" [" + note + "]") if note and gain == 0 else ""))
        j.cleanup(keep)
        self.sample(case)

    def certificate(self, case, j):
        """a certificate arm ended: record "exact optimum L family ..." (event, SEARCHED.md, memo); no word."""
        j.t_end = j.t_end or now()
        wall = j.active_s()
        try:
            text = open(j.log, "rb").read().decode("latin-1")
        except OSError:
            text = ""
        m = re.findall(r"exact (optimum|bound) (\d+) (family .*)", text)
        best = db.best_plan(self.c, j.case)
        if m:
            kind, L, fam = m[-1][0], int(m[-1][1]), m[-1][2].strip()
            note = "exact %s %d %s" % (kind, L, fam)
            status = "done"
            if kind == "optimum":
                tail = (" (= the optimum)" if L == best["length"] else
                        " (the family holds a SHORTER word)" if L < best["length"] else "")
            else:
                tail = " (lower bound only: the window %d..%d is open in this family)" % (L, best["length"] - 1) \
                    if L < best["length"] else " (bound = best: optimal in this family)"
            line = "case %s n = %d: %s; best plan %d%s" % (case["name"], case["n"], note, best["length"], tail)
            for w in re.findall(r"solver word (\d+) kept as (\S+)", text):
                self.ev(j.case, "best", "certificate solver found a word of %s letters: %s (not yet in the store)" % w)
            self.ev(j.case, "exact", line)
            with open(os.path.join(HERE, "SEARCHED.md"), "a", encoding="utf-8") as f:
                f.write("- %s %s\n" % (time.strftime("%Y-%m-%d %H:%M"), line))
            db.memo_put(self.c, self.mkey(j.case, j.plan["sha"]), j.arm.name, j.rung, str(j.variant), j.id, 0)
        else:
            note = "certificate failed: " + (text.strip().splitlines()[-1:] or [""])[0][:200]
            status = "failed"
            self.ev(j.case, "end", "run %d %s: %s" % (j.id, j.arm.name, note))
        self.c.execute("UPDATE runs SET status=?, t_end=?, wall_s=?, cpu_h=?, gpu_h=0, len_out=NULL, gain=0, note=? "
                       "WHERE id=?", (status, now(), wall, j.threads * wall / 3600, note, j.id))

    def new_best(self, case, j, length, word, sha, old):
        cfg = db.config(db.case_row(self.c, case["name"]))     # fresh: self.cases holds the rows of the start
        prev = cfg.get("best_word")
        norm = lambda p: os.path.normcase(os.path.abspath(p))
        if prev and norm(prev) != norm(word) and os.path.exists(prev) and norm(prev).startswith(norm(WORK)):
            try:
                os.remove(prev)
            except OSError:
                pass
        cfg["best_word"] = word
        self.c.execute("UPDATE cases SET config=? WHERE name=?", (json.dumps(cfg), case["name"]))
        self.ev(case["name"], "best", "%d -> %d by %s rung %d variant %d (run %d), plan %s, word %s" %
                (old, length, j.arm.name, j.rung, j.variant, j.id, sha[:16], word))
        rb = cfg.get("report_below")
        if rb and length < rb:
            self.report_found(case, length, word, sha)

    def report_found(self, case, length, word, sha):
        """a verified word below the case's --report-below: run the --on-record command (if any) as CMD LENGTH WORD PLAN"""
        prow = self.c.execute("SELECT path, base FROM plans WHERE sha=?", (sha,)).fetchone()
        plan, pbase = prow["path"], prow["base"]
        self.ev(case["name"], "record", "verified %d below %d (credit as for the start word: %s): %s" %
                (length, db.config(case)["report_below"], db.config(case).get("credit", "see the case"), word))
        if self.on_record:
            try:
                subprocess.Popen(shlex.split(self.on_record, posix=os.name != "nt") + [str(length), word, plan])
            except OSError as e:
                self.ev(case["name"], "record", "--on-record failed: %s" % e)

    def sample(self, case):
        b = db.best_plan(self.c, case["name"])
        cpu = self.c.execute("SELECT COALESCE(SUM(cpu_h),0)+%f*COALESCE(SUM(gpu_h),0) FROM runs WHERE case_name=?"
                             % GPU_WEIGHT, (case["name"],)).fetchone()[0]
        self.c.execute("INSERT INTO samples VALUES (?,?,?,?,?)",
                       (now(), case["name"], (now() - self.case_t0(case)) / 3600, cpu, b["length"]))

    def case_t0(self, case):
        r = self.c.execute("SELECT MIN(ts) FROM samples WHERE case_name=?", (case["name"],)).fetchone()[0]
        return r or now()

    def snapshot(self):
        if now() - self.last_snap < 60:
            return
        self.last_snap = now()
        th, gb, gpu = self.used()
        tot, avail = winproc.mem_status()
        gpu_job = next((j.case + ":" + j.arm.name for j in self.jobs.values() if j.arm.gpu), None)
        self.c.execute("INSERT INTO sched VALUES (?,?,?,?,?,?,?,?,?)",
                       (now(), th, self.eff_cap, gpu_job, tot, avail, gb, len(self.jobs), self.paused))

    # -- main loop ---------------------------------------------------------------------------------------------
    def case_finished(self, case):
        cfg = db.config(case)
        b = db.best_plan(self.c, case["name"])
        if case["target"] and b["length"] <= case["target"]:
            return "target %d reached" % case["target"]
        for r in self.c.execute("SELECT note FROM runs WHERE case_name=? AND status='done' AND note LIKE 'exact optimum %'",
                                (case["name"],)).fetchall():
            L = int(r["note"].split()[2])
            if L == b["length"] and not any(a.changes_base and a.name != "rebase" and a.applicable(case["n"], cfg)
                                            for a in ARMS.values()):
                return "best %d = the exact optimum of its family (%s); no selection-change arm applies" % (L, r["note"][:80])
        mh = cfg.get("max_hours")
        if mh and now() - self.case_t0(case) > mh * 3600:
            return "time limit %.1f h" % mh
        mc = cfg.get("max_cpu_hours")
        if mc:
            used = self.c.execute("SELECT COALESCE(SUM(cpu_h),0)+%f*COALESCE(SUM(gpu_h),0) FROM runs WHERE case_name=?"
                                  % GPU_WEIGHT, (case["name"],)).fetchone()[0]
            if used > mc:
                return "budget %.1f CPU hours used (GPU hours x %g)" % (mc, GPU_WEIGHT)
        return None

    def fixed_point(self, case):
        b = db.best_plan(self.c, case["name"])
        n = case["n"]
        rows = []
        for a in ARMS.values():
            if a.applicable(n, db.config(case)) and a.name in db.config(case).get("arms", ARMS.keys()):
                rows.append("%s rungs 0-%d (%s)" % (a.name, len(a.ladder) - 1, json.dumps(a.ladder[-1])))
        text = "case %s n = %d: fixed point at %d (plan %s): every arm gave 0 at every rung on the population: %s" % (
            case["name"], n, b["length"], b["sha"][:16], "; ".join(rows))
        self.ev(case["name"], "fixed_point", text)
        with open(os.path.join(HERE, "SEARCHED.md"), "a", encoding="utf-8") as f:
            f.write("- %s %s\n" % (time.strftime("%Y-%m-%d %H:%M"), text))

    def reload_code(self):
        """the file RELOAD next to foreman.py: re-import fm.arms, fm.runner and fm.db (new arms, ladders, wrappers) without stopping the
        running jobs; they keep their old Job objects.  Changes to fm/sched.py itself still need a restart."""
        f = os.path.join(HERE, "RELOAD")
        if not os.path.exists(f):
            return
        os.remove(f)
        global ARMS, Job, store_plan
        from . import arms as arms_mod, runner as runner_mod
        try:
            importlib.reload(arms_mod)
            importlib.reload(runner_mod)
            importlib.reload(db)
            ARMS, Job, store_plan = arms_mod.ARMS, runner_mod.Job, runner_mod.store_plan
            self.ev(None, "reload", "reloaded fm.arms, fm.runner, fm.db: arms %s" % ", ".join(ARMS))
        except Exception as e:                    # keep the old code if the new one does not import
            self.ev(None, "error", "reload failed, old code kept: %r" % e)

    def pickup(self):
        """cases queued while the scheduler runs (foreman.py queue CASE) join without a restart."""
        for cs in self.c.execute("SELECT * FROM cases WHERE state='queued'").fetchall():
            self.c.execute("UPDATE cases SET state='running' WHERE name=?", (cs["name"],))
            self.cases = [c for c in self.cases if c["name"] != cs["name"]] + [cs]
            self.done_cases.discard(cs["name"])
            if not self.c.execute("SELECT 1 FROM samples WHERE case_name=?", (cs["name"],)).fetchone():
                b = db.best_plan(self.c, cs["name"])
                self.c.execute("INSERT INTO samples VALUES (?,?,?,?,?)", (now(), cs["name"], 0.0, 0.0, b["length"]))
            self.ev(cs["name"], "joined", "case joined the running scheduler")

    def run(self):
        for cs in self.cases:
            self.c.execute("UPDATE cases SET state='running' WHERE name=?", (cs["name"],))
            if not self.c.execute("SELECT 1 FROM samples WHERE case_name=?", (cs["name"],)).fetchone():
                b = db.best_plan(self.c, cs["name"])
                self.c.execute("INSERT INTO samples VALUES (?,?,?,?,?)", (now(), cs["name"], 0.0, 0.0, b["length"]))
        self.ev(None, "start", "scheduler: cases %s, threads %d, GB %d, until %s" %
                ([c["name"] for c in self.cases], self.threads_cap, self.gb_cap, time.strftime("%m-%d %H:%M", time.localtime(self.t_stop))))
        stopping = False
        while True:
            for rid, j in list(self.jobs.items()):
                if j.done():
                    del self.jobs[rid]
                    self.finish(j)
                else:
                    j.scan_log()
                    if not j.early and j.plateau():
                        j.stop_early("plateau")
                        self.ev(j.case, "plateau", "run %d %s: no gain after %.0f s, stopped" % (rid, j.arm.name, j.active_s()))
            self.pickup()
            self.reload_code()
            self.preempt()
            self.snapshot()
            if os.path.exists(os.path.join(HERE, "STOP")) or now() > self.t_stop:
                if not stopping:
                    self.ev(None, "stop", "STOP file or time limit: no new jobs; stopping running jobs early")
                    for j in self.jobs.values():
                        j.stop_early("stop")
                    stopping = True
                if not self.jobs:
                    break
                time.sleep(5)
                continue
            if not self.paused:
                for cs in self.cases:
                    if cs["name"] not in self.done_cases:
                        why = self.case_finished(cs)
                        if why:
                            self.done_cases.add(cs["name"])
                            self.ev(cs["name"], "case_end", why)
                # fair share: passes of one launch per case, the case with the fewest threads in use first
                while True:
                    active = [cs for cs in self.cases if cs["name"] not in self.done_cases]
                    active.sort(key=lambda cs: sum(j.threads for j in self.jobs.values() if j.case == cs["name"]))
                    launched_any = False
                    for cs in active:
                        mj = db.config(cs).get("max_jobs")    # e.g. 1: equal parallelism in a comparison, and room
                        if mj and sum(1 for j in self.jobs.values() if j.case == cs["name"]) >= mj:   # for big jobs
                            continue
                        cands = self.candidates(cs)
                        if not cands and not any(j.case == cs["name"] for j in self.jobs.values()):
                            cands = self.candidates(cs, use_dead=False)     # final sweep: dead rungs too
                        if not cands:
                            if not any(j.case == cs["name"] for j in self.jobs.values()):
                                self.fixed_point(cs)
                                self.done_cases.add(cs["name"])
                            continue
                        st = self.arm_values(cs["name"])
                        cands.sort(key=lambda k: -self.score(cs, k, st))
                        for k in cands:
                            if self.fits(k[2], cs["n"], k[3]):
                                self.launch(cs, k)
                                launched_any = True
                                break
                    if not launched_any:
                        break
                for name in self.done_cases:
                    self.c.execute("UPDATE cases SET state='done' WHERE name=?", (name,))
            if len(self.done_cases) == len(self.cases) and not self.jobs:
                break
            time.sleep(1 if self.dry else 5)
        self.ev(None, "exit", "scheduler ends")
