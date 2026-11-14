"""foreman.py: runs the search tools of this repository for you (README.md next to this file).

  foreman.py add-case NAME --n N --base BASE --plan PLAN [--length L] [--target T] [--report-below R]
                      [--max-hours H] [--max-cpu-hours C] [--arms ts,loop,...] [--credit TEXT]
                      [--explorers K] [--own-memo]
  foreman.py add-plan CASE PLAN [--length L]
  foreman.py run CASE[,CASE...] [--threads 12] [--floor F] [--gb 48] [--hours 24] [--reserve 10] [--on-record CMD]
                 [--dry]
  foreman.py queue CASE[,CASE...]       (a running scheduler takes the case in without a restart)
  foreman.py status [CASE]
  foreman.py forget CASE ARM             (drop memo zeros of plateau-stopped runs, after a plateau-rule change)
  foreman.py arms
  foreman.py report [CASE,...] [--out FILE]   (benchmark table, anytime curves, gains per arm, from foreman.db)

Without --length the plan's length is read from trailsearch --time 0 ("model length of the plan").
Stop cleanly: create the file STOP next to foreman.py (running jobs stop early, then the scheduler ends); pause: PAUSE.
"""
import json
import os
import re
import subprocess
import sys
import time

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fm import db                                    # noqa: E402
from fm.arms import ARMS, tool                       # noqa: E402
from fm.runner import store_plan                     # noqa: E402


def opt(args, name, default=None, conv=str):
    if name in args:
        i = args.index(name)
        v = args[i + 1]
        del args[i:i + 2]
        return conv(v)
    return default


def flag(args, name):
    if name in args:
        args.remove(name)
        return True
    return False


def plan_length(base, plan):
    r = subprocess.run([tool("trailsearch"), base, os.devnull, "--plan-in", plan, "--time", "0",
                        "--threads", "1"], capture_output=True, text=True)
    m = re.search(r"model length of the plan: (\d+)", r.stdout + r.stderr)
    if not m:
        raise SystemExit("could not read the plan length:\n" + (r.stdout + r.stderr)[-800:])
    return int(m.group(1))


def main():
    a = sys.argv[1:]
    if not a:
        print(__doc__)
        return
    cmd = a.pop(0)
    c = db.connect()
    if cmd == "add-case":
        name = a.pop(0)
        n = opt(a, "--n", conv=int)
        base = os.path.abspath(opt(a, "--base"))
        plan = os.path.abspath(opt(a, "--plan"))
        length = opt(a, "--length", None, int) or plan_length(base, plan)
        cfg = {}
        for k, conv in (("--report-below", int), ("--max-hours", float), ("--max-cpu-hours", float), ("--credit", str),
                        ("--explorers", int)):
            v = opt(a, k, None, conv)
            if v is not None:
                cfg[k[2:].replace("-", "_")] = v
        if flag(a, "--own-memo"):
            cfg["own_memo"] = True             # memo keys of this case are its own (controlled comparisons)
        arms = opt(a, "--arms")
        if arms:
            cfg["arms"] = arms.split(",")
        target = opt(a, "--target", None, int)
        c.execute("INSERT OR REPLACE INTO cases (name, n, base, base_tsv, start_sha, target, created, config, state) "
                  "VALUES (?,?,?,?,?,?,?,?,?)", (name, n, base, None, None, target, time.time(), json.dumps(cfg), "idle"))
        sha = store_plan(c, name, n, base, plan, length, note="start plan " + plan)
        c.execute("UPDATE cases SET start_sha=? WHERE name=?", (sha, name))
        db.event(c, name, "case", "added: n = %d, start %d (%s), target %s, config %s" % (n, length, plan, target, cfg))
        print("case %s: start plan %s length %d" % (name, sha[:16], length))
    elif cmd == "add-plan":
        name, plan = a.pop(0), os.path.abspath(a.pop(0))
        cs = db.case_row(c, name)
        length = opt(a, "--length", None, int) or plan_length(cs["base"], plan)
        sha = store_plan(c, name, cs["n"], cs["base"], plan, length, note="added " + plan)
        print("plan %s length %d" % (sha[:16], length))
    elif cmd == "run":
        from fm.sched import Scheduler
        names = a.pop(0).split(",")
        th = opt(a, "--threads", 12, int)
        s = Scheduler(names, threads_cap=th, gb_cap=opt(a, "--gb", 48, int), hours=opt(a, "--hours", 24.0, float),
                      reserve_gb=opt(a, "--reserve", 10, int), floor=opt(a, "--floor", th, int),
                      on_record=opt(a, "--on-record"), dry=flag(a, "--dry"))
        s.run()
    elif cmd == "status":
        name = a.pop(0) if a else None
        for cs in c.execute("SELECT * FROM cases" + (" WHERE name=?" if name else ""), (name,) if name else ()):
            b = db.best_plan(c, cs["name"])
            nr = c.execute("SELECT COUNT(*), COALESCE(SUM(cpu_h),0), COALESCE(SUM(gpu_h),0) FROM runs WHERE case_name=?",
                           (cs["name"],)).fetchone()
            print("%s n=%d state %s best %d (start %s, target %s) runs %d cpu %.2f h gpu %.2f h" %
                  (cs["name"], cs["n"], cs["state"], b["length"],
                   c.execute("SELECT length FROM plans WHERE sha=?", (cs["start_sha"],)).fetchone()[0],
                   cs["target"], nr[0], nr[1], nr[2]))
            for r in c.execute("SELECT arm, COUNT(*) k, SUM(gain) g, SUM(cpu_h) h, MAX(rung) mr, "
                               "SUM(gain=0) z FROM runs WHERE case_name=? AND status='done' GROUP BY arm",
                               (cs["name"],)):
                print("   %-8s runs %3d gain %6d  cpu %6.2f h  top rung %d  zero runs %d" %
                      (r["arm"], r["k"], r["g"] or 0, r["h"] or 0, r["mr"], r["z"]))
        for e in c.execute("SELECT * FROM events ORDER BY ts DESC LIMIT 12").fetchall()[::-1]:
            print(time.strftime("%m-%d %H:%M:%S", time.localtime(e["ts"])), e["case_name"], e["kind"], e["text"][:150])
    elif cmd == "forget":
        # forget CASE ARM: drop the memo zeros of that arm's plateau-stopped runs (after a change of the plateau rule)
        name, arm = a.pop(0), a.pop(0)
        k = c.execute("DELETE FROM memo WHERE run_id IN (SELECT id FROM runs WHERE case_name=? AND arm=? AND "
                      "note LIKE 'plateau%' AND gain=0)", (name, arm)).rowcount
        db.event(c, name, "forget", "memo zeros of %d plateau-stopped %s runs dropped" % (k, arm))
        print("dropped %d memo rows" % k)
    elif cmd == "queue":
        for name in a.pop(0).split(","):
            db.case_row(c, name)
            c.execute("UPDATE cases SET state='queued' WHERE name=?", (name,))
            print("queued %s (a running scheduler picks it up)" % name)
    elif cmd == "report":
        from fm.report import report
        out = opt(a, "--out")
        names = a.pop(0).split(",") if a and not a[0].startswith("--") else None
        text = report(c, names)
        if out:
            open(out, "w", encoding="utf-8").write(text)
            print("wrote " + out)
        else:
            print(text)
    elif cmd == "arms":
        for arm in ARMS.values():
            print("%-8s n %d-%d gpu %s stopfile %s rungs %s variants %s" %
                  (arm.name, arm.nmin, arm.nmax, arm.gpu, arm.stopfile, arm.ladder, arm.variants))
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
