"""One foreman job: an arm at a rung and variant on a plan, run (under the optional memory guard), watched, verified.

Plateau rule: a run that has gained nothing for max(25 % of its budget, 3 min) is stopped early.
Stopping is lossless because nothing was gained: arms with a stop file get DIR/STOP (they write their word and end),
the others are killed.  A run that has gained keeps running to its own end.
A gain counts only after delcheck says the new word has 0 missing permutations.
"""
import hashlib
import os
import re
import shutil
import subprocess
import sys
import time

from . import winproc
from .arms import ARMS, DELCHECK, tool
import importlib
from . import config
config = importlib.reload(config)          # RELOAD re-imports runner; config.json comes along
from .config import P

PY = P("python") or sys.executable
GUARD = P("guard")
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PLANS = os.path.join(HERE, "plans")
RE_WROTE = re.compile(r"wrote \S+ length (\d+)")
RE_MODEL = re.compile(r"model length of the plan: (\d+)")
RE_GAIN = re.compile(r"(\d{5,}) -> (\d{5,})")
RE_BEST = re.compile(r"\bbest (\d{5,})")           # trailsearch progress: "t=200s best 408718 (thread 0: ...)"
CREATE_NEW_PROCESS_GROUP = 0x200
BELOW_NORMAL = 0x4000
CREATION = CREATE_NEW_PROCESS_GROUP | BELOW_NORMAL if sys.platform == "win32" else 0


def guarded(args, gb):
    """the command line: under the memory guard of config.json ("guard"), or the tool itself"""
    return [PY, "-I", GUARD, "--gb", str(gb), "--"] + args if GUARD else args


MINCUT_ARMS = ("ts", "ils", "or3", "recut", "dpa")   # tools that read gap-1 openings only with --mincut 1


def plan_has_gap1(path):
    """True if a plan opens some trail at a gap-1 step ("O t start g g1" with g = 1; foreman's ts top rung makes them)."""
    with open(path) as f:
        for line in f:
            p = line.split()
            if len(p) >= 4 and p[0] == "O" and p[3] == "1":
                return True
    return False


def sha_file(path, extra=None):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    if extra:
        h.update(b"\nBASE " + extra.encode())
    return h.hexdigest()


def store_plan(c, case, n, base, path, length, parent=None, arm=None, rung=None, variant=None, note=None):
    """copy a plan into foreman's plans/CASE/ under its SHA-256 and record it; returns the sha.  A plan on a base
    other than the case's base is hashed together with that base's path (a plan only means something on its base)."""
    cb = c.execute("SELECT base FROM cases WHERE name=?", (case,)).fetchone()
    sha = sha_file(path, base if cb and base != cb[0] else None)
    if c.execute("SELECT 1 FROM plans WHERE sha=? AND case_name=?", (sha, case)).fetchone():
        return sha
    d = os.path.join(PLANS, case)
    os.makedirs(d, exist_ok=True)
    dst = os.path.join(d, sha[:16] + ".plan")
    shutil.copyfile(path, dst)
    c.execute("INSERT INTO plans VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
              (sha, case, n, dst, base, length, parent, arm, rung, variant, time.time(), note))
    return sha


class Job:
    def __init__(self, run_id, case, n, base, plan, arm, rung, variant, seed, workdir, cfg=None):
        self.cfg = cfg or {}
        self.id, self.case, self.n, self.base = run_id, case, n, base
        self.plan = plan                       # plans row
        self.arm = ARMS[arm]
        self.rung, self.variant, self.seed = rung, variant, seed
        self.dir = workdir
        self.out = os.path.join(workdir, "o.txt")
        self.log = os.path.join(workdir, "o.log")
        self.threads = self.arm.threads(n, rung)
        self.gb = self.arm.gb(n, rung)
        self.budget = self.arm.budget(n, rung)
        self.proc = None
        self.t0 = self.t_end = None
        self.susp_since = None
        self.susp_s = 0.0
        self.last_gain = None                  # wall time of the last gain line in the log
        self.best_seen = None
        self.early = False
        self._logpos = 0

    def start(self):
        os.makedirs(self.dir, exist_ok=True)
        cfg = dict(self.cfg, _plan_length=self.plan["length"])     # arms that need the parent length
        args = self.arm.args(self.base, self.plan["path"], self.out, self.n, self.rung, self.variant, self.seed, cfg)
        if self.arm.name in MINCUT_ARMS and "--mincut" not in args and plan_has_gap1(self.plan["path"]):
            args += ["--mincut", "1"]          # the plan opens a trail at a gap-1 step: the tool must offer such cuts
        cmd = guarded(args, self.gb)
        with open(os.path.join(self.dir, "cmd.txt"), "w") as f:
            f.write(" ".join('"%s"' % a if " " in a else a for a in cmd) + "\n")
        env = dict(os.environ)
        env.update(config.env())               # tool paths for the wrappers (wrap/paths.sh)
        env.update(self.arm.env(self.n, self.rung))
        self.t0 = time.time()
        self.proc = subprocess.Popen(cmd, cwd=self.dir, stdout=open(self.log, "wb"), stderr=subprocess.STDOUT,
                                     env=env, creationflags=CREATION)
        return self.proc.pid

    # -- watching ----------------------------------------------------------------------------------------------
    def active_s(self):
        end = self.t_end or time.time()
        s = self.susp_s + ((time.time() - self.susp_since) if self.susp_since else 0)
        return max(0.0, end - self.t0 - s)

    def scan_log(self):
        try:
            with open(self.log, "rb") as f:
                f.seek(self._logpos)
                chunk = f.read().decode("latin-1")
                self._logpos = f.tell()
        except OSError:
            return
        vals = [int(b) for a, b in RE_GAIN.findall(chunk) if int(b) < int(a)] + [int(x) for x in RE_BEST.findall(chunk)]
        for b in vals:
            if b < self.plan["length"] and (self.best_seen is None or b < self.best_seen):
                self.best_seen = b
                self.last_gain = time.time()

    def plateau(self):
        """True if the run has gained nothing for max(arm.plateau_share of its budget, 180 s) of active time."""
        if self.best_seen is not None and self.best_seen < self.plan["length"]:
            return False
        share = self.arm.plateau_share
        return self.active_s() > max(share * self.budget, 180) and self.arm.name in ("ts", "ils", "or3", "gpu_or3")

    def stop_early(self, reason="stop"):
        self.early = reason
        if self.arm.stopfile:
            open(os.path.join(self.dir, "STOP"), "w").close()
        else:
            self.kill()

    def pids(self):
        return winproc.tree(self.proc.pid) if self.proc else []

    def suspend(self):
        if self.susp_since is None and self.proc and self.proc.poll() is None:
            winproc.suspend(self.pids())
            self.susp_since = time.time()

    def resume(self):
        if self.susp_since is not None:
            winproc.resume(self.pids())
            self.susp_s += time.time() - self.susp_since
            self.susp_since = None

    def kill(self):
        if self.proc and self.proc.poll() is None:
            self.resume()
            winproc.kill(self.pids())

    def done(self):
        return self.proc is not None and self.proc.poll() is not None

    # -- result ------------------------------------------------------------------------------------------------
    def rescue(self):
        """a run killed after a gain (trailsearch writes its best plan every --ckpt seconds): render the last
        checkpoint plan with trailsearch --time 0; returns the render log text, or None."""
        plan = self.out + ".plan"
        if not os.path.exists(plan) or os.path.getmtime(plan) < self.t0:
            return None
        ck = os.path.join(self.dir, "rescue.plan")
        shutil.copyfile(plan, ck)
        log = os.path.join(self.dir, "rescue.log")
        with open(log, "wb") as f:
            subprocess.run(guarded([tool("trailsearch"), self.base, self.out, "--plan-in", ck, "--time", "0", "--threads",
                                    "4", "--mincut", "1"], self.gb), stdout=f, stderr=subprocess.STDOUT)
        return open(log, "rb").read().decode("latin-1")

    def result(self):
        """(length or None, plan path or None, word path or None, note).  A shorter word is verified by delcheck."""
        self.scan_log()
        self.t_end = self.t_end or time.time()
        try:
            text = open(self.log, "rb").read().decode("latin-1")
        except OSError:
            return None, None, None, "no log"
        m = RE_WROTE.findall(text)
        if not m and self.best_seen is not None and self.best_seen < self.plan["length"]:
            text = self.rescue() or text   # killed after a gain: render its last checkpoint plan
            m = RE_WROTE.findall(text)
        if not m:
            tail = text.strip().splitlines()[-1:] or [""]
            return None, None, None, "no word: " + tail[0][:200]
        length = int(m[-1])
        plan = self.out + ".plan"
        terminal = re.search(r"^terminal\s*$", text, re.M) is not None   # a word without a plan (wide joins)
        if not os.path.exists(self.out) or (not os.path.exists(plan) and not terminal):
            return None, None, None, "word or plan file missing"
        if terminal and not os.path.exists(plan):
            plan = None
        if length >= self.plan["length"]:
            return length, plan, self.out, ""
        r = subprocess.run([DELCHECK, self.out, str(min(self.threads, 8))], capture_output=True, text=True)
        js = (r.stdout.strip().splitlines() or [""])[-1]
        with open(self.out + ".delcheck.json", "w") as f:
            f.write(js + "\n")
        if '"missing_permutations":0' not in js:
            return None, None, None, "delcheck FAILED: " + js[:200]
        flen = os.path.getsize(self.out) - (1 if open(self.out, "rb").read()[-1:] in (b"\n",) else 0) \
            if self.n <= 11 else length
        if flen != length:
            return None, None, None, "file length %d differs from the reported %d" % (flen, length)
        return length, plan, self.out, "delcheck ok" + (" (terminal: no plan)" if plan is None else "")

    def new_base(self):
        """the base an arm that changes bases wrote its plan on ("newbase PATH" in its log), or None."""
        try:
            m = re.findall(r"^newbase (.+)$", open(self.log, "rb").read().decode("latin-1"), re.M)
        except OSError:
            return None
        return m[-1].strip() if m else None

    def cleanup(self, keep_word):
        """delete the word unless it is kept (n = 13 words are 6.7 GB); plans stay (they are copied into the store)."""
        if not keep_word and os.path.exists(self.out):
            try:
                os.remove(self.out)
            except OSError:
                pass
