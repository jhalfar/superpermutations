"""Arms of foreman: (tool, setting) wrappers with a ladder of rungs.

An arm builds one command line from (base, plan, out dir, rung, variant, n) and reads the result from the log: every
tool used here prints "model length of the plan: L" (or loopscan's "length A -> B") and ends with "wrote OUT length L".
A rung is a dict of settings; higher rungs lift caps or give more time.  Variants are settings that do not lift a cap
(T0, seed lanes); each (rung, variant) is a separate memo key.  Arms never edit the tools: they call the programs
built from tools/ of this repository (tools/README.md says how to build them).
"""
import os
import sys

from .config import P

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

BIN = P("bin")
UNLIMITED = 1000000000


def tool(name):
    """path of a built tool in the bin folder (NAME.exe on Windows, NAME elsewhere); "gpucuts/tsw5g2" for a subfolder"""
    p = os.path.join(BIN, *name.split("/"))
    return p + ".exe" if sys.platform == "win32" and os.path.exists(p + ".exe") else p


DELCHECK = tool("delcheck")


def tbase(n):
    """seconds per trailsearch setting (the prepublication check's times: <= 9: 60, 10: 300, 11: 600, >= 12: 1200)."""
    return 60 if n <= 9 else 300 if n == 10 else 600 if n == 11 else 1200


def gb_for(n, kind="cpu"):
    """memory limit in GB per job (n = 13: one trailsearch or loopscan peaks at about 7-13 GB)."""
    g = {8: 2, 9: 2, 10: 3, 11: 5, 12: 10, 13: 14, 14: 40}.get(n, 2 if n < 8 else 48)
    return g + 6 if kind == "gpu" and n >= 13 else g


class Arm:
    name = ""
    exe = ""
    nmin, nmax = 1, 99
    gpu = False
    stopfile = False          # the tool stops cleanly (and writes its word) when DIR/STOP appears
    ladder = [{}]
    variants = [{}]
    repeats = 1               # stochastic arms: seeds per (rung, variant) before a 0 counts as searched
    changes_base = False      # the arm writes its plan on another base: kept even at equal length
    terminal = False          # its plans cannot be read by the other arms (wide joins): words kept, plans not reused
    accept_slack = 0          # keep a plan up to this many letters longer than its parent (late acceptance)
    certificate = False       # makes no word, prints "exact optimum L family ..." (a proof inside a named family)
    per_base = False          # runs once per base (its result does not depend on the plan)
    plateau_escape = False    # offered only when no other arm has a candidate on the case
    plateau_share = 0.25      # share of the budget without gain after which the run is stopped (runner.plateau)

    def ok(self, n):
        return self.nmin <= n <= self.nmax

    def applicable(self, n, cfg):
        return self.ok(n)

    def threads(self, n, rung):
        return 4

    def gb(self, n, rung):
        return gb_for(n, "gpu" if self.gpu else "cpu")

    def budget(self, n, rung):
        """planned wall seconds (for the plateau rule and the scheduler's estimate)."""
        return 600

    def args(self, base, plan, out, n, rung, variant, seed, cfg=None):
        raise NotImplementedError

    def env(self, n, rung):
        return {"OMP_NUM_THREADS": str(self.threads(n, rung))}

    def setting(self, rung, variant):
        s = dict(self.ladder[rung])
        s.update(self.variants[variant % len(self.variants)])
        if variant >= len(self.variants):
            s["repeat"] = variant // len(self.variants)
        return s


class TrailSearch(Arm):
    """trailsearch (the search of the prepublication check).  Rungs: kmax 8 at the check's time, kmax 12, kmax 12 at
    3x, kmax 16 at 6x, then the split caps lifted, then gap-1 cuts (--mincut 1).  Variants: T0 0.4 / 0.7 / 1.2."""
    name = "ts"
    exe = tool("trailsearch")
    ladder = [dict(kmax=8, tmul=1), dict(kmax=12, tmul=1), dict(kmax=12, tmul=3), dict(kmax=16, tmul=6),
              dict(kmax=16, tmul=6, splitmax=UNLIMITED, split_cands=1000000, split_pairs=512),
              dict(kmax=16, tmul=6, splitmax=UNLIMITED, split_cands=1000000, split_pairs=512, mincut=1)]
    variants = [dict(T0=0.4), dict(T0=0.7), dict(T0=1.2)]
    repeats = 2
    plateau_share = 0.6

    def budget(self, n, rung):
        return tbase(n) * self.ladder[rung]["tmul"]

    def args(self, base, plan, out, n, rung, variant, seed, cfg=None):
        s = self.setting(rung, variant)
        a = [self.exe, base, out, "--plan-in", plan, "--time", str(self.budget(n, rung)), "--seed", str(seed),
             "--kmax", str(s["kmax"]), "--T0", str(s["T0"]), "--threads", str(self.threads(n, rung)),
             "--sync", "15", "--ckpt", "60"]          # a killed run is rescued from its last checkpoint
        if n >= 12:
            a += ["--focus", "0.85"]
        for k in ("splitmax", "split_cands", "split_pairs", "mincut"):
            if k in s:
                a += ["--" + k.replace("_", "-"), str(s[k])]
        return a


class LoopScan(Arm):
    """loopscan (polish.sh's loop step run past its 40 rounds).  Rungs: 40 rounds, 1000, unlimited with long blocks
    scanned on big sequences (--big-events), then gap-1 ports and kind C added."""
    name = "loop"
    exe = tool("loopscan")
    ladder = [dict(rounds=40), dict(rounds=1000), dict(rounds=UNLIMITED, big_events=200000),
              dict(rounds=UNLIMITED, big_events=200000, gap1=1, kinds="PABCD")]

    def threads(self, n, rung):
        return 6 if n >= 12 else 4

    def budget(self, n, rung):
        return {0: 1800, 1: 6 * 3600, 2: 12 * 3600, 3: 12 * 3600}[rung] if n >= 12 else 900

    def args(self, base, plan, out, n, rung, variant, seed, cfg=None):
        s = self.setting(rung, variant)
        a = [self.exe, base, "--plan", plan, "--only", s.get("kinds", "PABD")]
        if not s.get("gap1"):
            a.append("--nogap1")
        a += ["--threads", str(self.threads(n, rung)), "--quiet", "--greedy", "--neutral", "--nbatch", "16",
              "--maxrounds", str(s["rounds"]), "--planout", out + ".plan", "--out", out]
        if "big_events" in s:
            a += ["--big-events", str(s["big_events"])]
        return a


class Recut(Arm):
    """recut --co-skip (the check's last step): deterministic, one rung."""
    name = "recut"
    exe = tool("recut")

    def threads(self, n, rung):
        return 1

    def budget(self, n, rung):
        return 300 if n <= 11 else 3600

    def args(self, base, plan, out, n, rung, variant, seed, cfg=None):
        return [self.exe, base, out, "--plan-in", plan, "--co-skip", "--time", "0"]


class Relocate(Arm):
    """relocate --dpa (polish.sh's first step).  Rungs: defaults, then --dpa-imax 3 --dpa-theta 4."""
    name = "dpa"
    exe = tool("relocate")
    ladder = [{}, dict(imax=3, theta=4)]

    def budget(self, n, rung):
        return 600 if n <= 11 else 3 * 3600

    def args(self, base, plan, out, n, rung, variant, seed, cfg=None):
        a = [self.exe, base, out, "--plan-in", plan, "--time", "0", "--threads", str(self.threads(n, rung)), "--dpa"]
        s = self.setting(rung, variant)
        if "imax" in s:
            a += ["--dpa-imax", str(s["imax"]), "--dpa-theta", str(s["theta"])]
        return a


class SegIns(Arm):
    """segins segment insertion on the CPU (polish.sh's or3 step).  Rungs: 3 cuts slack 0, 3/1, 5/0, 5/1, then
    --or3-xmax lifted.  n <= 12 (at n = 13 the GPU arm does this)."""
    name = "or3"
    exe = tool("segins")
    nmax = 12
    stopfile = True
    ladder = [dict(k=3, slack=0), dict(k=3, slack=1), dict(k=5, slack=0), dict(k=5, slack=1),
              dict(k=5, slack=1, xmax=64000)]

    def budget(self, n, rung):
        return 600 if n <= 10 else 3600

    def args(self, base, plan, out, n, rung, variant, seed, cfg=None):
        s = self.setting(rung, variant)
        a = [self.exe, base, out, "--plan-in", plan, "--time", "0", "--threads", str(self.threads(n, rung)),
             "--or3", str(s["k"]), "--or3-slack", str(s["slack"]), "--or3-maxcand", "3000",
             "--or3-sec", str(self.budget(n, rung)), "--or3-stop", os.path.join(os.path.dirname(out), "STOP")]
        if "xmax" in s:
            a += ["--or3-xmax", str(s["xmax"])]
        return a


class GpuOr3(Arm):
    """Segment insertion with the candidates judged on an NVIDIA card (tools/gpucuts/tsw5g2 --or3-gpu, 200,000
    candidates per batch: the program of the passes behind the n = 12 and n = 13 words of November 2026).  The card is
    one exclusive token.  Rungs: 3 cuts slack 0, 3/1, 5/0."""
    name = "gpu_or3"
    exe = tool("gpucuts/tsw5g2")
    nmin = 11
    gpu = True
    stopfile = True
    ladder = [dict(k=3, slack=0), dict(k=3, slack=1), dict(k=5, slack=0)]

    def threads(self, n, rung):
        return 6

    def gb(self, n, rung):
        return gb_for(n, "gpu") + (6 if self.ladder[rung]["k"] >= 5 else 0)

    def budget(self, n, rung):
        return 2400 if n >= 13 else 1800

    def args(self, base, plan, out, n, rung, variant, seed, cfg=None):
        s = self.setting(rung, variant)
        return [self.exe, base, out, "--plan-in", plan, "--time", "0", "--threads", str(self.threads(n, rung)),
                "--or3", str(s["k"]), "--or3-slack", str(s["slack"]), "--or3-gpu", "--or3-maxcand", "200000",
                "--or3-sec", str(self.budget(n, rung)), "--or3-stop", os.path.join(os.path.dirname(out), "STOP")]


class Ils(Arm):
    """segins_ils local kicks.  Rungs: kick depth kmax 1, 2, 3 at the base time; kmax 3 at 2x time with deeper kicks
    (--ils-kup 8 --ils-kcuts 4); kmax 3 at 4x time.  Variants: two seed lanes, two seeds each.  Gains at n = 12 often
    come late in long runs, so the plateau share is 50 %."""
    name = "ils"
    exe = tool("segins_ils")
    stopfile = True
    ladder = [dict(kmax=1, tmul=1), dict(kmax=2, tmul=1), dict(kmax=3, tmul=1),
              dict(kmax=3, tmul=2, kup=8, kcuts=4), dict(kmax=3, tmul=4, kup=8, kcuts=4)]
    variants = [dict(lane=0), dict(lane=1)]
    repeats = 2
    plateau_share = 0.5

    def gb(self, n, rung):
        return 20 if n >= 13 else gb_for(n)

    def threads(self, n, rung):
        return 2

    def budget(self, n, rung):
        return (300 if n <= 9 else 3000) * self.ladder[rung]["tmul"]

    def args(self, base, plan, out, n, rung, variant, seed, cfg=None):
        s = self.setting(rung, variant)
        a = [self.exe, base, out, "--plan-in", plan, "--time", "0", "--threads", str(self.threads(n, rung)),
             "--seed", str(seed), "--ils", str(self.budget(n, rung)), "--ils-log", "600",
             "--ils-kmax", str(s["kmax"]), "--ils-slack", "2", "--ils-near", "-1", "--ils-cuts", "3",
             "--or3-stop", os.path.join(os.path.dirname(out), "STOP")]
        if "kup" in s:
            a += ["--ils-kup", str(s["kup"]), "--ils-kcuts", str(s["kcuts"])]
        return a


class Wide(Arm):
    """Joins that overlap in up to n - 1 letters (the wide model; the other tools use h = n - 3).  Rungs: recut_wide
    --wide --co-skip, loopscan --wide 1000 rounds.  A plan with a tight join rebuilds a longer word with the other
    tools, so the arm is terminal: a shorter word is verified, kept and reported, its plan is not reused."""
    name = "wide"
    terminal = True
    ladder = [dict(tool="recut_wide"), dict(tool="loopscan", rounds=1000)]

    def threads(self, n, rung):
        return 1 if rung == 0 else 4

    def budget(self, n, rung):
        return 600 if n <= 11 else 3600

    def args(self, base, plan, out, n, rung, variant, seed, cfg=None):
        s = self.ladder[rung]
        if s["tool"] == "recut_wide":
            return [tool("recut_wide"), base, out, "--plan-in", plan, "--wide", "--co-skip", "--time", "0"]
        return [tool("loopscan"), base, "--plan", plan, "--only", "PABD", "--nogap1", "--wide",
                "--threads", str(self.threads(n, rung)), "--quiet", "--greedy", "--neutral", "--nbatch", "16",
                "--maxrounds", str(s["rounds"]), "--planout", out + ".plan", "--out", out]


class LongSA(Arm):
    """One long, hot trailsearch anneal.  Rungs: 3 h kmax 12, 6 h kmax 16; variants T0 1.5 / 3.0.  No plateau stop;
    a 300 s checkpoint, so a killed run is rescued."""
    name = "longsa"
    exe = tool("trailsearch")
    nmin = 10
    ladder = [dict(kmax=12, sec=3 * 3600), dict(kmax=16, sec=6 * 3600)]
    variants = [dict(T0=1.5), dict(T0=3.0)]
    plateau_share = 1.0

    def budget(self, n, rung):
        return self.ladder[rung]["sec"]

    def args(self, base, plan, out, n, rung, variant, seed, cfg=None):
        s = self.setting(rung, variant)
        a = [self.exe, base, out, "--plan-in", plan, "--time", str(s["sec"]), "--seed", str(seed), "--kmax", str(s["kmax"]),
             "--T0", str(s["T0"]), "--threads", str(self.threads(n, rung)), "--sync", "60", "--ckpt", "300"]
        if n >= 12:
            a += ["--focus", "0.85"]
        return a


class Cutlns(Arm):
    """The cut-opening reorder (tools/reorder, wrap/cutlns.sh): rounds that open weight-4 cuts (and the nearest weight-3
    cuts) next to K joins and solve the order of all pieces exactly as a maximum-weight path cover (one Gurobi model
    kept across rounds).  Rungs: weight 4 with K 2, 4, 8; then the nearest weight-3 cuts, 100, 300, 1000 per side.
    Variants: heaviest untried joins first, or random joins.  A word without a plan on the base is terminal.  Needs
    numpy, scipy and gurobipy (and a Gurobi licence for models of this size)."""
    name = "cutlns"
    exe = os.path.join(HERE, "wrap", "cutlns.sh")
    nmin, nmax = 11, 13
    stopfile = True
    plateau_share = 0.75
    ladder = [dict(K=2), dict(K=4), dict(K=8), dict(K=4, Rfine=100), dict(K=4, Rfine=300), dict(K=2, Rfine=1000)]
    variants = [dict(heavy=1), dict(heavy=0)]

    def threads(self, n, rung):
        return 3

    def gb(self, n, rung):
        return {11: 6, 12: 10, 13: 24}.get(n, 40)

    def budget(self, n, rung):
        return 1800 if n <= 12 else 3600

    def args(self, base, plan, out, n, rung, variant, seed, cfg=None):
        s = self.setting(rung, variant)
        a = [BASH, self.exe, out, plan, base, str(n), str(self.budget(n, rung)), str(self.threads(n, rung)),
             "--gopen", "4", "--K", str(s["K"]), "--heavy", str(s["heavy"]), "--seed", str(seed)]
        if "Rfine" in s:
            a += ["--gfine", "3", "--Rfine", str(s["Rfine"])]
        return a


class Rebase(Arm):
    """Move the plan onto another base (wrap/rebase.sh): a word read as its own base hides closed trails that the
    search cannot move.  Tries the bases in the case's config "alt_bases" (a selection's base or a hybrid base); the
    plan of the same length on the new base joins the population."""
    name = "rebase"
    per_base = True           # the answer depends on the base and the trails, not on the order
    exe = os.path.join(HERE, "wrap", "rebase.sh")
    changes_base = True

    def applicable(self, n, cfg):
        return bool((cfg or {}).get("alt_bases"))

    def budget(self, n, rung):
        return 1800

    def args(self, base, plan, out, n, rung, variant, seed, cfg=None):
        return [BASH, self.exe, out, plan, base] + list((cfg or {}).get("alt_bases", []))


class Expert12(Arm):
    """A whole chain of tools as one arm (wrap/expert12.sh), the chain that took William Echols's n = 12 word W-0091
    from 522,736,503 to 522,736,440 by hand: cycles of trailsearch kmax 8 T0 0.4 (1200 s), segment insertion with 3,
    4 and 5 cuts slack 1 (tools/gpucuts/tsw5g2, on the card when it is free), segins_ils kmax 1 (first cycle), ils12.sh
    (polish.sh, then two segins_ils lanes kmax 2 and 3 of 3000 s, repeated while a round gains) and recut, until a
    whole cycle gains nothing.  Run by foreman on the same word it gave 522,736,429 (wrap/../recipe/).  Opt-in (list
    it in --arms): the chain is tuned for n = 12."""
    name = "expert12"
    exe = os.path.join(HERE, "wrap", "expert12.sh")
    nmin = nmax = 12
    stopfile = True
    plateau_share = 1.0        # a cycle has long gain-free stretches; it stops itself at a fixed point
    ladder = [dict(sec=20 * 3600)]

    def applicable(self, n, cfg=None):
        return n == 12 and "expert12" in (cfg or {}).get("arms", [])

    def threads(self, n, rung):
        return 6

    def gb(self, n, rung):
        return 16

    def budget(self, n, rung):
        return self.ladder[rung]["sec"] + 1800

    def args(self, base, plan, out, n, rung, variant, seed, cfg=None):
        return [BASH, self.exe, out, plan, base, str(n), str((cfg or {}).get("_plan_length", 0)),
                str(self.ladder[rung]["sec"]), str(self.threads(n, rung))]


BASH = P("bash")

ARMS = {a.name: a for a in (TrailSearch(), LoopScan(), Recut(), Relocate(), SegIns(), GpuOr3(), Ils(), Wide(),
                            LongSA(), Cutlns(), Rebase(), Expert12())}
