"""The benchmark report from foreman.db (foreman.py report): one table row per case (start, target, best, wall and CPU
hours to the best, totals), the anytime curve (each new best with its wall and CPU hours) and the letters each arm
gained.  Times are from the samples table (wall h counts from the case's first sample; CPU h = thread-hours of
foreman's jobs, GPU hours x 8).  The comparison with manual chains stays in BENCHMARK.md (it needs their logs)."""
import time


def fmt(x):
    return "{:,}".format(x) if isinstance(x, int) else str(x)


def case_report(c, name):
    case = c.execute("SELECT * FROM cases WHERE name=?", (name,)).fetchone()
    start = c.execute("SELECT length FROM plans WHERE sha=? AND case_name=?", (case["start_sha"], name)).fetchone()
    start = start["length"] if start else None
    smp = c.execute("SELECT wall_h, cpu_h, best FROM samples WHERE case_name=? ORDER BY ts", (name,)).fetchall()
    curve, last = [], None
    for s in smp:
        if s["best"] is not None and (last is None or s["best"] < last):
            curve.append((s["wall_h"], s["cpu_h"], s["best"]))
            last = s["best"]
    best = last if last is not None else start
    to_best = curve[-1] if curve else (0, 0, best)
    tot = (smp[-1]["wall_h"], smp[-1]["cpu_h"]) if smp else (0, 0)
    arms = c.execute("SELECT arm, COUNT(*) n, SUM(CASE WHEN gain > 0 THEN gain ELSE 0 END) g, SUM(cpu_h) h "
                     "FROM runs WHERE case_name=? GROUP BY arm ORDER BY g DESC, h DESC", (name,)).fetchall()
    return dict(name=name, n=case["n"], start=start, target=case["target"], best=best, state=case["state"],
                to_best=to_best, total=tot, curve=curve, arms=arms,
                reached=case["target"] is not None and best is not None and best <= case["target"])


def report(c, names=None):
    names = names or [r["name"] for r in c.execute("SELECT name FROM cases ORDER BY n, name")]
    rs = [case_report(c, n) for n in names]
    out = ["# Foreman benchmark report (generated)", "",
           "Generated %s from foreman.db by `fm.sh report`. Wall h from the case's first sample; CPU h = thread-hours "
           "of foreman's jobs (GPU h x 8). Every best below passed delcheck (0 missing permutations)." %
           time.strftime("%Y-%m-%d %H:%M"), "",
           "| case | n | start | target | best | gain | target reached | wall h / CPU h to best | total wall h / CPU h |",
           "|---|---|---|---|---|---|---|---|---|"]
    for r in rs:
        gain = (r["start"] - r["best"]) if r["start"] is not None and r["best"] is not None else ""
        out.append("| %s | %d | %s | %s | %s | %s | %s | %.1f / %.1f | %.1f / %.1f |" % (
            r["name"], r["n"], fmt(r["start"]), fmt(r["target"]) if r["target"] else "-", fmt(r["best"]), gain,
            "yes" if r["reached"] else "no", r["to_best"][0], r["to_best"][1], r["total"][0], r["total"][1]))
    out += ["", "## Anytime curves (best: wall h / CPU h)", ""]
    for r in rs:
        pts = " -> ".join("%s (%.1f / %.1f)" % (fmt(b), w, h) for w, h, b in r["curve"])
        out.append("* %s: %s" % (r["name"], pts or "no samples"))
    out += ["", "## Letters gained per arm (runs, CPU h)", ""]
    for r in rs:
        parts = ["%s %d (%d runs, %.1f h)" % (a["arm"], a["g"] or 0, a["n"], a["h"] or 0) for a in r["arms"]]
        out.append("* %s: %s" % (r["name"], ", ".join(parts) or "no runs"))
    return "\n".join(out) + "\n"
