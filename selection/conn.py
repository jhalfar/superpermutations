"""conn.py - connector cycles for the completion of a selection of full and short rows, and the rule that carries
them one level up.

Pantone joins the closed trails of the completion with connector cycles (sections 4 to 6 of his paper): the cycle
of a word v of h = n - 3 letters is v -> rot(v) -> .. -> v; it meets a closed trail when one of its h rotations is a
vertex (an end word of a slice) on that trail.  The coefficient of (n-3)! in his bound is
    Q / (k-2)!  +  (number of cycles that together meet every closed trail) / (n-4)!.
This script is for selections small enough to hold the completion as Python tuples (up to 10 symbols);
conn_big.py does the part with z for 11 symbols.

  python conn.py SEL --cover OUT [--time SEC]
      completes SEL on n = K + 2 symbols, follows the closed trails, and chooses cycles:
        * small trails (of loops without a row; their vertices do not contain z): the cycle of a word v without z
          meets exactly the small trails of the loops "v with its missing letter in one gap", one F-orbit; the
          fewest such cycles that meet all small trails are found by an integer programme (a cover of the loops
          without a row by F-orbits);
        * closed trails of the walks: cycles that contain z, greedy first, then an integer programme on the
          candidates that meet many trails.
      Writes the cycles (one word of h letters per line), checks on the completed graph that every closed trail
      is met, and prints the coefficient for this n and for one level up.
  python conn.py SEL --lift CYCLES
      the check of the rule for one level up, literally: SEL is transported by one letter w and completed on
      n + 1 symbols; every cycle with z is replaced by the h cycles "w in one of its h gaps"; every loop L without
      a row gets the cycle without z of the word L (its K loops above are a whole F-orbit of w).  The program
      counts the closed trails that the new cycles meet and prints ALL MET or NOT ALL MET.

What was run: Pantone's 8-symbol selection (9 to 10 symbols: 49 cycles become 54 and meet all 364 closed trails)
and the 9-symbol selection of n = 10 (10 to 11 symbols: 52 cycles become 364 and meet all 2,800).  These two runs
are the evidence that the rule also holds for walks in which k - 2 does not divide f - t; it is not proved here.

usage:    as above.
inputs:   SEL: a selection of full and short rows ("x v" lines or F S D, or construction-input.txt);
          CYCLES: one word of h letters per line, # for comments.
outputs:  --cover: the file OUT and text; --lift: text.
needs:    Python 3 and gcore.py; --cover also needs Gurobi with its Python package gurobipy.
          Gurobi needs a full licence: academic licences are free, and the size-limited licence that
          comes with the package is too small for these models.
cost:     measured here: --lift on the 9-symbol selection 2 s, 0.2 GB; --cover on it under 1 s.
"""
import argparse
import time
from array import array
from collections import Counter, defaultdict
from fractions import Fraction
from math import factorial

from gcore import read_any, transport, canon

ALPH = "0123456789ABCDEFGHIJ"


def complete(sel):
    """The completion of a selection of full and short rows, as end words: returns K and a list of (head, tail,
    kind) per slice, head and tail as tuples of h = K - 1 letters; kind 0 = inserted slice, 1 = repair slice of
    a short row, 2 = repair slice of a loop without a row."""
    K = len(next(iter(sel)))
    s, z = K, K + 1
    h = K - 1                       # n - 3 with n = K + 2
    out = []
    for L0, (x, L) in sel.items():
        assert L in (K, K - 2, 0), "full and short rows only"
        if L:
            for i in range(K):
                y = x[:i] + (z,) + x[i:]
                v = L + 1 if i < L else L
                r = (v + 1) % (K + 1)
                out.append((y[:h], (y[r:] + y[:r])[:h], 0))
        for i in range(L, K):
            y = x[i:] + x[:i] + (s,)
            out.append((y[:h], y[1:h + 1], 1 if L else 2))
    return K, out


def trails(slices):
    """Follow the closed trails of the completed endpoint graph.  Returns (trail number of every slice, number of
    trails, for every trail whether it is a small trail, dict head -> slice)."""
    nxt = {}
    for i, (hd, tl, kind) in enumerate(slices):
        assert hd not in nxt, "out-degree 2"
        nxt[hd] = i
    tid = array("l", [-1]) * len(slices)
    nt = 0
    small = []
    for i0 in range(len(slices)):
        if tid[i0] >= 0:
            continue
        i = i0
        allD = True
        while tid[i] < 0:
            tid[i] = nt
            allD &= slices[i][2] == 2
            i = nxt[slices[i][1]]
        assert i == i0
        small.append(allD)
        nt += 1
    return tid, nt, small, nxt


def zrot(v, z):
    """The rotation of the word v that starts with z: the name of its cycle."""
    i = v.index(z)
    return v[i:] + v[:i]


def cover(sel, out, tlimit):
    """Choose cycles that meet every closed trail of the completion of sel, write them to `out`, print the
    coefficient.  tlimit: seconds for each of the two integer programmes."""
    t0 = time.time()
    K, sl = complete(sel)
    n, h, z = K + 2, K - 1, K + 1
    tid, nt, small, nxt = trails(sl)
    nsmall = sum(small)
    print("completion on n = %d symbols: %d slices, %d closed trails (%d small trails of loops without a slice, %d walk trails)  %.0f s" % (
        n, len(sl), nt, nsmall, nt - nsmall, time.time() - t0), flush=True)
    vert = {hd: tid[i] for i, (hd, tl, kind) in enumerate(sl)}
    cycles = []
    # ---- small trails: z-free cycles.  The cycle of v (h letters, missing one old letter e) meets the small trails of
    # the loops v + e in gap j.  Cover the loops without a row by such orbits (integer programme).
    dl = [L for L, (x, v) in sel.items() if v == 0]
    if dl:
        import gurobipy as gp
        from gurobipy import GRB
        dset = set(dl)
        orbs = {}
        for L in dl:
            for e in L:
                i = L.index(e)
                v = canon(L[:i] + L[i + 1:]) if e != 0 else L[i + 1:] + L[:i]
                # canonical cyclic word of the other letters: rotate the least letter first
                j = v.index(min(v))
                v = v[j:] + v[:j]
                orbs.setdefault((v, e), set()).add(L)
        whole = sum(1 for o in orbs.values() if len(o) == K - 1)
        print("loops without a slice: %d; F-orbits that contain some: %d, of which whole (%d loops): %d" % (len(dl), len(orbs), K - 1, whole), flush=True)
        m = gp.Model()
        m.Params.OutputFlag = 0
        m.Params.TimeLimit = tlimit
        m.Params.Threads = 2
        keys = list(orbs)
        xv = [m.addVar(vtype=GRB.BINARY, obj=1.0) for _ in keys]
        by = defaultdict(list)
        for q, key in enumerate(keys):
            for L in orbs[key]:
                by[L].append(xv[q])
        for L in dl:
            m.addConstr(gp.quicksum(by[L]) >= 1)
        m.optimize()
        zf = [keys[q][0] for q in range(len(keys)) if xv[q].X > 0.5]
        print("z-free cycles: %d (bound %.1f; the least possible is %d loops / %d = %.1f)" % (
            len(zf), m.ObjBound, len(dl), K - 1, len(dl) / (K - 1)), flush=True)
        for v in zf:
            # check on the completed graph: the rotations of v are vertices of small trails
            assert any(v[j:] + v[:j] in vert for j in range(h))
            cycles.append(v)
    # ---- walk trails: cycles with z
    big = [t for t in range(nt) if not small[t]]
    cand = defaultdict(set)
    for hd, t in vert.items():
        if z in hd and not small[t]:
            cand[zrot(hd, z)].add(t)
    hist = Counter(len(v) for v in cand.values())
    print("walk trails %d; candidate cycles with z: %d; by number of trails met: %s  %.0f s" % (
        len(big), len(cand), dict(sorted(hist.items())), time.time() - t0), flush=True)
    # greedy
    unc = set(big)
    chosen = []
    bytrail = defaultdict(list)
    for v, ts in cand.items():
        for t in ts:
            bytrail[t].append(v)
    gain = {v: len(ts) for v, ts in cand.items()}
    buckets = defaultdict(set)
    for v, g_ in gain.items():
        buckets[g_].add(v)
    top = max(buckets) if buckets else 0
    while unc:
        while top > 0 and not buckets[top]:
            top -= 1
        v = buckets[top].pop()
        g_ = len(cand[v] & unc)
        if g_ < top:
            buckets[g_].add(v)
            continue
        chosen.append(v)
        unc -= cand[v]
    print("greedy: %d cycles with z for %d walk trails (least possible %d)" % (len(chosen), len(big), -(-len(big) // h)), flush=True)
    # integer program on the candidates that meet many trails
    try:
        import gurobipy as gp
        from gurobipy import GRB
        thr = max(2, max(hist) - 3)
        keys = [v for v, ts in cand.items() if len(ts) >= thr] + chosen
        keys = list(dict.fromkeys(keys))
        if len(keys) > 400000:
            keys = keys[:400000] + chosen
            keys = list(dict.fromkeys(keys))
        m = gp.Model()
        m.Params.OutputFlag = 0
        m.Params.TimeLimit = tlimit
        m.Params.Threads = 2
        xv = [m.addVar(vtype=GRB.BINARY, obj=1.0) for _ in keys]
        by = defaultdict(list)
        for q, v in enumerate(keys):
            for t in cand[v]:
                by[t].append(xv[q])
        for t in big:
            m.addConstr(gp.quicksum(by[t]) >= 1)
        cs = set(chosen)
        for q, v in enumerate(keys):
            xv[q].Start = 1 if v in cs else 0
        m.optimize()
        if m.SolCount:
            ch2 = [keys[q] for q in range(len(keys)) if xv[q].X > 0.5]
            print("integer program on %d candidates: %d cycles (bound %.1f)" % (len(keys), len(ch2), m.ObjBound), flush=True)
            if len(ch2) < len(chosen):
                chosen = ch2
    except Exception as e:
        print("integer program skipped:", e)
    met = set()
    for v in chosen:
        for j in range(h):
            w = v[j:] + v[:j]
            if w in vert:
                met.add(vert[w])
    assert set(big) <= met
    cycles += chosen
    # final check: every closed trail is met
    met = set()
    for v in cycles:
        for j in range(h):
            w = v[j:] + v[:j]
            if w in vert:
                met.add(vert[w])
    assert len(met) == nt, "not all closed trails are met"
    with open(out, "w") as f:
        for v in cycles:
            f.write("".join(ALPH[c] for c in v) + "\n")
    t = sum(1 for (x, v) in sel.values() if v == K - 2)
    cQ = Fraction(2 * t, factorial(K - 1))
    cC = Fraction(len(cycles), factorial(n - 4))
    print("all %d closed trails are met by %d cycles (%d z-free, %d with z); wrote %s" % (nt, len(cycles), len(cycles) - len(chosen), len(chosen), out))
    print("coefficient with these cycles at n = %d:  %s + %s = %s = %.6f   (floor %.6f)" % (
        n, cQ, cC, cQ + cC, cQ + cC, cQ + Fraction(nt, factorial(K - 1))))
    # one level up (n + 1): every loop L without a row has the K loops above it without a row, a whole F-orbit of
    # the new letter, met by the z-free cycle of the word L; the cycles with z are transported (h cycles each).
    c1 = Fraction(len(dl) + h * len(chosen), factorial(n - 3))
    print("one level up (n = %d): %d z-free cycles (one per loop without a slice) + %d x %d transported cycles with z:" % (
        n + 1, len(dl), h, len(chosen)))
    print("   coefficient  %s + %s = %s = %.6f     [193/360 = %.6f, 4061/7560 = %.6f]" % (
        cQ, c1, cQ + c1, cQ + c1, 193 / 360, 4061 / 7560))
    return cycles


def lift_check(sel, cyc_path):
    """The rule for one level up, checked literally on the transport of sel (see the header)."""
    K = len(next(iter(sel)))
    h = K - 1
    cyc = [tuple(ALPH.index(c) for c in line.split()[0]) for line in open(cyc_path) if line.strip() and not line.startswith("#")]
    # this level
    K0, sl = complete(sel)
    tid, nt, small, nxt = trails(sl)
    vert = {hd: tid[i] for i, (hd, tl, kind) in enumerate(sl)}
    met = set()
    for v in cyc:
        for j in range(h):
            w = v[j:] + v[:j]
            if w in vert:
                met.add(vert[w])
    print("n = %d: %d closed trails, met by the %d cycles: %d" % (K + 2, nt, len(cyc), len(met)))
    # next level: transport renames nothing in our convention: new letter w = K, the distinguished letter becomes K + 1
    # and the completion letter K + 2.  Cycles: old z = K + 1 becomes K + 2, then w = K is put into each of the h gaps.
    sel2 = transport(sel)
    K2, sl2 = complete(sel2)
    tid2, nt2, small2, nxt2 = trails(sl2)
    vert2 = {hd: tid2[i] for i, (hd, tl, kind) in enumerate(sl2)}
    cyc2 = set()
    nz = 0
    for v in cyc:
        if K + 1 not in v:
            continue                      # z-free cycles are chosen afresh at the next level
        nz += 1
        v = tuple(K + 2 if c == K + 1 else c for c in v)
        for g in range(h):
            y = v[:g] + (K,) + v[g:]
            j = y.index(min(y))
            cyc2.add(y[j:] + y[:j])
    nd = 0
    for L, (x, v) in sel.items():
        if v == 0:
            cyc2.add(L)                   # the word L (K letters, without the new letter): canonical, starts with 0
            nd += 1
    print("next level: %d loops without a slice below -> %d z-free cycles; %d cycles with z -> %d transported" % (nd, nd, nz, nz * h))
    cyc = [v for v in cyc if K + 1 in v]
    met2 = set()
    for v in cyc2:
        for j in range(h + 1):
            w = v[j:] + v[:j]
            if w in vert2:
                met2.add(vert2[w])
    print("n = %d: %d closed trails (%d x %d = %d), cycles %d (= %d + %d x %d: %s), trails met: %d  -> %s" % (
        K + 3, nt2, nt, h + 1, nt * (h + 1), len(cyc2), nd, len(cyc), h, len(cyc2) == nd + len(cyc) * h, len(met2),
        "ALL MET" if len(met2) == nt2 else "NOT ALL MET"))


def main():
    """Read the selection and run --cover and / or --lift."""
    ap = argparse.ArgumentParser()
    ap.add_argument("sel")
    ap.add_argument("--cover")
    ap.add_argument("--lift")
    ap.add_argument("--time", type=float, default=120)
    a = ap.parse_args()
    sel = read_any(a.sel)
    if a.cover:
        cover(sel, a.cover, a.time)
    if a.lift:
        lift_check(sel, a.lift)


if __name__ == "__main__":
    main()
