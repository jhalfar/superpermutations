"""conn_big.py - connector cycles with z for the walk trails of the completion of an 11-symbol selection.

The same construction as conn.py for a selection too big for tuples (11 symbols: 3.8 million slices on 12
symbols), with the completion held in numpy arrays.  This is the computation behind the coefficient 1771/3456 of
the transportable selection.

Completion (section 3 of the paper): a row at x with L classes (L = K full, K - 2 short, 0 no row), z = K + 1,
s = K:  inserted slices, i = 0 .. K-1:  y = x with z in front of x[i], v = L + 1 (i < L) or L classes;
        repair slices, i = L .. K-1:   y = rot^i(x) s, distinguished letter z, v = K + 1 classes;
        head = y[0 .. h-1],  tail = rot^(v+1)(y)[0 .. h-1],  h = K - 1.
Words are packed 4 bits per letter, first letter highest.  The program checks that every head occurs once and
every tail is the head of exactly one slice, follows the closed trails, and separates the small trails (all their
slices are repair slices of loops without a row) from the closed trails of the walks.

Cycles: every vertex that contains z and lies on a walk trail names a candidate cycle (its rotation that starts
with z).  A greedy choice and then an integer programme (minimum cover, time limit) pick cycles that meet every
walk trail; the result is checked on the completed graph and written.  The loops without a row are dealt with one
level up, as in conn.py: one cycle without z per such loop.  The program prints
    (loops without a row + h * cycles with z) / (n-3)!   and   Q/(K-1)! + that:   the coefficient one level up.

For the transportable selection: 7,200 closed trails at n = 12 (6,048 small, 1,152 of walks), 895,936 candidate
cycles, greedy 218, integer programme 203 (bound 201 when the time limit of 240 s ended it); one level up
6,048 + 9 x 203 = 7,875 cycles and 53/108 + 7875/9! = 1771/3456.  data/zcycles_n12.txt holds the 203 cycles;
cyccheck.c checks them with a separate completion.  Run again here (twice, Gurobi 13.0, --time 240) the program
wrote the same 203 cycles; since the integer programme ends by its time limit, another machine may get others.

usage:    python conn_big.py SEL OUT [--time SEC]
inputs:   SEL: a selection of full and short rows on 11 symbols (hybrid3.py with --fsd or without).
outputs:  OUT: the cycles with z, one word of h letters per line (LF line ends); text on standard output.
needs:    Python 3, numpy, gcore.py, Gurobi with its Python package gurobipy.
          Gurobi needs a full licence: academic licences are free, and the size-limited licence that
          comes with the package is too small for these models.
cost:     measured here with --time 240 on two threads: 4.5 minutes, 2.1 GB (the first run logged 2.75 GB).
"""
import argparse
import time
from collections import Counter, defaultdict
from fractions import Fraction
from math import factorial

import numpy as np

from gcore import read_any

ALPH = "0123456789ABCDEFGHIJ"


def pack(cols):
    """cols: list of h integer arrays (one letter of every word each) -> the words as numbers, 4 bits per letter"""
    k = np.zeros(len(cols[0]), dtype=np.int64)
    for c in cols:
        k = (k << 4) | c
    return k


def main():
    """Complete the selection in arrays, follow the closed trails, choose the cycles with z, check and write."""
    ap = argparse.ArgumentParser()
    ap.add_argument("sel")
    ap.add_argument("out")
    ap.add_argument("--time", type=float, default=300)
    a = ap.parse_args()
    t0 = time.time()
    sel = read_any(a.sel)
    K = len(next(iter(sel)))
    n, h, s, z = K + 2, K - 1, K, K + 1
    assert all(v in (K, K - 2, 0) for (x, v) in sel.values()), "full and short rows only"
    X = np.array([x for (x, v) in sel.values()], dtype=np.int64)             # rows x K
    TY = np.array([v for (x, v) in sel.values()], dtype=np.int64)
    nD = int((TY == 0).sum())
    nS = int((TY == K - 2).sum())
    del sel
    heads, tails, kinds, rows = [], [], [], []
    live = np.nonzero(TY > 0)[0]
    Xl, Ll = X[live], TY[live]
    for i in range(K):                                   # inserted slices
        Y = np.concatenate([Xl[:, :i], np.full((len(Xl), 1), z, dtype=np.int64), Xl[:, i:]], axis=1)      # K + 1 letters
        v = np.where(i < Ll, Ll + 1, Ll)
        r = (v + 1) % (K + 1)
        heads.append(pack([Y[:, j] for j in range(h)]))
        idx = (r[:, None] + np.arange(h)[None, :]) % (K + 1)
        T = np.take_along_axis(Y, idx, axis=1)
        tails.append(pack([T[:, j] for j in range(h)]))
        kinds.append(np.zeros(len(Xl), dtype=np.int8))
    for i in range(K):                                   # repair slices of the classes i >= L
        sub = np.nonzero(TY <= i)[0]
        if len(sub) == 0:
            continue
        Xs = X[sub]
        Y = np.concatenate([np.roll(Xs, -i, axis=1), np.full((len(Xs), 1), s, dtype=np.int64)], axis=1)
        heads.append(pack([Y[:, j] for j in range(h)]))
        tails.append(pack([Y[:, j + 1] for j in range(h)]))
        kinds.append(np.where(TY[sub] == 0, 2, 1).astype(np.int8))
    H = np.concatenate(heads)
    T = np.concatenate(tails)
    Kd = np.concatenate(kinds)
    del heads, tails, kinds
    NS = len(H)
    assert NS == factorial(n - 2) + 2 * nS
    order = np.argsort(H, kind="stable")
    Hs = H[order]
    assert (Hs[1:] != Hs[:-1]).all(), "out-degree 2"
    pos = np.searchsorted(Hs, T)
    assert (Hs[pos] == T).all(), "a tail is not a head"
    nxt = order[pos]
    assert len(np.unique(nxt)) == NS, "in-degree 2"
    # trails by pointer chasing
    nx = nxt.tolist()
    kd = Kd.tolist()
    tid = [-1] * NS
    small = []
    nt = 0
    for i0 in range(NS):
        if tid[i0] >= 0:
            continue
        i, allD = i0, True
        while tid[i] < 0:
            tid[i] = nt
            if kd[i] != 2:
                allD = False
            i = nx[i]
        small.append(allD)
        nt += 1
    tid = np.array(tid, dtype=np.int64)
    small = np.array(small, dtype=bool)
    nsmall = int(small.sum())
    print("completion on n = %d symbols: %d slices, %d closed trails (%d small trails of loops without a slice, %d walk trails)  %.0f s" % (
        n, NS, nt, nsmall, nt - nsmall, time.time() - t0), flush=True)
    assert nsmall == nD
    # vertices with z on walk trails; cycle key = rotation with z first
    digs = [(H >> (4 * (h - 1 - j))) & 15 for j in range(h)]
    zpos = np.full(NS, -1, dtype=np.int64)
    for j in range(h):
        zpos[digs[j] == z] = j
    sel_v = np.nonzero((zpos >= 0) & (~small[tid]))[0]
    mask = (1 << (4 * h)) - 1
    key = np.zeros(len(sel_v), dtype=np.int64)
    Hv, zp = H[sel_v], zpos[sel_v]
    for p in range(h):
        m_ = zp == p
        hv = Hv[m_]
        key[m_] = ((hv << (4 * p)) & mask) | (hv >> (4 * (h - p)))
    tv = tid[sel_v]
    pair = np.unique(np.stack([key, tv], axis=1), axis=0)                 # distinct (cycle, trail)
    ck, start, cnt = np.unique(pair[:, 0], return_index=True, return_counts=True)
    hist = Counter(cnt.tolist())
    big = np.nonzero(~small)[0].tolist()
    print("walk trails %d; candidate cycles with z: %d; by number of trails met: %s  %.0f s" % (
        len(big), len(ck), dict(sorted(hist.items())), time.time() - t0), flush=True)
    thr = max(1, max(hist) - 3)
    cand = {}
    while True:
        keep = np.nonzero(cnt >= thr)[0]
        cand = {int(ck[q]): set(pair[start[q]:start[q] + cnt[q], 1].tolist()) for q in keep}
        covered = set().union(*cand.values()) if cand else set()
        if covered >= set(big) or thr == 1:
            break
        thr -= 1
    print("candidates that meet at least %d trails: %d" % (thr, len(cand)), flush=True)
    # greedy
    unc = set(big)
    chosen = []
    buckets = defaultdict(set)
    for v, ts in cand.items():
        buckets[len(ts)].add(v)
    top = max(buckets)
    while unc:
        while top > 0 and not buckets[top]:
            top -= 1
        v = buckets[top].pop()
        g_ = len(cand[v] & unc)
        if g_ < top:
            if g_ > 0:
                buckets[g_].add(v)
            continue
        chosen.append(v)
        unc -= cand[v]
    lb = -(-len(big) // h)
    print("greedy: %d cycles with z for %d walk trails (least possible %d)" % (len(chosen), len(big), lb), flush=True)
    import gurobipy as gp
    from gurobipy import GRB
    keys = list(cand)
    if len(keys) > 600000:
        keys = sorted(keys, key=lambda v: -len(cand[v]))[:600000]
        keys = list(dict.fromkeys(keys + chosen))
    m = gp.Model()
    m.Params.OutputFlag = 0
    m.Params.TimeLimit = a.time
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
        print("integer program on %d candidates: %d cycles (bound %.1f, status %d)" % (len(keys), len(ch2), m.ObjBound, m.Status), flush=True)
        if len(ch2) <= len(chosen):
            chosen = ch2
    # check on the completed graph: every walk trail has a vertex on a chosen cycle
    vert = dict(zip(Hv.tolist(), tv.tolist()))
    met = set()
    words = []
    for v in chosen:
        w = [(v >> (4 * (h - 1 - j))) & 15 for j in range(h)]
        words.append(w)
        for j in range(h):
            r = w[j:] + w[:j]
            kk = 0
            for c in r:
                kk = (kk << 4) | c
            if kk in vert:
                met.add(vert[kk])
    assert met >= set(big), "a walk trail is not met"
    with open(a.out, "w", newline="\n") as f:
        f.write("# connector cycles with z (letter %s) for the walk trails of the completion of %s on n = %d symbols\n" % (ALPH[z], a.sel, n))
        for w in words:
            f.write("".join(ALPH[c] for c in w) + "\n")
    cQ = Fraction(2 * nS, factorial(K - 1))
    c1 = Fraction(nD + h * len(chosen), factorial(n - 3))
    floor_ = cQ + Fraction(nt, factorial(K - 1))
    print("all %d walk trails are met by %d cycles with z; wrote %s" % (len(big), len(chosen), a.out))
    print("one level up (n = %d): %d z-free cycles (one per loop without a slice) + %d x %d transported cycles with z = %d cycles" % (
        n + 1, nD, h, len(chosen), nD + h * len(chosen)))
    print("   coefficient  %s + %s = %s = %.6f     [floor of the selection %s = %.6f; 193/360 = %.6f; 4061/7560 = %.6f]" % (
        cQ, c1, cQ + c1, cQ + c1, floor_, floor_, 193 / 360, 4061 / 7560))


if __name__ == "__main__":
    main()
