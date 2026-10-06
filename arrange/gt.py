#!/usr/bin/env python
"""gt.py - for every group of small trails the table of its traversals in one run.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: gt.py BASE.txt OUT.npz [--cmax C]

  BASE.txt  a base word of Pantone's form with groups of small trails (n = 10)
  OUT.npz   T[g][x_in, x_out] = the smallest W-sum of the joins of a path through all trails of group g that enters
            at cut x_in (first trail) and leaves at cut x_out (last trail), every trail written once from one cut;
            closed[g][q] = the smallest W-sum of a closed tour through all trails of the group with the trail of
            q cut at q.  Only joins with W below 2 (C + 1) are used (C = 4: W < 10); a pair that needs another join
            has the value 10000.  Cuts are numbered inside their group.

Exact: a dynamic programme over the subsets of the trails of a group, for all pairs of cuts at once.
Prints, for some groups, how many pairs have each value up to 16 and the values of the closed tours.

Needs: Python 3, numpy, top.py, grp.py, countn.py, tm.py.
Time and memory, measured at n = 10: 31 s and 0.29 GB for the 48 groups.
"""
import sys
import time
import numpy as np
import top
import grp

BIG = 10000


def table(G):
    """(T, closed) of one group.  g[S][x_in, x] = the cheapest path through exactly the trails of S from x_in to x."""
    k, m = G.k, G.m
    full = (1 << k) - 1
    g = [None] * (1 << k)
    for t in range(k):
        v = np.full((m, m), BIG, np.int16)
        ct = G.cuts_of[t]
        v[ct, ct] = 0
        g[1 << t] = v
    for S in range(1, full):
        cur = g[S]
        if cur is None:
            continue
        rows = np.nonzero((cur < BIG).any(1))[0]
        for t in range(k):
            if (S >> t) & 1:
                continue
            at, bt, wt, st, ub = G.arcs[t]
            Tm = S | (1 << t)
            if g[Tm] is None:
                g[Tm] = np.full((m, m), BIG, np.int16)
            vals = np.minimum.reduceat(cur[np.ix_(rows, at)] + wt[None, :].astype(np.int16), st, axis=1)
            sub = g[Tm][np.ix_(rows, ub)]
            g[Tm][np.ix_(rows, ub)] = np.minimum(sub, np.minimum(vals, BIG))
        if S != full:
            g[S] = None if bin(S).count("1") > 1 else g[S]
    Tt = g[full]
    # closing join x_out -> x_in
    Wm = np.full((m, m), BIG, np.int16)
    for t in range(k):
        at, bt, wt, st, ub = G.arcs[t]
        Wm[at, bt] = wt
    closed = (Tt.astype(np.int32) + Wm.T.astype(np.int32)).min(1)
    return Tt, np.minimum(closed, BIG).astype(np.int16)


if __name__ == "__main__":
    log = lambda *x: print(*x, flush=True)
    cmax = int(sys.argv[sys.argv.index("--cmax") + 1]) if "--cmax" in sys.argv else 4
    T = top.Top(sys.argv[1], cmax=cmax, log=lambda *x: None)
    t0 = time.time()
    Ts, Cs = [], []
    for g in range(T.NG):
        G = grp.Group(T, g)
        Tt, cl = table(G)
        Ts.append(Tt); Cs.append(cl)
        if g < 2 or (g + 1) % 8 == 0:
            h = {int(a): int(b) for a, b in zip(*np.unique(Tt[Tt < BIG], return_counts=True)) if a <= 16}
            hc = {int(a): int(b) for a, b in zip(*np.unique(cl, return_counts=True))}
            log("group %d: T values (<= 16) %s; closed tours %s  (%.0fs)" % (g, h, hc, time.time() - t0))
    np.savez_compressed(sys.argv[2], T=np.stack(Ts), closed=np.stack(Cs))
