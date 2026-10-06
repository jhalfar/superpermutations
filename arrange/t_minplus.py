#!/usr/bin/env python
"""t_minplus.py - test of the min-plus steps of top.py against the direct formula.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: t_minplus.py BASE.txt

top.Top.in_best and out_best compute, for all cuts at once and through tables of k-letter strings, the minimum of
val + scale * W over the cuts of another object.  Here they are compared with the direct formula
W(x, y) = 2 (h - largest overlap <= h) + D_x + D_y on cuts drawn at random (fixed seed), with random values, in
every variant the bounds use: all cuts against all cuts, small cuts into big cuts, big cuts into small cuts, big
cuts among themselves.  Three trials, 2,250 comparisons.  The last line must report 0 differences.
The direct formula itself is compared with the overlap of the parser on 300 random pairs.

Needs: Python 3, numpy, top.py, countn.py, tm.py.  Time and memory, measured at n = 10: 49 s, 0.31 GB.
"""
import sys, numpy as np
import top

T = top.Top(sys.argv[1], cmax=4, log=lambda *x: None)
F = T.F
h = T.h
K = T.K
rng = np.random.default_rng(12345)
V = T.V
allc = np.arange(V)


def wcol(X, y):
    """W(x, y) for all cuts x of X and one cut y, directly"""
    w = np.full(len(X), 2 * h, np.int64)
    for k in range(1, K + 1):
        eq = F.suf[k][X] == F.pre[k][y]
        w = np.where(eq, np.minimum(w, 2 * (h - k)), w)
    return w + T.D[X] + T.D[y]


def wrow(x, Y):
    """W(x, y) for one cut x and all cuts y of Y, directly"""
    w = np.full(len(Y), 2 * h, np.int64)
    for k in range(1, K + 1):
        eq = F.suf[k][x] == F.pre[k][Y]
        w = np.where(eq, np.minimum(w, 2 * (h - k)), w)
    return w + T.D[x] + T.D[Y]


bad = 0
for trial in range(3):
    val = rng.integers(-9, 10, size=V).astype(np.int64)
    gin = T.in_best(val, scale=2)
    gout = T.out_best(val, scale=2)
    # restricted variants as used by the bound
    sm = np.nonzero(T.is_small)[0]
    bg = np.nonzero(~T.is_small)[0]
    lab = T.is_small.astype(np.int64)
    g1 = T.in_best(val[sm], X=sm, Y=bg, lab=lab, scale=2)
    g2 = T.out_best(val[sm], X=bg, Y=sm, lab=lab, scale=2)
    g3 = T.in_best(val[bg], X=bg, Y=bg, scale=2)
    pos_bg = np.full(V, -1, np.int64)
    pos_bg[bg] = np.arange(len(bg))
    for y in rng.choice(V, 150, replace=False):
        w = wcol(allc, y)
        other = T.obj != T.obj[y]
        ref = int((val[other] + 2 * w[other]).min())
        bad += ref != int(gin[y])
        w2 = wrow(y, allc)
        ref = int((val[other] + 2 * w2[other]).min())
        bad += ref != int(gout[y])
    for y in rng.choice(bg, 150, replace=False):
        w = wcol(sm, y)
        bad += int((val[sm] + 2 * w).min()) != int(g1[pos_bg[y]])
        w = wrow(y, sm)
        bad += int((val[sm] + 2 * w).min()) != int(g2[pos_bg[y]])
        w = wcol(bg, y)
        other = T.obj[bg] != T.obj[y]
        bad += int((val[bg][other] + 2 * w[other]).min()) != int(g3[pos_bg[y]])
# the dense formula against the parser's own overlap on random pairs
for _ in range(300):
    a, b = rng.integers(0, V, 2)
    assert T.W(a, b) == int(wrow(a, np.array([b]))[0])
print("min-plus over the tries against the dense formula: %d differences in %d comparisons" % (bad,
    3 * (150 * 2 + 150 * 3)))
