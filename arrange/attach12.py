#!/usr/bin/env python
"""attach12.py - how cheaply the trails of the walks attach to the small trails (n = 12).

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: attach12.py     needs cuts12c.bin; writes attach12.npz

The piece set.  These scripts were written for one piece set at n = 12, the first one that beat Pantone's pieces:
the 11-symbol selection with full and short rows only (Q = 178,080).  Its numbers are fixed in the code: 7,200
closed trails, of which the first 6,048 of the table are small trails with 110 cuts each (100 at steps of weight 2,
10 at vertices); then 144 trails of the three short walks of every block (63, 133 and 182 loops, one trail each;
kinds 1 to 3 of the table, "short-walk trails" below); then 1,008 big trails.  Letters: 0 .. 6 are the old letters,
7, 8, 9 the added letters, A the distinguished letter, B the completion letter.

Half letters.  For a cut x written before a cut y, W(x, y) = 2 (h - k) + D_x + D_y, where k is the largest number of
letters (at most h = 9) in which the end of the piece cut at x agrees with the start of the piece cut at y, and D is
the cost of a cut (0 at a vertex, 1 at a step of weight 2).  A join of cost c between two vertices has W = 2 c.
For a word, 2 (cuts + joins) = D(first cut) + sum of W over its joins + D(last cut).

For every cut c of a trail that is not small:  bin(c) = the smallest W(x, c) over all cuts x of small trails,
bout(c) = the smallest W(c, y).  For every small cut the same towards the other trails (out_s, in_s).  All four are
exact minima over all cuts (min-plus over the overlaps, c12.py).
Prints the histograms, and bin + bout per cut separately for the short-walk trails and for the big trails.

What the bound of bound12.py takes from here: the smallest bin + bout over the cuts of the short-walk trails.  It
is 4 on this piece set, so a short-walk trail that stands alone between two small trails costs a W-sum of at least 4.

attach12.npz holds the four arrays (out_s, in_s per small cut; bin, bout per other cut, in the order of the file of
cuts).  No other script reads it.

Needs: Python 3, numpy, c12.py.
All files are read from and written to the working directory.
Time and memory, measured: 80 s, 1.79 GB.
"""
import sys, time, numpy as np, pickle
import c12

log = lambda *x: print(*x, flush=True)
C = c12.Cuts("cuts12c.bin", log=log)
H = lambda a: {int(k): int(v) for k, v in zip(*np.unique(a, return_counts=True))}
h = C.h
NSm = 6048
ns = NSm * 110
w = C.col("w", 0, ns).astype(np.int64)
D = C.D[:ns].astype(np.int64)
exs = w & ((1 << 36) - 1)
ens = w >> (4 * D)
wb = C.col("w", ns, None).astype(np.int64)
Db = C.D[ns:]
exb = wb & ((1 << 36) - 1)
enb = wb >> (4 * Db.astype(np.int64))
del wb
t0 = time.time()
Db64 = Db.astype(np.int64)
out_s = c12.minplus_rev(enb, Db64, exs, h=h) + D  # small exit x -> non-small entry y: W = 2c + D_x + D_y
in_s = c12.minplus(exb, Db64, ens, h=h) + D
print("small cut and a non-small cut, smallest W: out", H(out_s), "in", H(in_s), "(%.0fs)" % (time.time() - t0))
bin_ = (c12.minplus(exs, D, enb, h=h) + Db64).astype(np.int8)
bout = (c12.minplus_rev(ens, D, exb, h=h) + Db64).astype(np.int8)
del exb, enb, Db64
HB = lambda a: {int(k): int(v) for k, v in enumerate(np.bincount(a)) if v}
print("non-small cut: smallest W from a small cut", HB(bin_), "; to a small cut", HB(bout))
sm_ = (bin_ + bout).astype(np.int8)
print("  sum of both for one cut:", HB(sm_))
kt = C.kind[C.t[ns:]]
for name, m in (("short-walk trails", kt <= 3), ("big trails", kt >= 4)):
    print("  %s: in+out %s" % (name, HB(sm_[m])))
np.savez("attach12.npz", out_s=out_s.astype(np.int8), in_s=in_s.astype(np.int8), bin=bin_, bout=bout)
