#!/usr/bin/env python
"""prep_hop.py - the start and end values of the block programme over the big trails (n = 12).

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: prep_hop.py     needs cuts12c.bin; writes hop_src.i16, hop_snk.i16, hop_d.i16 (read by hop12.c)

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

A block is a sequence of cuts of big trails between two "inner" cuts, that is cuts of small or short-walk trails.
For every big cut c, in the order of the file of cuts and as 16-bit numbers:
    hop_src   SRC(c) = 2 min over inner cuts x of W(x, c)      (the block is entered at c)
    hop_snk   SNK(c) = 2 min over inner cuts y of W(c, y)      (the block is left at c)
    hop_d     2 D(c)                                           (the block stands at an end of the word)
The minima are exact, over all inner cuts (min-plus over the overlaps, c12.py).
Prints the histograms of SRC and SNK, the smallest SRC + SNK at one cut (the value of a block of one big trail)
and the number of the first big cut, which hop12 needs as its second argument (2,678,592 on this piece set).

Needs: Python 3, numpy, c12.py.
All files are read from and written to the working directory.
Time and memory, measured: 55 s, 1.70 GB.
"""
import sys, time, numpy as np
import c12

log = lambda *x: print(*x, flush=True)
C = c12.Cuts("cuts12c.bin", log=log)
h = C.h
kt = C.kind[C.t]
nin = int((kt <= 3).sum())
assert (kt[:nin] <= 3).all() and (kt[nin:] >= 4).all()
print("inner cuts (small + short-walk):", nin, "; big cuts:", C.nc - nin)
wi = C.col("w", 0, nin).astype(np.int64)
Di = C.D[:nin].astype(np.int64)
exi = wi & ((1 << 36) - 1)
eni = wi >> (4 * Di)
wb = C.col("w", nin, None).astype(np.int64)
Db = C.D[nin:]
t0 = time.time()
enb = wb >> (4 * Db.astype(np.int64))
src = (2 * (c12.minplus(exi, Di, enb, h=h) + Db)).astype(np.int16)
del enb
exb = wb & ((1 << 36) - 1)
snk = (2 * (c12.minplus_rev(eni, Di, exb, h=h) + Db)).astype(np.int16)
del exb, wb
HB = lambda a: {int(k): int(v) for k, v in enumerate(np.bincount(a)) if v}
print("2 x smallest W from an inner cut:", HB(src), "(%.0fs)" % (time.time() - t0))
print("2 x smallest W to an inner cut:", HB(snk))
print("both ends at one cut (B_1):", int((src.astype(np.int32) + snk).min()))
src.tofile("hop_src.i16")
snk.tofile("hop_snk.i16")
(2 * Db.astype(np.int16)).tofile("hop_d.i16")
print("first big cut", nin)
