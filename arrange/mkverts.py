#!/usr/bin/env python
"""mkverts.py - the list of vertices at which lift13.py lets an n = 12 trail be cut.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: mkverts.py OUT.txt SEL      needs cuts12c.bin

  OUT.txt  one vertex per line as a 9-letter word in the letters of the base word (0-9, A, B), sorted
  SEL      the 11-symbol selection with full and short rows

The piece set.  These scripts were written for one piece set at n = 12, the first one that beat Pantone's pieces:
the 11-symbol selection with full and short rows only (Q = 178,080).  Its numbers are fixed in the code: 7,200
closed trails, of which the first 6,048 of the table are small trails with 110 cuts each (100 at steps of weight 2,
10 at vertices); then 144 trails of the three short walks of every block (63, 133 and 182 loops, one trail each;
kinds 1 to 3 of the table, "short-walk trails" below); then 1,008 big trails.  Letters: 0 .. 6 are the old letters,
7, 8, 9 the added letters, A the distinguished letter, B the completion letter.

The list is the input of the option --gap3-list of tools/segins_gpu: with it the passes at n = 12 use only cuts
that lift to n = 13, so that they optimise the n = 13 length directly.
It is computed as in the first part of lift13.py: a small trail keeps all its 10 vertices; a walk trail keeps the
vertices that are candidate cuts of its chain at n = 13 (the first words b[:9] and b[1:10] at every full row b of
the transported walk).  The script asserts that every candidate is a vertex of n = 12 and that no vertex word occurs
in two cuts.
On this piece set: 60,480 + 3,222,240 = 3,282,720 of the 3,628,800 vertices (33 MB of text, SHA-256 b7e4e973...
db8fef for the list I used).

Needs: Python 3, numpy; c12.py; gen12.py and gen13.py next to this file or on PYTHONPATH.
All files are read from and written to the working directory.
Time and memory, measured: 44 s, 1.90 GB.
"""
import sys, os, time
import numpy as np

out = sys.argv[1]
import gen12 as G
import gen13 as G13
import c12

log = lambda *x: print(*x, flush=True)
SEL = sys.argv[2]
NS12 = 6048
K2 = 11
t0 = time.time()
C = c12.Cuts("cuts12c.bin", log=log)
D = C.D
skc = C.col("sk", 0, None)
wall = C.w
v0 = np.nonzero((D == 0) & (skc == 0))[0]  # plain weight-3 cuts
wv = wall[v0].copy()
tv = C.t[v0].copy()
assert len(np.unique(wv)) == len(wv), "a vertex word occurs in two cuts"
log("n = 12: %d vertices (plain weight-3 cuts), all different words; on small trails %d" % (len(v0),
    int((tv < NS12).sum())))
rows = G.read_sel(SEL)
walks = sorted(G.sel_walks([r for r in rows if r[2] >= 0]), key=len)
RELAB = list(range(16))
RELAB[10] = 11
cc = []
for wi, wk in enumerate(walks):
    for li, W2 in enumerate(G13.transport_walk(wk)):
        for i0, r in enumerate(W2):
            if r[2] == K2:
                bb = r[0]
                for S in (bb[:9], bb[1:10]):
                    c = 0
                    for a in S:
                        c = (c << 4) | RELAB[a]
                    cc.append(c)
cc = np.unique(np.array(cc, np.int64))
ws = np.sort(wv)
p = np.minimum(np.searchsorted(ws, cc), len(ws) - 1)
assert (ws[p] == cc).all(), "a candidate of a walk chain is not a vertex of n = 12"
small = wv[tv < NS12]
allv = np.unique(np.concatenate([small, cc]))
assert len(allv) == len(small) + len(cc)
log("allowed: %d vertices of small trails + %d candidate vertices of walk trails = %d of %d (%.0fs)" % (len(small),
    len(cc), len(allv), len(wv), time.time() - t0))
AL = "0123456789ABCDEF"
with open(out, "w", newline="\n") as f:
    buf = []
    for code in allv.tolist():
        buf.append("".join(AL[(code >> (4 * (8 - i))) & 15] for i in range(9)))
        if len(buf) == 100000:
            f.write("\n".join(buf) + "\n")
            buf = []
    if buf:
        f.write("\n".join(buf) + "\n")
log("wrote %s: %d words (%.0fs)" % (out, len(allv), time.time() - t0))
