#!/usr/bin/env python
"""smallpos.py - where the cuts of the small trails lie in their pieces (n = 12).

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: smallpos.py BASE.txt BASE.tsv      needs cuts12c.bin; writes smallpos12.npz (read by build12.py)

  BASE.txt  the base word of the piece set (mapped)
  BASE.tsv  its table

The piece set.  These scripts were written for one piece set at n = 12, the first one that beat Pantone's pieces:
the 11-symbol selection with full and short rows only (Q = 178,080).  Its numbers are fixed in the code: 7,200
closed trails, of which the first 6,048 of the table are small trails with 110 cuts each (100 at steps of weight 2,
10 at vertices); then 144 trails of the three short walks of every block (63, 133 and 182 loops, one trail each;
kinds 1 to 3 of the table, "short-walk trails" below); then 1,008 big trails.  Letters: 0 .. 6 are the old letters,
7, 8, 9 the added letters, A the distinguished letter, B the completion letter.

For every cut of every small trail, in the order of the file of cuts, two numbers: start = the offset, in the piece
of the trail, of the window the cut piece begins with; gap = the weight of the step that is cut (3 at a vertex, 2
otherwise).  These are the numbers of a plan line "O t start gap 0".
The cut words are built again from the base word and compared with the file of cuts; the script stops if they
differ.

Needs: Python 3, numpy, c12.py.
All files are read from and written to the working directory.
Time and memory, measured: 4 s, 0.55 GB.
"""
import numpy as np, sys
import c12

C = c12.Cuts("cuts12c.bin", log=print)
tab = [l.split("\t") for l in open(sys.argv[2])]
off = np.array([int(t[3]) for t in tab])
R = np.array([int(t[2]) for t in tab])
word = np.memmap(sys.argv[1], np.uint8, "r")
lut = np.full(256, 255, np.uint8)
lut[np.frombuffer(b"0123456789ABCDEF", np.uint8)] = np.arange(16, dtype=np.uint8)
NS = 6048
n = 12
h = 9
start = np.zeros((NS, 110), np.int32)
gap = np.zeros((NS, 110), np.int8)
wchk = np.zeros((NS, 110), np.int64)
# for every small trail: the positions wp of its permutation windows (a window is a permutation when the bit mask
# of its 12 letters is full), the steps g between consecutive windows, and the cuts at the steps of weight 2 and 3
for t in range(NS):
    s = lut[np.array(word[off[t]:off[t] + R[t]])].astype(np.int64)
    Rt = int(R[t])
    ext = np.concatenate([s, s[:n]])
    m = np.zeros(Rt, np.int64)
    for k in range(n):
        m |= 1 << ext[k:k + Rt]
    wp = np.nonzero(m == (1 << n) - 1)[0]
    g = np.diff(np.concatenate([wp, [wp[0] + Rt]]))
    ci = np.nonzero(g >= 2)[0]
    assert len(ci) == 110 and g.max() <= 3
    S = (wp[ci] + g[ci]) % Rt
    start[t] = S
    gap[t] = g[ci]
    # the cut word: letters from S to the end of the E window = 12 - g letters starting at S
    ext2 = np.concatenate([s, s, s[:n]])
    for j in range(110):
        L = 12 - int(g[ci[j]])
        code = 0
        for a in ext2[S[j]:S[j] + L].tolist():
            code = (code << 4) | a
        wchk[t, j] = code
w = C.col("w", 0, NS * 110).astype(np.int64).reshape(NS, 110)
assert (w == wchk).all(), "the cut words differ from cuts12c.bin"
np.savez("smallpos12.npz", start=start, gap=gap)
print("openings of the small cuts written; words agree with cuts12c.bin; gaps", dict(zip(*np.unique(gap,
    return_counts=True))))
