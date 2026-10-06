"""build12.py - the 12-symbol selection for n = 13: one transport outside the blocks, a (7, 4) block solution inside.

SEL11 is the transportable selection on 11 symbols (K = 10 letters; full rows, short rows and loops without a row,
made by hybrid3.py with a full / short block solution).  Its loops fall into two kinds:
  * loops whose old letters 0 .. 6 stand in the cyclic order of one of the 48 left-over loops of the 8-symbol base
    (48 blocks of 504 loops): dropped.  In their place the block solution BLOCK4 of the (7, 4) block (5,040 loops
    above (0 1 .. 6), added letters 7 8 9 A) is written above every left-over loop D, relabelled i -> D[i].
  * all other loops: their rows are transported once (gcore.transport_row: a full row at x gives the K rows with
    the new letter in front of x[j]; a short row x = u a b the same, except that u a w b becomes b u a w).
BLOCK4 may contain rows of any visible length; such rows have no transport, which is why the block is solved on 12
symbols directly instead of being transported from 11.

The file is written line by line (10! = 3,628,800 lines); only BLOCK4 and one line of SEL11 are in memory.  The
order of the lines is: the rows of SEL11 in its own order, each followed by its transports in the order of the gap;
then the blocks in increasing order of D.  check12.py checks the result.

usage:    python build12.py SEL11 BASE8 BLOCK4 OUT
inputs:   SEL11   selection on 11 symbols, "x T" lines with T = F, S, D or the number of visible classes
          BASE8   Pantone's 8-symbol selection (untransport.py --out); only its loops without a row are used
          BLOCK4  a (7, 4) block solution, "x v" lines (data/block_7_4_n13.txt, found by gsegip.py)
outputs:  OUT     selection on 12 symbols, "x v" lines, LF line ends (53 MB)
needs:    Python 3 and gcore.py.  No other package, no solver.
cost:     measured here: 9 to 13 s, 0.02 GB.
"""
import sys
import time
from gcore import ALPH, canon, read_gsel, transport_row

t0 = time.time()
p10, p7, pblk, out = sys.argv[1:5]
base = read_gsel(p7)
m = len(next(iter(base)))
dets = sorted(L for L, (x, v) in base.items() if v == 0)       # the left-over loops of the 8-symbol base
detset = set(dets)
blk4 = read_gsel(pblk)
K = len(next(iter(blk4)))
assert K == m + 4
fs = False                                  # always the numbers v, never the letters F S D
name = {0: "D", K: "F", K - 2: "S"}
vin = {"F": K - 1, "S": K - 3, "D": 0}      # row types of SEL11 (K - 1 letters) as numbers of visible classes
nout = nblock = nbase = 0
with open(out, "w", newline="\n") as f:
    f.write("# selection on k = %d symbols (K = %d letters, distinguished letter %s): x v  (v visible classes; "
            "%d full, %d short, 0 = loop without a row)%s\n" % (K + 1, K, ALPH[K], K, K - 2, ""))
    f.write("# build12.py %s %s %s: rows outside the blocks transported once, block solution above every left-over loop\n" % (p10, p7, pblk))
    for line in open(p10):
        if line.startswith("#") or not line.strip():
            continue
        a, ty = line.split()[:2]
        x = tuple(ALPH.index(c) for c in a)
        v10 = vin[ty] if ty in vin else int(ty)
        assert len(x) == K - 1 and v10 in (K - 1, K - 3, 0), "SEL11 must have full and short rows only"
        if canon(tuple(c for c in x if c < m)) in detset:      # a loop of a block: replaced below
            nblock += 1
            continue
        assert v10, "a loop without a slice outside the blocks"
        for y in transport_row(x, v10):
            v = v10 + 1
            f.write("".join(ALPH[c] for c in y) + " " + (name[v] if fs else str(v)) + "\n")
            nout += 1
        nbase += 1
    for D in dets:                          # the block solution above D: old letter i becomes D[i]
        phi = list(D) + list(range(m, K))
        for L, (x, v) in blk4.items():
            y = tuple(phi[c] for c in x)
            if v == 0:
                y = canon(y)
            f.write("".join(ALPH[c] for c in y) + " " + (name[v] if fs else str(v)) + "\n")
            nout += 1
print("rows of %s outside the blocks: %d (x %d by transport), inside (dropped): %d; blocks: %d x %d loops" % (
    p10, nbase, K - 1, nblock, len(dets), len(blk4)))
print("wrote %s: %d rows  (%.0fs)" % (out, nout, time.time() - t0))
