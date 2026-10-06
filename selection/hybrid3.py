"""hybrid3.py - a selection on m + r letters: a transported base outside the blocks, one block solution in every block.

This builds the 11-symbol selections (K = 10 = 7 + 3 letters) from which the n = 12 pieces come.

  BASE_M  a selection on m letters; only its loops without a row are used: they are the left-over loops D above
          which the blocks stand (Pantone's 8-symbol selection has 48 of them, m = 7).
  BASE    a selection of full and short rows whose loops without a row are exactly the loops above those D; it is
          transported (Pantone, section 4) until it has m + r letters.  Here: the 9-symbol selection with two
          walks, transported twice.
  r       the number of letters added above BASE_M.
  BLOCK   a solution of the (m, r) block: the loops above (0 1 .. m-1), rows of any visible length that never
          exchange two old letters.  It is carried above every D by the relabelling i -> D[i] of the old letters.
The loops above the left-over loops are a closed sub-problem: transport would leave all of them without a row
(one closed trail each); a block solution replaces that by rows that cost less in Q + closed trails, and nothing
outside the block is touched.  The result is balanced again; the program follows its closed walks and counts
the closed trails after completion by the port rule.

A selection whose block has rows of other visible lengths serves its own n only (such rows have no transport);
with a block of full and short rows the result can be transported further (build12.py does that for n = 13).

usage:    python hybrid3.py BASE_M BASE r BLOCK OUT [--fsd]
          --fsd  write the letters F, S, D instead of the numbers of visible classes (only for a block of full
                 and short rows)
          n = 12 selection:           python hybrid3.py base8.txt n10-selection.txt 3 data/block_7_3_n12.txt OUT
          transportable selection:    python hybrid3.py base8.txt n10-selection.txt 3 data/block_7_3_c.txt OUT --fsd
inputs:   BASE_M, BASE: selection files (or construction-input.txt); BLOCK: a block solution; see gcore.py.
outputs:  OUT   the selection, one line per loop in increasing order of the loops, LF line ends
          text: rows by deficit (K - v; a loop without a row is listed under K), Q, loops without a row, closed
                walks and closed trails after completion, the floor constant (Q + closed trails)/(K-1)!
needs:    Python 3 and gcore.py.  No other package, no solver.
cost:     measured here for K = 10: 6 to 8 s, 0.3 GB.
"""
import math
import sys
from collections import Counter
from fractions import Fraction

from gcore import ALPH, canon, read_any, read_gsel, transport, walks, walk_trails

fsd = "--fsd" in sys.argv
argv = [a for a in sys.argv[1:] if a != "--fsd"]
basem = read_any(argv[0])
base = read_any(argv[1])
r = int(argv[2])
block = read_gsel(argv[3])
out = argv[4]
m = len(next(iter(basem)))
dets = [L for L, (x, v) in basem.items() if v == 0]            # the left-over loops of BASE_M
K = m + r
sel0 = base
while len(next(iter(sel0))) < K:
    sel0 = transport(sel0)
sel = {}
nd0 = 0
for L, (x, v) in sel0.items():                                 # the transported base; its loops without a row
    if v == 0:                                                 # are the places of the blocks
        nd0 += 1
        sel[L] = None
    else:
        sel[L] = (x, v)
assert nd0 == len(dets) * len(block), (nd0, len(dets), len(block))
for D in dets:                                                 # the block solution above D: old letter i -> D[i]
    phi = list(D) + list(range(m, K))
    for L, (x, v) in block.items():
        y = tuple(phi[c] for c in x)
        c = canon(y)
        assert c in sel and sel[c] is None, "a loop above D is not free"
        sel[c] = (y if v else c, v)
assert all(v is not None for v in sel.values())
ws, chosen = walks(sel)                                        # fails unless the selection is balanced
Q = sum(K - v for (x, v) in sel.values() if v)
nd = sum(1 for (x, v) in sel.values() if v == 0)
stat = Counter()
tr = 0
for w in ws:
    g = walk_trails(w, chosen, K)
    tr += g
    stat[(len(w), sum(K - chosen[x] for x in w), g)] += 1
N = math.factorial(K - 1)
print("K = %d, %d loops: rows by deficit %s" % (K, len(sel), dict(sorted(Counter(K - v for (x, v) in sel.values()).items()))))
print("Q = %d, loops without a slice %d, walks %d with %d closed trails after completion; trails at n = %d: %d; sum R = F3(%d) + %d" % (
    Q, nd, len(ws), tr, K + 2, tr + nd, K + 2, Q))
print("floor (this n only: rows of other lengths do not transport): (Q + trails)/(k-2)! = %s = %.6f" % (
    Fraction(Q + tr + nd, N), (Q + tr + nd) / N))
for key in sorted(stat, reverse=True)[:16]:
    print("   %5d walk(s): %6d loops, Q %6d, %d trails" % ((stat[key],) + key))
letter = {K: "F", K - 2: "S", 0: "D"}
if fsd:
    assert all(v in letter for (x, v) in sel.values()), "--fsd needs a selection of full and short rows only"
with open(out, "w", newline="\n") as f:
    f.write("# selection on k = %d symbols, K = %d letters 0..%s, distinguished letter %s; one line per loop: x v, v = visible classes "
            "(%d full, %d short, 0 = no slice)%s\n" % (K + 1, K, ALPH[K - 1], ALPH[K], K, K - 2,
                                                       "; written as the letters F, S, D" if fsd else ""))
    f.write("# hybrid3.py %s : Q = %d, loops without a slice %d, trails after completion %d\n" % (" ".join(argv[0:4]), Q, nd, tr + nd))
    for L in sorted(sel):
        x, v = sel[L]
        f.write("".join(ALPH[c] for c in x) + (" " + letter[v] if fsd else " %d" % v) + "\n")
print("wrote", out)
