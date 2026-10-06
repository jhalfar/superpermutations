"""lit_block.py - literal completion of a block solution: the check of a block that does not use the port rule.

A block solution (the loops above one left-over loop, see gcore.py) is not a whole selection, so the selection
checkers do not read it.  This script completes it on its own:
  * every row and every loop without a row is completed slice by slice (inserted and repair slices), each slice
    with its head and its tail (first and last h = K - 1 letters of its word);
  * every head must occur once and every tail must be the head of exactly one slice (endpoint graph balanced);
  * the closed trails of that graph are counted and compared with the count by the port rule
    (loops without a row + cycles of the port products of the walks), and the number of slices with
    K x loops + Q;
  * no row may exchange two old letters (letters 0 .. 6): otherwise the walk would leave the block.
The program ends with AGREE or fails at the first difference.

usage:    python lit_block.py BLOCKFILE
inputs:   a block solution with 7 old letters ("x v" lines; F, S, D are read for K, K - 2, 0).
outputs:  text on standard output.
needs:    Python 3 and gcore.py.  No other package.
cost:     measured here: the (7, 4) block of n = 13 (5,040 loops, 58,051 slices) under 1 s.
"""
import sys
import gcore
sel = gcore.read_gsel(sys.argv[1])
K = len(next(iter(sel)))
r = gcore.exact(sel)                      # (Q + D + trails, Q + D, walk trails, walks, Q, D) by the port rule
lit, nsl = gcore.literal_trails(sel)      # closed trails and slices of the literal completion
print("%s: %d loops, K = %d" % (sys.argv[1], len(sel), K))
print("  port rule:              Q %d, D %d, walks %d, walk trails %d" % (r[4], r[5], r[3], r[2]))
print("  literal completion:     %d slices (= K x loops + Q = %d: %s), endpoint graph balanced, %d closed trails (= D + walk trails = %d: %s)" % (
    nsl, K * len(sel) + r[4], nsl == K * len(sel) + r[4], lit, r[5] + r[2], lit == r[5] + r[2]))
assert lit == r[5] + r[2] and nsl == K * len(sel) + r[4]
m = 7                                     # old letters: the blocks stand above loops of the 8-symbol selection
bad = 0
for L, (x, v) in sel.items():
    if v == 0:
        continue
    a, b = (x[K - 1], x[0]) if v == K else (x[v - 1], x[v])
    bad += (a < m and b < m)
print("  rows that exchange two old letters (would leave the block): %d" % bad)
assert bad == 0
print("  AGREE")
