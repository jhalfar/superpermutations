"""gapply.py - put one block solution above every left-over loop of a selection (the n = 11 selection, first step).

BASE is a selection on K letters; for n = 11 it is Pantone's 10-symbol selection (K = 9), read from his
construction-input.txt.  In that file the loops above the 48 left-over loops of his 8-symbol selection carry full
rows, which form closed walks of K - 1 full rows.  Such a walk gives K - 1 closed trails after completion, as many
as its K - 1 loops give when they have no row at all, so these walks are turned into loops without a row first.
The loops without a row then fall into blocks: a block is the set of all loops whose old letters 0 .. m-1 stand in
one cyclic order D (48 blocks of 56 loops for K = 9, m = 7).  BLOCK is a solution of the (m, K - m) block above
(0 1 .. m-1), found by gblock.py; it is carried above every D by the relabelling i -> D[i] of the old letters
(the added letters m .. K-1 keep their names).  A row of a block solution never exchanges two old letters, so the
rest of the selection is not touched and the result is balanced again.

usage:    python gapply.py BASE BLOCK OUT [--m 7] [--literal]
inputs:   BASE   construction-input.txt, or a selection file ("x v" lines, see gcore.py)
          BLOCK  a block solution ("x v" lines for the loops of the (m, K - m) block)
outputs:  OUT    the selection, "x v" lines in increasing order of the loops, LF line ends
          text:  Q, loops without a row, walks and closed trails of BASE and of the result; with --literal the
                 closed trails are counted again in the endpoint graph of all slices of the completion and the
                 program fails unless that count and the number of slices K! + Q agree with the port rule
needs:    Python 3 and gcore.py.  No other package, no solver.
cost:     measured here for n = 11 with --literal: 3 s, 0.2 GB.
"""
import math
import sys
from collections import defaultdict

from gcore import canon, read_any, read_gsel, write_gsel, walks, report, literal_trails


def main():
    """Read BASE and BLOCK, empty the walks of full rows, find the blocks, relabel BLOCK into each, write OUT."""
    base = read_any(sys.argv[1])
    block = read_gsel(sys.argv[2])
    out = sys.argv[3]
    m = int(sys.argv[sys.argv.index("--m") + 1]) if "--m" in sys.argv else 7
    K = len(next(iter(base)))
    ws, chosen = walks(base)
    for w in ws:
        if all(chosen[x] == K for x in w):
            for x in w:
                base[canon(x)] = (canon(x), 0)
    r0 = report(base, "base: ")
    blocks = defaultdict(list)
    for L, (x, v) in base.items():
        if v == 0:
            y = tuple(c for c in L if c < m)
            i = y.index(0)
            blocks[y[i:] + y[:i]].append(L)
    size = math.factorial(K - 1) // math.factorial(m - 1)
    assert all(len(b) == size for b in blocks.values()), "a block is not complete"
    assert len(block) == size
    sel = dict(base)
    for D, Ls in blocks.items():
        phi = list(D) + list(range(m, K))
        got = set()
        for L, (x, v) in block.items():
            y = tuple(phi[c] for c in x)
            c = canon(y)
            assert base[c][1] == 0, "block solution leaves the block"
            sel[c] = (y if v else c, v)
            got.add(c)
        assert got == set(Ls)
    r1 = report(sel, "with the block solution in %d blocks: " % len(blocks))
    write_gsel(out, sel, "gapply.py %s + %s (m = %d, %d blocks): floor %d = Q %d + D %d + walk trails %d" % (
        sys.argv[1], sys.argv[2], m, len(blocks), r1[0], r1[4], r1[5], r1[2]))
    print("wrote", out)
    if "--literal" in sys.argv:
        lit, nsl = literal_trails(sel)
        print("literal endpoint graph of the completion: %d closed trails (formula %d), %d slices (K! + Q = %d)" % (
            lit, r1[2] + r1[5], nsl, math.factorial(K) + r1[4]))
        assert lit == r1[2] + r1[5] and nsl == math.factorial(K) + r1[4]


if __name__ == "__main__":
    main()
