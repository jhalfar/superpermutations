"""untransport.py - is a selection the transport of a selection on one letter less?  Optionally write that selection.

Transport (Pantone, section 4) puts a new letter w into every gap of a row: the K - 1 loops above a loop on K - 1
letters all carry "the same row".  This script goes the other way.  For a selection on K letters and each letter w
it deletes w from every row (a short row whose last letter is w is rotated back first, the inverse of the special
case of the transport) and looks at the K - 1 rows that land on the same loop below: the loop is "consistent" when
they all give one state and one type.

Applied to Pantone's 10-symbol selection (construction-input.txt, K = 9) this shows where it comes from:
  * deleting letter 8: 5,012 of the 5,040 loops below are consistent; on the other 28 the rows above disagree
    (votes 7:1, 6:2 or 5:3).  56 rows of his selection are full where the transport has a short row, or the other
    way round (28 each).  These exchanges join walks: the plain double transport of the 8-symbol selection has 28
    walks besides the full ones, his selection 14.
  * deleting letter 7 from the result: 672 of the 720 loops below are consistent; on the other 48 the seven loops
    above carry seven full rows at seven different states, a closed walk of full rows in which the deleted letter
    moves.  These 48 are the left-over loops: loops without a row of the 8-symbol selection.
So his 10-symbol selection is his 8-symbol selection transported twice, apart from those 56 rows, and the loops
above the 48 left-over loops carry no short row at any level.

With --out the selection below is written for w = the last letter (the one a transport would have added): a loop
gets the state and type that more than half of the rows above it give; a loop whose rows above are all full and
all different gets no row; anything else is an error.  The result is checked to be balanced, transported again,
and compared with the input row by row.
    python untransport.py construction-input.txt --out sel9.txt    # 9 symbols: 4 walks, 336 loops in full walks
    python untransport.py sel9.txt --out base8.txt                 # Pantone's 8-symbol selection, 48 left-over loops

usage:    python untransport.py SELECTION [--out FILE]
inputs:   a selection file or construction-input.txt (see gcore.py).
outputs:  one line of text per letter w; with --out the selection on one letter less (LF line ends) and two more
          lines of text.
needs:    Python 3 and gcore.py.  No other package.
cost:     measured here: K = 9, all letters and --out, 2 s.
"""
import sys
from collections import Counter, defaultdict
from gcore import canon, read_any, write_gsel, walks, transport, exact
p = sys.argv[1]
sel = read_any(p)
K = len(next(iter(sel)))


def below(w):
    """Delete the letter w from every row.  Returns dict loop below -> Counter of the (state, type) that the rows
    above it give; the type is written as on K - 1 letters (full K - 1, short K - 3, no row 0)."""
    low = defaultdict(Counter)
    for L, (y, v) in sel.items():
        xp = tuple(c for c in y if c != w)
        xp = tuple(c - 1 if c > w else c for c in xp)
        if v == K - 2 and y[-1] == w:
            xp = xp[1:] + xp[:1]
        low[canon(xp)][(xp, v - 1 if v else 0)] += 1
    return low


for w in range(K):
    low = below(w)
    cons = sum(1 for v in low.values() if len(v) == 1)
    print("letter %d: %d lower loops, %d consistent (one state and type from all %d loops above)" % (w, len(low), cons, K - 1),
          Counter(len(v) for v in low.values()))
if "--out" in sys.argv:
    out = sys.argv[sys.argv.index("--out") + 1]
    low = below(K - 1)
    new = {}
    votes = Counter()
    for L, cnt in low.items():
        (xp, v), top = cnt.most_common(1)[0]
        if 2 * top > K - 1:                                    # more than half of the rows above agree
            new[L] = (xp if v else L, v)
            if len(cnt) > 1:
                votes[tuple(sorted(cnt.values(), reverse=True))] += 1
        else:                                                  # a walk of full rows in which the letter moves
            assert len(cnt) == K - 1 and all(v == K - 1 for (xp, v) in cnt), "not a transport at loop %r" % (L,)
            new[L] = (L, 0)
    walks(new)                                                 # fails unless the result is balanced
    r = exact(new)
    write_gsel(out, new, "untransport.py %s: letter %d deleted; Q %d, loops without a row %d, closed trails after completion %d" % (
        p, K - 1, r[4], r[5], r[2] + r[5]))
    print("wrote %s: %d loops, Q %d, loops without a row %d, %d walks, floor Q + trails = %d; loops decided by a majority: %s" % (
        out, len(new), r[4], r[5], r[3], r[0], dict(sorted(votes.items(), reverse=True))))
    up = transport(new)
    diff = Counter((up[L][1], sel[L][1]) for L in sel if up[L] != sel[L])
    print("rows of the input that differ from the transport of the result: %d; (visible classes in the transport, in the input): %s" % (
        sum(diff.values()), dict(sorted(diff.items()))))
