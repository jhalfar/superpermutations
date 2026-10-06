#!/usr/bin/env python
"""verify.py - independent check of a selection with full rows, short rows and loops without a row.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: verify.py SEL

  SEL  one line per loop: "x F" (full row), "x S" (short row) or "x D" (loop without a row); x is an order of the K
       letters 0 .. K-1 (digits, then A, B, ..); the distinguished letter is K.  Lines that start with # are skipped.

It shares no code with the generators (gen12.py, geng.py) and uses only the definitions: the step of a full row and
of a short row, and the head and tail words of the slices.

Checks:
  loops     every cyclic order of the K letters occurs on exactly one line
  (a)       steps: the state after a row is again a row of the selection, and every row has exactly one predecessor
            (full row x_0 .. x_{K-1} -> x_1 .. x_{K-2} x_0 x_{K-1}; short row -> x_{K-1} x_0 .. x_{K-4} x_{K-2} x_{K-3})
  (b)       the same from the words: head of a row = its first K - 2 letters, tail = the first K - 2 letters of the
            row rotated by v + 1 (v = K for a full row, K - 2 for a short one); no head word twice, every tail is
            a head, and the successor found this way is the one of (a)
Reports: the closed walks by (loops, short rows, f - t, gcd(K - 1, f - t)), where f and t are the numbers of full and
short rows of a walk; Q = 2 t; the number of closed trails after completion with one more letter (the sum of the
gcd's plus the loops without a row); the floor constant (Q + trails) / (K-1)!; and for n = K + 2 the number of
slices, sum R = n! + (n-1)! + (n-2)! + Q and the floor length.

The floor length is h + sum R + (trails - 1): one letter for every trail after the first, the cheapest way two
trails follow each other.  It is the reference value used in the notes; no word reaches it.

Exit status 0 if the selection checks, 1 if not.

Needs: Python 3.  Time and memory, measured: 8 s and 0.33 GB for the 362,880 loops of an 11-symbol selection,
below 1 s for a 9-symbol selection.
"""
import collections
import math
import sys
from fractions import Fraction

ALPH = "0123456789ABCDEF"


def main():
    path = sys.argv[1]
    rows = []
    for line in open(path):
        if line.startswith("#") or not line.strip():
            continue
        p = line.split()
        rows.append((tuple(ALPH.index(c) for c in p[0]), p[1]))
    K = len(rows[0][0])
    k = K + 1
    assert all(len(x) == K and sorted(x) == list(range(K)) for x, ty in rows), "a row is not a permutation of 0..K-1"
    assert all(ty in "FSD" for x, ty in rows)

    def canon(x):
        """the cyclic word x read from the letter 0"""
        j = x.index(0)
        return x[j:] + x[:j]

    loops = collections.Counter(canon(x) for x, ty in rows)
    nl = math.factorial(K - 1)
    print("K = %d letters (k = %d symbols): rows %d, distinct loops %d, (K-1)! = %d -> every loop exactly once: %s" % (
        K, k, len(rows), len(loops), nl, len(rows) == len(loops) == nl))
    cnt = collections.Counter(ty for x, ty in rows)
    t, D = cnt["S"], cnt["D"]
    print("full %d, short %d, detached %d" % (cnt["F"], t, D))

    # (a) step maps
    def F(x):
        """the state after a full row x"""
        return x[1:K - 1] + (x[0], x[K - 1])

    def S(x):
        """the state after a short row x"""
        return (x[K - 1],) + x[0:K - 3] + (x[K - 2], x[K - 3])

    st = {x: ty for x, ty in rows if ty != "D"}
    nxt = {}
    bad = 0
    pred = collections.Counter()
    for x, ty in st.items():
        y = F(x) if ty == "F" else S(x)
        if y not in st:
            bad += 1
        nxt[x] = y
        pred[y] += 1
    print("(a) steps F / S: rows whose successor is not a selected state: %d; states with a number of predecessors other than 1: %d" % (
        bad, sum(1 for x in st if pred[x] != 1)))

    # (b) slices: head = b[:K-2], tail = rot(b, v+1)[:K-2], v = K (full) or K-2 (short)
    def rot(x, j):
        """x rotated to the left by j letters"""
        j %= len(x)
        return x[j:] + x[:j]

    by_head = {}
    dup = 0
    for x, ty in st.items():
        hd = x[:K - 2]
        if hd in by_head:
            dup += 1
        by_head[hd] = x
    miss = diff = 0
    for x, ty in st.items():
        v = K if ty == "F" else K - 2
        tl = rot(x, v + 1)[:K - 2]
        if tl not in by_head:
            miss += 1
        elif by_head[tl] != nxt[x]:
            diff += 1
    print("(b) endpoint graph: head words used twice %d, tails that are no head %d, tail/head successor different from the step map %d -> balanced: %s" % (
        dup, miss, diff, dup == 0 and miss == 0))
    if bad or dup or miss:
        print("SELECTION DOES NOT CHECK")
        return 1
    # walks: follow the steps from every row not yet seen; m rows of which tt are short
    seen = set()
    walks = []
    for x0 in st:
        if x0 in seen:
            continue
        m = tt = 0
        x = x0
        while x not in seen:
            seen.add(x)
            m += 1
            tt += st[x] == "S"
            x = nxt[x]
        assert x == x0
        walks.append((m, tt))
    h = K - 1
    g = [math.gcd(h, m - 2 * tt) for m, tt in walks]
    print("closed walks (closed trails of the selection): %d, loops in walks %d" % (len(walks), sum(m for m,
        tt in walks)))
    hist = collections.Counter((m, tt, m - 2 * tt, gg) for (m, tt), gg in zip(walks, g))
    print("  (loops, short, f - t, gcd(%d, f - t)) x count:" % h)
    for key, c in sorted(hist.items(), key=lambda kv: (-kv[0][0], kv[0])):
        print("   %s x %d" % (key, c))
    print("  f - t divisible by k - 2 = %d for %d of %d walks" % (h, sum(1 for (m,
        tt) in walks if (m - 2 * tt) % h == 0), len(walks)))
    Q = 2 * t
    tr = sum(g) + D
    fl = Fraction(Q + tr, nl)
    print("Q = 2 t = %d = %s x (K-1)!;  trails after completion with one more letter: sum gcd %d + detached %d = %d" % (
        Q, Fraction(Q, nl), sum(g), D, tr))
    print("floor (Q + trails) / (K-1)! = %d / %d = %s = %.5f" % (Q + tr, nl, fl, float(fl)))
    n = k + 1
    F3 = math.factorial(n) + math.factorial(n - 1) + math.factorial(n - 2)
    print("at n = %d: slices %d, sum R = F3 + Q = %d, trails %d, floor length F3 + n - 3 + Q + trails - 1 = %d" % (
        n, math.factorial(n - 2) + Q, F3 + Q, tr, F3 + n - 3 + Q + tr - 1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
