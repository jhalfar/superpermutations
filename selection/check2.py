"""check2.py - checker of a selection with rows of any visible length, from the letters of the slices.

An independent checker: it imports nothing from this directory.  Every row is spelled letter by letter from the
definition of a 2-loop (section 2 of the paper), and head and tail are taken as the first and last k - 3 letters of
that word.  For a selection on K letters (k = K + 1 symbols, distinguished letter s = K):

  1. one line per 2-loop, (K-1)! lines;
  2. the endpoint graph of the rows has in-degree and out-degree one at every vertex it uses, so the rows fall
     into closed walks and the closed trails are forced;
  3. Q = sum of (K - v) over the rows;
  4. for every closed walk the number of closed trails after completion, by composing the port permutations
     (the rule is written out again in this file);
  5. the floor constant (Q + closed trails after completion) / (K-1)!.
With --complete (K <= 9) the completion on n = K + 2 symbols is built literally: every inserted and repair slice
is spelled, every cyclic class must occur exactly once, and the closed trails are counted in the completed endpoint
graph; the count must agree with point 4.

usage:    python check2.py SELECTION [--complete]
inputs:   a selection file ("x v" lines; F, S, D are read for K, K - 2, 0).
outputs:  text on standard output; the program fails on the first check that does not hold, and the last line of
          --complete says AGREE or DISAGREE.
needs:    Python 3.  No other package.
cost:     measured here: 11 symbols (362,880 loops) 12 s and 0.3 GB; 10 symbols 1 s, with --complete 49 s and
          0.85 GB; 9 symbols with --complete 2 s.  For 12 symbols use check12.py.
"""
import sys
from collections import Counter
from fractions import Fraction
from math import factorial

ALPH = "0123456789ABCDEFGHIJ"


def read(path):
    """Read the selection as a list of (x, v)."""
    rows = []
    for line in open(path):
        if not line.strip() or line.startswith("#"):
            continue
        a, ty = line.split()[:2]
        x = tuple(ALPH.index(c) for c in a)
        K = len(x)
        v = {"F": K, "S": K - 2, "D": 0}[ty] if ty in ("F", "S", "D") else int(ty)
        assert 0 <= v <= K and v != K - 1, line
        rows.append((x, v))
    return rows


def cyc_class(p):
    """The cyclic class of a tuple: its rotation that starts with the least letter."""
    i = p.index(min(p))
    return p[i:] + p[:i]


def slice_word(x, s, L):
    """The word of the slice S(x, s; L): start at the permutation x s and go through L cyclic classes of the
    2-loop of (x, s).  Inside a class k - 1 steps of one letter (x' s -> .. -> s x'); between two classes one step
    of two letters (a1 a2 a3 .. ak -> a3 .. ak a2 a1)."""
    p = list(x) + [s]
    k = len(p)
    word = list(p)
    for c in range(L):
        for _ in range(k - 1):
            p = p[1:] + p[:1]
            word.append(p[-1])
        if c < L - 1:
            p = p[2:] + [p[1], p[0]]
            word += [p[-2], p[-1]]
    return word


def port(K, v, i):
    """The port permutation of a row with v visible classes: a trail that enters the row at port i (the inserted
    slice with z in gap i) enters the next row at port port(K, v, i)."""
    if v == K:
        return (i - 1) % (K - 1)
    d = K - v
    if i < v:
        return i + d - 1
    if i == v:
        return d - 2
    return i - v - 1


def main():
    """Run the checks in the order of the list in the header."""
    rows = read([a for a in sys.argv[1:] if not a.startswith("--")][0])
    K = len(rows[0][0])
    k, s, h = K + 1, K, K - 2
    N = factorial(K - 1)
    assert len(rows) == N and len({cyc_class(x) for x, v in rows}) == N, "not exactly one line per 2-loop"
    print("selection on k = %d symbols: %d 2-loops, each once; rows by visible classes: %s" % (
        k, N, dict(sorted(Counter(v for x, v in rows).items(), reverse=True))))
    head, tails = {}, []
    live = [(x, v) for x, v in rows if v > 0]
    for i, (x, v) in enumerate(live):
        w = slice_word(x, s, v)
        assert len(w) == (k + 1) * v + k - 2
        hd = tuple(w[:h])
        assert hd not in head, "a vertex has out-degree 2"
        head[hd] = i
        tails.append(tuple(w[-h:]))
    assert len(set(tails)) == len(tails), "a vertex has in-degree 2"
    assert set(tails) == set(head), "endpoint graph not balanced"
    Q = sum(K - v for x, v in live)
    D = N - len(live)
    seen = [False] * len(live)
    stat = Counter()
    tr = 0
    for i0 in range(len(live)):
        if seen[i0]:
            continue
        P = list(range(K - 1))
        i, n_, q_ = i0, 0, 0
        while not seen[i]:
            seen[i] = True
            v = live[i][1]
            P = [port(K, v, p) for p in P]
            n_ += 1
            q_ += K - v
            i = head[tails[i]]
        assert i == i0
        done = [False] * (K - 1)
        c = 0
        for a in range(K - 1):
            if not done[a]:
                c += 1
                b = a
                while not done[b]:
                    done[b] = True
                    b = P[b]
        tr += c
        stat[(n_, q_, c)] += 1
    print("endpoint graph balanced, all degrees one; closed walks %d; Q = %d; loops without a slice %d" % (sum(stat.values()), Q, D))
    for key in sorted(stat, reverse=True)[:20]:
        print("   %6d x  %6d rows, Q %6d, %d closed trails after completion" % ((stat[key],) + key))
    c = Fraction(Q + tr + D, N)
    print("closed trails after completion (port rule): %d = %d from walks + %d small;  sum R at n = %d: F3 + %d" % (tr + D, tr, D, K + 2, Q))
    print("floor (Q + trails)/(k-2)! = %s = %.6f" % (c, c))
    if "--complete" in sys.argv:
        z = K + 1
        hh = K - 1
        sl = []
        for x, v in rows:
            if v:
                for i in range(K):
                    sl.append((x[:i] + (z,) + x[i:], s, v + 1 if i < v else v))
            for i in range(v, K):
                sl.append((x[i:] + x[:i] + (s,), z, K + 1))
        seenc = set()
        H, T = {}, []
        for j, (y, dist, v) in enumerate(sl):
            yy = y
            for _ in range(v):
                cc = cyc_class(yy + (dist,))
                assert cc not in seenc, "a cyclic class occurs twice"
                seenc.add(cc)
                yy = yy[1:] + yy[:1]
            w = slice_word(y, dist, v)
            assert tuple(w[:hh]) not in H
            H[tuple(w[:hh])] = j
            T.append(tuple(w[-hh:]))
        assert len(seenc) == factorial(K + 1), "a cyclic class is missing"
        done = [False] * len(sl)
        nt = 0
        for j0 in range(len(sl)):
            if done[j0]:
                continue
            nt += 1
            j = j0
            while not done[j]:
                done[j] = True
                j = H[T[j]]
        print("literal completion on n = %d symbols: %d slices = (n-2)! + Q: %s; every class once; closed trails %d -> %s" % (
            K + 2, len(sl), len(sl) == factorial(K) + Q, nt, "AGREE" if nt == tr + D else "DISAGREE"))


if __name__ == "__main__":
    main()
