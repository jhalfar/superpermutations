"""gcover.py - coverage check of the completion of a selection, straight from the completion rule.

An independent checker: it imports nothing from this directory, uses no ports and spells no word.  For a selection
on K letters (distinguished letter s = K, completion letter z = K + 1, n = K + 2 symbols) it writes down the slices
of the completion,

    row (x, v):             (x with z in front of x[j], s, v + [j < v] classes),  j = 0 .. K-1
                            (rot(x, i) s, z, K + 1 classes),                      i = v .. K-1
    loop L without a row:   (rot(L, i) s, z, K + 1 classes),                      i = 0 .. K-1

lists the cyclic classes [rot(b, j) d], j = 0 .. c-1, of every slice (b, d, c), and checks
    1. one line per 2-loop, (K-1)! lines;
    2. closure under the step: the row after (x, v) is the row of its loop, at exactly that state;
    3. the number of slices is K! + Q;
    4. the class visits are (n-1)! in number and all different: every cyclic class on n symbols lies in exactly
       one slice, so the pieces contain every permutation.

usage:    python gcover.py SELECTION
inputs:   a selection file ("x v" lines; F, S, D are read for K, K - 2, 0).
outputs:  two lines of text; exit status 0 when everything holds, 1 otherwise.
needs:    Python 3 and numpy.
cost:     the class visits are held as Python integers before they go into one array, so memory grows with (n-1)!:
          measured here n = 10: 1 s, 0.1 GB; n = 11: 10 s, 0.5 GB.  n = 12 has eleven times as many and was not
          tried; use check12.py and the generator of the reproduction package there.
"""
import math
import sys

import numpy as np

ALPH = "0123456789ABCDEF"


def main():
    """Read the selection, check closure, enumerate the class visits of all slices, compare the counts."""
    rows = []
    for line in open(sys.argv[1]):
        if line.startswith("#") or not line.strip():
            continue
        a, ty = line.split()[:2]
        x = tuple(ALPH.index(c) for c in a)
        K = len(x)
        v = {"F": K, "S": K - 2, "D": 0}[ty] if ty in "FSD" else int(ty)
        rows.append((x, v))
    K = len(rows[0][0])
    s, z, n = K, K + 1, K + 2

    def canon(x):
        """the 2-loop of the state x: its rotation that starts with 0"""
        i = x.index(0)
        return x[i:] + x[:i]
    loops = {canon(x): (x, v) for x, v in rows}
    assert len(loops) == len(rows) == math.factorial(K - 1), "not one line per loop"
    for x, v in rows:                                   # closure under the step
        if v == 0:
            continue
        assert v != K - 1 and 1 <= v <= K
        y = x[1:K - 1] + (x[0], x[K - 1]) if v == K else x[v + 1:] + x[:v - 1] + (x[v], x[v - 1])
        ny = loops[canon(y)]
        assert ny[1] > 0 and ny[0] == y, "the step from %s leaves the selection" % (x,)
    Q = sum(K - v for x, v in rows if v)
    codes = []
    nsl = 0
    pw = [n ** i for i in range(n - 1, -1, -1)]

    def add(b, d, c):
        """one slice (b, d, c): note its c cyclic classes, each as the base-n number of its rotation that
        starts with the letter 0"""
        nonlocal nsl
        nsl += 1
        m = len(b)
        for j in range(c):
            cyc = b[j:] + b[:j] + (d,)
            i = cyc.index(0)
            cyc = cyc[i:] + cyc[:i]
            code = 0
            for q in range(n):
                code += cyc[q] * pw[q]
            codes.append(code)
    for x, v in rows:
        if v:
            for j in range(K):
                add(x[:j] + (z,) + x[j:], s, v + (1 if j < v else 0))
            for i in range(v, K):
                add(x[i:] + x[:i] + (s,), z, K + 1)
        else:
            for i in range(K):
                add(x[i:] + x[:i] + (s,), z, K + 1)
    a = np.array(codes, dtype=np.int64)
    u = np.unique(a)
    print("K = %d, n = %d: Q = %d, slices %d (K! + Q = %d), class visits %d, distinct classes %d, (n-1)! = %d" % (
        K, n, Q, nsl, math.factorial(K) + Q, len(a), len(u), math.factorial(n - 1)))
    ok = nsl == math.factorial(K) + Q and len(a) == len(u) == math.factorial(n - 1)
    print("every class exactly once:", ok)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
