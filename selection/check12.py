"""check12.py - checker of a selection with rows of any visible length that fits 12 symbols into 2 GB.

An independent checker: it imports nothing from this directory and holds the selection in numpy arrays (the other
checker, check2.py, keeps every state as a Python tuple and is meant for up to 11 symbols).  The step and the port
permutations are written out again in this file.  For a selection on K letters, distinguished letter s = K:

  1. every line is an ordering of the K letters; every 2-loop (cyclic order) occurs exactly once; (K-1)! lines;
  2. the row after (x, v) starts at the state
         G_K(x) = x[1 .. K-2] x[0] x[K-1],     G_v(x) = x[v+1 ..] x[.. v-2] x[v] x[v-1]   (v <= K - 2);
     that state must be the chosen row of its loop, and every chosen row must follow exactly one row (the endpoint
     graph is balanced and the closed trails are forced);
  3. on a random sample of rows the slice S(x, s; v) is spelled letter by letter from the definition of a 2-loop
     and its last K - 2 letters are compared with the first K - 2 letters of the next row;
  4. the closed walks are followed; for each its cost (sum of K - v) and its number of closed trails after
     completion (cycles of the product of the port permutations); totals Q, D = loops without a row, closed trails;
     the floor constant (Q + closed trails) / (K-1)! as a fraction, and for n = K + 2
         sum R = F3(n) + Q,      floor length = F3(n) + n - 3 + Q + (closed trails) - 1.
What it does not check: that the completion covers every class (gcover.py does, up to n = 11; for n = 12 and 13 the
generator of the reproduction package counts the class visits) and the letters of the words.

usage:    python check12.py SELECTION [--sample N]         (N sampled rows are spelled; default 20,000)
inputs:   a selection file ("x v" lines; F, S, D are read for K, K - 2, 0).
outputs:  text on standard output; the program fails on the first check that does not hold.
needs:    Python 3 and numpy.
cost:     measured here: 12 symbols (3,628,800 loops) 14 to 20 s and 1.0 GB; 11 symbols 2 s, 0.15 GB; 10 symbols
          1 s.
"""
import math
import sys
import time
from collections import Counter
from fractions import Fraction

import numpy as np

ALPH = "0123456789ABCDEFGHIJ"


def port(v, K):
    """The port permutation of a row with v visible classes as a list: a trail that enters the row at port j
    enters the next row at port port(v, K)[j]."""
    if v == K:
        return [(j - 1) % (K - 1) for j in range(K - 1)]
    return [j + K - v - 1 if j < v else (K - v - 2 if j == v else j - v - 1) for j in range(K - 1)]


def slice_word(x, s, L):
    """The word of the slice S(x, s; L): start at the permutation x s, go through L cyclic classes of the 2-loop
    of (x, s).  Inside a class k - 1 steps of one letter; between two classes one step of two letters
    (a1 a2 a3 .. ak -> a3 .. ak a2 a1)."""
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


def main():
    """Read the file into arrays and run the four checks in the order of the list above."""
    t0 = time.time()
    path = sys.argv[1]
    nsample = int(sys.argv[sys.argv.index("--sample") + 1]) if "--sample" in sys.argv else 20000
    toks = []
    with open(path) as f:
        for line in f:
            if line[0] != "#" and line.strip():
                toks.append(line.split())
    N = len(toks)
    K = len(toks[0][0])
    lut = np.full(256, 255, dtype=np.uint8)
    for i, c in enumerate(ALPH):
        lut[ord(c)] = i
    X = lut[np.frombuffer("".join(t[0] for t in toks).encode(), dtype=np.uint8)].reshape(N, K)
    name = {"F": K, "S": K - 2, "D": 0}
    V = np.array([name[t[1]] if t[1] in name else int(t[1]) for t in toks], dtype=np.int16)
    del toks
    assert (np.sort(X, axis=1) == np.arange(K, dtype=np.uint8)).all(), "a row is not an ordering of the K letters"
    assert np.isin(V, [0, K] + list(range(1, K - 1))).all(), "a row with K - 1 visible classes or an unknown type"
    pw = (16 ** np.arange(K - 1, -1, -1)).astype(np.int64)

    def pack(A):
        """the rows of A (one state per row) as numbers, 4 bits per letter"""
        return (A.astype(np.int64) * pw).sum(axis=1)
    pos0 = (X == 0).argmax(axis=1)
    C = np.take_along_axis(X, (pos0[:, None] + np.arange(K)) % K, axis=1)
    nloops = np.unique(pack(C)).size
    print("%s: K = %d letters (k = %d symbols), rows %d, distinct 2-loops %d, (K-1)! = %d -> every loop once: %s  (%.0fs)" % (
        path, K, K + 1, N, nloops, math.factorial(K - 1), N == nloops == math.factorial(K - 1), time.time() - t0), flush=True)
    assert N == nloops == math.factorial(K - 1)
    cnt = Counter(V.tolist())
    print("rows by visible classes: %s" % dict(sorted(cnt.items(), reverse=True)))
    sel = np.nonzero(V > 0)[0]
    keys = pack(X[sel])
    order = np.argsort(keys)
    skeys = keys[order]
    succ = np.empty(sel.size, dtype=np.int64)
    for v in sorted(cnt):
        if v == 0:
            continue
        idx = list(range(1, K - 1)) + [0, K - 1] if v == K else list(range(v + 1, K)) + list(range(0, v - 1)) + [v, v - 1]
        assert sorted(idx) == list(range(K))
        rows = np.nonzero(V[sel] == v)[0]
        nk = pack(X[sel[rows]][:, idx])
        p = np.searchsorted(skeys, nk)
        p[p >= skeys.size] = 0
        ok = skeys[p] == nk
        assert ok.all(), "%d rows with %d visible classes lead to a state that is not a chosen row" % ((~ok).sum(), v)
        succ[rows] = order[p]
    indeg = np.bincount(succ, minlength=sel.size)
    assert (indeg == 1).all(), "a chosen row is the successor of %d rows" % indeg.max()
    print("steps: every chosen row leads to a chosen row and has exactly one predecessor (balanced, trails unique)  (%.0fs)" % (time.time() - t0), flush=True)
    # literal sample
    rng = np.random.default_rng(1)
    smp = rng.choice(sel.size, size=min(nsample, sel.size), replace=False)
    for i in smp.tolist():
        x = X[sel[i]].tolist()
        v = int(V[sel[i]])
        wd = slice_word(x, K, v)
        assert len(wd) == (K + 2) * v + K - 1
        assert wd[:K - 2] == x[:K - 2]
        assert wd[-(K - 2):] == X[sel[succ[i]]].tolist()[:K - 2], "tail of a spelled slice is not the head of the successor row"
    print("literal: %d sampled slices spelled letter by letter, tail = head of the successor row  (%.0fs)" % (smp.size, time.time() - t0), flush=True)
    # walks
    ports = {v: port(v, K) for v in cnt if v}
    Vs = V[sel].tolist()
    sc = succ.tolist()
    seen = bytearray(sel.size)
    stat = Counter()
    Qtot = trails = nw = 0
    ident = list(range(K - 1))
    for i0 in range(sel.size):
        if seen[i0]:
            continue
        i = i0
        p = ident
        ln = q = 0
        while not seen[i]:
            seen[i] = 1
            v = Vs[i]
            pv = ports[v]
            p = [pv[j] for j in p]
            ln += 1
            q += K - v
            i = sc[i]
        assert i == i0
        done = [False] * (K - 1)
        c = 0
        for a in range(K - 1):
            if not done[a]:
                c += 1
                b = a
                while not done[b]:
                    done[b] = True
                    b = p[b]
        stat[(ln, q, c)] += 1
        Qtot += q
        trails += c
        nw += 1
    D = cnt.get(0, 0)
    Nl = math.factorial(K - 1)
    print("closed walks %d; (loops, Q, closed trails after completion) x count:" % nw)
    for key, c in sorted(stat.items(), key=lambda kv: (-kv[0][0], kv[0]))[:30]:
        print("   %s x %d" % (key, c))
    fl = Fraction(Qtot + D + trails, Nl)
    print("Q = %d = %s x (K-1)!;  loops without a row D = %d;  walk trails %d;  trails after completion %d" % (
        Qtot, Fraction(Qtot, Nl), D, trails, D + trails))
    print("floor c = (Q + trails) / (K-1)! = %d / %d = %s = %.6f     [193/378 = %.6f, 193/360 = %.6f]" % (
        Qtot + D + trails, Nl, fl, float(fl), 193 / 378, 193 / 360))
    n = K + 2
    F3 = math.factorial(n) + math.factorial(n - 1) + math.factorial(n - 2)
    print("at n = %d: sum R = F3 + Q = %d, trails %d, floor length F3 + n - 3 + Q + trails - 1 = %d   (%.0fs)" % (
        n, F3 + Qtot, D + trails, F3 + n - 3 + Qtot + D + trails - 1, time.time() - t0))


if __name__ == "__main__":
    main()
