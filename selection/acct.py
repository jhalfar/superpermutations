"""acct.py - the accounting of Pantone's own input: what his 10-symbol selection costs, counted from the definitions.

The comparison of every selection in this directory rests on these numbers, so they are computed here from
Pantone's published file alone.  The script is written from the definitions of the paper (sections 2 to 5); it
imports nothing from this directory and does not use Pantone's construct.cpp.

Conventions.  k symbols, K = k - 1 letters other than the distinguished letter s.  A 2-loop is a cyclic order of
the K letters; a row (x, d) is the slice S(x, s; L) that starts at the rotation x, with L = K (full, d = 0) or
L = K - 2 (short, d = 2).  Its end words have k - 3 letters:
    head(x)       = x[0 : K-2]
    tail, full    = x[1 : K-1]
    tail, short   = x[K-1] + x[0 : K-3]
What is computed from construction-input.txt (k = 10, K = 9):
  * one row per 2-loop, 8! = 40,320 rows; the endpoint graph is balanced with all degrees one, so the closed
    trails of the selection are forced;
  * t = 9,408 short rows, Q = 2 t = 18,816 = 7/15 x 8!;
  * 350 closed trails: 14 big ones and 336 of 8 full rows; gcd(k - 2, f - t) = 8 on each, so 2,800 closed trails
    after completion; floor (Q + trails)/8! = 193/360;
  * the 357 connector cycles of the file and the coefficient 43/80 = 7/15 + 357/7!;
  * the value of Theorem 2 of the paper for n = 11, 12, 13 (43,932,117 at n = 11).
With --full the completion on 11 symbols is built literally: 8! x 9 + Q slices, every one of the 10! cyclic classes
in exactly one slice, 2,800 closed trails in the completed endpoint graph, and the 357 cycles meet all of them.

usage:    python acct.py construction-input.txt [--full]
inputs:   Pantone's construction-input.txt (header CIRCLE4380V1, the rows "x type", then the connector cycles).
outputs:  text on standard output.
needs:    Python 3.  No other package.
cost:     measured here: without --full 1 s; with --full 38 s and 0.7 GB.
"""
import sys
from fractions import Fraction
from math import factorial, gcd
from collections import Counter, defaultdict

ALPH = "0123456789ABC"


def read_input(path):
    """Read construction-input.txt: the rows as (x, type) with type 0 (full) or 2 (short), and the connector
    cycles (words of n - 3 letters)."""
    tok = open(path).read().split()
    assert tok[0] == "CIRCLE4380V1"
    nrow, ncirc = int(tok[1]), int(tok[2])
    rows = []
    p = 3
    for _ in range(nrow):
        rows.append((tuple(ALPH.index(c) for c in tok[p]), int(tok[p + 1])))
        p += 2
    circ = [tuple(ALPH.index(c) for c in tok[p + i]) for i in range(ncirc)]
    assert p + ncirc == len(tok)
    return rows, circ


def canon(x):
    """The cyclic order of x: its rotation that starts with the least letter."""
    j = x.index(min(x))
    return x[j:] + x[:j]


def selection_trails(rows, K):
    """rows: (x, deficit) with deficit 0 (full) or 2 (short).  Checks that there is one row per 2-loop and that the
    endpoint graph (head -> tail, words of K - 2 letters) is balanced.  Returns the closed trails of the selection
    as lists of row indices, and the largest out-degree (1 means that the trails are forced)."""
    loops = Counter(canon(x) for x, d in rows)
    assert len(loops) == factorial(K - 1) and set(loops.values()) == {1}, "not one slice per 2-loop"
    head, tail = {}, {}
    outdeg, indeg = Counter(), Counter()
    for i, (x, d) in enumerate(rows):
        assert d in (0, 2)
        h = x[:K - 2]
        t = x[1:K - 1] if d == 0 else (x[K - 1],) + x[:K - 3]
        head[i], tail[i] = h, t
        outdeg[h] += 1
        indeg[t] += 1
    assert outdeg == indeg, "endpoint graph not balanced"
    # the closed trails: Euler circuits of the components.  Report whether the trail decomposition is forced.
    maxdeg = max(outdeg.values())
    by_head = defaultdict(list)
    for i in range(len(rows)):
        by_head[head[i]].append(i)
    seen = [False] * len(rows)
    trails = []
    for i0 in range(len(rows)):
        if seen[i0]:
            continue
        tr, i = [], i0
        while not seen[i]:
            seen[i] = True
            tr.append(i)
            nxt = [j for j in by_head[tail[i]] if not seen[j]]
            if not nxt:
                break
            i = nxt[0]
        assert tail[tr[-1]] == head[tr[0]]
        trails.append(tr)
    return trails, maxdeg


def complete(rows, K):
    """The completion with a new letter z = K + 1 (s = K), as in section 3 of the paper: for every row the K
    inserted slices (z in front of x[i]; L + 1 classes for i < L, else L) and the K - L repair slices
    (rot^i(x) s with distinguished letter z, K + 1 classes).  Returns the slices on n = K + 2 symbols as
    (y, dist, L): y = ordering of the n - 1 letters other than the distinguished letter dist, L classes."""
    s, z = K, K + 1
    out = []
    for x, d in rows:
        L = K - d
        for i in range(K):                       # inserted slices: z just before x_i
            y = x[:i] + (z,) + x[i:]
            out.append((y, s, L + 1 if i < L else L))
        for i in range(L, K):                    # repair slices for the missed classes [rot^i(x) s]
            y = x[i:] + x[:i] + (s,)
            out.append((y, z, K + 1))
    return out


def slice_ends(y, L, h):
    """head and tail (h = n - 3 letters) of the slice starting at y dist with L classes; len(y) = n - 1 = h + 2."""
    m = len(y)
    r = (L + 1) % m
    return y[:h], (y[r:] + y[:r])[:h]


def main():
    """The accounting in the order of the list in the header; with --full the literal completion as well."""
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if not args:
        sys.exit("usage: python acct.py construction-input.txt [--full]")
    path = args[0]
    full = "--full" in sys.argv
    rows, circ = read_input(path)
    K = len(rows[0][0])
    k = K + 1
    n = k + 1
    h = n - 3
    print("selection on k = %d symbols: %d slices = (k-2)! = %d; %d connector cycles of length %d" % (
        k, len(rows), factorial(k - 2), len(circ), len(circ[0])))
    trails, maxdeg = selection_trails(rows, K)
    t = sum(1 for x, d in rows if d == 2)
    Q = 2 * t
    print("short slices t = %d, Q = 2t = %d = %s * (k-2)!" % (t, Q, Fraction(Q, factorial(k - 2))))
    print("endpoint graph balanced, max out-degree %d (1 = the closed trails are forced)" % maxdeg)
    stat = Counter()
    sumg = 0
    for tr in trails:
        tt = sum(1 for i in tr if rows[i][1] == 2)
        ff = len(tr) - tt
        g = gcd(k - 2, ff - tt)
        sumg += g
        stat[(len(tr), ff, tt, (ff - tt) % (k - 2), g)] += 1
    print("closed trails: %d;  sum of gcd(k-2, f-t) = %d" % (len(trails), sumg))
    for key in sorted(stat, reverse=True):
        print("   %4d trail(s) with %5d slices, f = %5d, t = %5d, (f-t) mod %d = %d, gcd = %d" % (
            (stat[key],) + key[:3] + (k - 2,) + key[3:]))
    div = all(key[3] == 0 for key in stat)
    print("k-2 divides f-t on every closed trail:", div)
    cQ = Fraction(Q, factorial(k - 2))
    cT = Fraction(sumg, factorial(k - 2))
    print("Q-term %s, trails after completion per (n-3)!: %s  (= %d * (n-3)!/%d!), floor %s = %.6f" % (
        cQ, cT, sumg, k - 2, cQ + cT, cQ + cT))
    cC = Fraction(len(circ), factorial(h - 1))          # c = 357/7! (n-4)!  ->  h c = 357/7! (n-3)!
    print("connector cycles at n = %d: %d = %s (n-4)!; join term %s; coefficient %s = %.6f" % (
        n, len(circ), cC, cC, cQ + cC, cQ + cC))

    # Theorem 2 at n = 11
    def thm2(n, ell):
        """the bound of Theorem 2 of the paper for the parameter ell"""
        c = Fraction(17, 240) * factorial(n - 4)
        f3 = factorial(n) + factorial(n - 1) + factorial(n - 2)
        return f3 + Fraction(43, 80) * factorial(n - 3) + (n - 4 - ell) * c + ell * min(
            c, Fraction(factorial(n - 1), factorial(n - 1 - ell)))
    for nn in (11, 12, 13):
        best = min((thm2(nn, e), e) for e in range(0, nn - 3))
        print("Theorem 2, n = %d: best ell = %d, bound %d" % (nn, best[1], best[0].numerator // best[0].denominator))

    if not full:
        return
    # literal completion on n = 11 symbols
    sl = complete(rows, K)
    assert len(sl) == factorial(n - 2) + Q
    print("completion: %d slices = (n-2)! + Q" % len(sl))
    # every cyclic class on n symbols exactly once
    seen = set()
    for y, dist, L in sl:
        m = len(y)
        for j in range(L):
            c = y[j:] + y[:j] + (dist,)
            i0 = c.index(0)
            c = c[i0:] + c[:i0]
            assert c not in seen
            seen.add(c)
    assert len(seen) == factorial(n - 1)
    print("classes covered exactly once: %d = (n-1)!" % len(seen))
    del seen
    vid = {}
    hd, tl = [], []
    for y, dist, L in sl:
        a, b = slice_ends(y, L, h)
        hd.append(vid.setdefault(a, len(vid)))
        tl.append(vid.setdefault(b, len(vid)))
    nv = len(vid)
    outd = Counter(hd)
    assert outd == Counter(tl)
    print("completed endpoint graph: %d vertices, balanced, max degree %d" % (nv, max(outd.values())))
    par = list(range(nv))

    def find(a):
        """union-find over the vertices of the completed endpoint graph"""
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a
    for a, b in zip(hd, tl):
        ra, rb = find(a), find(b)
        if ra != rb:
            par[ra] = rb
    comp = {find(a) for a in hd}
    print("closed trails after completion (components; max degree 1 means cycles): %d" % len(comp))
    # connector cycles
    met = set()
    per = []
    absent = 0
    for c in circ:
        m = set()
        for j in range(h):
            v = c[j:] + c[:j]
            if v in vid:
                m.add(find(vid[v]))
            else:
                absent += 1
        per.append(len(m))
        met |= m
    print("connector cycles: trails met %d of %d; rotations that are not vertices: %d; cycles by number of trails met: %s" % (
        len(met), len(comp), absent, dict(sorted(Counter(per).items()))))
    zc = sum(1 for c in circ if (K + 1) in c)
    print("cycles containing z: %d, without z: %d" % (zc, len(circ) - zc))
    # components after adding the cycles
    par2 = {r: r for r in comp}

    def find2(a):
        """union-find over the closed trails, joined by the connector cycles"""
        while par2[a] != a:
            par2[a] = par2[par2[a]]
            a = par2[a]
        return a
    ncomp = len(comp)
    for c in circ:
        rs = {find2(find(vid[c[j:] + c[:j]])) for j in range(h) if (c[j:] + c[:j]) in vid}
        rs = list(rs)
        for r in rs[1:]:
            if find2(r) != find2(rs[0]):
                par2[find2(r)] = find2(rs[0])
                ncomp -= 1
    print("components after adding the connector cycles: %d (<= %d cycles)" % (ncomp, len(circ)))


if __name__ == "__main__":
    main()
