"""transport_search.py - is there a transport for a row of any visible length?  Brute force, same deficit above.

Pantone's transport (section 4) replaces a full or short row on K letters by K rows on K + 1 letters, one in each
loop above, so that completion one level up gives the same picture.  The question here: does a row (x, v) with
deficit d = K - v (d = 0 full, 2 short, 3 .. K-1 the other lengths) have such a transport?

The test.  One level up (new letter w = K) take one row of the same deficit d in each of the K loops above the loop
of x: a rotation of "x with w in gap j", j = 0 .. K-1, with v + 1 visible classes.  The K rows are wanted to form
K - 1 paths in the endpoint graph, from "head of x with w at position i" to "tail of x with w at position pi(i)",
i = 0 .. K-2, where pi is the port permutation of the row: these are the ends that the completion of (x, v) has.
All (K + 1)^K choices of the rotations are tried.

Result (K = 5, 6, 7): exactly one transport for d = 0 and one for d = 2, Pantone's; none for any d >= 3.
transport_search2.py allows any deficits above and finds none that keeps the cost either.

usage:    python transport_search.py K
outputs:  one line per deficit: the number of transports and the rotations of the first few.
needs:    Python 3 and gcore.py.  No other package.
cost:     measured here: K = 6: 2 s; K = 7: 47 s; the time grows like (K + 1)^K.
"""
import sys, itertools
from gcore import gstep, port as port_perm


def nxt(y, d):
    """the state after a row of deficit d at the state y (d = 0: full)"""
    return gstep(y, len(y) - d)


def port(K, d, i):
    """port permutation of a row of deficit d on K letters, at port i"""
    return port_perm(K - d, K)[i]


K = int(sys.argv[1])
w = K
x = tuple(range(K))
for d in [0] + list(range(2, K)):
    L = K - d
    hx = x[:K - 2]
    r = (L + 1) % K
    tx = (x[r:] + x[:r])[:K - 2]
    P = [hx[:i] + (w,) + hx[i:] for i in range(K - 1)]
    T = [tx[:i] + (w,) + tx[i:] for i in range(K - 1)]
    want = {(P[i], T[port(K, d, i)]) for i in range(K - 1)}
    cands = []
    for j in range(K):
        base = x[:j] + (w,) + x[j:]
        cj = []
        for rot in range(K + 1):
            y = base[rot:] + base[:rot]
            head = y[:K - 1]
            y2 = nxt(y, d)                     # deficit d on K + 1 letters: L + 1 visible
            tail = y2[:K - 1]
            cj.append((rot, head, tail))
        cands.append(cj)
    sols = []
    for combo in itertools.product(*cands):
        heads = [c[1] for c in combo]
        tails = [c[2] for c in combo]
        if len(set(heads)) < K or len(set(tails)) < K:
            continue
        hmap = {h: i for i, h in enumerate(heads)}
        # paths: start at rows whose head is not a tail
        tset = set(tails)
        starts = [i for i in range(K) if heads[i] not in tset]
        if len(starts) != K - 1:
            continue
        got = set()
        ok = True
        used = 0
        for s in starts:
            i = s
            while tails[i] in hmap:
                i = hmap[tails[i]]
                used += 1
            used += 1
            got.add((heads[s], tails[i]))
        if used == K and got == want:
            sols.append(tuple(c[0] for c in combo))
    print("K = %d, d = %d (L = %d): %d transport rules; rotations (per gap j = 0..K-1): %s" % (K, d, L, len(sols), sols[:4]))
