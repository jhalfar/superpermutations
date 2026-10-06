"""transport_search2.py - a transport of a row by rows of ANY deficits in the loops above?  Brute force.

The wider question after transport_search.py.  A row (x, v) on K letters with deficit d = K - v; new letter w = K.
The row above gap i <= K-2 must start at "x with w in gap i" (its head is the port "w at position i"), with any
deficit; the row above gap K-1 may start at any rotation, with any deficit.  Wanted: K - 1 paths in the endpoint
graph from port i to "tail of x with w at position pi(i)", pi the port permutation of the row (x, v).
All solutions are counted by their total deficit; a transport that keeps the cost per loop has total deficit K * d.

Result (K = 6, 7, 8): for d = 0 and d = 2 there is exactly one solution, Pantone's transport, and it keeps the
cost; for d >= 3 there is no solution of any total deficit.  So a selection with rows of other visible lengths
cannot be carried to the next n by a rule of this kind: every n needs its own block search.

usage:    python transport_search2.py K
outputs:  one line per deficit: the number of solutions by total deficit, and an example of the cheapest.
needs:    Python 3 and gcore.py.  No other package.
cost:     measured here: under 1 s for K up to 8.
"""
import sys, itertools
from collections import Counter
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
DEF = [0] + list(range(2, K + 1))          # deficits on K + 1 letters: 0, 2 .. K  (visible K+1, K-1 .. 1)
for d in [0] + list(range(2, K)):
    L = K - d
    hx = x[:K - 2]
    r = (L + 1) % K
    tx = (x[r:] + x[:r])[:K - 2]
    P = [hx[:i] + (w,) + hx[i:] for i in range(K - 1)]
    T = [tx[:i] + (w,) + tx[i:] for i in range(K - 1)]
    want = {P[i]: T[port(K, d, i)] for i in range(K - 1)}
    # rows above gaps 0 .. K-2: state ins(x, w, i), deficit e -> tail
    first = []
    for i in range(K - 1):
        y = x[:i] + (w,) + x[i:]
        first.append([(e, nxt(y, e)[:K - 1]) for e in DEF])
    base = x[:K - 1] + (w,) + x[K - 1:]
    last = []
    for rot in range(K + 1):
        y = base[rot:] + base[:rot]
        for e in DEF:
            last.append((rot, e, y[:K - 1], nxt(y, e)[:K - 1]))
    res = Counter()
    ex = {}
    for (rot, e, hl, tl) in last:
        # the last row is internal: its head is the tail of exactly one port row i0, and its tail is want[P[i0]]
        for i0 in range(K - 1):
            if tl != want[P[i0]]:
                continue
            # port row i0 must have tail hl; the others must have tail want directly
            opts = []
            ok = True
            for i in range(K - 1):
                target = hl if i == i0 else want[P[i]]
                oi = [ee for (ee, t) in first[i] if t == target]
                if not oi:
                    ok = False
                    break
                opts.append(oi)
            if not ok:
                continue
            for combo in itertools.product(*opts):
                tot = sum(combo) + e
                res[tot] += 1
                ex.setdefault(tot, (combo, rot, e))
    print("K = %d, d = %d: transports by total deficit %s (cost-preserving total = %d)%s" % (
        K, d, dict(sorted(res.items())), K * d, "; example (deficits of gaps 0..K-2, rotation and deficit of gap K-1): %s" % (ex[min(res)],) if res else ""))
