#!/usr/bin/env python
"""gen13.py - from a selection with full and short rows to the pieces two symbols higher: one transport, then the
completion.  Writes the base word, its table and a chained plan, trail by trail.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: gen13.py SEL OUT_BASE.txt [--table TSV] [--plan PLAN] [--no-word] [--time SEC] [--maxrot N]

  SEL       selection on k = K + 1 symbols, one line per loop: "x F" (full row), "x S" (short row) or "x D" (loop
            without a row), x an order of the K letters; the older format "x+s full|short|detached" is read too.
            Rows of other lengths are not accepted, because they do not transport (see liftmip.py).
  OUT_BASE  the base word on n = K + 3 symbols.  With --no-word it is not written: counts, table and plan only.
  --table   one line per trail in the order written: kind, slices, R, offset of the piece in the word
  --plan    the chained plan on that base word
  --time    time limit of the integer program in seconds (default 300)
  --maxrot  how many vertices of a trail are tried until its piece joins cleanly to the word so far (default 200)

I used it to go from the 11-symbol selection to the pieces of n = 13: every count of n = 12 comes out times 10
(72,000 trails, Q = 1,780,800, sum R = 6,747,720,000).

The transport (Pantone's paper, section 4), written walk by walk; only one walk of SEL is in memory at a time.
  Letters: 0 .. K-1 are the letters of SEL, w = K is the new letter, s = K + 1 the distinguished letter,
  z = K + 2 the completion letter; n = K + 3 and h = n - 3 = K.
  A walk of SEL has K - 1 ports.  Port j of a full row b carries the full row "w before b_j" (port 0 also "w before
  b_{K-1}"); port j of a short row carries the short row "w before b_j" (the last port also "u a w b" turned into
  "b u a w").  A full row moves the port by -1, a short row by +1.  One orbit of ports is one walk on k + 1 symbols.
  A loop x without a row gives the K loops "w in a gap of x".  They stay without a row, and each completes to a
  small trail (K + 1 slices, each a whole 2-cycle with distinguished letter z).
  Every walk on k + 1 symbols is then completed as in gen12.py (orbits of ports again).  It gives gcd(K, f - t)
  closed trails, f and t being its numbers of full and short rows; for the selections I used this is always K.

The base word: every closed trail once, as a piece that starts at a vertex where the step into the trail has weight 3
and no window is repeated; consecutive pieces overlap in at most h - 1 letters and no permutation window lies across
a junction (the rules of gen12.py).

The chained plan, events in the order in which the trails are written:
  small trails   The K trails above one loop x of SEL are one whole F-orbit with mobile letter w.  Each is cut at
                 its vertex without w; these vertices are x read from K consecutive letters, so the K trails form a
                 chain with K - 1 joins of cost 1.  No integer program is needed at this level.
                 Two such chains whose loops x, x' are consecutive in an F-orbit of SEL (mobile letter m) join at
                 cost 2 when x is read from the letter after m.  The links between loops of SEL are chosen as in
                 chainplan.py (largest set with one F-orbit per loop, an integer program); the chains they make
                 are printed as "units".  The units are ordered greedily by overlap.
  walk trails    The K trails of one walk pass a full row b of the walk with the completion letter z in the gaps
                 0 .. K - 1.  The trail with z in gap q is cut at the step of weight 2 after class q of that row
                 (cost 1); its piece then ends with the word that the trail of gap q + 1 starts with, so the K
                 trails form a chain with joins of cost 0.  A walk that completes to one trail is one event, the
                 piece as written.
  The walk chains follow the small trails in the order of the walks.  Nothing in the order of the units is
  optimised here; order13.py does that.

Prints the counts expected from SEL (Q, sum R, small trails), then what was written (trails, slices, sum R against
F3 = n! + (n-1)! + (n-2)!, class visits against (n-1)!), the trails by kind, and the model length of the plan:
h + sum R + cuts + joins.  The word of the plan has exactly that length (applyplan.py writes it).

What is exact here: the counts, and the number of links between loops of SEL when the solver's status is 2.  The
order of the units is a heuristic.

Needs: Python 3; gen12.py from the same repository next to this file or on PYTHONPATH (slices, port paths, the rules
for the base word); Gurobi (gurobipy, with a licence beyond the size-limited one) if SEL has loops without a row.
Time and memory, measured: n = 11 (2,800 trails) 2 s; n = 13 (72,000 trails) 290 s and 0.18 GB with --no-word.
The run that wrote the n = 13 word (6.7 GB on disk) took 278 s.

Words.  The text printed and the names in the code say "detached" for a loop without a row, "slice" both for a row
of the selection and for the part of a trail that one row gives, and "opening" for a cut.
"""
import argparse
import collections
import math
import os
import sys
import time
from array import array

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen12 as G

rot, ins = G.rot, G.ins


def tport(r, w, s2, j):
    """the rows on k + 1 symbols that carry port j of the row r = (b, s, v) of the selection: the new letter w is put
    before b_j; s2 is the distinguished letter one level up.  A full row (v = K) gives full rows (K + 1 classes), a
    short row (v = K - 2) short rows (K - 1 classes).  Port 0 of a full row and the last port of a short row carry two
    rows."""
    b, s, v = r
    K = len(b)
    if v == K:
        if j == 0:
            return [(ins(b, w, 0), s2, K + 1), (ins(b, w, K - 1), s2, K + 1)]
        return [(ins(b, w, j), s2, K + 1)]
    if j < K - 2:
        return [(ins(b, w, j), s2, K - 1)]
    y = ins(b, w, K - 1)
    y = (y[-1],) + y[:-1]
    return [(ins(b, w, K - 2), s2, K - 1), (y, s2, K - 1)]


def transport_walk(walk):
    """generator: the walks on k + 1 symbols above one walk on k symbols, each as the list of its rows in walk order.
    A port is followed around the walk (a full row moves it by -1, a short row by +1) until it is back at the first
    row with the port it started from; every orbit of ports gives one walk.  The result is checked to be closed."""
    K = len(walk[0][0])
    H = K - 1
    w, s2 = K, K + 1
    m = len(walk)
    step = [(H - 1 if r[2] == K else 1) for r in walk]
    done = bytearray(H)
    for p0 in range(H):
        if done[p0]:
            continue
        rows = []
        i, p = 0, p0
        while True:
            if i == 0:
                done[p] = 1
            rows += tport(walk[i], w, s2, p)
            p = (p + step[i]) % H
            i += 1
            if i == m:
                i = 0
            if i == 0 and p == p0:
                break
        for a in range(len(rows)):
            assert G.tail(rows[a]) == G.head(rows[(a + 1) % len(rows)]), "transported walk is not closed"
        yield rows


def complete_detail(walk, z, i0):
    """generator: the closed trails of the completion of a walk with the letter z, one per orbit of ports.  For each
    trail: (its slices in order, {port with which it passes row i0 of the walk: index of the first slice it has
    there}).  The second part is what the chained plan needs to find the place of the cut."""
    K = len(walk[0][0])
    H = K - 1
    m = len(walk)
    step = [(H - 1 if r[2] == K else 1) for r in walk]
    done = bytearray(H)
    for p0 in range(H):
        if done[p0]:
            continue
        sl = []
        at = {}
        i, p = 0, p0
        while True:
            if i == 0:
                done[p] = 1
            if i == i0:
                at[p] = len(sl)
            sl += G.port_path(walk[i], z, p)
            p = (p + step[i]) % H
            i += 1
            if i == m:
                i = 0
            if i == 0 and p == p0:
                break
        yield sl, at


def canon(x):
    """the cyclic word x read from its smallest letter"""
    i = x.index(min(x))
    return x[i:] + x[:i]


def old_chains(det, K, tlimit=300, log=print):
    """the chains of the loops without a row of a selection (det: the loops, K letters each).
    A link is two such loops consecutive in an F-orbit (c, m): the cyclic order c of the other K - 1 letters with m
    in two neighbouring gaps.  The largest set of links in which every loop uses one orbit only, and no orbit is
    closed into a ring, is found by an integer program (the model of chainplan.py); the maximal runs of used links
    are the chains.  Returns the units: lists of (x, b0), x a loop as a tuple read from its smallest letter, b0 the
    index in x of the letter after the mobile letter of its chain (None for a loop with no link: it may be read
    from any letter)."""
    D = [canon(tuple(x)) for x in det]
    orb = collections.defaultdict(dict)        # (m, c) -> {gap j of c in which m stands: loop}
    for x in D:
        for i in range(K):
            m = x[i]
            c = x[i + 1:] + x[:i]
            cc = canon(c)
            orb[m, cc][cc.index(c[-1])] = x
    links = [(key, j) for key, d in orb.items() for j in d if (j + 1) % (K - 1) in d]
    used = []
    if links:
        import gurobipy as gp
        from gurobipy import GRB
        mdl = gp.Model("chains", env=gp.Env(params={"OutputFlag": 0}))
        mdl.Params.OutputFlag = 0
        mdl.Params.Threads = 2
        mdl.Params.TimeLimit = tlimit
        p = {lk: mdl.addVar(vtype=GRB.BINARY, obj=-1.0) for lk in links}
        u = {}
        for (key, j) in links:
            for x in (orb[key][j], orb[key][(j + 1) % (K - 1)]):
                if (x, key) not in u:
                    u[x, key] = mdl.addVar(vtype=GRB.BINARY)
                mdl.addConstr(p[key, j] <= u[x, key])
        byx = collections.defaultdict(list)
        for (x, key), v in u.items():
            byx[x].append(v)
        for x, vs in byx.items():
            if len(vs) > 1:
                mdl.addConstr(gp.quicksum(vs) <= 1)
        for key, d in orb.items():
            if len(d) == K - 1:
                mdl.addConstr(gp.quicksum(p[key, j] for j in range(K - 1)) <= K - 2)
        mdl.optimize()
        used = [lk for lk in links if p[lk].X > 0.5]
        log("links between detached loops of the selection: %d possible pairs, %d used (status %d, bound %.0f)" % (
            len(links) // 2, len(used), mdl.Status, -mdl.ObjBound))
    byo = collections.defaultdict(set)
    for (key, j) in used:
        byo[key].add(j)
    units, inchain = [], set()
    for key, js in byo.items():
        d = orb[key]
        m = key[0]
        for j in sorted(js):
            if (j - 1) % (K - 1) in js:
                continue
            ch = [j]
            while ch[-1] in js:
                ch.append((ch[-1] + 1) % (K - 1))
            un = []
            for jj in ch:
                x = d[jj]
                un.append((x, (x.index(m) + 1) % K))
                inchain.add(x)
            units.append(un)
    nsingle = 0
    for x in D:
        if x not in inchain:
            units.append([(x, None)])
            nsingle += 1
    log("units of detached loops: %d chains (lengths %s) + %d single loops" % (
        len(units) - nsingle,
        dict(sorted(collections.Counter(len(un) for un in units if un[0][1] is not None).items())), nsingle))
    return units


def order_units(units, K):
    """greedy order of the units: after a unit, the unused unit whose first word has the largest overlap (K - 2 down
    to 3 letters) with the last word of the unit just written; if none overlaps, the first unused unit.  A loop with
    no link is read from the letter that fits.  Returns the units in the new order."""
    def S(x, b0):
        """first word of the chain above loop x read from position b0"""
        return x[b0:] + x[:b0]

    def E(x, b0):
        """last word of that chain: x read from one position earlier"""
        b = (b0 - 1) % K
        return x[b:] + x[:b]

    heads = collections.defaultdict(list)
    for ui, un in enumerate(units):
        x, b0 = un[0]
        for bb in ([b0] if b0 is not None else range(K)):
            wd = S(x, bb)
            for k in range(K - 2, 2, -1):
                heads[wd[:k]].append((ui, bb))
    done = bytearray(len(units))
    seq = []
    cur, b00 = 0, (units[0][0][1] if units[0][0][1] is not None else 0)
    left = len(units)
    ptr = 0
    while True:
        done[cur] = 1
        left -= 1
        un = units[cur]
        if un[0][1] is None:
            un = [(un[0][0], b00)]
        seq.append(un)
        if not left:
            break
        e = E(*un[-1])
        nx = None
        for k in range(K - 2, 2, -1):
            for (ui, bb) in heads.get(e[-k:], ()):
                if not done[ui]:
                    nx = (ui, bb)
                    break
            if nx:
                break
        if nx is None:
            while done[ptr]:
                ptr += 1
            nx = (ptr, units[ptr][0][1] if units[ptr][0][1] is not None else 0)
        cur, b00 = nx
    return seq


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sel")
    ap.add_argument("out")
    ap.add_argument("--table")
    ap.add_argument("--plan")
    ap.add_argument("--no-word", action="store_true",
        help="do not write the base word (counts, table and plan length only)")
    ap.add_argument("--time", type=float, default=300)
    ap.add_argument("--maxrot", type=int, default=200)
    a = ap.parse_args()
    t0 = time.time()
    rows = G.read_sel(a.sel)
    K = len(rows[0][0])
    K2 = K + 1
    n = K + 3
    h = n - 3
    w, s2, z = K, K + 1, K + 2
    det = [r[0] for r in rows if r[2] < 0]
    walks = G.sel_walks([r for r in rows if r[2] >= 0])
    tshort = sum(1 for r in rows if r[2] == K - 2)
    F3 = math.factorial(n) + math.factorial(n - 1) + math.factorial(n - 2)
    print("selection on %d symbols: %d loops, short %d, detached %d, walks %d -> n = %d, h = %d (%.0fs)" % (
        K + 1, len(rows), tshort, len(det), len(walks), n, h, time.time() - t0), flush=True)
    print("expected: Q = %d, sum R = %d, small trails %d" % (2 * tshort * K, F3 + 2 * tshort * K, len(det) * K),
        flush=True)
    units = order_units(old_chains(det, K, a.time), K) if det else []
    fo = None if a.no_word else open(a.out, "wb")
    ft = open(a.table, "w") if a.table else None
    total = 0
    tailw = b""
    ntr = nsl = sumR = 0
    events = []            # (text, R + h + D, S, E)
    kinds = collections.Counter()
    sizes = collections.Counter()
    moved = 0

    def write(kind, nslices, c, offs, want=0):
        """write the closed trail c (cyclic word; offs = offsets of its vertices) as a piece of R + h letters that
        starts at a vertex.  The vertex at offset `want` is taken if the step into it has weight 3 with no repeated
        window and the piece joins cleanly to the word so far; otherwise the first vertex that does.  Adds the line
        of the table.  Returns the offset used."""
        nonlocal total, tailw, ntr, nsl, sumR, moved
        R = len(c)
        cc = c + c[:n + h]
        cand = [want] + [r for r in offs[:a.maxrot] if r != want]
        for r in cand:
            if not G.plain_vertex(c, r, n):
                continue
            if total == 0:
                k, ok = 0, True
            else:
                k, ok = G.clean_join(tailw, cc[r:r + n + h], n)
            if ok:
                piece = c[r:] + c[:r] + cc[r:r + h]
                if fo:
                    fo.write(piece[k:].translate(G.TOTXT))
                if ft:
                    ft.write("%s\t%d\t%d\t%d\n" % (kind, nslices, R, total - k))
                total += len(piece) - k
                tailw = piece[-(n + h):]
                ntr += 1
                nsl += nslices
                sumR += R
                kinds[kind] += 1
                sizes[R] += 1
                if r != want:
                    moved += 1
                return r
        raise AssertionError("no clean vertex for a trail of kind %s" % kind)

    # ---- small trails, unit after unit.  Above the loop x the new letter w stands in the gaps b0, b0 + 1, ..: K
    # small trails, each made of K + 1 whole 2-cycles; the piece is written from the vertex without w.
    for un in units:
        for (x, b0) in un:
            for i in range(K):
                b = (b0 + i) % K
                y = x[:b] + (w,) + x[b:]
                tr = [(rot(y, (b + 1 + q) % K2) + (s2,), z, K2 + 1) for q in range(K2)]
                c, offs = G.spell(tr, n)
                R = len(c)
                r = write("D", K2, c, offs, 0)
                vw = bytes(x[b:] + x[:b])
                assert c[:h] == vw
                events.append(("O %d %d 3 0" % (ntr - 1, (-r) % R), R + h, vw, vw))
        if ntr % 10000 < K * len(un) and ntr >= 10000:
            print("  small trails %d, letters %d (%.0fs)" % (ntr, total, time.time() - t0), flush=True)
    nsmall = ntr
    print("small trails written: %d (%.0fs)" % (nsmall, time.time() - t0), flush=True)
    # ---- walks, shortest first; every transported walk is completed and its trails are written and chained
    nchain = nsingle_w = 0
    for wk in sorted(walks, key=len):
        tt = sum(1 for r in wk if r[2] == K - 2)
        kind = "W%d.%d" % (len(wk), tt)
        for W2 in transport_walk(wk):
            i0 = next(i for i, r in enumerate(W2) if r[2] == K2)      # a full slice of the walk
            b = W2[i0][0]
            trs = []
            for sl, at in complete_detail(W2, z, i0):
                c, offs = G.spell(sl, n)
                r = write(kind, len(sl), c, offs, 0)
                trs.append((ntr - 1, len(c), c[r:r + h], offs, at, r))
            g = len(trs)
            if g == 1:
                t, R, hw, offs, at, r = trs[0]
                events.append(("P %d" % t, R + h, hw, hw))
                nsingle_w += 1
                continue
            # chain: port q = 0 .. g-1, trail that has port q at position i0, cut after class q of "z before b_q"
            byport = {}
            for tr in trs:
                for q in tr[4]:
                    byport[q] = tr
            assert len({id(byport[q]) for q in range(g)}) == g
            prevE = None
            for q in range(g):
                t, R, hw, offs, at, r = byport[q]
                B = ins(b, z, q)
                S = bytes(rot(B, q + 1)[:h])
                E = bytes(rot(B, q + 2)[:h])
                assert prevE is None or prevE == S
                prevE = E
                start = (offs[at[q]] + (q + 1) * (n + 1) - r) % R
                events.append(("O %d %d 2 0" % (t, start), R + h + 1, S, E))
            nchain += 1
        if ntr % 500 < 10 * (K - 1):
            print("  trails %d, slices %d, letters %d (%.0fs)" % (ntr, nsl, total, time.time() - t0), flush=True)
    if fo:
        fo.write(b"\n")
        fo.close()
    if ft:
        ft.close()
    visits = (sumR - nsl) // (n + 1)
    print("n = %d: trails %d (small %d), slices %d (= (n-2)! + %d), sum R %d = F3 + %d, class visits %d ((n-1)! = %d)" % (
        n, ntr, nsmall, nsl, nsl - math.factorial(n - 2), sumR, sumR - F3, visits, math.factorial(n - 1)))
    print("base word %d letters%s; pieces not written from the intended vertex %d (%.0fs)" % (
        total, "" if a.no_word else " -> " + a.out, moved, time.time() - t0))
    print("R histogram, most frequent: %s" % sorted(sizes.items(), key=lambda kv: -kv[1])[:8])
    print("largest R: %s" % sorted(sizes.items(), reverse=True)[:5])
    print("trails by kind (W loops.short of the walk of the selection, D = small): %s" % sorted(kinds.items(),
        key=lambda kv: -kv[1])[:40])
    # ---- the plan and its model length: letters of all events minus the overlaps of consecutive events
    length = sum(e[1] for e in events)
    joins = collections.Counter()
    for i in range(len(events) - 1):
        e, s = events[i][3], events[i + 1][2]
        k = 0
        for q in range(h, 0, -1):
            if e[-q:] == s[:q]:
                k = q
                break
        length -= k
        joins[h - k] += 1
    ncut = sum(1 for e in events if e[0].endswith(" 2 0"))
    print("plan: %d events (%d small trails in %d units, %d walk chains, %d single walk trails); cuts at weight-2 steps %d" % (
        len(events), nsmall, len(units), nchain, nsingle_w, ncut))
    print("plan: joins by cost %s" % dict(sorted(joins.items())))
    print("plan: predicted model length %d = h + sum R + %d  (%.3f per trail)" % (length, length - h - sumR,
        (length - h - sumR) / float(ntr)))
    if a.plan:
        with open(a.plan, "w", newline="\n") as fp:
            fp.write("TRAILSEARCH-PLAN %d %d %d\n" % (n, total, len(events)))
            for e in events:
                fp.write(e[0] + "\n")
        print("wrote %s" % a.plan)


if __name__ == "__main__":
    main()
