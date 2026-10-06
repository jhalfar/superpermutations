#!/usr/bin/env python
"""order13.py - a better order of the units of the chained plan that gen13.py writes.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: order13.py SEL BASE.txt BASE.tsv PLAN_IN PLAN_OUT

  SEL       the selection that gen13.py was run on (full and short rows, loops without a row)
  BASE.txt  the base word of gen13.py (mapped; only h-letter words are read from it, h = n - 3)
  BASE.tsv  its table
  PLAN_IN   the plan of gen13.py
  PLAN_OUT  the same chains in a better order, the walk chains cut where they fit

Units of the plan of gen13.py (K = n - 3 letters in a word, K + 1 letters in a row of the transported walks):
  small units   A chain above one loop of SEL is K small trails with joins of cost 1; I call it an orbit chain.
                A small unit is a run of orbit chains with joins of cost 2 between them.  A unit of several orbit
                chains has fixed end words.  A single orbit chain may start at any of its K trails, because its
                trails form a ring of joins of cost 1.
  walk chains   The K trails of one walk, cut at one full row b of the walk and chained at cost 0.  Any full row
                may be used, in two ways:
                  A: completion letter in the gaps 0 .. K-1 of b:  first word b[:K],  last word b[K] b[:K-1]
                  B: completion letter in the gaps 1 .. K:        first word b[1:],  last word b[:K]
Order: greedy.  After a unit that ends with the word E, the next unit is an unused one whose first word overlaps E
most (overlaps K - 1 down to 3, looked up in sorted tables; for a walk chain at most 4,000 table entries are
examined per overlap); if nothing overlaps, the next unused unit.  The first unit is the first small unit.
The trails are numbered as in BASE.tsv, the order in which gen13.py wrote them; this script repeats its order of
the walks and asserts that the trail counts and the R of every trail agree with the table.

Prints the number of units, the joins between units by cost (-1: nothing overlapped), the joins of the new plan by
cost and its model length h + sum R + cuts + joins.  applyplan.py writes the word.

This is a heuristic start for the passes, not an optimiser.  On the n = 13 pieces of the transported selection it
took the plan of gen13.py from 6,747,820,565 to 6,747,813,583 letters (both words checked), and 539 times no unit
overlapped the last word.

Needs: Python 3; gen12.py and gen13.py next to this file or on PYTHONPATH.  No solver.
Time and memory, measured: n = 11 (2,800 trails) 1 s; n = 13 (72,000 trails) 89 s and 0.46 GB.

Words.  In the names of the code and the text printed, a "slice" is a row of a walk, a "detached" trail (kind D in
the table) is a small trail.
"""
import bisect
import collections
import mmap
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen12 as G
import gen13 as G13

rot, ins = G.rot, G.ins


def main():
    selp, basep, tsvp, planin, planout = sys.argv[1:6]
    t0 = time.time()
    tab = [l.split("\t") for l in open(tsvp)]
    Rt = [int(t[2]) for t in tab]
    st = [int(t[3]) for t in tab]
    kindt = [t[0] for t in tab]
    f = open(basep, "rb")
    W = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
    lines = open(planin).read().split("\n")
    hdr = lines[0].split()
    n = int(hdr[1])
    h = n - 3
    K = h
    K2 = K + 1
    z = K + 2
    FROMTXT = bytes((G.ALPH.index(chr(c)) if chr(c) in G.ALPH else 255) for c in range(256))

    def cyc(t, pos, ln):
        """ln letters of trail t from offset pos of its piece, read around the closed trail, as letter values"""
        r = Rt[t]
        pos %= r
        a = st[t]
        if pos + ln <= r:
            return W[a + pos:a + pos + ln].translate(FROMTXT)
        return (W[a + pos:a + r] + W[a:a + ln - (r - pos)]).translate(FROMTXT)

    def ov(e, s):
        """largest overlap of the end of word e with the start of word s"""
        for q in range(h, 0, -1):
            if e[-q:] == s[:q]:
                return q
        return 0

    ev = [l for l in lines[1:] if l.strip()]
    nsmall = sum(1 for k in kindt if k == "D")
    assert all(kindt[int(l.split()[1])] == "D" for l in ev[:nsmall])
    # ---- small units from the plan: the first events are the small trails, K per orbit chain; consecutive orbit
    # chains that join at cost 2 (overlap h - 2) belong to one unit
    words = []
    for l in ev[:nsmall]:
        p = l.split()
        words.append(cyc(int(p[1]), int(p[2]), h))
    assert nsmall % K == 0
    orbs = [list(range(a, a + K)) for a in range(0, nsmall, K)]
    for o in orbs:
        for i in range(K):
            assert ov(words[o[i]], words[o[(i + 1) % K]]) == h - 1, "small trails are not an orbit chain"
    units = []                      # ("S", [orbit chains]) ; single if one orbit chain
    cur = [orbs[0]]
    for a in range(1, len(orbs)):
        if ov(words[orbs[a - 1][-1]], words[orbs[a][0]]) == h - 2:
            cur.append(orbs[a])
        else:
            units.append(cur)
            cur = [orbs[a]]
    units.append(cur)
    nsingle = sum(1 for u in units if len(u) == 1)
    print("small units %d (%d single orbit chains), orbit chains %d (%.0fs)" % (len(units), nsingle, len(orbs),
        time.time() - t0), flush=True)
    # ---- walk chains: the walks of SEL are transported again, in the order of gen13.py; every full row of a
    # transported walk gives two candidate cuts of its chain (ways A and B), stored with their first word
    import math
    import struct
    rows = G.read_sel(selp)
    assert len(rows[0][0]) == K
    walks = sorted(G.sel_walks([r for r in rows if r[2] >= 0]), key=len)
    chains = []                     # (walk index, lifted index, first trail index, number of trails)
    cand = []                       # S (K bytes) + packed (chain, i0, option): sorts by S
    firstc = {}
    tcount = nsmall
    for wi, wk in enumerate(walks):
        for li, W2 in enumerate(G13.transport_walk(wk)):
            nf = sum(1 for r in W2 if r[2] == K2)
            g = math.gcd(K2 - 1, nf - (len(W2) - nf))
            assert g == K2 - 1, "a lifted walk that does not give K trails"
            ci = len(chains)
            chains.append((wi, li, tcount, g))
            tcount += g
            for i0, r in enumerate(W2):
                if r[2] == K2:
                    bb = bytes(r[0])
                    cand.append(bb[:K] + struct.pack(">HHB", ci, i0, 0))
                    cand.append(bb[1:] + struct.pack(">HHB", ci, i0, 1))
                    if ci not in firstc:
                        firstc[ci] = (i0, 0, bb)
    assert tcount == len(tab), "trail count differs from the table"
    print("walk chains %d, candidate cuts %d (%.0fs)" % (len(chains), len(cand), time.time() - t0), flush=True)
    cand.sort()
    allb = bytes(range(K2))

    def slice_of(S, opt):
        """the full row b (K + 1 letters) of a candidate from its first word S: way A has S = b[:K], way B S = b[1:]"""
        miss = bytes(c for c in allb if c not in S)
        assert len(miss) == 1
        return S + miss if opt == 0 else miss + S

    # small candidates: (S, unit, rotation)
    scand = []
    for ui, u in enumerate(units):
        if len(u) == 1:
            for i in range(K):
                scand.append((words[u[0][i]], ui, i))
        else:
            scand.append((words[u[0][0]], ui, 0))
    scand.sort()
    skeys = [c[0] for c in scand]
    used_s = bytearray(len(units))
    used_c = bytearray(len(chains))

    def find(E):
        """best unused unit after a word E: (overlap, kind, index in its candidate table)"""
        for k in range(h - 1, 2, -1):
            pre = E[-k:]
            a = bisect.bisect_left(skeys, pre)
            while a < len(skeys) and skeys[a][:k] == pre:
                if not used_s[scand[a][1]]:
                    return k, "S", a
                a += 1
            a = bisect.bisect_left(cand, pre)
            lim = a + 4000
            while a < len(cand) and a < lim and cand[a][:k] == pre:
                if not used_c[struct.unpack(">HHB", cand[a][K:])[0]]:
                    return k, "W", a
                a += 1
        return 0, None, -1

    seq = []                        # ("S", unit, rotation) / ("W", chain, i0, option, b)
    left = len(units) + len(chains)
    pick = ("S", 0, 0)
    ps = pw = 0
    hist = collections.Counter()
    while True:
        seq.append(pick)
        left -= 1
        if pick[0] == "S":
            used_s[pick[1]] = 1
            u = units[pick[1]]
            E = words[u[0][(pick[2] - 1) % K]] if len(u) == 1 else words[u[-1][-1]]
        else:
            used_c[pick[1]] = 1
            b = pick[4]
            E = (b[K:] + b[:K - 1]) if pick[3] == 0 else b[:K]
        if not left:
            break
        k, kind, a = find(E)
        hist[h - k if kind else -1] += 1
        if kind == "S":
            pick = ("S", scand[a][1], scand[a][2])
        elif kind == "W":
            ci, i0, opt = struct.unpack(">HHB", cand[a][K:])
            pick = ("W", ci, i0, opt, slice_of(cand[a][:K], opt))
        else:
            while ps < len(units) and used_s[ps]:
                ps += 1
            if ps < len(units):
                pick = ("S", ps, 0)
            else:
                while used_c[pw]:
                    pw += 1
                pick = ("W", pw, firstc[pw][0], 0, firstc[pw][2])
    print("greedy order: joins between units by cost (-1 = nothing fits): %s (%.0fs)" % (dict(sorted(hist.items())),
        time.time() - t0), flush=True)
    del cand
    # ---- events of the walk chains.  For the chosen row of every walk the walk is completed again; each trail is
    # found in the table (same R), the vertex at which its piece was written gives its rotation r, and the trail
    # that passes the row with the completion letter in gap q is cut at the weight-2 step after class q.
    chosen = {p[1]: p for p in seq if p[0] == "W"}
    wev = {}                        # chain -> list of (text, len, S, E)
    tidx = nsmall
    cnum = 0
    for wi, wk in enumerate(walks):
        for li, W2 in enumerate(G13.transport_walk(wk)):
            ci = cnum               # chains are numbered in this same order
            cnum += 1
            wi_, li_, t0i, g = chains[ci]
            assert (wi_, li_) == (wi, li) and t0i == tidx
            _, _, i0, opt, b = chosen[ci]
            assert bytes(W2[i0][0]) == b and W2[i0][2] == K2
            trs = []
            for sl, at in G13.complete_detail(W2, z, i0):
                offs = [0]
                for (bb, s, v) in sl:
                    offs.append(offs[-1] + (n + 1) * v + 1)
                R = offs[-1]
                assert R == Rt[tidx], "R differs from the table"
                hw = cyc(tidx, 0, h)
                r = None
                for q, (bb, s, v) in enumerate(sl):
                    if bytes(bb[:h]) == hw:
                        r = offs[q]
                        break
                assert r is not None, "written vertex not found"
                trs.append((tidx, R, offs, at, r))
                tidx += 1
            byport = {}
            for tr in trs:
                for q in tr[3]:
                    byport[q] = tr
            bt = tuple(b)
            evs = []
            prevE = None
            lifts = range(0, g) if opt == 0 else range(1, g + 1)
            for q in lifts:
                port = q if q < K2 - 1 else 0
                t, R, offs, at, r = byport[port]
                si = at[port] + (1 if q == K2 - 1 else 0)
                B = ins(bt, z, q)
                S = bytes(rot(B, q + 1)[:h])
                E = bytes(rot(B, q + 2)[:h])
                assert prevE is None or prevE == S
                prevE = E
                start = (offs[si] + (q + 1) * (n + 1) - r) % R
                evs.append(("O %d %d 2 0" % (t, start), R + h + 1, S, E))
            assert len({e[0].split()[1] for e in evs}) == g
            wev[ci] = evs
    # ---- the new plan: small units keep their events (a single orbit chain is rotated to its chosen first trail)
    out = []
    for p in seq:
        if p[0] == "S":
            u = units[p[1]]
            if len(u) == 1:
                o = u[0]
                idx = [o[(p[2] + i) % K] for i in range(K)]
            else:
                idx = [i for o in u for i in o]
            for i in idx:
                t = int(ev[i].split()[1])
                out.append((ev[i], Rt[t] + h, words[i], words[i]))
        else:
            out += wev[p[1]]
    assert len(out) == len(ev) and len({int(e[0].split()[1]) for e in out}) == len(tab)
    length = sum(e[1] for e in out)
    joins = collections.Counter()
    for i in range(len(out) - 1):
        k = ov(out[i][3], out[i + 1][2])
        length -= k
        joins[h - k] += 1
    sumR = sum(Rt)
    print("new plan: %d events; joins by cost %s" % (len(out), dict(sorted(joins.items()))))
    print("new plan: predicted model length %d = h + sum R + %d (%.3f per trail)" % (length, length - h - sumR,
        (length - h - sumR) / float(len(tab))))
    with open(planout, "w", newline="\n") as fp:
        fp.write("TRAILSEARCH-PLAN %d %s %d\n" % (n, hdr[2], len(out)))
        for e in out:
            fp.write(e[0] + "\n")
    print("wrote %s (%.0fs)" % (planout, time.time() - t0))


if __name__ == "__main__":
    main()
