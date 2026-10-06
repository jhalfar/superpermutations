#!/usr/bin/env python
"""plan13n.py - chained start plan for a base word of geng.py, written from the selection and the table alone.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: plan13n.py SEL BASE.txt BASE.tsv PLAN_OUT [--assign N] [--time SEC]

  SEL       selection, one line per loop: "x v", x an order of the K letters, v the number of visible classes of
            its row (K a full row, K - 2 a short row, 1 .. K - 3 rows of other lengths, 0 a loop without a row).
            n = K + 2, h = K - 1.
  BASE.txt  the base word that geng.py wrote from SEL (mapped; only h-letter words are read from it)
  BASE.tsv  its table: kind, slices, R, offset of the piece; trail t is line t
  PLAN_OUT  the plan
  --assign  rounds of the assignment order (default 3; 0 = greedy order only)
  --time    time limit of the integer program in seconds (default 300)

It works at any n.  The name is from n = 13, where the loader of the search programs needs 11 to 13 GB and this
script needs none of it; the start plan of the n = 13 word came from here.

Trails are numbered as geng.py writes them: the loops without a row in the order of the file, then the walks by
length (stable), the trails of a walk by their smallest port at its first row.  The script asserts that the number
of trails and the R of every trail it cuts agree with the table.

Units of the plan:
  small trails   Loops without a row.  A link is two such loops consecutive in one F-orbit (c, m).  The largest set
                 of links with one orbit per loop is found by an integer program (old_chains in gen13.py).  A chain
                 is written with every trail cut at its vertex without m: joins of cost 1.  A loop with no link may
                 be cut at any of its K vertices.
  walk trails    At a full row b of a walk, the trail that passes with the completion letter in gap q is cut at
                 the step of weight 2 after class q of that row (cost 1); the trails of consecutive gaps then join
                 at cost 0.  A walk whose K - 1 ports are K - 1 different trails gives one chain of K - 1 at any
                 full row, in two ways (gaps 0 .. K-2 or 1 .. K-1).  For other walks (rows of other lengths merge
                 ports into fewer trails) the longest runs of consecutive gaps that belong to different trails are
                 taken, row by row, until no run of two is left; the trails that remain are single events, the
                 piece as written.
Order of the units:
  greedy       After a unit that ends with the word E, the unused unit whose first word overlaps E most (overlaps
               K - 2 down to 3; for the chains of K - 1 walk trails at most 4,000 table entries are examined per
               overlap); if nothing overlaps, the next unused unit.
  assignment   (--assign N) Each round: for the order as it is, every chain of K - 1 walk trails gets its best
               row and way, every single small trail its best vertex; then the cheapest successor for all units
               at once (a linear assignment on the costs of the joins between unit ends); its cycles are joined
               one by one, each time the smallest cycle with the cheapest exchange of two successors; the closed
               order is opened at its most expensive join; cuts are chosen again.  A round is kept if the plan got
               shorter, otherwise the rounds stop.

What is exact and what is not.  The number of links of the small trails is exact when the solver's status is 2
(optimal).  The value of the assignment ("assignment bound") is a lower bound for a CLOSED order of these units
with these end words: every unit has a successor there.  The plan is an open order with one join fewer, so its
unit joins can lie up to h below that value, and no further (at n = 11 the program prints 1,110 against a bound of
1,118).  The value moves when cuts are chosen again, and it says nothing about other cuts inside the chains or about
the piece set.  The order itself is a heuristic.

Prints the counts of rows, loops and walks, the chains of small trails, the walk chains, the joins of the greedy
order between units by cost (-1: nothing overlapped), for every assignment round the sum of the unit joins before
and after with the assignment bound and its number of cycles, and at the end the joins of the plan by cost and its
model length h + sum R + cuts + joins.  applyplan.py writes the word; its length equals the model length.

Needs: Python 3; geng.py, gen13.py and gen12.py from the same repository next to this file or on PYTHONPATH;
Gurobi (gurobipy, with a licence beyond the size-limited one) if SEL has loops without a row; numpy and scipy for
--assign above 0.
Time and memory, measured: n = 11 (880 trails, 206 units) 2 s and 0.13 GB with the assignment.
n = 13 (23,808 trails, 5,280 units): 185 s and 1.05 GB with the three assignment rounds, numpy held to two
threads; the run of the day, with numpy free, shows 2.43 GB.

Words.  In the names of the code and the text printed, an "opening" is a cut and a "lift" of a row is the row with
the completion letter in one of its gaps.
"""
import argparse
import bisect
import collections
import mmap
import os
import struct
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen13 as G13
import geng

ALPH = "0123456789ABCDEF"
FROMTXT = bytes((ALPH.index(chr(c)) if chr(c) in ALPH else 255) for c in range(256))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sel")
    ap.add_argument("base")
    ap.add_argument("tsv")
    ap.add_argument("planout")
    ap.add_argument("--time", type=float, default=300)
    ap.add_argument("--assign", type=int, default=3, help="rounds of the assignment order (0 = greedy order only)")
    a = ap.parse_args()
    t0 = time.time()
    tab =[l.split("\t") for l in open(a.tsv)]
    Rt = [int(t[2]) for t in tab]
    st = [int(t[3]) for t in tab]
    kindt = [t[0] for t in tab]
    fb = open(a.base, "rb")
    W = mmap.mmap(fb.fileno(), 0, access=mmap.ACCESS_READ)
    blen = len(W) - (1 if W[len(W) - 1:len(W)] == b"\n" else 0)

    # ---- selection
    vof = {}
    dloops = []
    for line in open(a.sel):
        if line.startswith("#") or not line.strip():
            continue
        p = line.split()
        x = p[0].encode().translate(FROMTXT)
        v = int(p[1])
        if v == 0:
            dloops.append(x)
        else:
            vof[x] = v
    K = len(dloops[0]) if dloops else len(next(iter(vof)))
    n, h = K + 2, K - 1
    sb, zb = bytes((K,)), bytes((K + 1,))
    step = geng.step
    PI = {v: [geng.port_perm(v, j, K) for j in range(K - 1)] for v in list(range(1, K - 1)) + [K]}
    walks = []
    for x0 in list(vof):
        if vof[x0] < 0:
            continue
        wk, x = [], x0
        while True:
            v = vof[x]
            if v < 0:
                break
            vof[x] = -v
            wk.append(x)
            x = step(x, v, K)
        assert x == x0
        walks.append(wk)
    walks.sort(key=len)
    nsmall = len(dloops)
    assert all(k == "D" for k in kindt[:nsmall]) and (nsmall == len(tab) or kindt[nsmall] != "D")
    print("K = %d (n = %d): rows %d, loops without a row %d, walks %d (%.0fs)" % (K, n, len(vof), nsmall, len(walks),
        time.time() - t0), flush=True)

    def head_at(t):
        """the first h letters of the piece of trail t in the base word, as letter values"""
        return W[st[t]:st[t] + h].translate(FROMTXT)

    def ov(e, s):
        """largest overlap of the end of word e with the start of word s"""
        for q in range(h, 0, -1):
            if e[-q:] == s[:q]:
                return q
        return 0

    # ---- small trails: chains.  A small trail is K slices of sl1 letters, each a whole 2-cycle that starts at a
    # vertex; trail i belongs to the i-th loop without a row of the file.
    sl1 = (n + 1) * (K + 1) + 1
    canon = G13.canon
    tix = {}
    for i, x in enumerate(dloops):
        tix[canon(tuple(x))] = i
        assert Rt[i] == K * sl1
    units0 = G13.old_chains(dloops, K, a.time) if dloops else []

    def small_event(x, i):
        """event of the small trail of loop x (tuple read from its smallest letter) cut at the vertex that starts
        with x[i]: (plan line, letters written, first word, last word).  The piece in the base word starts at the
        vertex that begins with x[ir]; the wanted vertex lies i - ir slices further."""
        t = tix[x]
        xb = bytes(x)
        hw = head_at(t)
        ir = next(q for q in range(K) if (xb[q:] + xb[:q])[:h] == hw)
        wd = (xb[i:] + xb[:i])[:h]
        return ("O %d %d 3 0" % (t, ((i - ir) * sl1) % Rt[t]), Rt[t] + h, wd, wd)

    fixed = []          # units with fixed events: list of [events]
    singles = []        # small trails with no link: canonical loop
    for un in units0:
        if un[0][1] is None:
            singles.append(un[0][0])
        else:
            evs = [small_event(x, b0) for (x, b0) in un]
            for e1, e2 in zip(evs, evs[1:]):
                assert ov(e1[3], e2[2]) == h - 1
            fixed.append(evs)
    nchain_small = len(fixed)
    print("small trails: %d chains + %d singles (%.0fs)" % (nchain_small, len(singles), time.time() - t0), flush=True)

    # ---- walks: trails, chains.  A trail of a walk is an orbit of ports: the ports are followed once around the
    # walk (arr = the permutation they undergo), lab[p] = number of the trail of port p at the first row.
    tfirst = []         # first trail index of each walk
    ntrail = []
    label0 = []         # per walk: trail (local index) of each port at row 0
    tcount = nsmall
    wchain = []         # walks with K - 1 trails: candidates in the greedy
    cand = []
    firstc = {}
    wanted = collections.defaultdict(dict)       # walk -> {(row, port): None -> letter offset}
    pending = []        # (walk, [ (local trail, row, lift q) ... ]) chains of block walks; events made after pass 2
    psingle = []        # (walk, local trail)
    runhist = collections.Counter()
    for wi, wk in enumerate(walks):
        m = len(wk)
        arr = list(range(K - 1))
        for x in wk:
            T = PI[-vof[x]]
            arr = [T[q] for q in arr]
        lab = [-1] * (K - 1)
        nt = 0
        for p0 in range(K - 1):
            if lab[p0] >= 0:
                continue
            p = p0
            while lab[p] < 0:
                lab[p] = nt
                p = arr[p]
            nt += 1
        tfirst.append(tcount)
        ntrail.append(nt)
        label0.append(lab)
        tcount += nt
        if nt == K - 1:
            ci = len(wchain)
            wchain.append(wi)
            for i0, x in enumerate(wk):
                if vof[x] == -K:
                    cand.append(x[:K - 1] + struct.pack(">HHB", ci, i0, 0))
                    cand.append(x[1:] + struct.pack(">HHB", ci, i0, 1))
                    if ci not in firstc:
                        firstc[ci] = (i0, x)
            continue
        # other walks: runs of consecutive gaps at full rows with different trails
        rowsfull = []
        cur = lab[:]
        for i0, x in enumerate(wk):
            v = -vof[x]
            if v == K:
                rowsfull.append((i0, cur[:] + [cur[0]]))        # trail of the lifts 0 .. K-1 (lift K-1 = port 0)
            T = PI[v]
            nxt = [0] * (K - 1)
            for q in range(K - 1):
                nxt[T[q]] = cur[q]
            cur = nxt
        assert cur == lab or sorted(cur) == sorted(lab)
        used = set()
        chains = []
        while len(used) < nt:
            best = None
            for i0, ls in rowsfull:
                q = 0
                while q < K:
                    if ls[q] in used:
                        q += 1
                        continue
                    seen = {ls[q]}
                    e = q + 1
                    while e < K and ls[e] not in used and ls[e] not in seen:
                        seen.add(ls[e])
                        e += 1
                    if best is None or e - q > best[0]:
                        best = (e - q, i0, q, [ls[j] for j in range(q, e)])
                    q += 1
            if best is None or best[0] < 2:
                break
            L, i0, q0, ts = best
            chains.append([(ts[j], i0, q0 + j) for j in range(L)])
            used.update(ts)
            runhist[L] += 1
            for j in range(L):
                q = q0 + j
                wanted[wi][(i0, q if q < K - 1 else 0)] = None
        for ch in chains:
            pending.append((wi, ch))
        for tl in range(nt):
            if tl not in used:
                psingle.append((wi, tl))
                runhist[1] += 1
    assert tcount == len(tab), "trail count differs from the table (%d, %d)" % (tcount, len(tab))
    print("walks with %d trails: %d (candidate cuts %d); other walks %d: runs by length %s (%.0fs)" % (
        K - 1, len(wchain), len(cand), len(walks) - len(wchain), dict(sorted(runhist.items())), time.time() - t0),
        flush=True)
    cand.sort()

    # ---- words of the fixed walk units (known from the rows), events completed after the offsets are known
    def lift_words(xb, q):
        """first and last word of the trail that passes the full row xb with the completion letter in gap q, when it
        is cut at the weight-2 step after class q of that row"""
        B = xb[:q] + zb + xb[q:]
        return (B[q + 1:] + B[:q + 1])[:h], ((B + B)[q + 2:q + 2 + h])

    wfixed = []         # [(walk, [(local trail, row, q, S, E)])]
    for wi, ch in pending:
        wk = walks[wi]
        evs = []
        prevE = None
        for (tl, i0, q) in ch:
            S, E = lift_words(wk[i0], q)
            assert prevE is None or prevE == S
            prevE = E
            evs.append((tl, i0, q, S, E))
        wfixed.append((wi, evs))

    # ---- greedy order
    # table of the units with a fixed first word and of the small singles (any vertex)
    scand = []          # (S, kind, index, variant)
    for ui, evs in enumerate(fixed):
        scand.append((evs[0][2], 0, ui, 0))
    for ui, (wi, evs) in enumerate(wfixed):
        scand.append((evs[0][3], 1, ui, 0))
    for ui, x in enumerate(singles):
        xb = bytes(x)
        for i in range(K):
            scand.append(((xb[i:] + xb[:i])[:h], 2, ui, i))
    pwords = []
    for ui, (wi, tl) in enumerate(psingle):
        hw = head_at(tfirst[wi] + tl)
        pwords.append(hw)
        scand.append((hw, 3, ui, 0))
    scand.sort()
    skeys = [c[0] for c in scand]
    usedu = [bytearray(len(fixed)), bytearray(len(wfixed)), bytearray(len(singles)), bytearray(len(psingle))]
    usedc = bytearray(len(wchain))

    def find(E):
        """the unused unit whose first word has the largest overlap with the word E: (overlap, unit) or (0, None).
        Units with a fixed first word and single trails are looked up in scand, chains of K - 1 walk trails in cand
        (any full row, two ways)."""
        for k in range(h - 1, 2, -1):
            pre = E[-k:]
            i = bisect.bisect_left(skeys, pre)
            while i < len(skeys) and skeys[i][:k] == pre:
                c = scand[i]
                if not usedu[c[1]][c[2]]:
                    return k, c
                i += 1
            i = bisect.bisect_left(cand, pre)
            lim = i + 4000
            while i < len(cand) and i < lim and cand[i][:k] == pre:
                ci, i0, opt = struct.unpack(">HHB", cand[i][K - 1:])
                if not usedc[ci]:
                    return k, ("W", ci, i0, opt)
                i += 1
        return 0, None

    seq = []
    left = len(fixed) + len(wfixed) + len(singles) + len(psingle) + len(wchain)
    pick = scand[0] if scand else ("W", 0, firstc[0][0], 0)
    ptr = [0, 0, 0, 0]
    pw = 0
    hist = collections.Counter()
    while True:
        seq.append(pick)
        left -= 1
        if pick[0] == "W":
            usedc[pick[1]] = 1
            xb = walks[wchain[pick[1]]][pick[2]]
            E = (xb[K - 1:] + xb[:K - 2]) if pick[3] == 0 else xb[:K - 1]
        else:
            usedu[pick[1]][pick[2]] = 1
            if pick[1] == 0:
                E = fixed[pick[2]][-1][3]
            elif pick[1] == 1:
                E = wfixed[pick[2]][1][-1][4]
            else:
                E = pick[0]
        if not left:
            break
        k, c = find(E)
        hist[h - k if c else -1] += 1
        if c is None:
            c = None
            for kd in (0, 1, 2, 3):
                while ptr[kd] < len(usedu[kd]) and usedu[kd][ptr[kd]]:
                    ptr[kd] += 1
                if ptr[kd] < len(usedu[kd]):
                    ui = ptr[kd]
                    if kd == 0:
                        c = (fixed[ui][0][2], 0, ui, 0)
                    elif kd == 1:
                        c = (wfixed[ui][1][0][3], 1, ui, 0)
                    elif kd == 2:
                        c = (bytes(singles[ui])[:h], 2, ui, 0)
                    else:
                        c = (pwords[ui], 3, ui, 0)
                    break
            if c is None:
                while usedc[pw]:
                    pw += 1
                c = ("W", pw, firstc[pw][0], 0)
        pick = c
    print("greedy order: joins between units by cost (-1 = nothing fitted): %s (%.0fs)" % (dict(sorted(hist.items())),
        time.time() - t0), flush=True)
    del cand, scand, skeys

    # ---- better order: assignment (cheapest successor for all units at once), cycles joined, cuts re-chosen
    def words(p):
        """first and last word of a unit as it stands in the order"""
        if p[0] == "W":
            xb = walks[wchain[p[1]]][p[2]]
            return (xb[:K - 1], xb[K - 1:] + xb[:K - 2]) if p[3] == 0 else (xb[1:], xb[:K - 1])
        if p[1] == 0:
            return fixed[p[2]][0][2], fixed[p[2]][-1][3]
        if p[1] == 1:
            return wfixed[p[2]][1][0][3], wfixed[p[2]][1][-1][4]
        return p[0], p[0]

    def total(sq):
        """sum of the costs of the joins between consecutive units of the order sq"""
        c, prev = 0, None
        for p in sq:
            S, E = words(p)
            if prev is not None:
                c += h - ov(prev, S)
            prev = E
        return c

    def rechoose(sq):
        """for the order as it is: the best cut of every chain of K - 1 walk trails (any full row, two ways) and
        the best vertex of every single small trail, one unit at a time"""
        sq = list(sq)
        U = len(sq)
        for i, p in enumerate(sq):
            if not (p[0] == "W" or p[1] == 2):
                continue
            pe = words(sq[i - 1])[1] if i > 0 else None
            ns = words(sq[i + 1])[0] if i + 1 < U else None
            best = None
            if p[0] == "W":
                for i0, xb in enumerate(walks[wchain[p[1]]]):
                    if vof[xb] != -K:
                        continue
                    for opt in (0, 1):
                        S, E = (xb[:K - 1], xb[K - 1:] + xb[:K - 2]) if opt == 0 else (xb[1:], xb[:K - 1])
                        c = (h - ov(pe, S) if pe is not None else 0) + (h - ov(E, ns) if ns is not None else 0)
                        if best is None or c < best[0]:
                            best = (c, ("W", p[1], i0, opt))
            else:
                xb = bytes(singles[p[2]])
                for q in range(K):
                    wd = (xb[q:] + xb[:q])[:h]
                    c = (h - ov(pe, wd) if pe is not None else 0) + (h - ov(wd, ns) if ns is not None else 0)
                    if best is None or c < best[0]:
                        best = (c, (wd, 2, p[2], q))
            sq[i] = best[1]
        return sq

    def assign(sq):
        """a new order of the units of sq: the cheapest successor for every unit at once (linear assignment on
        C[u][v] = h - overlap of the last word of u with the first word of v), the cycles of that assignment joined
        into one (the smallest cycle each time, with the exchange of two successors that costs least), the closed
        order opened at its most expensive join.  Returns (order, value of the assignment, number of its cycles).
        C is a dense matrix of units by units in 16-bit numbers."""
        import numpy as np
        from scipy.optimize import linear_sum_assignment
        U = len(sq)
        Wd = [words(p) for p in sq]
        C = np.full((U, U), h, dtype=np.int16)
        for k in range(1, h + 1):
            dE = collections.defaultdict(list)
            dS = collections.defaultdict(list)
            for u, (S, E) in enumerate(Wd):
                dE[E[-k:]].append(u)
                dS[S[:k]].append(u)
            for key, us in dE.items():
                vs_ = dS.get(key)
                if vs_:
                    C[np.ix_(us, vs_)] = h - k
        np.fill_diagonal(C, 1000)
        row, col = linear_sum_assignment(C)
        succ = col.copy()
        lb = int(C[row, col].sum())
        lab = -np.ones(U, dtype=np.int64)
        alive = {}
        for u in range(U):
            if lab[u] < 0:
                cyc, x = [], u
                while lab[x] < 0:
                    lab[x] = u
                    cyc.append(x)
                    x = succ[x]
                alive[u] = cyc
        ncyc = len(alive)
        while len(alive) > 1:
            ia = min(alive, key=lambda q: len(alive[q]))
            A = np.array(alive[ia])
            B = np.nonzero(lab != ia)[0]
            sA, sB = succ[A], succ[B]
            d = (C[np.ix_(A, sB)].astype(np.int32) + C[np.ix_(B, sA)].T
                 - C[A, sA].astype(np.int32)[:, None] - C[B, sB].astype(np.int32)[None, :])
            ai, bi = np.unravel_index(int(np.argmin(d)), d.shape)
            a_, b_ = int(A[ai]), int(B[bi])
            succ[a_], succ[b_] = succ[b_], succ[a_]
            ib = int(lab[b_])
            alive[ib] = alive[ib] + alive[ia]
            lab[A] = ib
            del alive[ia]
        arc = C[np.arange(U), succ]
        cut = int(np.argmax(arc))
        order = []
        x = int(succ[cut])
        for _ in range(U):
            order.append(x)
            x = int(succ[x])
        assert len(set(order)) == U and order[-1] == cut
        return [sq[u] for u in order], lb, ncyc

    if a.assign and len(seq) > 2:
        best = (total(seq), seq)
        print("order: greedy %d" % best[0], flush=True)
        cur = seq
        for rnd in range(a.assign):
            cur = rechoose(cur)
            c1 = total(cur)
            cur, lb, ncyc = assign(cur)
            c2 = total(cur)
            cur = rechoose(cur)
            c3 = total(cur)
            print("order round %d: cuts re-chosen %d, assignment bound %d in %d cycles, joined %d, cuts re-chosen %d (%.0fs)" % (
                rnd + 1, c1, lb, ncyc, c2, c3, time.time() - t0), flush=True)
            if c3 < best[0]:
                best = (c3, cur)
            else:
                break
        seq = best[1]
    for p in seq:
        if p[0] == "W":
            wi = wchain[p[1]]
            for q in (range(0, K - 1) if p[3] == 0 else range(1, K)):
                wanted[wi][(p[2], q if q < K - 1 else 0)] = None

    # ---- pass 2: where the cuts are, in letters.  Every trail that gets a cut is followed once along its port path;
    # the lengths of the slices it passes are added up (L1 letters for a whole 2-cycle), which gives the offset of
    # every wanted row in the trail and, as a check, R.  rot_of: the offset at which the piece in the base word starts.
    L1 = (n + 1) * (K + 1) + 1
    rot_of = {}         # trail -> written rotation (letters), for the trails with events
    for wi, want in wanted.items():
        wk = walks[wi]
        m = len(wk)
        vs = [-vof[x] for x in wk]
        wrows = {i0 for (i0, p) in want}
        done = bytearray(K - 1)
        tl = 0
        for p0 in range(K - 1):
            if done[p0]:
                continue
            t = tfirst[wi] + tl
            off = 0
            i, p = 0, p0
            while True:
                if i == 0:
                    done[p] = 1
                if i in wrows and (i, p) in want:
                    want[(i, p)] = (tl, off)
                v = vs[i]
                if v == K:
                    off += 2 * L1 if p == 0 else L1
                elif p != v:
                    off += (n + 1) * (v + (1 if p < v else 0)) + 1
                else:
                    off += 2 * ((n + 1) * v + 1) + (K - v) * L1
                p = PI[v][p]
                i += 1
                if i == m:
                    i = 0
                if i == 0 and p == p0:
                    break
            assert off == Rt[t], "R of trail %d differs from the table" % t
            # written rotation: the piece starts at a slice head; usually the first slice
            x0 = wk[0]
            h0 = (x0[:p0] + zb + x0[p0:])[:h]
            hw = head_at(t)
            if h0 == hw:
                rot_of[t] = 0
            else:
                sls = []
                i, p = 0, p0
                while True:
                    sls += geng.port_path(wk[i], vs[i], p, K, sb, zb)
                    p = PI[vs[i]][p]
                    i += 1
                    if i == m:
                        i = 0
                    if i == 0 and p == p0:
                        break
                o = 0
                r = None
                for s_ in sls:
                    if s_[0][:h] == hw:
                        r = o
                        break
                    o += (n + 1) * s_[2] + 1
                assert r is not None
                rot_of[t] = r
            tl += 1
        assert tl == ntrail[wi]
    print("offsets of the cut slices computed (%.0fs)" % (time.time() - t0), flush=True)

    def walk_event(wi, i0, q):
        """event of the trail of walk wi that passes row i0 with the completion letter in gap q, cut at the weight-2
        step after class q: (plan line, letters written, first word, last word)"""
        port = q if q < K - 1 else 0
        tl, off = wanted[wi][(i0, port)]
        t = tfirst[wi] + tl
        if q == K - 1:
            off += L1                     # second slice of the path of port 0
        S, E = lift_words(walks[wi][i0], q)
        start = (off + (q + 1) * (n + 1) - rot_of[t]) % Rt[t]
        return ("O %d %d 2 0" % (t, start), Rt[t] + h + 1, S, E)

    out = []
    for p in seq:
        if p[0] == "W":
            wi = wchain[p[1]]
            evs = [walk_event(wi, p[2], q) for q in (range(0, K - 1) if p[3] == 0 else range(1, K))]
            assert len({e[0].split()[1] for e in evs}) == K - 1
            for e1, e2 in zip(evs, evs[1:]):
                assert e1[3] == e2[2]
            out += evs
        elif p[1] == 0:
            out += fixed[p[2]]
        elif p[1] == 1:
            wi, evs = wfixed[p[2]]
            for (tl, i0, q, S, E) in evs:
                e = walk_event(wi, i0, q)
                assert e[2] == S and e[3] == E and int(e[0].split()[1]) == tfirst[wi] + tl
                out.append(e)
        elif p[1] == 2:
            out.append(small_event(singles[p[2]], p[3]))
        else:
            wi, tl = psingle[p[2]]
            t = tfirst[wi] + tl
            out.append(("P %d" % t, Rt[t] + h, pwords[p[2]], pwords[p[2]]))
    assert len(out) == len(tab) and len({int(e[0].split()[1]) for e in out}) == len(tab), "not every trail once"
    length = sum(e[1] for e in out)
    joins = collections.Counter()
    for i in range(len(out) - 1):
        k = ov(out[i][3], out[i + 1][2])
        length -= k
        joins[h - k] += 1
    sumR = sum(Rt)
    ncut = sum(1 for e in out if e[0].endswith(" 2 0"))
    print("plan: %d events; small chains %d, small singles %d, chains of %d walk trails %d, other walk chains %d, single walk trails %d; cuts at weight-2 steps %d" % (
        len(out), nchain_small, len(singles), K - 1, len(wchain), len(wfixed), len(psingle), ncut))
    print("plan: joins by cost %s" % dict(sorted(joins.items())))
    print("plan: predicted model length %d = h + sum R + %d (%.3f per trail)" % (length, length - h - sumR,
        (length - h - sumR) / float(len(tab))))
    with open(a.planout, "w", newline="\n") as fp:
        fp.write("TRAILSEARCH-PLAN %d %d %d\n" % (n, blen, len(out)))
        for e in out:
            fp.write(e[0] + "\n")
    print("wrote %s (%.0fs)" % (a.planout, time.time() - t0))


if __name__ == "__main__":
    main()
