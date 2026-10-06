"""lns.py - neighbourhood search on a selection of full and short rows, with the exact floor as objective.

This is how the 9-symbol selection of n = 10 was found: Pantone's 8-symbol selection transported once has four
closed walks (28 closed trails after completion); the search joins them into two (14 closed trails) by changing 32
rows, and Q and the loops without a row stay as they are.

    cost = 2 * (short rows) + (loops without a row) + (closed trails of all walks after completion)
         = Q + closed trails after completion, the floor of the selection.

One round: a ball of about --free loops around a random centre in the graph of loops (two loops are neighbours when
they differ by the exchange of two cyclically adjacent letters), closed under the segments of the present
selection, is freed; everything else stays.  A segment is a short row followed by j - 1 full rows.  The integer
programme over the segments inside the region (j = 1 .. K-2; a loop may also get no row) minimises 2 t + (loops
without a row); it does not see the walks.  So a pool of its best solutions is measured with the exact cost, and the
best one is taken when it is better than the present selection (or equal, with --plateau).  A walk of full rows only
is turned into loops without a row at the start (same number of closed trails).

Nothing is proved by this search.  What is known about its result for n = 10: the floor 2,702 = 2,352 + 336 + 14
(Pantone's 8-symbol selection transported once: 2,716); in the 120 rounds of the original run no region programme
lowered 2 t + (loops without a row) = 2,688.

The random choices depend on the order of the loops, which is the order of the input file.  --order walk lists the
loops walk by walk first (each walk from its least state, the walks in increasing order of that state, then the
loops without a row in increasing order); this is the order of the file that the run for n = 10 read.  With it
    python lns.py base8.txt OUT --transport 1 --order walk --free 300 --rounds 3 --time 30 --pool 40 --seed 1
                  --threads 2
writes the n = 10 selection again, data line for data line (3 s; found in the third round, Gurobi 13.0).  Another
order, seed or solver version gives another search and need not end at the same selection.

usage:    python lns.py IN OUT [--transport n] [--order walk] [--free R] [--rounds N] [--time SEC] [--total SEC]
                        [--pool P] [--seed S] [--plateau] [--threads T] [--centre any|det|short] [--maxseg J]
                        [--gapabs G] [--every N]
          --transport n   transport IN n times first        --centre   draw the centres from all loops, from the
          --time          seconds per region programme                 loops without a row, or from the short rows
          --total         seconds in all                    --maxseg   longest segment (default K - 2)
          --gapabs        let the region programme be this much worse in 2 t + (loops without a row)
          --every         print a line every N rounds
inputs:   IN    a selection of full and short rows ("x v" lines or F S D, see gcore.py), or construction-input.txt
outputs:  OUT   the selection after every improvement and at the end (letters F, S, D; LF line ends)
          text: one line per improvement or every --every rounds, and the numbers of the final selection
                ("detached" in that text means a loop without a row)
needs:    Python 3, gcore.py, Gurobi with its Python package gurobipy.
          Gurobi needs a full licence: academic licences are free, and the size-limited licence that
          comes with the package is too small for these models.
cost:     measured here for K = 8 (5,040 loops): 1 s per round, 0.05 GB.
"""
import argparse
import math
import random
import time
from collections import Counter
from fractions import Fraction

import gurobipy as gp
from gurobipy import GRB

from gcore import canon, gstep, read_any, write_gsel, walks, walk_trails, transport


def seg_states(u, j):
    """The segment (u, j): a short row at the state u followed by j - 1 full rows.  Returns the list of its j
    states and the state at which the next segment starts."""
    K = len(u)
    st = [u]
    v = gstep(u, K - 2)
    for _ in range(j - 1):
        st.append(v)
        v = gstep(v, K)
    return st, v


def segments_of(sel):
    """Cut every closed walk at its short rows.  Returns (dict start state -> j for all segments, list of the
    walks that have no short row)."""
    K = len(next(iter(sel)))
    ws, chosen = walks(sel)
    segs = {}
    pure = []
    for w in ws:
        kinds = [chosen[x] for x in w]
        if K - 2 not in kinds:
            pure.append(w)
            continue
        i0 = kinds.index(K - 2)
        w = w[i0:] + w[:i0]
        kinds = kinds[i0:] + kinds[:i0]
        i = 0
        while i < len(w):
            j = 1
            while i + j < len(w) and kinds[i + j] == K:
                j += 1
            segs[w[i]] = j
            i += j
    return segs, pure


def neighbours(L):
    """The K loops that differ from the loop L by the exchange of two cyclically adjacent letters."""
    K = len(L)
    out = []
    for i in range(K):
        y = list(L)
        j = (i + 1) % K
        y[i], y[j] = y[j], y[i]
        out.append(canon(tuple(y)))
    return out


def exact_cost(sel, K):
    """The exact cost of a selection: (2 t + loops without a row + closed trails of the walks after completion,
    2 t + loops without a row, closed trails of the walks, number of walks).  Fails when the selection is not
    balanced."""
    ws, chosen = walks(sel)
    det = sum(1 for (x, v) in sel.values() if v == 0)
    t = sum(1 for v in chosen.values() if v == K - 2)
    tr = 0
    for w in ws:
        tr += walk_trails(w, chosen, K)
    return 2 * t + det + tr, 2 * t + det, tr, len(ws)


def summary(sel):
    """Print the numbers of the selection (short rows t, loops without a row, walks, closed trails after
    completion, the parts of the floor constant, the walks by size).  Returns (cost, floor constant)."""
    K = len(next(iter(sel)))
    N = math.factorial(K - 1)
    assert len(sel) == N, "not every loop present"
    ws, chosen = walks(sel)
    det = sum(1 for (x, v) in sel.values() if v == 0)
    t = sum(1 for v in chosen.values() if v == K - 2)
    stat = Counter()
    trails = 0
    for w in ws:
        tt = sum(1 for x in w if chosen[x] == K - 2)
        g = walk_trails(w, chosen, K)
        trails += g
        stat[(len(w), tt, g)] += 1
    cost = 2 * t + det + trails
    print("K = %d: t = %d, detached = %d, walks = %d, trails after completion = %d (+ %d detached)" % (
        K, t, det, len(ws), trails, det))
    print("  Q-term %s, detached %s, walk trails %s;  c_floor = %s = %.6f" % (
        Fraction(2 * t, N), Fraction(det, N), Fraction(trails, N), Fraction(cost, N), Fraction(cost, N)))
    for key in sorted(stat, reverse=True)[:20]:
        print("   %5d walk(s): %6d loops, %6d short, gcd(K-1, f-t) = %d" % ((stat[key],) + key))
    return cost, Fraction(cost, N)


def walk_order(sel):
    """The same selection with its loops listed walk by walk: every walk from its least state, the walks in
    increasing order of that state, then the loops without a row in increasing order."""
    ws, chosen = walks(sel)
    out = {}
    for w in sorted((w[w.index(min(w)):] + w[:w.index(min(w))] for w in ws), key=lambda w: w[0]):
        for x in w:
            out[canon(x)] = sel[canon(x)]
    for L in sorted(sel):
        if sel[L][1] == 0:
            out[L] = sel[L]
    assert len(out) == len(sel)
    return out


def main():
    """Read the selection, then the rounds: free a region, solve it, measure the pool exactly, keep the best."""
    ap = argparse.ArgumentParser()
    ap.add_argument("inp")
    ap.add_argument("out")
    ap.add_argument("--transport", type=int, default=0)
    ap.add_argument("--order", default="file", help="file | walk : the order of the loops (see the header)")
    ap.add_argument("--free", type=int, default=150)
    ap.add_argument("--rounds", type=int, default=100)
    ap.add_argument("--time", type=float, default=20, help="seconds per region program")
    ap.add_argument("--total", type=float, default=1e9, help="seconds in all")
    ap.add_argument("--pool", type=int, default=40)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--plateau", action="store_true")
    ap.add_argument("--threads", type=int, default=2)
    ap.add_argument("--centre", default="any", help="any | det | short : where the centres are drawn")
    ap.add_argument("--maxseg", type=int, default=0)
    ap.add_argument("--gapabs", type=float, default=0.0, help="pool: accept programs up to this much worse in 2t + det")
    ap.add_argument("--every", type=int, default=10)
    a = ap.parse_args()
    rnd = random.Random(a.seed)
    sel = read_any(a.inp)
    if a.order == "walk":
        sel = walk_order(sel)
    for _ in range(a.transport):
        sel = transport(sel)
    K = len(next(iter(sel)))
    N = math.factorial(K - 1)
    assert all(v in (K, K - 2, 0) for (x, v) in sel.values()), "full and short rows only"
    # walks of full rows only -> loops without a row (same cost, and the segment model has no such walks)
    segs, pure = segments_of(sel)
    for w in pure:
        for x in w:
            sel[canon(x)] = (canon(x), 0)
    cur = exact_cost(sel, K)
    print("K = %d, %d loops; start: cost %d = 2t+det %d + trails %d (%d walks); c_floor = %.6f" % (
        K, N, cur[0], cur[1], cur[2], cur[3], cur[0] / N), flush=True)
    maxseg = a.maxseg or (K - 2)
    env = gp.Env(empty=True)
    env.setParam("OutputFlag", 0)
    env.start()
    t0 = time.time()
    loops_all = list(sel)
    # the rounds
    for rd in range(a.rounds):
        if time.time() - t0 > a.total:
            break
        segs, _ = segments_of(sel)
        segof = {}
        for u, j in segs.items():
            st, _e = seg_states(u, j)
            for x in st:
                segof[canon(x)] = (u, j)
        if a.centre == "det":
            pool_c = [L for L, (x, v) in sel.items() if v == 0] or loops_all
        elif a.centre == "short":
            pool_c = [L for L, (x, v) in sel.items() if v == K - 2] or loops_all
        else:
            pool_c = loops_all
        # the region: a ball around a random centre, then closed under the segments of the present selection
        c0 = rnd.choice(pool_c)
        free, frontier = {c0}, [c0]
        while frontier and len(free) < a.free:
            nf = []
            rnd.shuffle(frontier)
            for L in frontier:
                for M in neighbours(L):
                    if M not in free and len(free) < a.free:
                        free.add(M)
                        nf.append(M)
            frontier = nf
        for L in list(free):
            if L in segof:
                st, _e = seg_states(*segof[L])
                free.update(canon(x) for x in st)
        inside = {u: j for u, j in segs.items() if canon(u) in free}
        outside_start = {u for u in segs if canon(u) not in free}
        # states where an outside segment ends
        out_end = Counter()
        for u, j in segs.items():
            if canon(u) not in free:
                out_end[seg_states(u, j)[1]] += 1
        # the programme on the region: segments inside it; a segment may end where a segment outside starts
        m = gp.Model(env=env)
        m.Params.TimeLimit = a.time
        m.Params.Threads = a.threads
        m.Params.Seed = a.seed + rd
        av = {}
        cover = {L: [] for L in free}
        inflow, outflow = {}, {}
        for L in free:
            for r in range(K):
                u = L[r:] + L[:r]
                for j in range(1, maxseg + 1):
                    st, end = seg_states(u, j)
                    ls = [canon(x) for x in st]
                    if len(set(ls)) < j or any(M not in free for M in ls):
                        continue
                    if canon(end) not in free and end not in outside_start:
                        continue
                    v = m.addVar(vtype=GRB.BINARY, obj=2.0)
                    av[u, j] = v
                    for M in ls:
                        cover[M].append(v)
                    outflow.setdefault(u, []).append(v)
                    inflow.setdefault(end, []).append(v)
        det = {L: m.addVar(vtype=GRB.BINARY, obj=1.0) for L in free}
        for L in free:
            m.addConstr(gp.quicksum(cover[L]) + det[L] == 1)
        for v_ in set(inflow) | set(outflow) | {u for u in out_end if canon(u) in free}:
            lhs = gp.quicksum(inflow.get(v_, [])) + out_end.get(v_, 0)
            if canon(v_) in free:
                m.addConstr(lhs == gp.quicksum(outflow.get(v_, [])))
            else:
                m.addConstr(lhs == 1)                 # v_ starts an outside segment
        for u in outside_start:                       # outside segments that lost their predecessor
            if u not in inflow and out_end.get(u, 0) == 0:
                m.addConstr(gp.LinExpr() == 1)        # infeasible by construction; cannot happen
        cur_in = 2 * len(inside) + sum(1 for L in free if sel[L][1] == 0)
        m.addConstr(gp.quicksum(2 * v for v in av.values()) + gp.quicksum(det.values()) <= cur_in + a.gapabs)
        for key, v in av.items():
            v.Start = 1 if inside.get(key[0]) == key[1] else 0
        for L in free:
            det[L].Start = 1 if sel[L][1] == 0 else 0
        # a pool of solutions of the programme; each is put into the selection and measured with the exact cost
        m.Params.PoolSolutions = a.pool
        m.Params.PoolSearchMode = 2
        m.Params.PoolGap = 1e9
        m.Params.PoolGapAbs = 1e9
        m.optimize()
        best = None
        nsol = m.SolCount
        mintr = None
        for kk in range(nsol):
            m.Params.SolutionNumber = kk
            used = [key for key, v in av.items() if v.Xn > 0.5]
            if kk > 0 and set(used) == {(u, j) for u, j in inside.items()}:
                continue
            new = dict(sel)
            for L in free:
                new[L] = (L, 0)
            for (u, j) in used:
                st, _e = seg_states(u, j)
                new[canon(st[0])] = (st[0], K - 2)
                for x in st[1:]:
                    new[canon(x)] = (x, K)
            try:
                c = exact_cost(new, K)
            except AssertionError:
                continue
            same = all(new[L] == sel[L] for L in free)
            if same:
                continue
            if mintr is None or c[2] < mintr[2]:
                mintr = c
            if best is None or c < best[0]:
                best = (c, new)
        msg = "round %d: free %d loops, %d vars, %d pool solutions, region 2t+det %d -> best %s" % (
            rd, len(free), len(av), nsol, cur_in, ("%.0f" % m.ObjVal) if nsol else "-")
        if best is not None and (best[0][0] < cur[0] or (a.plateau and best[0][0] == cur[0])):
            improved = best[0][0] < cur[0]
            cur, sel = best
            if improved:
                print(msg + "  ** cost %d = %d + trails %d (%d walks), c_floor %.6f  (%.0f s)" % (
                    cur[0], cur[1], cur[2], cur[3], cur[0] / N, time.time() - t0), flush=True)
                write_gsel(a.out, sel, "lns.py from %s: cost %d / %d" % (a.inp, cur[0], N))
        elif rd % a.every == 0 or (mintr is not None and mintr[2] < cur[2]):
            print(msg + "  (cost %d, %.0f s)%s" % (cur[0], time.time() - t0,
                  "" if mintr is None or mintr[2] >= cur[2] else "  fewest trails in pool: %s" % (mintr,)), flush=True)
        m.dispose()
    cost, c = summary(sel)
    write_gsel(a.out, sel, "lns.py from %s: cost %d / %d, c_floor = %s" % (a.inp, cost, N, c))
    print("wrote", a.out)


if __name__ == "__main__":
    main()
