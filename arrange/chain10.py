#!/usr/bin/env python
"""chain10.py - the chain model at n = 10: the order of the chains and the places of the big trails, by an integer
program for every partition.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: chain10.py tables BASE.txt GT.npz
           needs c10m_states.pkl (trav10.py); writes c10m_tab.npz and c10m_tab.pkl
       chain10.py solve P [P ...] [--verify] [--slack S]
           needs c10m_tab.npz, c10m_tab.pkl and c10m_parts.pkl (parts10.py); writes c10m_sol_run.pkl after every
           partition and at the end c10m_sol_<the first three P joined by _>.pkl, which plans10.py reads

  BASE.txt  the base word of the n = 10 pieces;  GT.npz  its traversal tables (gt.py)
  P         numbers of partitions (0 .. 55)
  --verify  after every optimum, check that the pruning of blocks (below) lost nothing
  --slack S the pruning constant (default 3)

Written for the n = 10 pieces: 48 groups of 7 small trails with 504 cuts per group, 14 big trails.  These numbers
are fixed in the code.  W is the cost of a join in half letters with the cuts counted in, and "2 cost" of a word
is D(first cut) + the sum of W + D(last cut), as in tl10.py.

The model.
  CHAINS.  The 56 cycles of six traversals joined at W = 8 (trav10.py).  A partition is 8 disjoint chains that
  cover the 48 groups; there are 56 (parts10.py).  A chain cut at one of its six joins (rotation r) is a path
  through six groups g1 .. g6.  Its cost is taken as alpha(y) + 8 + beta(x):
      alpha(y) = the cheapest way to enter g1 at cut y and reach the exit of the traversal of g3, with g1 and g2
                 written in any mode of tl10.py (path or loop) and g3 leaving at the exit of its traversal;
      beta(x)  = the same from the entry of the traversal of g4 to leaving g6 at cut x;
      8        = the join between the traversals of g3 and g4, which is kept.
  Keeping that join makes the cost an upper bound of what the order can do; plans10.py values the whole order
  again exactly.
  GAPS.  Between the end of a chain A and the start of the next chain B, and at the two ends of the word, stands
  nothing (a direct join) or a block: a sequence s of big trails, each written once from one cut.
      value(A, s, B) = the cheapest way through the cuts of the trails of s in this order, from the exit of A to
                       the entry of B, by min-plus over the cuts.
  Joins between big trails with W <= 5 are listed exactly.  A join that is not listed is charged 20 on top of the
  best value so far, so that it is not used; value is exact for blocks whose inner joins all have W <= 5 and an
  upper bound otherwise.
  The sequences offered as blocks are: every single trail, every ordered pair, the runs along the joins with
  W = 1 up to 7 trails, and every triple whose two joins have W <= 2 (638 sequences on these pieces).
tables: alpha and beta for the 336 (chain, rotation), their values on all cuts of the big trails, the direct joins,
  and value(A, s, B) for all A, B and all sequences.
solve: for one partition, an integer program (Gurobi): the order of its 8 chains, the rotation of each, and what
  stands in the 9 gaps.  A binary variable for every arc (state A, state B) with nothing between, and one for every
  arc with a set of big trails between, in the best order offered for that set.  Every chain is entered once, what
  enters a state leaves it, the word has one start and one end, every big trail is in exactly one block.  A
  solution in which the chains do not form one sequence is cut off and the program solved again.
  Pruning: a set of trails on an arc gets a variable only if its value is at most (direct join of the arc) +
  S x (trails in the set) + 2.  With --verify the linear relaxation at the optimum is solved and the reduced cost
  of EVERY block on EVERY arc is computed, the pruned ones too; the line "PRUNED blocks with reduced cost below the
  gap: 0" says that no pruned block can be part of a better solution.  This check is in floating point.
  2 cost of a solution = the optimum + 64 (the 8 kept joins).

What a result means.  With status 2 the value is the optimum of THIS model for the partition: these chains, the
blocks offered, the middle join of every chain kept.  It is not a bound for other arrangements of the pieces: a
chain cut in two, a block that is not among the sequences offered, or groups not in chains are outside.
On the n = 10 pieces every one of the 56 partitions ends with status 2: 25 of them at 2 cost 992, which is
4,034,855 letters, 17 at 994, 7 at 996 and 7 at 1,004.  With --verify, 55 partitions print 0 pruned blocks
below the gap; one partition (optimum 996) prints 9, and there the relaxation over all blocks, 994, is
already above 992.  The plan of the word comes from partition 2 (plans10.py).

Needs: Python 3, numpy; tl10.py and what it imports; Gurobi (gurobipy, with a licence beyond the size-limited
one: about 255,000 variables per partition) for solve.  All files are read from and written to the working
directory.
Time and memory: tables 40 minutes and 1.70 GB; solve 30 s and 0.85 GB for one partition with --verify (measured, one thread).
"""
import sys, time, pickle, itertools
import numpy as np
import gurobipy as gp
from gurobipy import GRB
import tl10

log = lambda *x: print(*x, flush=True)
BIG = 10 ** 6


def sequences(mw, NB):
    """the sequences of big trails that are offered as blocks: every single trail, every ordered pair, the runs
    that follow the joins with W = 1 from each trail up to 7 trails, and every triple whose two joins have W <= 2
    (mw[i, j] = the smallest W from big trail i to big trail j).  Sorted by length, so that a sequence comes after
    its beginnings."""
    seqs = [(i,) for i in range(NB)] + [(i, j) for i in range(NB) for j in range(NB) if i != j]
    succ = {i: int(np.argmin(mw[i])) for i in range(NB) if mw[i].min() == 1}
    have = set(seqs)
    for i in range(NB):
        s = (i,)
        while len(s) < 7 and s[-1] in succ and succ[s[-1]] not in s:
            s = s + (succ[s[-1]],)
            if s not in have:
                seqs.append(s)
                have.add(s)
    for i in range(NB):
        for j in range(NB):
            for k in range(NB):
                if len({i, j, k}) == 3 and mw[i, j] <= 2 and mw[j, k] <= 2 and (i, j, k) not in have:
                    seqs.append((i, j, k))
                    have.add((i, j, k))
    return sorted(seqs, key=len)


def tables():
    """alpha and beta of every chain cut at each of its six joins, their values on all cuts of the big trails, the
    direct join between every chain end and every chain start, and the value of every block between them"""
    t0 = time.time()
    M = tl10.TL(sys.argv[2], sys.argv[3], log)
    T = M.T
    NG = M.NG
    NB = M.NO - NG
    st = pickle.load(open("c10m_states.pkl", "rb"))
    nodes, cyc = st["nodes"], st["cyc"]
    CR = [(ci, r) for ci in range(len(cyc)) for r in range(6)]
    alpha, beta, g_first, g_last = [], [], [], []
    for ci, r in CR:
        path = [nodes[i] for i in (cyc[ci][r:] + cyc[ci][:r])]
        (g1, y1, x1), (g2, y2, x2), (g3, y3, x3), (g4, y4, x4), (g5, y5, x5), (g6, y6, x6) = path
        h3 = np.full(504, BIG, np.int64)
        h3[x3] = 0
        G3 = (M.M[g3] + h3[None, :]).min(1)
        G2 = (M.M[g2] + M.join_back(G3, M.cuts[g2], M.cuts[g3])[None, :]).min(1)
        G1 = (M.M[g1] + M.join_back(G2, M.cuts[g1], M.cuts[g2])[None, :]).min(1)
        gi = np.full(504, BIG, np.int64)
        gi[y4] = 0
        f4 = (gi[:, None] + M.M[g4]).min(0)
        f5 = (M.join(f4, M.cuts[g4], M.cuts[g5])[:, None] + M.M[g5]).min(0)
        f6 = (M.join(f5, M.cuts[g5], M.cuts[g6])[:, None] + M.M[g6]).min(0)
        alpha.append(G1)
        beta.append(f6)
        g_first.append(g1)
        g_last.append(g6)
    alpha = np.array(alpha)
    beta = np.array(beta)
    log("alpha, beta for %d (chain, rotation); smallest alpha %s, beta %s  (%.0fs)" % (
        len(CR), dict(zip(*[a.tolist() for a in np.unique(alpha.min(1), return_counts=True)])),
        dict(zip(*[a.tolist() for a in np.unique(beta.min(1), return_counts=True)])), time.time() - t0))
    bg = np.nonzero(~T.is_small)[0]
    lab = T.is_small.astype(np.int64)
    NA = len(CR)
    bA = np.zeros((NA + 1, len(bg)), np.int16)
    aB = np.zeros((NA + 1, len(bg)), np.int16)
    for a in range(NA):
        bA[a] = np.minimum(T.in_best(beta[a], X=M.cuts[g_last[a]], Y=bg, lab=lab), 30000)
        aB[a] = np.minimum(T.out_best(alpha[a], X=bg, Y=M.cuts[g_first[a]], lab=lab), 30000)
    bA[NA] = T.D[bg]  # the dummy: start / end of the word
    aB[NA] = T.D[bg]
    log("values on the big cuts done (%.0fs)" % (time.time() - t0))
    # direct joins
    direct = np.full((NA + 1, NA + 1), BIG, np.int64)
    gf = np.array(g_first)
    chain_of = np.array([c for c, r in CR])
    for a in range(NA):
        for g in range(NG):
            bs = np.nonzero((gf == g) & (chain_of != CR[a][0]))[0]
            if not len(bs) or g == g_last[a]:
                continue
            J = M.join(beta[a], M.cuts[g_last[a]], M.cuts[g])
            direct[a, bs] = (J[None, :] + alpha[bs]).min(1)
        direct[a, NA] = int((beta[a] + T.D[M.cuts[g_last[a]]]).min())
        direct[NA, a] = int((T.D[M.cuts[g_first[a]]] + alpha[a]).min())
    log("direct joins done: values between chains %s (%.0fs)" % (dict(zip(*[x.tolist() for x in np.unique(direct[:NA,
        :NA][direct[:NA, :NA] < BIG], return_counts=True)])), time.time() - t0))
    # big-big arcs
    bpos = np.full(T.V, -1, np.int64)
    bpos[bg] = np.arange(len(bg))
    bc = [M.cuts[NG + i] for i in range(NB)]
    first = [int(bpos[c[0]]) for c in bc]
    for c in bc:
        assert (np.diff(bpos[c]) > 0).all()
    loc = np.full(T.V, -1, np.int64)
    for c in bc:
        loc[c] = np.arange(len(c))
    arcs = {}
    mw = np.full((NB, NB), 99, np.int64)
    for i in range(NB):
        for j in range(NB):
            if i != j:
                pa, pb, pw = T.pairs(bc[i], bc[j], 5)
                arcs[i, j] = (loc[pa], loc[pb], pw.astype(np.int64))
                mw[i, j] = int(pw.min()) if len(pw) else 6
    seqs = sequences(mw, NB)
    log("big-big joins with W <= 5: %d; sequences %d (%.0fs)" % (sum(len(a[0]) for a in arcs.values()), len(seqs),
        time.time() - t0))
    # positions of the cuts of each big trail inside bg (they are not contiguous in bg if skip cuts interleave: use index arrays)
    bidx = [bpos[c] for c in bc]
    val = np.full((NA + 1, len(seqs), NA + 1), 30000, np.int16)
    aBt = [aB[:, bidx[t]].astype(np.int32) for t in range(NB)]  # per trail: (chain starts) x (cuts of the trail)
    aBmin = [x.min(1) for x in aBt]
    tt = time.time()
    for a in range(NA + 1):
        cache = {}
        for si, s in enumerate(seqs):
            if len(s) == 1:
                v = bA[a][bidx[s[0]]].astype(np.int64)
                val[a, si] = np.minimum((aBt[s[0]] + v[None, :]).min(1), 30000)
            else:
                pv = cache[s[:-1]]
                ia, ib, w = arcs[s[-2], s[-1]]
                dflt = int(pv.min()) + 20  # a join that is not listed (W >= 6) is not used inside a block
                v = np.full(len(bc[s[-1]]), dflt, np.int64)
                np.minimum.at(v, ib, pv[ia] + w)
                tch = np.nonzero(v < dflt)[0]
                e = dflt + aBmin[s[-1]]
                if len(tch):
                    e = np.minimum(e, (aBt[s[-1]][:, tch] + v[tch][None, :]).min(1))
                val[a, si] = np.minimum(e, 30000)
            cache[s] = v
        if a % 48 == 0:
            log("  block values from %d of %d chain ends (%.0fs)" % (a, NA + 1, time.time() - tt))
    np.savez_compressed("c10m_tab.npz", alpha=alpha, beta=beta, g_first=np.array(g_first), g_last=np.array(g_last),
        direct=direct, val=val, mw=mw)
    pickle.dump(dict(CR=CR, seqs=seqs), open("c10m_tab.pkl", "wb"))
    log("tables written (%.0fs)" % (time.time() - t0))


SLACK = 3
NTHREADS = 1
VERIFY = False
vres = {}


def solve(parts, tlim=300, extra=None):
    """the integer program of the header for every partition of the list; returns the solutions as (2 cost,
    partition, gaps) and the list of the states (chain, rotation).  A gap is (state before, state after, block or
    None, value); the state number 336 stands for the two ends of the word."""
    z = np.load("c10m_tab.npz")
    meta = pickle.load(open("c10m_tab.pkl", "rb"))
    CR, seqs = meta["CR"], meta["seqs"]
    direct, val = z["direct"], z["val"]
    NA = len(CR)
    allparts = pickle.load(open("c10m_parts.pkl", "rb"))
    NB = 14
    # per trail set the positions of its orderings
    bysets = {}
    for si, s in enumerate(seqs):
        bysets.setdefault(frozenset(s), []).append(si)
    sets = list(bysets)
    env = gp.Env(params={"OutputFlag": 0})
    res = []
    for pi in parts:
        t0 = time.time()
        chains = allparts[pi]
        states = [a for a in range(NA) if CR[a][0] in chains]
        cl = {a: chains.index(CR[a][0]) for a in states}
        DUM = NA
        m = gp.Model("p", env=env)
        m.Params.Threads = NTHREADS
        m.Params.TimeLimit = tlim
        m.Params.MIPFocus = 1
        arcsl = [(a, b) for a in states for b in states if cl[a] != cl[b]] + [(DUM, b) for b in states] + [(a,
            DUM) for a in states]
        yv = {}
        best_order = {}
        for (a, b) in arcsl:
            yv[a, b, -1] = m.addVar(vtype=GRB.BINARY, obj=float(direct[a, b]))
            for k, st in enumerate(sets):
                sis = bysets[st]
                vals = val[a, sis, b].astype(np.int64)
                j = int(np.argmin(vals))
                if vals[j] < 30000 and vals[j] <= direct[a, b] + SLACK * len(st) + 2:
                    yv[a, b, k] = m.addVar(vtype=GRB.BINARY, obj=float(vals[j]))
                    best_order[a, b, k] = sis[j]
        inn = {}
        out = {}
        for (a, b, k), v in yv.items():
            out.setdefault(a, []).append(v)
            inn.setdefault(b, []).append(v)
        for c in range(8):
            m.addConstr(gp.quicksum(v for a in states if cl[a] == c for v in inn[a]) == 1)
        for a in states:
            m.addConstr(gp.quicksum(inn[a]) == gp.quicksum(out[a]))
        m.addConstr(gp.quicksum(out[DUM]) == 1)
        m.addConstr(gp.quicksum(inn[DUM]) == 1)
        for t in range(NB):
            m.addConstr(gp.quicksum(v for (a, b, k), v in yv.items() if k >= 0 and t in sets[k]) == 1)
        subsets = []
        while True:
            m.optimize()
            if m.SolCount == 0:
                break
            sel = [(a, b, k) for (a, b, k), v in yv.items() if v.X > 0.5]
            nxt = {a: (b, k) for a, b, k in sel}
            tour = [DUM]
            cur = DUM
            while True:
                cur = nxt[cur][0]
                if cur == DUM:
                    break
                tour.append(cur)
            if len(tour) == 9:
                break
            # subtour: the chains not on the tour form cycles; cut them
            on = {cl[a] for a in tour[1:]}
            off = [a for a in states if cl[a] not in on]
            m.addConstr(gp.quicksum(v for (a, b, k), v in yv.items() if a in off and b not in off) >= 1)
            subsets.append(set(off))
        if m.SolCount == 0:
            log("partition %d: no solution" % pi)
            continue
        cost = round(m.ObjVal) + 8 * 8
        if VERIFY:
            # root relaxation with the subtour rows found; reduced costs of ALL blocks on ALL arcs (also the pruned ones)
            m.update()
            r = m.relax()
            r.Params.OutputFlag = 0
            r.Params.Method = 1
            r.optimize()
            pi_ = np.array([c.Pi for c in r.getConstrs()])
            lp = r.ObjVal
            ncl = 8
            p_cl = pi_[:ncl]
            p_bal = dict(zip(states, pi_[ncl:ncl + len(states)]))
            p_do, p_di = pi_[ncl + len(states)], pi_[ncl + len(states) + 1]
            p_tr = pi_[ncl + len(states) + 2:ncl + len(states) + 2 + NB]
            p_sub = pi_[ncl + len(states) + 2 + NB:]
            assert len(p_sub) == len(subsets)
            seqpi = np.array([sum(p_tr[t] for t in sq) for sq in seqs])
            minrc = 1e9
            nneg = 0
            worst = None
            nbelow = 0
            gap_ = (cost - 64) - lp
            for (a, b) in arcsl:
                base = 0.0
                if b != DUM:
                    base += p_cl[cl[b]] + p_bal[b]
                else:
                    base += p_di
                if a != DUM:
                    base -= p_bal[a]
                else:
                    base += p_do
                for off_, pv in zip(subsets, p_sub):
                    if a in off_ and b not in off_:
                        base += pv
                rc = val[a, :, b].astype(np.float64) - base - seqpi
                rc[val[a, :, b] >= 30000] = 1e9
                j = int(np.argmin(rc))
                for k_, st_ in enumerate(sets):
                    if (a, b, k_) not in yv:  # pruned away on this arc
                        if rc[bysets[st_]].min() < gap_ - 1e-6:
                            nbelow += 1
                if rc[j] < minrc:
                    minrc = rc[j]
                    worst = (a, b, seqs[j])
            log("   check without pruning: root LP %.3f (optimum %d, gap %.3f); smallest reduced cost over all %d x %d blocks %.3f; PRUNED blocks with reduced cost below the gap: %d" % (
                lp + 64, cost, gap_, len(arcsl), len(seqs), minrc, nbelow))
            vres[pi] = (lp + 64, cost, float(minrc), nbelow)
        gaps = []
        cur = DUM
        while True:
            b, k = nxt[cur]
            gaps.append((cur, b, None if k < 0 else seqs[best_order[cur, b, k]], int(direct[cur,
                b]) if k < 0 else int(val[cur, best_order[cur, b, k], b])))
            cur = b
            if cur == DUM:
                break
        log("partition %2d (%d variables): 2 cost %d (status %d, bound %.0f); gaps (content: value): %s  (%.0fs)" % (
            pi, len(yv), cost, m.Status, m.ObjBound + 64, [("-" if s is None else s, v) for a, b, s, v in gaps],
            time.time() - t0))
        res.append((cost, pi, gaps))
        pickle.dump((res, CR), open("c10m_sol_run.pkl", "wb"))
    return res, CR


if __name__ == "__main__":
    if sys.argv[1] == "tables":
        tables()
    else:
        args = sys.argv[2:]
        if "--verify" in args:
            VERIFY = True
            args = [a for a in args if a != "--verify"]
        if "--slack" in args:
            SLACK = int(args[args.index("--slack") + 1])
            args = [a for i_, a in enumerate(args) if a != "--slack" and args[i_ - 1] != "--slack"]
        parts = [int(x) for x in args]
        res, CR = solve(parts)
        pickle.dump((res, CR), open("c10m_sol_%s.pkl" % "_".join(args[:3]), "wb"))
