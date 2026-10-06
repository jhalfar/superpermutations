#!/usr/bin/env python
"""q12b.py - symmetric run systems of the small trails: the programme of q12.py in integers (n = 12).

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: q12b.py E [--d0] [--even] [--time T] [--prove SEC] [--maxrounds R]
  E             level: joins with W < E may be used inside runs
  --d0          only cuts at vertices (D = 0), so only joins between vertices
  --even        only joins with even W
  --time T      time limit of every round in seconds (default 300)
  --prove SEC   when a round ends without a cycle but at the time limit, go on with the same model for up to SEC
                seconds, the solver set to move the bound, until the optimum is proved
  --maxrounds R after R rounds the cycles that are left are broken at their most expensive join instead of
                being excluded
needs cuts12c.bin and sym12.pkl; writes runs12_E.pkl, or runs12_E_d0.pkl with --d0

The piece set.  These scripts were written for one piece set at n = 12, the first one that beat Pantone's pieces:
the 11-symbol selection with full and short rows only (Q = 178,080).  Its numbers are fixed in the code: 7,200
closed trails, of which the first 6,048 of the table are small trails with 110 cuts each (100 at steps of weight 2,
10 at vertices); then 144 trails of the three short walks of every block (63, 133 and 182 loops, one trail each;
kinds 1 to 3 of the table, "short-walk trails" below); then 1,008 big trails.  Letters: 0 .. 6 are the old letters,
7, 8, 9 the added letters, A the distinguished letter, B the completion letter.

Half letters.  For a cut x written before a cut y, W(x, y) = 2 (h - k) + D_x + D_y, where k is the largest number of
letters (at most h = 9) in which the end of the piece cut at x agrees with the start of the piece cut at y, and D is
the cost of a cut (0 at a vertex, 1 at a step of weight 2).  A join of cost c between two vertices has W = 2 c.
For a word, 2 (cuts + joins) = D(first cut) + sum of W over its joins + D(last cut).

A symmetric system is a set of joins between small cuts that the 168 relabellings map to itself, with one cut per
trail and at most one join out of and one into a cut.  In orbit variables (binary y per orbit of cuts, z per orbit
of joins) this is a small integer program with the objective of q12.py, sum (E - W) z.  Its solution, expanded by
the group, is a system of paths and cycles on all 6,048 trails.  Cycles are excluded round by round: for one cycle
of every orbit of cycles, the joins between the trails of the cycle, at any cuts and in both directions, number at
most (trails - 1).  That constraint holds for every system of paths, so nothing feasible is lost.

What the result is.
  - A real system of runs of the small trails, written to the file: the runs as lists of trails, the cut of every
    trail, the W of the join after every trail.
  - Optimal among symmetric systems (within the options given) when the LAST round ended with status 2 and has
    no cycle.  The constraints of the earlier rounds hold for every system, whatever the status of those rounds.
    A last round with status 9 hit the time limit; then the bound printed for it is what is proved.
  - Not shown to be optimal among all systems: its value is a lower bound of the true maximum of sum (E - W) z,
    and the linear programme of q12.py is the upper bound.
  - With --maxrounds, a feasible system without any proof.

Prints one line per round (value, status and bound of the solver, runs, cycles) and at the end the runs by number
of trails, the joins by W and the sum over runs, 2 E N - 2 (value).

Results on this piece set (value per orbit x 168; the last round of each has status 2 and no cycle):
  level  cuts      command                                value   runs    joins inside by W
  8      all       q12b.py 8                              140     1,344   2: 3,360   4: 336   6: 1,008
  10     vertices  q12b.py 10 --d0                        200     1,008   the same and 8: 336
  10     all       q12b.py 10 --time 60 --prove 2700      200     1,008   the same system
  12     vertices  q12b.py 12 --d0                        266     504     the same and 10: 504
  12     all       not settled: between 266 and 276.  One run; its first round, before any cycle is excluded,
                   has optimum 276 (an upper bound); the run then stopped at 3 GB of memory.

Needs: Python 3, numpy, scipy, c12.py, q12.py, Gurobi (gurobipy, with a licence beyond the size-limited one).  The
solver is told to stop at 2.2 GB of its own memory and may write node files to the working directory.
All files are read from and written to the working directory.
Time and memory, measured: level 8 with all cuts: 3 rounds, 30 s; level 10 with vertex cuts: 6 rounds, 35 s;
level 12 with vertex cuts: 12 rounds, 95 s; 0.57 GB each (about 20 s of every run go into the orbits).
Level 10 with all cuts, --time 60 --prove 2700: 1,105 s in all, 1.14 GB.
"""
import sys, time, pickle
import numpy as np
import gurobipy as gp
from gurobipy import GRB
import scipy.sparse as sp
import q12, c12

log = lambda *x: print(*x, flush=True)
E = int(sys.argv[1])
tlim = float(sys.argv[sys.argv.index("--time") + 1]) if "--time" in sys.argv else 300
S = q12.Small(log)
if '--d0' in sys.argv:
    # vertices only: joins between D = 0 cuts, generated directly (few)
    d0 = np.nonzero(S.D == 0)[0]
    reps0 = S.rep[S.D[S.rep] == 0]
    h_ = S.h
    exr = S.ex[reps0]
    en0 = S.en[d0]
    Wm = np.full((len(reps0), len(d0)), 2 * h_, np.int64)
    for k_ in range(1, h_ + 1):
        Wm = np.where(c12.suffix(exr, k_)[:, None] == c12.prefix(en0, k_, h_)[None, :], 2 * (h_ - k_), Wm)
    ii, jj = np.nonzero((Wm < E) & (S.t[reps0][:, None] != S.t[d0][None, :]))
    repidx = np.nonzero(S.D[S.rep] == 0)[0]  # positions of these representatives in S.rep
    assert (S.rep[repidx] == reps0).all()
    I, J, W = repidx[ii], d0[jj], Wm[ii, jj]
else:
    I, J, W = S.arcs_from(S.rep, E - 1)
if '--even' in sys.argv:
    k_ = W % 2 == 0
    I, J, W = I[k_], J[k_], W[k_]
if '--d0' in sys.argv:
    k_ = (S.D[S.rep[I]] == 0) & (S.D[J] == 0)
    I, J, W = I[k_], J[k_], W[k_]
log('joins out of the representative cuts: %d' % len(I))
no = S.no
src_o = S.orb[S.rep[I]]
tgt_o = S.orb[J]
# group element that carries the representative of the orbit of J to J: needed to expand; store images instead
na = len(I)
env = gp.Env(params={"OutputFlag": 0})
m = gp.Model("qi", env=env)
m.Params.Threads = 2
m.Params.TimeLimit = tlim
m.Params.MIPFocus = 1
m.Params.SoftMemLimit = 2.2
m.Params.NodefileStart = 0.3
m.Params.Presolve = 1
y = m.addMVar(no, vtype=GRB.BINARY)
z = m.addMVar(na, vtype=GRB.BINARY, obj=(E - W).astype(float))
m.ModelSense = GRB.MAXIMIZE
A_out = sp.csr_matrix((np.ones(na), (src_o, np.arange(na))), shape=(no, na))
A_in = sp.csr_matrix((np.ones(na), (tgt_o, np.arange(na))), shape=(no, na))
m.addConstr(A_out @ z - y <= 0)
m.addConstr(A_in @ z - y <= 0)
rows, cols = [], []
for to in range(S.nto):
    tr = int(np.nonzero(S.torb == to)[0][0])
    rows += [to] * 110
    cols += S.orb[tr * 110:(tr + 1) * 110].tolist()
m.addConstr(sp.csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(S.nto, no)) @ y <= 1)
# images of every cut under the group, to expand a symmetric solution: the cut words are sorted once, a relabelled
# word is looked up in that table
t0 = time.time()
ns = S.ns
wk = S.w * 2 + S.D
order = np.argsort(wk)
wks = wk[order]


def image(cuts, g):
    """the cuts onto which the relabelling g maps the given cuts"""
    k = q12.relabel(S.w[cuts], S.D[cuts], g) * 2 + S.D[cuts]
    p = np.searchsorted(wks, k)
    assert (wks[p] == k).all()
    return order[p]


rnd = 0
maxrounds = int(sys.argv[sys.argv.index('--maxrounds') + 1]) if '--maxrounds' in sys.argv else 10 ** 9
timg = None
prove = float(sys.argv[sys.argv.index('--prove') + 1]) if '--prove' in sys.argv else 0
proving = False

while True:
    m.optimize()
    zz = z.X > 0.5
    val = m.ObjVal
    # expand: the arcs (rep x -> J) and their images
    ai = np.nonzero(zz)[0]
    xs = S.rep[I[ai]]
    ys = J[ai]
    nxt = np.full(ns, -1, np.int64)
    wj = np.zeros(ns, np.int64)
    for g in S.G:
        a = image(xs, g)
        b = image(ys, g)
        assert (nxt[a] == -1).all()
        nxt[a] = b
        wj[a] = W[ai]
    # trail level
    tn = np.full(S.NS, -1, np.int64)
    tw = np.zeros(S.NS, np.int64)
    tcut_out = np.full(S.NS, -1, np.int64)
    tcut_in = np.full(S.NS, -1, np.int64)
    a = np.nonzero(nxt >= 0)[0]
    tn[S.t[a]] = S.t[nxt[a]]
    tw[S.t[a]] = wj[a]
    tcut_out[S.t[a]] = a
    tcut_in[S.t[nxt[a]]] = nxt[a]
    both = (tcut_out >= 0) & (tcut_in >= 0)
    assert (tcut_out[both] == tcut_in[both]).all(), "a trail enters and leaves at different cuts"
    indeg = np.bincount(tn[tn >= 0], minlength=S.NS)
    assert indeg.max() <= 1
    # cycles
    seen = np.zeros(S.NS, bool)
    cycles = []
    starts = np.nonzero(indeg == 0)[0]
    paths = []
    for s in starts.tolist():
        p = [s]
        seen[s] = True
        c = s
        while tn[c] >= 0:
            c = int(tn[c])
            p.append(c)
            seen[c] = True
        paths.append(p)
    for s in np.nonzero(~seen)[0].tolist():
        if seen[s]:
            continue
        p = [s]
        seen[s] = True
        c = int(tn[s])
        while c != s:
            p.append(c)
            seen[c] = True
            c = int(tn[c])
        cycles.append(p)
    log("round %d: symmetric integer optimum %.1f x %d = %.0f (status %d, bound %.1f); runs %d, cycles %d (lengths %s)  (%.0fs)" % (
        rnd, val, len(S.G), val * len(S.G), m.Status, m.ObjBound, len(paths), len(cycles),
        sorted(set(len(c) for c in cycles)), time.time() - t0))
    if not cycles:
        if prove > 0 and m.Status != GRB.OPTIMAL and not proving:
            proving = True
            m.Params.TimeLimit = prove
            m.Params.MIPFocus = 3
            log("no cycle left, optimum not proved (value %.1f, bound %.1f): the search goes on for up to %.0f s" % (
                val, m.ObjBound, prove))
            rnd += 1
            continue
        break
    if rnd >= maxrounds:
        # break every cycle at its most expensive join
        for cyc in cycles:
            k_ = max(range(len(cyc)), key=lambda i_: tw[cyc[i_]])
            a_ = cyc[k_]
            val -= (E - int(tw[a_])) / float(len(S.G)) * 1.0
            tn[a_] = -1
            tw[a_] = 0
            paths.append(cyc[k_ + 1:] + cyc[:k_ + 1])
        log("cycles broken at their most expensive join: %d more runs" % len(cycles))
        cycles = []
        break
    # exclude: for one cycle per orbit of cycles, the joins between the trails of the cycle (any cuts, both
    # directions) are at most (number of trails - 1); in orbit variables the coefficient of a variable is the number
    # of its images that lie inside the set of trails
    if timg is None:
        timg = np.zeros((len(S.G), S.NS), np.int64)
        firstcut = np.arange(S.NS) * 110
        for gi, g in enumerate(S.G):
            timg[gi] = S.t[image(firstcut, g)]
        t1_all = S.t[S.rep[I]]
        t2_all = S.t[J]
    added = set()
    for cyc in cycles:
        key = tuple(sorted(int(S.torb[t_]) for t_ in cyc)) + (len(cyc),)
        if key in added:
            continue
        added.add(key)
        inT = np.zeros(S.NS, bool)
        inT[np.array(cyc)] = True
        coef = np.zeros(na, np.int64)
        for gi in range(len(S.G)):
            coef += inT[timg[gi][t1_all]] & inT[timg[gi][t2_all]]
        nz = np.nonzero(coef)[0]
        m.addConstr(gp.quicksum(int(coef[v_]) * z[int(v_)] for v_ in nz.tolist()) <= len(cyc) - 1)
    rnd += 1
lens = np.bincount([len(p) for p in paths])
hist = {int(wv): int((tw[(tn >= 0)] == wv).sum()) for wv in np.unique(tw[tn >= 0]).tolist()}
tot = val * len(S.G)
log("E = %d: symmetric system: %d runs of small trails (trails per run: %s); joins by W %s; sum over runs = %d (LP bound of q12.py to compare)" % (
    E, len(paths), {i: int(c) for i, c in enumerate(lens) if c}, hist, 2 * E * S.NS - 2 * tot))
cut_of = np.where(tcut_out >= 0, tcut_out, tcut_in)
pickle.dump(dict(E=E, paths=paths, cut=cut_of, tw=tw, tn=tn, value=tot), open("runs12_%d%s.pkl" % (E,
    "_d0" if "--d0" in sys.argv else ""), "wb"))
