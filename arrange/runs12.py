#!/usr/bin/env python
"""runs12.py - the run programme of the small trails at a level E, solved exactly (n = 12, levels up to 8).

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: runs12.py [E ...]      (default 4 5 6)   needs small12_joins8.npz (joins12.py)

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

Level E.  A run is a maximal sequence of consecutive small trails joined by joins with W < E.  Charge every run 2 E
for its two ends and 2 W for every join inside.  With N = 6,048 small trails,
    sum over runs [2 E + 2 (W-sum inside)] = 2 E N - 2 sum (E - W) z,          z = the joins inside runs,
so the smallest value of the left side is 2 E N - 2 max sum (E - W) z, the maximum over all systems of paths: one
cut per trail, a join needs both its cuts, no cycle.
The maximum is computed exactly, one integer program per component of the graph "two trails have a join with
W < E" (single trails are skipped; cycles are cut off as they appear).  The list of joins is complete for W <= 7,
so E may be at most 8; in practice the components become too large above E = 6, and q12.py and q12b.py take over.

Prints, per level: the components by (number of trails, optimum) with their count, the joins used by W, and the
value 2 E N - 2 max.  On this piece set: 34,368 at E = 4 and 44,352 at E = 6.

Needs: Python 3, numpy, Gurobi (gurobipy, with a licence beyond the size-limited one).
All files are read from and written to the working directory.
Time and memory, measured: 70 s for the levels 4 and 6 together, 0.25 GB.
"""
import sys, time, numpy as np, pickle
import gurobipy as gp
from gurobipy import GRB

z_ = np.load("small12_joins8.npz")
I, J, W = z_["I"].astype(np.int64), z_["J"].astype(np.int64), z_["W"].astype(np.int64)
NSm = 6048
t_of = lambda c: c // 110
env = gp.Env(params={"OutputFlag": 0})


def comps(nn, a, b):
    """labels of the connected components of the graph on nn nodes with the edges (a[i], b[i]): the smallest node
    of the component, by repeated minimum over the edges"""
    lab = np.arange(nn)
    while True:
        mn = np.minimum(lab[a], lab[b])
        new = lab.copy()
        np.minimum.at(new, a, mn)
        np.minimum.at(new, b, mn)
        new = new[new]
        if (new == lab).all():
            return lab
        lab = new


def solve(a, b, w, E, relax=False):
    """largest sum of (E - w) over a system of paths made of the joins (a[i] -> b[i], weight w[i]) between cuts:
    y[c] = cut c is the cut of its trail (cut c belongs to trail c // 110), z = the join is used.  Cycles are cut off
    and the program solved again until none is left.  Returns (optimum, {W: joins used}).  relax=True: the linear
    relaxation, returned after the first solve."""
    m = gp.Model("r", env=env)
    m.Params.Threads = 2
    cuts = np.unique(np.concatenate([a, b])).tolist()
    vt = GRB.CONTINUOUS if relax else GRB.BINARY
    y = {c: m.addVar(vtype=vt, ub=1) for c in cuts}
    z = {(int(x), int(y_)): m.addVar(vtype=vt, ub=1, obj=float(E - ww)) for x, y_, ww in zip(a.tolist(), b.tolist(),
        w.tolist())}
    m.ModelSense = GRB.MAXIMIZE
    bt = {}
    for c in cuts:
        bt.setdefault(c // 110, []).append(c)
    for tt, cs in bt.items():
        m.addConstr(gp.quicksum(y[c] for c in cs) <= 1)
    out = {}
    inn = {}
    for (x, y_), v in z.items():
        out.setdefault(x, []).append(v)
        inn.setdefault(y_, []).append(v)
    for c in cuts:
        if c in out:
            m.addConstr(gp.quicksum(out[c]) <= y[c])
        if c in inn:
            m.addConstr(gp.quicksum(inn[c]) <= y[c])
    while True:
        m.optimize()
        if relax:
            return m.ObjVal, None
        sel = [k for k, v in z.items() if v.X > 0.5]
        nxt = {x: y_ for x, y_ in sel}
        seen = set()
        cyc = []
        for x in list(nxt):
            if x in seen:
                continue
            p = [x]
            seen.add(x)
            cur = x
            while cur in nxt and nxt[cur] not in seen:
                cur = nxt[cur]
                p.append(cur)
                seen.add(cur)
            if cur in nxt and nxt[cur] == x:
                cyc.append(p)
        if not cyc:
            break
        for p in cyc:
            m.addConstr(gp.quicksum(z[(p[i], p[(i + 1) % len(p)])] for i in range(len(p))) <= len(p) - 1)
    assert m.Status == GRB.OPTIMAL
    hist = {}
    for k in sel:
        ww = int(E - round(z[k].Obj))
        hist[ww] = hist.get(ww, 0) + 1
    return round(m.ObjVal), hist


for E in [int(x) for x in sys.argv[1:]] or [4, 5, 6]:
    m = W < E
    a, b, w = I[m], J[m], W[m]
    lab = comps(NSm, a // 110, b // 110)
    ul, inv = np.unique(lab, return_inverse=True)
    sizes = np.bincount(inv)
    tot = 0
    res = {}
    t0 = time.time()
    la = inv[a // 110]
    o = np.argsort(la, kind="stable")
    la_s = la[o]
    st = np.searchsorted(la_s, np.arange(len(ul)), "left")
    en = np.searchsorted(la_s, np.arange(len(ul)), "right")
    allhist = {}
    for ci in range(len(ul)):
        if sizes[ci] == 1:
            continue
        s = o[st[ci]:en[ci]]
        v, hist = solve(a[s], b[s], w[s], E)
        tot += v
        res.setdefault((int(sizes[ci]), v), 0)
        res[(int(sizes[ci]), v)] += 1
        for k_, c_ in hist.items():
            allhist[k_] = allhist.get(k_, 0) + c_
    val = 2 * E * NSm - 2 * tot
    print("E = %d: components (trails, optimum): count %s; joins used by W %s; sum over runs of val >= 2*%d*%d - 2*%d = %d  (%.0fs)" % (
        E, dict(sorted(res.items())), dict(sorted(allhist.items())), E, NSm, tot, val, time.time() - t0), flush=True)
