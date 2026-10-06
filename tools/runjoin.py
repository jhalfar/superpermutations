"""runjoin.py - reorder the runs of a component-structured superpermutation word and re-open their end pieces.

Input: the output of pieces.c.  Model (Gurobi MIP, an asymmetric TSP path over runs):
  * one node per multi-piece run: its first piece may start at any listed start word (S), its last piece may end at
    any listed end word (E), independently;
  * a single-piece run becomes a cluster of nodes, one per opening word (the KS most promising ones), and exactly one
    node of each run is used;
  * arc a -> b costs h - (largest overlap between an end word of a and a start word of b); arcs of cost > ARC_MAXC
    are dropped (except those of the current order); a depot starts/ends the path and a "hub" allows any join with no
    overlap (cost h); subtours are cut lazily.
The current order is the MIP start, so the result is never worse.  A dynamic program over the final order then picks
the actual start/end words.  Output: a plan for assemble.c, one line "piece offset" per piece.

usage: python runjoin.py pieces.txt plan.txt [time_limit_s] [threads]
env:   ARC_MAXC (default: all arcs), KS (default 30), GRB_PARAMS (e.g. "MIPFocus=1")
needs: gurobipy with a full licence.  `pip install gurobipy` comes with a licence limited to about 2,000 variables and
       constraints, which is too small for these models (n = 11: 373 runs, n = 13: 25,946).  Academic users can get a
       free full licence from Gurobi; others need a commercial one.  Nothing else in this repository needs a solver:
       the words this step gave (43,930,674 and 6,747,918,058) are in words/, and every later plan refers to them or
       to Pantone's words, so the step does not have to be repeated to rebuild or check anything.
       I have not tried the model on an open solver.  It adds subtour cuts lazily in a callback; a version for HiGHS
       or for CP-SAT (which has a circuit constraint) would have to be written and tested.
"""
import collections
import os
import sys

import gurobipy as gp
from gurobipy import GRB


def main():
    tl = float(sys.argv[3]) if len(sys.argv) > 3 else 600; th = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    runs = []; S = collections.defaultdict(list); E = collections.defaultdict(list); O = collections.defaultdict(list)
    pieces = {}
    for line in open(sys.argv[1]):
        t = line.split()
        if t[0] == "N": n, h = int(t[1]), int(t[2])
        elif t[0] == "P": pieces[int(t[1])] = int(t[4])
        elif t[0] == "R": runs.append((int(t[2]), int(t[3])))
        elif t[0] == "S": S[int(t[1])].append((t[3], int(t[2])))
        elif t[0] == "E": E[int(t[1])].append((t[3], int(t[2])))
        elif t[0] == "O": O[int(t[1])].append((t[3], int(t[2])))
    R = len(runs)
    single = [runs[r][0] == runs[r][1] and pieces[runs[r][0]] == 1 for r in range(R)]
    print("n=%d runs %d single %d" % (n, R, sum(single)), flush=True)

    def ov(x, y):
        for k in range(min(len(x), len(y), h - 1), 0, -1):
            if x[-k:] == y[:k]: return k
        return 0
    # current start/end word of each run (offset 0 of first piece / last piece as written)
    def cur_start(r):
        lst = O[r] if single[r] else S[r]
        for w, off in lst:
            if off in (0, -1): return w
        return lst[0][0]

    def cur_end(r):
        lst = O[r] if single[r] else E[r]
        for w, off in lst:
            if off in (0, -1): return w
        return lst[0][0]
    cur = [ov(cur_end(r), cur_start(r + 1)) for r in range(R - 1)]
    print("current inter-run join cost %d" % sum(h - c for c in cur), flush=True)
    # nodes
    pidx = collections.defaultdict(int); sidx = collections.defaultdict(int)
    for r in range(R):
        if single[r]: continue
        for w, _ in S[r]:
            for k in range(1, h): pidx[(k, w[:k])] += 1
        for w, _ in E[r]:
            for k in range(1, h): sidx[(k, w[-k:])] += 1

    def bin_(v): return max([k for k in range(1, h) if sidx.get((k, v[:k]))] or [0])
    def bout(v): return max([k for k in range(1, h) if pidx.get((k, v[-k:]))] or [0])
    KS = int(os.environ.get("KS", "30"))
    nodes = []
    for r in range(R):
        if single[r]:
            vs = sorted(O[r], key=lambda wo: -(bin_(wo[0]) + bout(wo[0])))[:KS]
            c0 = [wo for wo in O[r] if wo[1] == 0]
            if c0 and c0[0] not in vs: vs.append(c0[0])
            for wo in vs: nodes.append((r, [wo], [wo]))
        else:
            nodes.append((r, S[r], E[r]))
    NN = len(nodes); nrun = [nd[0] for nd in nodes]
    byrun = collections.defaultdict(list)
    for a, nd in enumerate(nodes): byrun[nd[0]].append(a)
    pre = collections.defaultdict(set)
    for j, nd in enumerate(nodes):
        for w, _ in nd[1]:
            for k in range(1, h): pre[(k, w[:k])].add(j)
    maxc = int(os.environ.get("ARC_MAXC", "0")) or h
    arcs = {}
    for i, nd in enumerate(nodes):
        best = {}
        for w, _ in nd[2]:
            for k in range(h - 1, 0, -1):
                if h - k > maxc: break
                for j in pre.get((k, w[-k:]), ()):
                    if nrun[j] != nrun[i] and best.get(j, 0) < k: best[j] = k
        for j, k in best.items(): arcs[i, j] = h - k
    cur_node = []
    for r in range(R):
        cands = byrun[r]
        if len(cands) > 1:
            c0 = [a for a in cands if nodes[a][1][0][1] == 0]; cands = c0 or cands[:1]
        cur_node.append(cands[0])
    for q in range(R - 1):
        a, b = cur_node[q], cur_node[q + 1]
        if (a, b) not in arcs and cur[q] > 0: arcs[a, b] = h - cur[q]
    print("nodes %d arcs %d" % (NN, len(arcs)), flush=True)
    m = gp.Model("runs"); m.Params.TimeLimit = tl; m.Params.Threads = th; m.Params.LazyConstraints = 1
    for kv in filter(None, os.environ.get("GRB_PARAMS", "").split(",")):
        k_, v_ = kv.split("="); m.setParam(k_, float(v_) if "." in v_ else int(v_))
    D = NN; hub = NN + 1
    x = {}
    for (i, j), c in arcs.items(): x[i, j] = m.addVar(vtype=GRB.BINARY, obj=c)
    for i in range(NN):
        x[i, hub] = m.addVar(vtype=GRB.BINARY, obj=h); x[hub, i] = m.addVar(vtype=GRB.BINARY, obj=0)
        x[D, i] = m.addVar(vtype=GRB.BINARY, obj=0); x[i, D] = m.addVar(vtype=GRB.BINARY, obj=0)
    outs = collections.defaultdict(list); ins = collections.defaultdict(list)
    for (i, j), var in x.items(): outs[i].append(var); ins[j].append(var)
    for r in range(R): m.addConstr(gp.quicksum(v for a in byrun[r] for v in ins[a]) == 1)
    for a in range(NN): m.addConstr(gp.quicksum(outs[a]) == gp.quicksum(ins[a]))
    m.addConstr(gp.quicksum(outs[D]) == 1); m.addConstr(gp.quicksum(ins[D]) == 1)
    m.addConstr(gp.quicksum(outs[hub]) == gp.quicksum(ins[hub]))
    for var in x.values(): var.Start = 0
    for q in range(R - 1):
        a, b = cur_node[q], cur_node[q + 1]
        if (a, b) in x: x[a, b].Start = 1
        else: x[a, hub].Start = 1; x[hub, b].Start = 1
    x[D, cur_node[0]].Start = 1; x[cur_node[-1], D].Start = 1
    keys = list(x.keys())

    def cb(model, where):
        if where != GRB.Callback.MIPSOL: return
        val = model.cbGetSolution([x[k] for k in keys])
        succ = collections.defaultdict(list)
        for k, vv in zip(keys, val):
            if vv > 0.5: succ[k[0]].append(k[1])
        seen = set(); st = [D, hub]
        while st:
            u = st.pop()
            for w in succ[u]:
                if w not in seen: seen.add(w); st.append(w)
        active = {k[1] for k, vv in zip(keys, val) if vv > 0.5 and k[1] < NN}
        ms = active - seen
        while ms:
            comp = set(); stk = [next(iter(ms))]
            while stk:
                u = stk.pop()
                if u in comp: continue
                comp.add(u); stk.extend(w for w in succ[u] if w in ms)
            ms -= comp
            rset = {nrun[u] for u in comp}
            model.cbLazy(gp.quicksum(x[k] for k in keys if k[0] < NN and nrun[k[0]] in rset and (k[1] >= NN or nrun[k[1]] not in rset)) >= 1)

    m.optimize(cb)
    print("ATSP status", m.Status, "obj", m.ObjVal, "bound", m.ObjBound, flush=True)
    succ = collections.defaultdict(list)
    for k in keys:
        if x[k].X > 0.5: succ[k[0]].append(k[1])
    segs = []
    for st0 in succ[D] + succ[hub]:
        seg = []; u = st0
        while u not in (D, hub): seg.append(u); u = succ[u][0]
        segs.append((seg, u))
    first = segs[0]; rest = segs[1:]
    last = [sg for sg in rest if sg[1] == D]; mid = [sg for sg in rest if sg[1] == hub]
    norder = first[0] + [a for sg in mid for a in sg[0]] + ([] if first[1] == D else last[0][0])
    assert sorted(nrun[a] for a in norder) == list(range(R))
    # DP over the order for start / end words
    val = {None: (0, None)}; hist = []
    for a in norder:
        r = nrun[a]; nv = {}
        for pe, (sc, _) in val.items():
            for sw, so in nodes[a][1]:
                g = sc + (ov(pe, sw) if pe is not None else 0)
                ends = [(sw, so)] if single[r] else nodes[a][2]
                for ew, eo in ends:
                    if ew not in nv or nv[ew][0] < g: nv[ew] = (g, (pe, (sw, so), (ew, eo)))
        hist.append(nv); val = nv
    endw = max(val, key=lambda k: val[k][0]); total_ov = val[endw][0]
    choice = []
    for idx in range(len(norder) - 1, -1, -1):
        g, (pe, s_, e_) = hist[idx][endw]; choice.append((s_, e_)); endw = pe
    choice.reverse()
    with open(sys.argv[2], "w", newline="\n") as fo:
        for a, (s_, e_) in zip(norder, choice):
            r = nrun[a]; f, l = runs[r]
            if f == l: fo.write("%d %d\n" % (f, s_[1])); continue
            fo.write("%d %d\n" % (f, s_[1]))
            for p in range(f + 1, l): fo.write("%d %d\n" % (p, 0 if pieces[p] else -1))
            fo.write("%d %d\n" % (l, e_[1]))
    print("plan written; inter-run overlap %d -> join cost %d (was %d)" % (total_ov, (R - 1) * h - total_ov, sum(h - c for c in cur)), flush=True)


if __name__ == "__main__":
    main()
