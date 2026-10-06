#!/usr/bin/env python
"""liftmip.py - can a selection with rows of other lengths be carried one symbol higher, and at what price?

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: liftmip.py SEL [--free] [--time SEC] [--out FILE]

  SEL     a selection, or a part of one (a block), on K letters: lines "x v" with v the number of visible classes of
          the row (0: loop without a row), or "x F|S|D", or the older "x+s full|short|detached"
  --free  drop the condition that the new walk stays above the old one (see below)
  --time  time limit of the solver in seconds (default 300)
  --out   write the selection found (lines "x v" on K + 1 letters)

Question.  Pantone's transport carries a selection with full and short rows to one on one more symbol with K times
the Q.  Is there a selection one symbol higher that lies above a selection with rows of other lengths, and what is
its smallest Q?  This is an integer program, for small K only.

Model.  The new letter is w = K.  New loops are the cyclic orders of K + 1 letters; a new loop lies above the old
loop that is left when w is deleted.
  loops above an old loop without a row: no row
  loops above an old row: exactly one row (state rho, c visible classes, c in 1 .. K-1 or K+1); the state after the
      row must be the state of the row of its loop (a flow on the states)
  default: the step must stay above the old walk: deleting w from the next state gives the old loop itself or the
      loop of the next old row ("lift")
  --free: no such condition (any selection with these loops without a row)
  no closed walk may stay inside one fibre (the loops above one old loop): such walks are cut off as they appear
  minimise Q' = sum of (K + 1 - c)
For a selection with full and short rows only, the transport has Q' = K Q.

Prints the old rows by length and K Q; the smallest Q' with the solver's status, its bound and the number of
fibre cuts; and the walks, walk trails and floor Q + (loops without a row) + trails of the old and of the new
selection, with the cost of leaving all new loops without a row.  The trails are counted by the port rule (cycles of
the product of the port permutations of geng.py).

What it showed.  On the selection of Pantone's n = 8 word (K = 6) the cheapest lift is the transport (576 = K Q,
optimal).  With rows
of other lengths the lift is dearer than K Q: 426 against 288 on a 6-letter test selection (optimal).  For the
block of the n = 11 pieces (K = 9) a run of 400 s gave 466 with bound 451, and with the loops without a row the lift
costs at least 577 where leaving all loops above the block without a row costs 504.  So a block solution with rows
of other lengths gains at the level where it was found and has to be searched again one level up.
The program minimises Q' only, not the number of trails; the conclusion holds because Q' plus the loops without a
row is already above 504.  Status 2 means the minimum is proved; status 9 is the time limit, and then only the bound
printed is proved.

Needs: Python 3; Gurobi (gurobipy, with a licence beyond the size-limited one); geng.py next to this file or on
PYTHONPATH (port permutations).
Time and memory, measured: 2 s and 13 s for the two selections with K = 6, 0.06 GB.  The K = 9 block ran
into its time limit of 400 s (figures above from that run, in my notes).
"""
import argparse
import collections
import itertools
import sys

import gurobipy as gp
from gurobipy import GRB

ALPH = "0123456789ABCDEF"


def step(x, v, K):
    """the state after the row x with v visible classes (v = K: a full row)"""
    if v == K:
        return x[1:K - 1] + x[0:1] + x[K - 1:K]
    return x[v + 1:] + x[:v - 1] + x[v:v + 1] + x[v - 1:v]


def canon(x):
    """the cyclic word x read from the letter 0"""
    i = x.index(0)
    return x[i:] + x[:i]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sel")
    ap.add_argument("--free", action="store_true")
    ap.add_argument("--time", type=float, default=300)
    ap.add_argument("--out")
    a = ap.parse_args()
    rows = []
    for line in open(a.sel):
        if line.startswith("#") or not line.strip():
            continue
        p = line.split()
        x = tuple(ALPH.index(ch) for ch in p[0])
        K = len(x)
        if p[1] in ("full", "short", "detached"):
            x = x[:-1]
            K = len(x)
            v = {"full": K, "short": K - 2, "detached": 0}[p[1]]
        else:
            v = {"F": K, "S": K - 2, "D": 0}[p[1]] if p[1] in ("F", "S", "D") else int(p[1])
        rows.append((x, v))
    K = len(rows[0][0])
    K2 = K + 1
    w = K
    oldrow = {canon(x): (x, v) for x, v in rows}
    Q = sum(K - v for x, v in rows if v > 0)
    nextloop = {canon(x): canon(step(x, v, K)) for x, v in rows if v > 0}

    def below(y):
        """the old loop under the new loop or state y"""
        return canon(tuple(c for c in y if c != w))

    m = gp.Model("lift", env=gp.Env(params={"OutputFlag": 0}))
    m.Params.OutputFlag = 0
    m.Params.Threads = 2
    m.Params.TimeLimit = a.time
    r = {}
    out = collections.defaultdict(list)
    inn = collections.defaultdict(list)
    byloop = collections.defaultdict(list)
    lens = list(range(1, K2 - 1)) + [K2]
    nloops = 0
    newloops = []
    for ol0 in oldrow:                      # also for a part of a selection (a block): the loops above its loops
        for j in range(K):
            newloops.append(canon(ol0[:j] + (w,) + ol0[j:]))
    assert len(set(newloops)) == len(newloops)
    # one binary variable for every (state rho of a new loop above an old row, length c) whose step lands on a
    # loop above an old row (and, without --free, above the same old loop or the next one of the old walk)
    for y in newloops:
        ol = below(y)
        if oldrow[ol][1] == 0:
            continue
        nloops += 1
        for i in range(K2):
            rho = y[i:] + y[:i]
            for c in lens:
                t = step(rho, c, K2)
                tl = below(t)
                if tl not in oldrow or oldrow[tl][1] == 0:
                    continue
                if not a.free and tl != ol and tl != nextloop[ol]:
                    continue
                var = m.addVar(vtype=GRB.BINARY, obj=K2 - c)
                r[rho, c] = var
                out[rho].append(var)
                inn[t].append(var)
                byloop[y].append(var)
    for y, vs in byloop.items():
        m.addConstr(gp.quicksum(vs) == 1)
    if len(byloop) != nloops:
        print("%d loops above a row have no possible row" % (nloops - len(byloop)))
    for rho in set(out) | set(inn):
        m.addConstr(gp.quicksum(out[rho]) == gp.quicksum(inn[rho]))
    # no closed walk inside one fibre (the loops above one old loop): cuts added until none is left
    ncut = 0
    for it in range(200):
        m.optimize()
        if m.SolCount == 0:
            break
        nxt = {rho: step(rho, c, K2) for (rho, c), var in r.items() if var.X > 0.5}
        seen, cuts = set(), []
        for r0 in nxt:
            if r0 in seen:
                continue
            cyc, x = [], r0
            while x not in seen:
                seen.add(x)
                cyc.append(x)
                x = nxt[x]
            if x == r0 and len({below(q) for q in cyc}) == 1:
                cuts.append(cyc)
        if not cuts:
            break
        for cyc in cuts:
            sc = set(cyc)
            vs = [var for (rho, c), var in r.items() if rho in sc and step(rho, c, K2) in sc]
            m.addConstr(gp.quicksum(vs) <= len(cyc) - 1)
            ncut += 1
    print("K = %d: old rows %d (by length %s), loops without a row %d, Q = %d; K Q = %d" % (
        K, sum(1 for x, v in rows if v > 0), dict(sorted(collections.Counter(v for x, v in rows if v > 0).items())),
        sum(1 for x, v in rows if v == 0), Q, K * Q))
    if m.SolCount == 0:
        print("%s: NO selection above it without closed walks inside a fibre (status %d, %d cuts)" % (
            "free" if a.free else "lift", m.Status, ncut))
        return
    used = collections.Counter(c for (rho, c), var in r.items() if var.X > 0.5)
    print("%s: smallest Q' = %.0f (status %d, bound %.0f, %d fibre cuts); ratio Q' / (K Q) = %.3f; new rows by length %s" % (
        "free" if a.free else "lift", m.ObjVal, m.Status, m.ObjBound, ncut, m.ObjVal / (K * Q) if Q else 0,
        dict(sorted(used.items()))))
    if a.out:
        with open(a.out, "w") as fo:
            fo.write("# liftmip.py %s: selection on K = %d letters above it\n" % (a.sel, K2))
            for (rho, c), var in r.items():
                if var.X > 0.5:
                    fo.write("%s %d\n" % ("".join(ALPH[q] for q in rho), c))
            for y in newloops:
                if oldrow[below(y)][1] == 0:
                    fo.write("%s 0\n" % "".join(ALPH[q] for q in y))
        print("wrote %s" % a.out)
    # trails of the walks by the port rule: cycles of the product of the port permutations
    import os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import geng

    def trails_of(sel, KK):
        """(number of walks, number of closed trails after completion) of a selection given as {state: length}"""
        nx = {x: step(x, v, KK) for x, v in sel.items()}
        seen, tot, nw = set(), 0, 0
        for x0 in sel:
            if x0 in seen:
                continue
            perm = list(range(KK - 1))
            x = x0
            while x not in seen:
                seen.add(x)
                perm = [geng.port_perm(sel[x], p, KK) for p in perm]
                x = nx[x]
            done = [False] * (KK - 1)
            for p in range(KK - 1):
                if not done[p]:
                    tot += 1
                    q = p
                    while not done[q]:
                        done[q] = True
                        q = perm[q]
            nw += 1
        return nw, tot

    oldsel = {x: v for x, v in rows if v > 0}
    newsel = {rho: c for (rho, c), var in r.items() if var.X > 0.5}
    ow, ot = trails_of(oldsel, K)
    nw_, nt = trails_of(newsel, K2)
    d0 = sum(1 for x, v in rows if v == 0)
    print("old: walks %d, walk trails %d, loops without a row %d, floor Q + D + trails = %d;  K x floor = %d" % (
        ow, ot, d0, Q + d0 + ot, K * (Q + d0 + ot)))
    print("new: walks %d, walk trails %d, loops without a row %d, floor Q' + D' + trails' = %d;  all %d loops without a row would cost %d" % (
        nw_, nt, K * d0, m.ObjVal + K * d0 + nt, len(newloops), len(newloops)))


if __name__ == "__main__":
    main()
