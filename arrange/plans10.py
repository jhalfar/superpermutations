#!/usr/bin/env python
"""plans10.py - the solutions of the chain model at n = 10 valued exactly and written as plans.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: plans10.py SOL.pkl BASE.txt GT.npz [TOP]
       needs c10m_states.pkl (trav10.py); writes plan10m_pP_LENGTH.plan and .pkl for the TOP best solutions

  SOL.pkl   solutions written by chain10.py solve
  BASE.txt  the base word of the n = 10 pieces;  GT.npz  its traversal tables (gt.py)
  TOP       how many solutions, best first by the value of the chain model (default 3)

A solution of chain10.py is an order of the 8 chains of a partition, each cut at one of its joins, with blocks of big
trails in some of the gaps.  Here it is read as an order of the 62 objects (48 groups, 14 big trails) and handed to
tl10.py, which finds the best cuts and modes of all objects for that order exactly.  The chain model fixes more
than the order (the traversals of the two middle groups of every chain), so the exact value is at most the value of
the model.  The plan is written, its cost is computed a second time from the joins alone and asserted to be equal,
and the length of the word is printed.

Prints, per solution: the partition, the value of the chain model, the exact 2 cost, the length, the number of
groups written as loops, and the name of the plan.  P in the file name is the number of the partition.

Needs: Python 3, numpy; tl10.py and what it imports.  Time and memory, measured: 6 s and 0.44 GB for three solutions.
"""
import sys, pickle, numpy as np
import tl10

log = lambda *x: print(*x, flush=True)
BM = sys.argv[2]
res, CR = pickle.load(open(sys.argv[1], "rb"))
top = int(sys.argv[4]) if len(sys.argv) > 4 else 3
st = pickle.load(open("c10m_states.pkl", "rb"))
nodes, cyc = st["nodes"], st["cyc"]
M = tl10.TL(BM, sys.argv[3], log)
NG = M.NG
blen = len(open(BM, "rb").read().strip())
NA = len(CR)
best = None
for cost, pi, gaps in sorted(res)[:top]:
    order = []
    for a, b, s, v in gaps:
        if s is not None:
            order += [NG + x for x in s]
        if b != NA:
            ci, r = CR[b]
            order += [nodes[i][0] for i in (cyc[ci][r:] + cyc[ci][:r])]
    assert sorted(order) == list(range(M.NO))
    v, stt = M.evaluate(order, trace=True)
    ev = M.events(order, stt)
    assert M.cost_of_events(ev) == v
    L, _ = M.spell_len(ev)
    out = "plan10m_p%d_%d.plan" % (pi, L)
    M.write_plan(ev, out, blen)
    pickle.dump(dict(order=order, states=stt, ev=ev, val=v), open(out[:-5] + ".pkl", "wb"))
    log("partition %d: chain model %d, exact 2 cost %d, length %d, loops %d -> %s" % (pi, cost, v, L, sum(1 for (y, x),
        o in zip(stt, order) if o < NG and y == x), out))
    if best is None or L < best[0]:
        best = (L, out)
log("best %d %s" % best)
