#!/usr/bin/env python
"""joins12.py - the cheap joins between cuts of the small trails, and the largest set of cost-1 joins (n = 12).

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: joins12.py      needs cuts12c.bin; writes small12_joins8.npz (read by runs12.py)

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

1. Every pair (x, y) of small cuts whose words overlap in 6 letters or more is listed with its W (at most 8).  The
   list is complete for W <= 7.  The joins between cuts of different trails go to the file (I, J: numbers of the
   cuts, W).
2. The joins with W = 2, that is cost 1.  The largest number of them that one arrangement can use is found by an
   integer program: one cut per trail, a join needs both its cuts, a cut has at most one join out and one in, and
   cycles are cut off as they appear, until the optimum has none.  The value printed is exact when the status is 2.
   On this piece set it is 3,504, the number chainplan.py finds with its own model on the loops; so no arrangement
   has fewer than 6,048 - 3,504 = 2,544 runs of small trails joined at cost 1 (a single trail counts as a run).

Needs: Python 3, numpy, c12.py, Gurobi (gurobipy, with a licence beyond the size-limited one).
All files are read from and written to the working directory.
Time and memory, measured: 30 s, 1.27 GB.
"""
import sys, time, numpy as np, pickle
import c12
import gurobipy as gp
from gurobipy import GRB

log = lambda *x: print(*x, flush=True)
C = c12.Cuts("cuts12c.bin", log=log)
H = lambda a: {int(k): int(v) for k, v in zip(*np.unique(a, return_counts=True))}
h = C.h
NSm = 6048
ns = NSm * 110
w = C.col("w", 0, ns).astype(np.int64)
D = C.D[:ns].astype(np.int64)
t = C.t[:ns].astype(np.int64)
ex = w & ((1 << 36) - 1)
en = w >> (4 * D)
# all joins between small cuts with overlap >= 6 (c <= 3): W <= 8.  For every overlap k the start words are sorted
# by their first k letters and every end word looks up its last k letters; a pair found at several overlaps keeps
# the largest one (smallest W).
I, J, Wc = [], [], []
for k in range(h, 5, -1):
    a = c12.suffix(ex, k)
    b = c12.prefix(en, k, h)
    o = np.argsort(b, kind="stable")
    bs = b[o]
    lo = np.searchsorted(bs, a, "left")
    hi = np.searchsorted(bs, a, "right")
    cn = hi - lo
    tot = int(cn.sum())
    ii = np.repeat(np.arange(ns), cn)
    jj = o[np.repeat(lo, cn) + (np.arange(tot) - np.repeat(np.cumsum(cn) - cn, cn))]
    I.append(ii)
    J.append(jj)
    Wc.append(2 * (h - k) + D[ii] + D[jj])
I = np.concatenate(I)
J = np.concatenate(J)
Wc = np.concatenate(Wc)
key = I * ns + J
o = np.lexsort((Wc, key))
key, I, J, Wc = key[o], I[o], J[o], Wc[o]
f = np.concatenate([[True], key[1:] != key[:-1]])
I, J, Wc = I[f], J[f], Wc[f]
dt = t[I] != t[J]
print("joins between cuts of different small trails, W (complete for W <= 7): count", H(Wc[dt]))
print("joins between two different cuts of one small trail:", H(Wc[(~dt) & (I != J)]))
np.savez("small12_joins8.npz", I=I[dt].astype(np.int32), J=J[dt].astype(np.int32), W=Wc[dt].astype(np.int8))
# W = 2 joins: degrees of cuts
m2 = dt & (Wc == 2)
a2, b2 = I[m2], J[m2]
print("W=2 joins:", int(m2.sum()), "; D of the cuts:", H(D[a2] * 2 + D[b2]), "; out-degree of a cut", H(np.bincount(a2,
    minlength=ns)), "in-degree", H(np.bincount(b2, minlength=ns)))
# largest number of W=2 joins in an arrangement that writes every trail once: one cut per trail, a join needs both
# its cuts.  y[c] = 1: cut c is the cut of its trail; z[a, b] = 1: the join from cut a to cut b is used.
env = gp.Env(params={"OutputFlag": 0})
m = gp.Model("links", env=env)
m.Params.Threads = 2
cuts_used = np.unique(np.concatenate([a2, b2]))
y = {int(c): m.addVar(vtype=GRB.BINARY) for c in cuts_used.tolist()}
z = {(int(a), int(b)): m.addVar(vtype=GRB.BINARY) for a, b in zip(a2.tolist(), b2.tolist())}
bytrail = {}
for c in cuts_used.tolist():
    bytrail.setdefault(int(t[c]), []).append(c)
for tt, cs in bytrail.items():
    m.addConstr(gp.quicksum(y[c] for c in cs) <= 1)
out = {}
inn = {}
for (a, b), v in z.items():
    out.setdefault(a, []).append(v)
    inn.setdefault(b, []).append(v)
for c in y:
    if c in out:
        m.addConstr(gp.quicksum(out[c]) <= y[c])
    if c in inn:
        m.addConstr(gp.quicksum(inn[c]) <= y[c])
m.setObjective(gp.quicksum(z.values()), GRB.MAXIMIZE)
# cycles are cut off when they appear
while True:
    m.optimize()
    sel = [(a, b) for (a, b), v in z.items() if v.X > 0.5]
    nxt = {a: b for a, b in sel}
    seen = set()
    cyc = []
    for a in list(nxt):
        if a in seen:
            continue
        path = [a]
        seen.add(a)
        cur = a
        while cur in nxt and nxt[cur] not in seen:
            cur = nxt[cur]
            path.append(cur)
            seen.add(cur)
        if cur in nxt and nxt[cur] == a:
            cyc.append(path)
    if not cyc:
        break
    for p in cyc:
        m.addConstr(gp.quicksum(z[(p[i], p[(i + 1) % len(p)])] for i in range(len(p))) <= len(p) - 1)
print("largest number of W=2 joins usable at once (one cut per trail, no cycle): %d (status %d, bound %.1f) -> at least %d runs of small trails" % (
    round(m.ObjVal), m.Status, m.ObjBound, NSm - round(m.ObjVal)))
