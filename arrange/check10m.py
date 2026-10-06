#!/usr/bin/env python
"""check10m.py - the accounting of cert10.py checked on a real word of n = 10.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: check10m.py BASE.txt GT.npz SEQ.pkl [--a A --cap C]

  BASE.txt, GT.npz  as for cert10.py
  SEQ.pkl           a word read by anatomy.py (the cut at which every event enters and leaves its trail)

The family is that of cert10.py --multi: small trails in several segments, big trails written once.  The word is
split into runs (consecutive events of small trails of one group) and connections; the identity
    4 cost = sum over runs [ e_in + 2 inside + e_out ] + sum over connections (2 w - e_out - e_in) + end terms
is evaluated on both sides and the line ends with IDENTITY OK or MISMATCH.  The terms are printed so that they can
be compared with the minima of cert10.py: the value of every group against G, every block against Y_k.
On rumstd's word of 4,034,873 letters, with Pantone's word as base: 4 cost = 2,056 on both sides (369 events in
48 runs; every group at 40 except one at 42).

Needs: Python 3, numpy, top.py, countn.py, tm.py.  Time and memory, measured: 3 s, 0.34 GB.
"""
import sys, pickle, numpy as np
import top

base, gtf, seqf = sys.argv[1:4]
opt = lambda k, d: type(d)(sys.argv[sys.argv.index(k) + 1]) if k in sys.argv else d
A = opt("--a", 1)
C = opt("--cap", 2)
T = top.Top(base, cmax=4, log=lambda *x: None)
Tt = np.load(gtf)["T"].astype(np.int64)
sm = np.nonzero(T.is_small)[0]
hx = np.zeros(T.V, np.int64)
hy = np.zeros(T.V, np.int64)
for g in range(T.NG):
    cuts = np.nonzero(T.obj == g)[0]
    hx[cuts] = np.minimum(Tt[g].min(0) - 12, 8)
    hy[cuts] = np.minimum(Tt[g].min(1) - 12, 8)
ein = np.zeros(T.V, np.int64)
eout = np.zeros(T.V, np.int64)
ein[sm] = 8 - A * np.minimum(hy[sm], C)
eout[sm] = 8 - A * np.minimum(hx[sm], C)
d = pickle.load(open(seqf, "rb"))
ent, ext = [int(x) for x in d["ent"]], [int(x) for x in d["ext"]]
N = len(ent)
D = T.D
W = [T.W(ext[i], ent[i + 1]) for i in range(N - 1)]
cost2 = int(D[ent[0]] + sum(W) + D[ext[-1]])
small = [bool(T.is_small[c]) for c in ent]
obj = [int(T.obj[c]) for c in ent]
items = []
i = 0
while i < N:
    j = i
    if small[i]:
        while j + 1 < N and small[j + 1] and obj[j + 1] == obj[i]:
            j += 1
        items.append(("R", i, j))
    else:
        while j + 1 < N and not small[j + 1]:
            j += 1
        items.append(("B", i, j))
    i = j + 1
R = 0
per = {}
for kind, i, j in items:
    if kind == "R":
        v = int(ein[ent[i]] + 2 * sum(W[i:j]) + eout[ext[j]])
        R += v
        per[obj[i]] = per.get(obj[i], 0) + v
conn = 0
hist = {}
for k in range(len(items) - 1):
    it, nx = items[k], items[k + 1]
    if it[0] != "R":
        continue
    if nx[0] == "R":
        t = 2 * W[it[2]] - int(eout[ext[it[2]]]) - int(ein[ent[nx[1]]])
        name = "join"
    else:
        y = ent[items[k + 2][1]]
        t = 2 * sum(W[it[2]:nx[2] + 1]) - int(eout[ext[it[2]]]) - int(ein[y])
        name = "block of %d" % (nx[2] - nx[1] + 1)
    conn += t
    hist[(name, t)] = hist.get((name, t), 0) + 1
st = 2 * int(D[ent[0]]) - int(ein[ent[0]])
en = 2 * int(D[ext[-1]]) - int(eout[ext[-1]])
print("events %d, runs %d; group values (sum over the runs of a group): %s" % (N, sum(1 for x in items if x[0] == "R"),
    dict(zip(*[a.tolist() for a in np.unique(list(per.values()), return_counts=True)]))))
print("connections (kind, 2 w - e_out - e_in): count  %s" % dict(sorted(hist.items())))
print("4 cost of the word %d; runs %d + connections %d + start %d + end %d = %d   %s" % (2 * cost2, R, conn, st, en,
    R + conn + st + en, "IDENTITY OK" if 2 * cost2 == R + conn + st + en else "MISMATCH"))
