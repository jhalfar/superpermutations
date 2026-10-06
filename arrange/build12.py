#!/usr/bin/env python
"""build12.py - a plan from a system of runs of the small trails (n = 12).

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: build12.py RUNS.pkl POINTER.plan OUT.plan BASE.txt BASE.tsv
       needs cuts12c.bin and smallpos12.npz (smallpos.py)

  RUNS.pkl      a run system written by q12b.py
  POINTER.plan  a plan on BASE that writes every trail once from one cut (lines "O" only).  The events of the trails
                that are not small are taken from it, in blocks: maximal sequences of consecutive such events, order
                and cuts unchanged.  I used the best plan I had at the time.
  OUT.plan      the plan
  BASE.txt, BASE.tsv  the base word of the piece set and its table

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

Steps.
  1. Every run has its first and its last cut from the run system; a trail without a join is a run of its own and
     gets its first cut at a vertex.  Cm[u, v] = W from the last cut of run u to the first cut of run v.
  2. Order of the runs: the cheapest successor for all runs at once (linear assignment on Cm); the cycles of the
     assignment are joined one by one (the smallest cycle, with the cheapest exchange of two successors); the
     closed order is opened at its most expensive join; then segments of 1 to 3 consecutive runs are moved to the
     place where the move gains most, until nothing gains or 20 rounds have passed.
  3. The blocks of POINTER.plan go into the gaps between consecutive runs.  Block b in the gap after run i changes
     the plan by W(end of run i, first cut of b) + W(last cut of b, start of the next run) - W(the direct join);
     the blocks are assigned to different gaps so that the sum of the changes is smallest (linear assignment).
  4. The plan: the runs in order, every small trail at the cut of the run system, each block after its run.
The cuts should then be chosen again by the fixed-order pass (recut BASE.txt OUT.txt --plan-in OUT.plan --co-skip
--time 0), which is how the lengths in the README were obtained.

Status.  A heuristic.  The value of the first assignment is a lower bound only for closed orders of these runs
with these end cuts.  Nothing here says the plan is the best one for the run system.

Needs: Python 3, numpy, scipy, c12.py.
All files are read from and written to the working directory.
Time and memory, measured: 3 s, 0.61 GB.
"""
import sys, pickle, time
import numpy as np
from scipy.optimize import linear_sum_assignment
import c12

log = lambda *x: print(*x, flush=True)
runs_f, ptr_f, out_f = sys.argv[1:4]
h = 9
NS = 6048
BASE, TSV = sys.argv[4:6]
tab = [l.split("\t") for l in open(TSV)]
off = np.array([int(t[3]) for t in tab])
R = np.array([int(t[2]) for t in tab])
word = np.memmap(BASE, np.uint8, "r")
lut = np.full(256, 255, np.uint8)
lut[np.frombuffer(b"0123456789ABCDEF", np.uint8)] = np.arange(16, dtype=np.uint8)


def hw(t, pos):
    """code of the 9 letters of trail t from offset pos of its piece, read around the closed trail"""
    Rt = int(R[t])
    pos %= Rt
    idx = (pos + np.arange(h)) % Rt
    s = lut[np.array(word[off[t] + idx])]
    c = 0
    for a in s.tolist():
        c = (c << 4) | a
    return c


def wmat(ex, Dx, en, Dy):
    """the matrix of W from cuts with end codes ex and costs Dx (rows) to cuts with start codes en and costs Dy
    (columns), by comparing the last k letters with the first k for every k"""
    ex = np.asarray(ex, np.int64)
    en = np.asarray(en, np.int64)
    Wm = np.full((len(ex), len(en)), 2 * h, np.int64)
    for k in range(1, h + 1):
        a = c12.suffix(ex, k)
        b = c12.prefix(en, k, h)
        eq = a[:, None] == b[None, :]
        Wm = np.where(eq, 2 * (h - k), Wm)  # larger k overwrites: the largest overlap wins
    return Wm + np.asarray(Dx, np.int64)[:, None] + np.asarray(Dy, np.int64)[None, :]


C = c12.Cuts("cuts12c.bin", log=log)
ns = NS * 110
w = C.col("w", 0, ns).astype(np.int64)
D = C.D[:ns].astype(np.int64)
ex = w & ((1 << 36) - 1)
en = w >> (4 * D)
sp_ = np.load("smallpos12.npz")
sstart, sgap = sp_["start"], sp_["gap"]
Rn = pickle.load(open(runs_f, "rb"))
paths = Rn["paths"]
cut = Rn["cut"]
# trails without a join: any cut; take the first D = 0 cut (they are single runs)
for t in range(NS):
    if cut[t] < 0:
        cut[t] = t * 110 + int(np.nonzero(D[t * 110:(t + 1) * 110] == 0)[0][0])
U = len(paths)
first = np.array([cut[p[0]] for p in paths])
last = np.array([cut[p[-1]] for p in paths])
inside = sum(int(Rn["tw"][t]) for p in paths for t in p[:-1])
log("runs %d, joins inside %d (W-sum %d)" % (U, NS - U, inside))
Cm = wmat(ex[last], D[last], en[first], D[first])
BIGC = 10 ** 6
np.fill_diagonal(Cm, BIGC)
log("join weights between run ends: smallest per run (out) %s" % dict(zip(*[a.tolist() for a in np.unique(Cm.min(1),
    return_counts=True)])))
# single runs (one trail, no fixed cut) could use any cut: keep the chosen D = 0 cut (the fixed-order pass chooses
# their cuts again)
r, c = linear_sum_assignment(Cm)
nxt = np.empty(U, np.int64)
nxt[r] = c
log("assignment: sum of W %d (lower bound for any order of these runs with these end cuts)" % int(Cm[r, c].sum()))
# cycles of the assignment: lab[u] = number of the cycle of run u
lab = np.full(U, -1, np.int64)
cycles = []
for s in range(U):
    if lab[s] >= 0:
        continue
    cyc = [s]
    lab[s] = len(cycles)
    x = int(nxt[s])
    while x != s:
        cyc.append(x)
        lab[x] = len(cycles)
        x = int(nxt[x])
    cycles.append(cyc)
log("cycles of the assignment: %d" % len(cycles))
# patching: merge the two cycles with the cheapest exchange of successors
while len(cycles) > 1:
    # for the smallest cycle, find the best partner arc
    ci = min(range(len(cycles)), key=lambda i: len(cycles[i]))
    A = np.array(cycles[ci])
    mask = lab != lab[A[0]]
    others = np.nonzero(mask)[0]
    # exchange a->nxt[a], b->nxt[b] into a->nxt[b], b->nxt[a]
    d = Cm[np.ix_(A, nxt[others])] + Cm[np.ix_(others, nxt[A])].T - Cm[A, nxt[A]][:, None] - Cm[others,
        nxt[others]][None, :]
    i, j = np.unravel_index(np.argmin(d), d.shape)
    a, b = int(A[i]), int(others[j])
    na, nb = int(nxt[a]), int(nxt[b])
    nxt[a], nxt[b] = nb, na
    cj = int(lab[b])
    merged = cycles[ci] + cycles[cj]
    for x in merged:
        lab[x] = min(ci, cj)
    keep = [cyc for k_, cyc in enumerate(cycles) if k_ not in (ci, cj)]
    newc = []
    x = a
    while True:
        newc.append(x)
        x = int(nxt[x])
        if x == a:
            break
    cycles = keep + [newc]
    for k_, cyc in enumerate(cycles):
        lab[np.array(cyc)] = k_
cyc = cycles[0]
costs = [int(Cm[cyc[i], cyc[(i + 1) % U]]) for i in range(U)]
k0 = int(np.argmax(costs))
order = cyc[k0 + 1:] + cyc[:k0 + 1]
tot = sum(int(Cm[order[i], order[i + 1]]) for i in range(U - 1))
log("after patching: one path, sum of W between runs %d" % tot)


def oropt(order, Cm, maxlen=3, rounds=20):
    """segment moves on an order of runs: a segment of 1 .. maxlen consecutive runs is taken out and put between
    two other consecutive runs where the sum of W drops most; repeated over all segments until a whole round changes
    nothing or `rounds` rounds have passed.  The first and the last run stay where they are."""
    order = list(order)
    n = len(order)
    for _ in range(rounds):
        improved = False
        for L in range(1, maxlen + 1):
            i = 1
            while i + L < n:
                a, s0, s1, b = order[i - 1], order[i], order[i + L - 1], order[i + L]
                rem = Cm[a, s0] + Cm[s1, b] - Cm[a, b]
                arr = np.array(order)
                # insert between arr[j], arr[j+1] for j outside [i-1, i+L-1]
                pj = np.arange(n - 1)
                valid = (pj < i - 1) | (pj >= i + L)
                gain = rem - (Cm[arr[pj], s0] + Cm[s1, arr[pj + 1]] - Cm[arr[pj], arr[pj + 1]])
                gain = np.where(valid, gain, -10 ** 9)
                j = int(np.argmax(gain))
                if gain[j] > 0:
                    seg = order[i:i + L]
                    del order[i:i + L]
                    if j > i:
                        j -= L
                    order[j + 1:j + 1] = seg
                    improved = True
                else:
                    i += 1
        if not improved:
            break
    return order


order = oropt(order, Cm)
tot = sum(int(Cm[order[i], order[i + 1]]) for i in range(U - 1))
hist = dict(zip(*[a.tolist() for a in np.unique([int(Cm[order[i], order[i + 1]]) for i in range(U - 1)],
    return_counts=True)]))
log("after segment moves: sum of W between runs %d; by W %s" % (tot, hist))
# blocks of the other trails from the pointer plan
lines = [l.split() for l in open(ptr_f).read().split("\n") if l.strip()]
hdr = lines[0]
evs = lines[1:]
assert all(e[0] == "O" for e in evs)
blocks = []
cur = []
for e in evs:
    t = int(e[1])
    if t >= NS:
        cur.append(e)
    elif cur:
        blocks.append(cur)
        cur = []
if cur:
    blocks.append(cur)
nb = len(blocks)
log("pointer plan: %d events of other trails in %d blocks (sizes: %s)" % (sum(len(b) for b in blocks), nb,
    dict(zip(*[a.tolist() for a in np.unique([len(b) for b in blocks], return_counts=True)]))))
ben = np.array([hw(int(b[0][1]), int(b[0][2])) for b in blocks])
bDen = np.array([3 - int(b[0][3]) for b in blocks])
bex = np.array([hw(int(b[-1][1]), int(b[-1][2]) - int(b[-1][3]) + 3) for b in blocks])
bDex = np.array([3 - int(b[-1][3]) for b in blocks])
# gaps: after run order[i] (i = 0 .. U-2); cost of block b in gap i
o = np.array(order)
Win = wmat(ex[last[o[:-1]]], D[last[o[:-1]]], ben, bDen)  # gaps x blocks
Wout = wmat(bex, bDex, en[first[o[1:]]], D[first[o[1:]]])  # blocks x gaps
direct = Cm[o[:-1], o[1:]]
cost = Win.T + Wout - direct[None, :]  # blocks x gaps
rb, cg = linear_sum_assignment(cost)
log("blocks into gaps: sum of the changes %d (W units), per block %s" % (int(cost[rb, cg].sum()),
    dict(zip(*[a.tolist() for a in np.unique(cost[rb, cg], return_counts=True)]))))
at = {int(g): int(b) for b, g in zip(rb, cg)}
pred = inside + tot + int(cost[rb, cg].sum())
with open(out_f, "w", newline="\n") as fo:
    fo.write("TRAILSEARCH-PLAN %s %s %d\n" % (hdr[1], hdr[2], len(evs)))
    for i, u in enumerate(order):
        for t in paths[u]:
            j = int(cut[t]) - t * 110
            fo.write("O %d %d %d 0\n" % (t, int(sstart[t, j]), int(sgap[t, j])))
        if i in at:
            for e in blocks[at[i]]:
                fo.write(" ".join(e) + "\n")
log("wrote %s" % out_f)
