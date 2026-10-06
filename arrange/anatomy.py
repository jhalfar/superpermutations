#!/usr/bin/env python
"""anatomy.py - a word read as a sequence of cuts on the trails of a base word, with its top-level structure.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: anatomy.py BASE.txt WORD.txt OUTPREFIX

  BASE.txt   a base word of Pantone's form (n = 10 or 11)
  WORD.txt   a word made of the same closed trails
  writes OUTPREFIX_seq.pkl: the events of the word in order, with the cut at which each enters (ent) and leaves
         (ext) its trail, the W of every join (Wn), the object of every event (o) and the top-level items (seq):
         runs of small trails of one group or class ("C") and blocks of big trails ("B");
         and OUTPREFIX_bb3.npz: the joins with W <= 3 between cuts of different big trails

Prints the items in order as  C<group>[W-sum inside]>W of the join after  or  B<big trails>[..]>.. ; for every block
its joins; and for the joins with W <= 2 among the big cuts ("threads") their number, the degrees and the longest
path that never meets a big trail twice.

Used here by rumstd_order.py (the order of the groups in rumstd's word) and by check10m.py and check11.py.

Needs: Python 3, numpy, top.py, tm.py, countn.py.  Time and memory, measured: 6 s and 0.39 GB at n = 10, 90 s and 3.75 GB at
n = 11.
"""
import sys, time, pickle
import numpy as np
import top, tm

log = lambda *x: print(*x, flush=True)
H = lambda a: {int(k): int(v) for k, v in zip(*np.unique(a, return_counts=True))}
base, word, outp = sys.argv[1], sys.argv[2], sys.argv[3]
T = top.Top(base, cmax=4, log=log)
F = T.F
B = F.B
P = tm.Plan(B, word, log=log)
vid_keys = F.E.astype(np.int64) * (B.M + 1) + F.S
order = np.argsort(vid_keys)
sk = vid_keys[order]


def cut_id(E, S):
    """the number of the cut that leaves its trail after window E and enters at window S"""
    k = int(E) * (B.M + 1) + int(S)
    i = int(np.searchsorted(sk, k))
    assert sk[i] == k
    return int(order[i])


byE, byS = {}, {}
for (E, S, k) in P.cuts:
    c = cut_id(E, S)
    byE[int(E)] = c
    byS[int(S)] = c
ev = P.events
ent = np.array([byS[a] for a, _ in ev])
ext = np.array([byE[b] for _, b in ev])
Wn = np.array([2 * (F.h - P.ovs[i]) + int(F.D[ext[i]] + F.D[ent[i + 1]]) for i in range(len(ev) - 1)] + [0])
o = T.obj[ent]
small = T.is_small[ent]
log("events %d; sum W %d" % (len(ev), int(Wn.sum())))
# top-level sequence: runs of the same class / blocks of big trails
seq = []
i = 0
N = len(ev)
while i < N:
    j = i
    if small[i]:
        while j + 1 < N and small[j + 1] and o[j + 1] == o[i]:
            j += 1
        seq.append(("C", int(o[i]), i, j, int(Wn[i:j].sum()), int(Wn[j])))
    else:
        while j + 1 < N and not small[j + 1]:
            j += 1
        seq.append(("B", j - i + 1, i, j, int(Wn[i:j].sum()), int(Wn[j])))
    i = j + 1
log("top-level items: %d (class runs %d, blocks %d)" % (len(seq), sum(1 for s in seq if s[0] == "C"),
    sum(1 for s in seq if s[0] == "B")))
log("class runs: trails per run %s; internal W-sum %s" % (H(np.array([s[3] - s[2] + 1 for s in seq if s[0] == "C"])),
    H(np.array([s[4] for s in seq if s[0] == "C"]))))
line = []
for s in seq:
    line.append("%s%d[%d]>%d" % (s[0], s[1], s[4], s[5]))
log(" ".join(line))
for s in seq:
    if s[0] == "B":
        i, j = s[2], s[3]
        log("block of %d big trails: join before %d, inside %s (sum %d), after %d; trails %s" % (
            s[1], int(Wn[i - 1]) if i > 0 else -1, H(Wn[i:j]), int(Wn[i:j].sum()), int(Wn[j]),
            (o[i:j + 1] - T.NG).tolist()))
        log("    inside joins in order: %s" % "".join(str(int(x)) for x in Wn[i:j]))
# threads of joins W <= 2 among the big cuts
bg = np.nonzero(~T.is_small)[0]
t0 = time.time()
pa, pb, pw = T.pairs(bg, bg, 3)
log("big-big joins with W <= 3 between different trails: %d %s (%.0fs)" % (len(pa), H(pw), time.time() - t0))
m = pw <= 2
outd = np.bincount(pa[m], minlength=T.V)
ind = np.bincount(pb[m], minlength=T.V)
log("W <= 2: arcs %d; out-degree %s in-degree %s" % (int(m.sum()), H(outd[bg]), H(ind[bg])))
nxt = np.full(T.V, -1, np.int64)
nxt[pa[m]] = pb[m]  # one of the successors when there are several
NB = T.NO - T.NG
tr = T.obj - T.NG
cur = bg.copy()
alive = np.ones(len(bg), bool)
nw = (NB + 63) // 64
mask = np.zeros((len(bg), nw), np.uint64)
mask[np.arange(len(bg)), tr[bg] // 64] |= np.uint64(1) << (tr[bg] % 64).astype(np.uint64)
length = np.ones(len(bg), np.int64)
for step in range(NB + 2):
    n2 = np.where(alive, nxt[cur], -1)
    ok = n2 >= 0
    t2 = np.where(ok, tr[np.maximum(n2, 0)], 0)
    bit = np.uint64(1) << (t2 % 64).astype(np.uint64)
    used = (mask[np.arange(len(bg)), t2 // 64] & bit) != 0
    ok &= ~used
    mask[np.arange(len(bg))[ok], (t2 // 64)[ok]] |= bit[ok]
    length[ok] += 1
    cur = np.where(ok, n2, cur)
    alive = ok
    if not ok.any():
        break
log("longest rainbow path along the W <= 2 threads from every big cut: %s" % H(length))
np.savez(outp + "_bb3.npz", pa=pa, pb=pb, pw=pw)
pickle.dump(dict(seq=seq, ent=ent, ext=ext, Wn=Wn, o=o, small=small), open(outp + "_seq.pkl", "wb"))
