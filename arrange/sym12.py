#!/usr/bin/env python
"""sym12.py - the relabellings of the old letters that keep the cuts of the small trails (n = 12).

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: sym12.py        needs cuts12c.bin (cuts12.c); writes sym12.pkl

The piece set.  These scripts were written for one piece set at n = 12, the first one that beat Pantone's pieces:
the 11-symbol selection with full and short rows only (Q = 178,080).  Its numbers are fixed in the code: 7,200
closed trails, of which the first 6,048 of the table are small trails with 110 cuts each (100 at steps of weight 2,
10 at vertices); then 144 trails of the three short walks of every block (63, 133 and 182 loops, one trail each;
kinds 1 to 3 of the table, "short-walk trails" below); then 1,008 big trails.  Letters: 0 .. 6 are the old letters,
7, 8, 9 the added letters, A the distinguished letter, B the completion letter.

A permutation of the old letters is a symmetry of the arrangement of the small trails when it maps the set of their
cut words (with D) onto itself: the cost of a join depends only on the words.  The permutations with this property
form a group, the stabiliser of that set.
  1. All 5,040 permutations of 0 .. 6 are tried on 300 small cuts drawn at random (fixed seed).
  2. The survivors are checked on all 665,280 small cuts.
  3. Those that pass are tried on 20,000 cuts of the short-walk trails drawn at random (they must map into the cuts
     of small and short-walk trails together).
  4. The six permutations of the added letters 7, 8, 9 are tried on the sample of step 1 and printed.
Steps 1 and 2 together are exhaustive.  Step 3 is a sample, not a proof, and nothing later depends on it.

On this piece set 168 permutations keep all small cuts, the same 168 keep the sample of step 3, and of the
permutations of the added letters only the identity keeps the sample of step 1.  q12.py then finds that every orbit
of small cuts has exactly 168 cuts: 3,960 orbits of cuts, 36 orbits of trails.

sym12.pkl: {"small": the permutations that keep all small cuts, each a list of 16 letters; "sw": those that also
keep the sample of step 3}.

Needs: Python 3, numpy, c12.py.
All files are read from and written to the working directory.
Time and memory, measured: 35 s, 0.55 GB.
"""
import sys, time, itertools, numpy as np, pickle
import c12

log = lambda *x: print(*x, flush=True)
C = c12.Cuts("cuts12c.bin", log=log)
ns = 6048 * 110
kt = C.kind[C.t]
# cut words of the small trails and of the short-walk trails
nsw = int((kt <= 3).sum())
assert (kt[:nsw] <= 3).all()
w = C.col("w", 0, nsw).astype(np.int64)
D = C.D[:nsw].astype(np.int64)
wk = np.sort(w * 2 + D)
wk_small = np.sort(w[:ns] * 2 + D[:ns])
rng = np.random.default_rng(3)


def relabel(w, D, perm):
    """the cut words w (9 letters, or 10 where D = 1) with every letter a replaced by perm[a]"""
    out = np.zeros(len(w), np.int64)
    P = np.array(perm, np.int64)
    for i in range(10):
        a = (w >> (4 * i)) & 15
        valid = (i < 9) | (D == 1)
        out |= np.where(valid, P[a], 0) << (4 * i)
    return out


def member(srt, k):
    """which of the keys k are in the sorted array srt"""
    p = np.searchsorted(srt, k)
    p = np.minimum(p, len(srt) - 1)
    return srt[p] == k


idx = rng.choice(ns, 300, replace=False)
ws, Ds = w[idx], D[idx]
good = []
t0 = time.time()
for p in itertools.permutations(range(7)):
    perm = list(p) + list(range(7, 16))
    if member(wk_small, relabel(ws, Ds, perm) * 2 + Ds).all():
        good.append(perm)
print("permutations of the letters 0..6 that keep a sample of 300 small cuts inside the small cuts:", len(good),
    "(%.0fs)" % (time.time() - t0))
# full check of the survivors on all small cuts and on the short-walk cuts
ok_small = [p for p in good if member(wk_small, relabel(w[:ns], D[:ns], p) * 2 + D[:ns]).all()]
print("  that keep ALL small cuts:", len(ok_small))
idx2 = ns + rng.choice(nsw - ns, 20000, replace=False)
ok_sw = [p for p in ok_small if member(wk, relabel(w[idx2], D[idx2], p) * 2 + D[idx2]).all()]
print("  that also keep a sample of 20000 short-walk cuts inside small + short-walk cuts:", len(ok_sw))
# also letter permutations involving the tokens 7,8,9 (with 0..6 fixed)?
for p in itertools.permutations([7, 8, 9]):
    perm = list(range(7)) + list(p) + list(range(10, 16))
    print("  tokens ->", p, bool(member(wk_small, relabel(ws, Ds, perm) * 2 + Ds).all()))
pickle.dump(dict(small=ok_small, sw=ok_sw), open("sym12.pkl", "wb"))
