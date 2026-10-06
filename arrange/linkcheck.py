#!/usr/bin/env python
"""linkcheck.py - which small trails can follow each other at cost 1?  A check of the rule that chainplan.py uses.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: linkcheck.py BASE.txt BASE.tsv

  BASE.txt  base word of gen12.py or geng.py (mapped)
  BASE.tsv  its table; the lines of kind D are the small trails (closed trails of loops without a row)

Claim checked: two small trails can be written one after the other at cost 1 exactly when their loops are
consecutive in an F-orbit, that is, when one loop is the other with two neighbouring letters exchanged.

How.  Every cut of every small trail is listed: the cuts at steps of weight 3 (cost D = 0) and those at steps of
weight 2 (D = 1), each with the h-letter word S the piece would start with and the word E it would end with.  The cost
of writing trail B after trail A is taken as D_B + (h - overlap of E_A with S_B), for any cut of A and any cut of B.
All pairs of different trails with cost 1 are collected (overlap h into a cut with D = 1, or overlap h - 1 into a cut
with D = 0) and compared, as sets, with the pairs of loops that differ by one exchange of neighbours.
The count is exhaustive over the cuts listed.  Cuts that drop a repeated permutation are not listed; on the n = 12
piece set of the run systems the small trails have none (the file of cuts12.c holds exactly 110 cuts for each of
them: 100 at steps of weight 2 and 10 at vertices).

Prints n, the numbers of small trails and of cuts, the two numbers of pairs and whether the sets are equal.

Needs: Python 3.  Time and memory, measured: n = 11 (672 small trails, 60,480 cuts) 2 s and 0.04 GB; n = 12 (2,352
small trails, 258,720 cuts) 5 s and 0.13 GB.
"""
import collections
import mmap
import sys

tab = [l.split("\t") for l in open(sys.argv[2])]
f = open(sys.argv[1], "rb")
W = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
mx = max(W[:4096])
n = (mx - 48 if mx < 65 else mx - 55) + 1
h, K = n - 3, n - 2
D = [t for t in range(len(tab)) if tab[t][0] == "D"]
ops = []                       # (trail, S, E, D)
loops = {}


def canon(x):
    """the cyclic word x read from its smallest letter"""
    i = x.index(min(x))
    return x[i:] + x[:i]


# ---- the cuts of every small trail: consecutive permutation windows p, q of the closed trail with a step of weight
# 2 or 3 between them; the piece cut there starts with the first h letters of window q and ends with the last h
# letters of window p.  The loop of the trail is its first vertex word with the letter that follows it.
for t in D:
    R, st = int(tab[t][2]), int(tab[t][3])
    c = W[st:st + R]
    d = c + c[:2 * n]
    pos = [p for p in range(R) if len(set(d[p:p + n])) == n]
    for i in range(len(pos)):
        p, q = pos[i], pos[(i + 1) % len(pos)]
        g = (q - p) % R
        if g >= 2:
            ops.append((t, d[q:q + h], d[p + 3:p + n], 3 - g))
    loops[canon(c[:h + 1])] = t
# ---- pairs at cost 1: i9 holds the cuts with D = 1 by their whole first word, i8 the cuts with D = 0 by the first
# h - 1 letters of it
i9 = collections.defaultdict(set)
i8 = collections.defaultdict(set)
for (t, S, E, Dc) in ops:
    if Dc == 1:
        i9[S].add(t)
    else:
        i8[S[:h - 1]].add(t)
pairs = set()
for (t, S, E, Dc) in ops:
    for u in i9.get(E, ()):
        if u != t:
            pairs.add((min(t, u), max(t, u)))
    for u in i8.get(E[1:], ()):
        if u != t:
            pairs.add((min(t, u), max(t, u)))
# ---- pairs of loops that differ by an exchange of two cyclically neighbouring letters
nb = set()
for x, t in loops.items():
    for i in range(K):
        y = bytearray(x)
        j = (i + 1) % K
        y[i], y[j] = y[j], y[i]
        u = loops.get(canon(bytes(y)))
        if u is not None:
            nb.add((min(t, u), max(t, u)))
print("n = %d: detached-style trails %d, openings %d" % (n, len(D), len(ops)))
print("pairs that can follow each other at cost 1 (all openings): %d; pairs of loops consecutive in an F-orbit: %d; the two sets are equal: %s" % (
    len(pairs), len(nb), pairs == nb))
