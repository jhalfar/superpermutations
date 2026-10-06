#!/usr/bin/env python
"""bound12.py - a lower bound for the words that can be made of the n = 12 pieces of the transported selection.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: bound12.py      (no input: the numbers it combines are in the source, with where they come from)

What is bounded.  Words that write every one of the 7,200 closed trails once, from one cut (at a vertex, at a step
of weight 2, or dropping a repeated permutation), with consecutive pieces overlapping in at most h = 9 letters.
Words that write a trail in several segments, or with larger overlaps, are outside.  It is a bound for this piece
set only and says nothing about other piece sets or about superpermutations in general.

Units: the lines below are in quarter letters, "4 cost", where cost = cuts + joins and length = 9 + sum R + cost
with sum R = 522,725,280.

Ingredients.
  (a) RP[lam], from q12.py: a lower bound of the sum, over the runs of level lam, of 2 lam + 2 (W-sum of the joins
      inside), for lam = 4, 6, 7, .., 12.  Linear programmes in floating point, values integral, not certified.
  (b) B_k >= L(k) for a block of k cuts of big trails between two cuts of small or short-walk trails, B_k being
      twice the W-sum of its k + 1 joins.  L(k) = the exact value of hop12 for k <= 18, and at least
      3.5 (k - 1) + 8 for every k (hop12 --pot 7 2: a potential on the big cuts that leaves 3.5 for every join
      between big trails).  Exact integer computations over all 37.6 million big cuts; consecutive cuts lie in
      different trails, but a trail may come back later in a block, which only lowers the value.
  (c) A short-walk trail that stands alone between two small trails: twice its W-sum is at least 8 (attach12.py).
The argument.  Fix a level E.  A word has R runs of level E (maximal sequences of small trails joined by W < E).
What stands between two consecutive runs is a connection: a join with W >= E, or other trails with their joins.
    4 cost  =  sum over runs [2 E + 2 (W-sum inside)]  +  sum over connections (2 w - 2 E)  +  end terms,
w being the W-sum of the connection.  Then
    4 cost >= max over lam <= E of [RP[lam] + 2 (E - lam) R]                              (the runs)
            + s (8 - 2 E)                         (s <= 144 connections that are one short-walk trail)
            + min over m sub-blocks of big trails in c connections of [sum of L(k_j) - 2 E c]
                                                  (c <= R - 1 - s; m - c <= 144 - s: two sub-blocks of one
                                                   connection are separated by a short-walk trail)
            - 2 E                                 (the two ends of the word)
and the right side is minimised over R, s, m and c.  The best E gives the bound.

Result (one line is printed per level E = 6 .. 12): 4 cost >= 46,162 at every level from 7 on, so cost >= 11,541
and length >= 522,736,830.  The minimum is taken at 649 runs, 144 short-walk trails alone and 504 connections of two
big trails each.  At level 6, where the value of the runs is also the exact integer optimum (runs12.py), the line
reads 4 cost >= 45,780 and length >= 522,736,734.

Status.  The block values and the composition are exact integer computations; (a) rests on linear programmes
solved in floating point.  One implementation, no referee.  Where it is loose: the linear programme of the runs
(symmetric systems reach 49,728 / 53,760 / 55,776 at E = 8 / 10 / 12 against 47,040 / 49,056 / 49,728 here), and
pairs of big trails that count as nearly free connections because their ends may attach to short-walk cuts.

Needs: Python 3.  Time: about 50 s in plain Python.
"""
import math

# RP: "sum over runs >=" printed by  q12.py 4 6 7 8 9 10 11 12
RP = {4: 34272.0, 6: 44352.0, 7: 46032.0, 8: 47040.0, 9: 48048.0, 10: 49056.0, 11: 49392.0, 12: 49728.0}
# Bex[k]: column B_k printed by  hop12 cuts12c.bin 2678592 hop_src.i16 hop_snk.i16 hop_d.i16 hop_d.i16 19 5
Bex = [None, 16, 16, 20, 24, 28, 32, 36, 40, 44, 44, 50, 54, 60, 64, 66, 70, 74, 76]
# big trails, short-walk trails, small trails
NBIG, NSH, NSM = 1008, 144, 6048
# L(k): the exact value where there is one, and the line 3.5 (k - 1) + 8 of the potential
L = [None] + [max(Bex[k] if k < len(Bex) else 0, math.ceil(3.5 * (k - 1) + 8)) for k in range(1, NBIG + 1)]
INF = 10 ** 9
# Lmin[m] = cheapest sum of L over compositions of the big trails into exactly m sub-blocks
prev = [0] + [INF] * NBIG
Lmin = [INF] * (NBIG + 1)
for m in range(1, NBIG + 1):
    cur = [INF] * (NBIG + 1)
    for j in range(m, NBIG + 1):
        best = INF
        for k in range(1, min(j - (m - 1), 40) + 1):  # parts above 40 never pay against the line 3.5 k + 4.5
            v = prev[j - k] + L[k]
            if v < best:
                best = v
        # one long part
        k = j - (m - 1)
        if k > 40 and prev[j - k] < INF:
            best = min(best, prev[j - k] + L[k])
        cur[j] = best
    Lmin[m] = cur[NBIG]
    prev = cur
print("cheapest sum of L for m sub-blocks: m=1: %d, 112: %d, 252: %d, 504: %d, 1008: %d" % (Lmin[1], Lmin[112],
    Lmin[252], Lmin[504], Lmin[1008]))
# h + sum R of the piece set
base_const = 522725280 + 9
out = []
# for every level E: the smallest right side over R runs, s single short-walk trails, m sub-blocks in c connections
for E in (6, 7, 8, 9, 10, 11, 12):
    best = None
    for R in range(1, NSM + 1):
        g = max(RP[lam] + 2 * (E - lam) * R for lam in RP if lam <= E)
        for s in (0, min(NSH, R - 1)) if R > 1 else (0,):
            cmax = R - 1 - s
            tb = INF
            for m in range(1, NBIG + 1):
                c = min(m, cmax)
                if m - c > NSH - s:
                    continue
                if c == 0 and R > 1 and False:
                    continue
                v = Lmin[m] - 2 * E * c
                if v < tb:
                    tb, margs = v, (m, c)
            if tb >= INF:
                continue
            tot = g + s * (8 - 2 * E) + tb - 2 * E
            if best is None or tot < best[0]:
                best = (tot, R, s) + margs
    tot, R, s, m, c = best
    two = math.ceil(tot / 2 - 1e-9)
    cost = (two + 1) // 2
    print("E = %2d: 4 cost >= %.0f at R = %d runs, %d short-walk singles, %d big sub-blocks in %d connections  ->  cost >= %d, length >= %d" % (
        E, tot, R, s, m, c, cost, base_const + cost))
