#!/usr/bin/env python
"""cert10.py - a lower bound for words made of a piece set at n = 10, in exact integers.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: cert10.py BASE.txt GT.npz [--a A] [--cap C] [--multi]
       [--ain a --min m --aout b --mout p]     (other end prices, see below)

  BASE.txt  the base word of the piece set (Pantone's n = 10 word, or the base word of another selection with the
            same 48 groups of 7 small trails)
  GT.npz    the traversal tables of gt.py for that base word
  --multi   also the bound for the family in which small trails may be written in several segments

Families of words.  "Single-port": every closed trail is written once, from one cut.  "Multi-port": a trail may
be written in several segments.  "Narrow": consecutive pieces overlap in at most h = n - 3 letters.  A bound proved
for a family says nothing about words outside it, and nothing about other piece sets.
Here: single-port narrow (cuts at steps of weight 2 or 3 and cuts that drop a repeated permutation; h = 7), and with
--multi the family "small trails multi-port, big trails single-port, narrow", which is the family of rumstd's word.

UNITS: doubled half letters.  W(x,y) = 2 c(x,y) + D_x + D_y;  2 cost = D(first) + sum of W + D(last).
WORD = runs of small trails (a RUN: consecutive trails of one group), separated by CONNECTIONS: a join between two
runs of different groups, or a BLOCK of k >= 1 big trails with its k + 1 joins; a block may also stand at the start
or at the end of the word (k joins and the D of the end cut).
PRICES on the small cuts:  e_in(y) = 8 - A * min(hy(y), C),  e_out(x) = 8 - A * min(hx(x), C),  where hx(x) (hy(y))
is the excess over 12 of the cheapest single-run traversal of the group that leaves at x (enters at y), capped at 8
(tables of gt.py: joins with W < 10; a traversal with another join has W-sum >= 20).
With --ain .. the prices are e_in = 8 - min(a hy, m), e_out = 8 - min(b hx, p).
The bound is valid for ANY prices; they only decide how good it is.
CHECKED HERE, exhaustively:
 (1) for every group the exact programme (grp.py, any number of runs) gives
         G = min over configurations of sum over runs [ e_in(first) + 2 (joins inside) + e_out(last) ]
     (--multi: the programme with units instead, see multi_group)
 (2) every join between small cuts of two different groups has 2 W(x,y) >= e_out(x) + e_in(y)
 (3) Y_k = min over blocks of k big cuts c_1..c_k (consecutive ones in different trails) between small cuts x, y of
         2 (W(x,c_1) + ... + W(c_k,y)) - e_out(x) - e_in(y)
     and the same at the start of the word (Ys_k: 2 D(c_1) + 2 (joins) - e_in(y)) and at its end (Ye_k)
     (min-plus over the join tables, k = 1 .. number of big trails; a block may visit a big trail twice, which is a
     relaxation: the single cut of every big trail is kept, the rule "every big trail once" is not).
THEN   4 cost = sum over runs [ e_in + 2 inside + e_out ] + sum over connections (2 w - e_out - e_in) + (ends)
            >= sum of G + min over the ways to split the big trails into blocks of
                           [ start term + end term + sum of Y_k over the inner blocks ].

Results (the last line printed is the bound):
  Pantone's pieces    --a 2 --cap 2            single-port narrow                   length >= 4,034,860
  Pantone's pieces    --a 1 --cap 2 --multi    small multi-port, big single-port    length >= 4,034,849
  the n = 10 pieces of the record    --a 2 --cap 2            single-port narrow    length >= 4,034,848
  the n = 10 pieces of the record    --a 1 --cap 2 --multi    the family of the record    length >= 4,034,842
Status: exhaustive integer computation.  Cross-checks: the min-plus steps against the direct formula (t_minplus.py,
0 differences in 2,250 comparisons); the identity and its terms on a real word (check10m.py on rumstd's word).  The
parser and the programme with units (--multi) are taken over from an earlier program of this project, so they are
not an independent check.  There is one implementation of the block programme.  Not refereed.

Needs: Python 3, numpy, top.py, grp.py, countn.py, tm.py.  No solver.
Time and memory, measured: 30 s and 0.40 GB without --multi, 170 s and 0.44 GB with it (one thread).
On the pieces of the record: 17 s and 150 s.
"""
import sys
import time
import numpy as np
import top
import grp

BIG = 10 ** 9


def multi_group(G, ei, eo, JUMP=4):
    """the group programme for small trails written in several segments, with given end prices; weights of the
    joins inside doubled.  A UNIT is a maximal group of consecutive segments of one trail.  A trail is one unit
    (entry = exit, or entry != exit: then it has >= 3 segments and two joins of W >= 1 between them, + JUMP) or
    several units (each enters at its best cut and leaves anywhere).  States per trail: 0 not seen, 1 done as one
    unit, 2 one unit of several so far, 3 several units.  Returns the smallest sum over runs
    [ e_in + 2 inside + e_out ]."""
    k, m = G.k, G.m
    arcs_to = [(a, b, 2 * w) for (a, b, w, st, ub) in G.arcs]
    cuts_of = G.cuts_of
    pw4 = [4 ** t for t in range(k)]
    g = {}

    def put(M, vec):
        """lower the values of state M to vec where vec is smaller; True if anything changed"""
        old = g.get(M)
        if old is None:
            g[M] = vec.copy()
            return True
        new = np.minimum(old, vec)
        ch = bool((new < old).any())
        g[M] = new
        return ch

    def entry(cur, t):
        """cheapest arrival at every cut of trail t after units whose last exit costs are cur: over a listed join,
        or by ending the run and starting a new one"""
        ent = np.full(m, BIG, np.int64)
        a_, b_, w_ = arcs_to[t]
        if len(a_):
            np.minimum.at(ent, b_, cur[a_] + w_)
        base_ = int((cur + eo).min())
        ct_ = cuts_of[t]
        ent[ct_] = np.minimum(ent[ct_], base_ + ei[ct_])
        return ent

    for t in range(k):
        ct_ = cuts_of[t]
        v1 = np.full(m, BIG, np.int64); v1[ct_] = np.minimum(ei[ct_], int(ei[ct_].min()) + JUMP)
        put(pw4[t], v1)
        v2 = np.full(m, BIG, np.int64); v2[ct_] = int(ei[ct_].min())
        put(2 * pw4[t], v2)
    bysum = {}
    for M in range(4 ** k):
        bysum.setdefault(sum((M // pw4[t]) % 4 for t in range(k)), []).append(M)
    best = BIG
    for sm_ in sorted(bysum):
        for M in bysum[sm_]:
            if M not in g:
                continue
            dig = [(M // pw4[t]) % 4 for t in range(k)]
            for _ in range(50):
                cur = g[M]
                changed = False
                for t in range(k):
                    if dig[t] == 3:
                        ent = entry(cur, t)
                        v = np.full(m, BIG, np.int64); v[cuts_of[t]] = int(ent[cuts_of[t]].min())
                        changed |= put(M, v)
                if not changed:
                    break
            cur = g[M]
            for t in range(k):
                if dig[t] == 0:
                    ent = entry(cur, t)
                    ct_ = cuts_of[t]
                    mn = int(ent[ct_].min())
                    v1 = np.full(m, BIG, np.int64); v1[ct_] = np.minimum(ent[ct_], mn + JUMP)
                    put(M + pw4[t], v1)
                    v2 = np.full(m, BIG, np.int64); v2[ct_] = mn
                    put(M + 2 * pw4[t], v2)
                elif dig[t] == 2:
                    ent = entry(cur, t)
                    v = np.full(m, BIG, np.int64); v[cuts_of[t]] = int(ent[cuts_of[t]].min())
                    put(M + pw4[t], v)
            if all(d in (1, 3) for d in dig):
                best = min(best, int((cur + eo).min()))
    return best


def main():
    log = lambda *x: print(*x, flush=True)
    base, gtf = sys.argv[1], sys.argv[2]
    opt = lambda k, d: type(d)(sys.argv[sys.argv.index(k) + 1]) if k in sys.argv else d
    A = opt("--a", 1); C = opt("--cap", 2)
    T = top.Top(base, cmax=4, log=lambda *x: None)
    F = T.F
    t0 = time.time()
    Tt = np.load(gtf)["T"].astype(np.int64)
    sm = np.nonzero(T.is_small)[0]; bg = np.nonzero(~T.is_small)[0]
    NBT = T.NO - T.NG
    hx = np.zeros(T.V, np.int64); hy = np.zeros(T.V, np.int64)
    groups = [grp.Group(T, g) for g in range(T.NG)]
    for g, G in enumerate(groups):
        hx[G.cuts] = np.minimum(Tt[g].min(0) - 12, 8); hy[G.cuts] = np.minimum(Tt[g].min(1) - 12, 8)
    assert hx[sm].min() >= 0 and hy[sm].min() >= 0
    ein = np.zeros(T.V, np.int64); eout = np.zeros(T.V, np.int64)
    ein[sm] = 8 - A * np.minimum(hy[sm], C); eout[sm] = 8 - A * np.minimum(hx[sm], C)
    if "--ain" in sys.argv:          # asymmetric prices: e_in = 8 - min(ain * hy, min_), e_out = 8 - min(aout * hx, mout)
        ein[sm] = 8 - np.minimum(opt("--ain", 0) * hy[sm], opt("--min", 0)); eout[sm] = 8 - np.minimum(opt("--aout",
            0) * hx[sm], opt("--mout", 0))
    H = lambda a: {int(k): int(v) for k, v in zip(*np.unique(a, return_counts=True))}
    label = "A = %d, cap = %d" % (A, C)
    if "--ain" in sys.argv:
        label = "e_in = 8 - min(%d hy, %d), e_out = 8 - min(%d hx, %d)" % (opt("--ain", 0), opt("--min", 0),
            opt("--aout", 0), opt("--mout", 0))
    log("prices (%s): e_in %s  e_out %s" % (label, H(ein[sm]), H(eout[sm])))
    assert 2 * F.wcap >= int(ein[sm].max() + eout[sm].max()), "a join that is not listed could beat a new run"
    # (1) groups
    Gs = []
    for g, G in enumerate(groups):
        arcs = G.arcs
        G.arcs = [(a, b, 2 * w, st, ub) for (a, b, w, st, ub) in arcs]
        v, _ = G.solve(ein[G.cuts], eout[G.cuts], trace=False)
        G.arcs = arcs
        Gs.append(int(v))
    log("(1) group programme: G values %s, sum %d  (%.0fs)" % (H(np.array(Gs)), sum(Gs), time.time() - t0))
    Gm = None
    if "--multi" in sys.argv:
        assert F.w3 >= 1 and F.a >= 2 and 2 * 8 >= int(ein[sm].max() + eout[sm].max())
        Gm = []
        for g, G in enumerate(groups):
            Gm.append(multi_group(G, ein[G.cuts], eout[G.cuts]))
            if g < 2 or (g + 1) % 12 == 0:
                log("    group %d: programme with units %d  (%.0fs)" % (g, Gm[-1], time.time() - t0))
        log("(1m) group programme with small trails in several segments: G values %s, sum %d" % (H(np.array(Gm)),
            sum(Gm)))
    # (2) direct joins between groups
    m = T.out_best(-ein[sm], X=sm, Y=sm, scale=2)                 # min over y in another group of 2 W(x,y) - e_in(y)
    slack = m - eout[sm]
    log("(2) joins between small cuts of different groups: smallest 2 W - e_out - e_in = %d  %s" % (int(slack.min()),
        "OK" if slack.min() >= 0 else "VIOLATED"))
    if slack.min() < 0:
        return None
    # (3) blocks
    lab_sb = T.is_small.astype(np.int64)                         # small against big: never the same label
    o_end = T.out_best(-ein[sm], X=bg, Y=sm, lab=lab_sb, scale=2)   # min over small y of 2 W(d,y) - e_in(y)
    v = T.in_best(-eout[sm], X=sm, Y=bg, lab=lab_sb, scale=2)       # min over small x of 2 W(x,c) - e_out(x)
    vs = 2 * T.D[bg].astype(np.int64)
    Y, Ys, Ye = [None], [None], [None]
    for k in range(1, NBT + 1):
        Y.append(int((v + o_end).min())); Ys.append(int((vs + o_end).min())); Ye.append(int((v + 2 * T.D[bg]).min()))
        if k < NBT:
            v = T.in_best(v, X=bg, Y=bg, scale=2)
            vs = T.in_best(vs, X=bg, Y=bg, scale=2)
    S0 = int((2 * T.D[sm] - ein[sm]).min()); E0 = int((2 * T.D[sm] - eout[sm]).min())
    log("(3) blocks of k big cuts between small cuts, Y_k: %s" % Y[1:])
    log("    at the start of the word, Ys_k: %s ; no block: %d" % (Ys[1:], S0))
    log("    at the end of the word,   Ye_k: %s ; no block: %d" % (Ye[1:], E0))
    # a word that consists of big trails only does not exist (there are small trails); composition programme
    INF = 10 ** 9
    inner = [0] + [INF] * NBT                                   # inner[j] = cheapest way to put j big trails into inner blocks
    for j in range(1, NBT + 1):
        inner[j] = min(inner[j - k] + Y[k] for k in range(1, j + 1))
    best = INF
    arg = None
    for ks in range(0, NBT + 1):
        for ke in range(0, NBT + 1 - ks):
            val = (S0 if ks == 0 else Ys[ks]) + (E0 if ke == 0 else Ye[ke]) + inner[NBT - ks - ke]
            if val < best:
                best, arg = val, (ks, ke)
    tot4 = sum(Gs) + best
    two = -(-tot4 // 2)
    cost = (two + 1) // 2
    log("composition: cheapest split has %d big trails in a start block, %d in an end block; term %d (inner blocks alone: %d)" % (
        arg[0], arg[1], best, inner[NBT]))
    log("BOUND single-port narrow, %s: 4 cost >= %d + %d = %d  ->  2 cost >= %d, cost >= %d, length >= %d   (%.0fs)" % (
        label, sum(Gs), best, tot4, two, cost, F.B.base_const + cost, time.time() - t0))
    if Gm is not None:
        tot4m = sum(Gm) + best
        two = -(-tot4m // 2); cost = (two + 1) // 2
        log("BOUND small trails multi-port, big trails single-port, narrow, %s: 4 cost >= %d + %d = %d  ->  2 cost >= %d, cost >= %d, length >= %d" % (
            label, sum(Gm), best, tot4m, two, cost, F.B.base_const + cost))
    return tot4


if __name__ == "__main__":
    main()
