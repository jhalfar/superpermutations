#!/usr/bin/env python
"""check11.py - the accounting of cert11.py checked on a real single-port word of n = 11.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: check11.py BASE.txt SEQ.pkl

  BASE.txt  Pantone's n = 11 word
  SEQ.pkl   a word that writes every trail once, read by anatomy.py ('ent' = the cut of every trail in the order of
            the word)

The word is split into runs (joins with W < LOW), connections of type I and E, and blocks of big trails; the identity
    4 cost = sum over runs val + sum over connections (2 w - lb_out - lb_in) + end terms
is evaluated on both sides and the terms are printed, to be compared with V, Cx and Y_k of cert11.py.  The line ends
with IDENTITY OK when the two sides agree.  Every connection term is asserted to be non-negative.

Needs: Python 3, numpy, top.py, countn.py, tm.py.  Time and memory: 45 s, 2.86 GB.
"""
import sys, pickle
import numpy as np
import top


def main():
    base, seqf = sys.argv[1:3]
    T = top.Top(base, cmax=4, log=lambda *x: None)
    F = T.F
    sc = F.sc
    NC = len(sc)
    loc = np.full(F.V, -1, np.int64); loc[sc] = np.arange(NC)
    tr = F.ct[sc]
    lev_top = max(v for v in F.Lt if F.Lt[v] < F.NS)
    cls = F.tlab[lev_top]
    csize = int(np.bincount(cls[F.small_t]).max())
    LOW = max(v for v in F.Lc if F.Lc[v] < csize)
    dm = ~F.same
    A, Bn, Wv = loc[F.pa[dm]], loc[F.pb[dm]], F.pw[dm]
    low = Wv < LOW
    same_cls = cls[tr[A]] == cls[tr[Bn]]
    CAP = F.wcap; beta = F.beta
    lbI_in = np.full(NC, CAP, np.int64); lbI_out = np.full(NC, CAP, np.int64)
    mI = same_cls & ~low
    np.minimum.at(lbI_in, Bn[mI], Wv[mI]); np.minimum.at(lbI_out, A[mI], Wv[mI])
    E_in = np.full(NC, min(CAP, beta), np.int64); E_out = np.full(NC, min(CAP, beta), np.int64)
    mE = ~same_cls
    np.minimum.at(E_in, Bn[mE], np.minimum(Wv[mE], beta)); np.minimum.at(E_out, A[mE], np.minimum(Wv[mE], beta))
    cuts = [int(c) for c in pickle.load(open(seqf, "rb"))["ent"]]
    N = len(cuts)
    D = T.D
    W = [T.W(a, b) for a, b in zip(cuts[:-1], cuts[1:])]
    cost2 = int(D[cuts[0]] + sum(W) + D[cuts[-1]])
    small = T.is_small[np.array(cuts)]
    kl = cls[F.ct[np.array(cuts)]]
    # runs
    runs = []
    i = 0
    while i < N:
        if not small[i]:
            i += 1; continue
        j = i
        while j + 1 < N and small[j + 1] and W[j] < LOW:
            j += 1
        runs.append((i, j)); i = j + 1
    tot_val = 0; conn = 0
    hist = {}
    eends = {}
    types_in = []
    for r, (i, j) in enumerate(runs):
        # type of the connection before / after
        def typ(a, b):
            """type of the connection between positions a (last of a run) and b (first of the next run)"""
            if b == a + 1 and kl[a] == kl[b]:
                return "I"
            return "E"
        tin = "E" if r == 0 else typ(runs[r - 1][1], i)
        tout = "E" if r == len(runs) - 1 else typ(j, runs[r + 1][0])
        x, y = loc[cuts[j]], loc[cuts[i]]
        lin = E_in[y] if tin == "E" else lbI_in[y]
        lout = E_out[x] if tout == "E" else lbI_out[x]
        tot_val += int(lin + 2 * sum(W[i:j]) + lout)
        c = int(kl[i]); eends[c] = eends.get(c, 0) + (tin == "E") + (tout == "E")
        if r + 1 < len(runs):
            i2 = runs[r + 1][0]
            w = sum(W[j:i2])
            y2 = loc[cuts[i2]]
            lin2 = E_in[y2] if tout == "E" else lbI_in[y2]
            t = 2 * w - int(lout) - int(lin2)
            kind = "I join" if tout == "I" else ("E join" if i2 == j + 1 else "block of %d" % (i2 - j - 1))
            hist[(kind, t)] = hist.get((kind, t), 0) + 1
            conn += t
            assert t >= 0
    st = 2 * int(D[cuts[0]]) - int(E_in[loc[cuts[runs[0][0]]]]) if runs[0][0] == 0 else None
    en = 2 * int(D[cuts[-1]]) - int(E_out[loc[cuts[runs[-1][1]]]]) if runs[-1][1] == N - 1 else None
    print("runs %d (trails per run: %s); sum of val %d; E ends per class: %s" % (
        len(runs), dict(zip(*[a.tolist() for a in np.unique([j - i + 1 for i, j in runs], return_counts=True)])),
        tot_val,
        dict(zip(*[a.tolist() for a in np.unique(list(eends.values()), return_counts=True)]))))
    print("connections (kind, 2 w - lb_out - lb_in): count  %s" % dict(sorted(hist.items())))
    print("4 cost of the word %d; sum of val %d + connections %d + start %s + end %s = %s   %s" % (
        2 * cost2, tot_val, conn, st, en, tot_val + conn + (st or 0) + (en or 0),
        "IDENTITY OK" if st is not None and en is not None and 2 * cost2 == tot_val + conn + st + en else "CHECK"))


if __name__ == "__main__":
    main()
