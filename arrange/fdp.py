#!/usr/bin/env python
"""fdp.py - the fixed-order pass at the level of whole trails, exact.  A module.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

For a given order of the trails, every trail written once from one cut, the best cut of every trail is found by
dynamic programming over the cuts with the exact W(x, y) = 2 (h - overlap) + D_x + D_y, overlap at most h = n - 3.
    2 cost = D(first) + sum of W + D(last),   length = h + sum R + cost.

  Dp.step    g(y) = min over x of f(x) + W(x, y) for two sets of cuts
  Dp.wcol    W(x, y) for all x of a set and one cut y
  Dp.seq_dp  the pass: (2 cost, the cut of every trail) for an order of trails
  Dp.value   2 cost of a given list of cuts, with the W of every join
  Dp.spell   the word of a list of cuts

Needs: Python 3, numpy, top.py.
"""
import sys
import time
import numpy as np

BIG = 10 ** 9


class Dp:
    """cut_list[t] = the cuts of trail t that may be used: all of them, or with plain_only only those that drop no
    repeated permutation"""

    def __init__(self, T, plain_only=True):
        self.T = T
        F = T.F
        self.F = F
        ok = (F.SK < 0) if plain_only else np.ones(T.V, bool)
        order = np.argsort(F.ct, kind="stable")
        order = order[ok[order]]
        tt = F.ct[order]
        self.cuts_of = {}
        st = np.searchsorted(tt, np.arange(F.NT), "left"); en = np.searchsorted(tt, np.arange(F.NT), "right")
        self.cut_list = [order[st[t]:en[t]] for t in range(F.NT)]
        self.h, self.K = T.h, T.K

    def step(self, f, X, Y):
        """g(y) = min over x of f(x) + W(x,y)"""
        F, h, K = self.F, self.h, self.K
        D = self.T.D
        fx = f + D[X]
        if len(X) * len(Y) <= 400000:
            g = np.full(len(Y), fx.min() + 2 * h, np.int64)
            for k in range(1, K + 1):
                eq = F.suf[k][X][:, None] == F.pre[k][Y][None, :]
                if eq.any():
                    v = np.where(eq, fx[:, None], BIG).min(0) + 2 * (h - k)
                    g = np.minimum(g, v)
            return g + D[Y]
        g = np.full(len(Y), fx.min() + 2 * h, np.int64)
        for k in range(1, K + 1):
            a = F.suf[k][X]; b = F.pre[k][Y]
            u, inv = np.unique(np.concatenate([a, b]), return_inverse=True)
            tab = np.full(len(u), BIG, np.int64)
            np.minimum.at(tab, inv[:len(a)], fx)
            g = np.minimum(g, tab[inv[len(a):]] + 2 * (h - k))
        return g + D[Y]

    def wcol(self, X, y):
        """W(x, y) for all x in X and one cut y"""
        F, h, K = self.F, self.h, self.K
        D = self.T.D
        w = np.full(len(X), 2 * h, np.int64)
        for k in range(1, K + 1):
            eq = F.suf[k][X] == F.pre[k][y]
            w = np.where(eq, np.minimum(w, 2 * (h - k)), w)
        return w + D[X] + D[y]

    def seq_dp(self, order, f0=None, gend=None, log=None):
        """order: list of trail ids.  Returns (value, cuts).  f0: start costs on the cuts of the first trail
        (default D), gend: end costs on the cuts of the last trail (default D)."""
        D = self.T.D
        cl = self.cut_list
        fs = []
        X = cl[order[0]]
        f = D[X].astype(np.int64) if f0 is None else f0
        fs.append(f)
        t0 = time.time()
        for i in range(1, len(order)):
            Y = cl[order[i]]
            f = self.step(f, X, Y)
            fs.append(f)
            X = Y
            if log and i % 500 == 0:
                log("   dp step %d of %d (%.0fs)" % (i, len(order), time.time() - t0))
        fin = f + (D[X] if gend is None else gend)
        j = int(np.argmin(fin))
        val = int(fin[j])
        cuts = [int(X[j])]
        for i in range(len(order) - 2, -1, -1):
            Xp = cl[order[i]]
            w = self.wcol(Xp, cuts[-1])
            j = int(np.argmin(fs[i] + w))
            cuts.append(int(Xp[j]))
        return val, cuts[::-1]

    def value(self, cuts):
        """(2 cost, list of W) of the word that writes the trails at these cuts in this order"""
        D = self.T.D
        tot = int(D[cuts[0]] + D[cuts[-1]])
        ws = []
        for a, b in zip(cuts[:-1], cuts[1:]):
            w = self.T.W(a, b)
            ws.append(w); tot += w
        return tot, ws

    def spell(self, cuts):
        """the word (letter values) of the trails written at these cuts in this order"""
        F = self.F
        ev = [(int(F.S[c]), int(F.E[c])) for c in cuts]
        return F.B.spell(ev)
