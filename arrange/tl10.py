#!/usr/bin/env python
"""tl10.py - the top-level model at n = 10: an order of the groups and the big trails, valued exactly.  A module.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

For a base word with 48 groups of 7 small trails and some big trails (Pantone's n = 10 word, or the base word of a
selection with the same loops without a row).

OBJECTS: the groups and the big trails.  A word of the model is an order of the objects.
  A big trail is written once from one cut (at a step of weight 2 or 3, or dropping a repeated permutation).
  A group is written in one run, in one of two modes:
    path: enter at cut y, leave at cut x of another trail, the 7 trails each written once from one cut.
          Cost T[y, x], the table of gt.py.
    loop: enter and leave at the SAME cut p of a trail t.  Then t is written in two segments, from p to a second cut
          q and from q back to p, with the other 6 trails between them: the group is closed into a loop and hung on
          the cut p.  Cost L(p) = min over q != p of the cheapest closed tour through q (closed[] of gt.py).
          This is the pattern of rumstd's n = 10 word.
For a fixed order of the objects the best cuts and modes are found exactly by a dynamic programme over the cuts,
    2 cost = D(first) + sum of W + sum of the costs of the groups + D(last),
and the word is written as a plan.  The joins are the narrow ones (overlap at most h = 7).

  TL.forward        the programme over an order
  TL.evaluate       2 cost of an order, with the cut at which every object is entered and left
  TL.events         the events of a solution: whole trails and, for a group in loop mode, the two segments
  TL.cost_of_events 2 cost of a list of events from the joins alone (a check that does not use the programme)
  TL.write_plan     the events as a plan on the base word
  TL.spell_len      the length of the word of the events
  trail_keys        a name for every small trail that does not depend on the base word

What is exact: the value of a given order.  Which order is best is not decided here.

Needs: Python 3, numpy; top.py, grp.py, fdp.py, countn.py, tm.py; the tables of gt.py for the base word.
"""
import sys, time, pickle
import numpy as np
import top, grp, fdp

BIGT = 10000


class TL:
    """the model on a base word: groups (grp.Group), cuts[o] = the cuts of object o (objects 0 .. NG-1 are the
    groups, then the big trails), M[g][y, x] = cost of group g entered at its cut y and left at x: the table of
    gt.py, with the loop cost L(p) on the diagonal; loopq[g][p] = the second cut q of the loop at p"""

    def __init__(self, base, gtfile, log=print):
        self.log = log
        T = top.Top(base, cmax=4, log=lambda *x: None)
        self.T, self.F, self.B = T, T.F, T.F.B
        self.P = fdp.Dp(T, plain_only=False)
        z = np.load(gtfile)
        Tt = z["T"].astype(np.int64); cl = z["closed"].astype(np.int64)
        self.NG, self.NO = T.NG, T.NO
        self.groups = [grp.Group(T, g) for g in range(T.NG)]
        self.M = []
        self.Tt = Tt; self.closed = cl
        self.loopq = []
        for g, G in enumerate(self.groups):
            M = Tt[g].copy()
            lq = np.full(G.m, -1, np.int64)
            for t in range(G.k):
                ct = G.cuts_of[t]
                c = cl[g][ct]
                o = np.argsort(c, kind="stable")
                b1, b2 = ct[o[0]], ct[o[1]]
                for p in ct.tolist():
                    q = b1 if p != b1 else b2
                    M[p, p] = cl[g][q]; lq[p] = q
            self.M.append(M); self.loopq.append(lq)
        self.cuts = [G.cuts for G in self.groups] + [self.P.cut_list[int(t)] for t in self.F.big_t]
        self.D = T.D

    # ---- joins
    def join(self, f, X, Y):
        """g(y) = min over x in X of f(x) + W(x, y), for the cuts y of Y"""
        return self.P.step(f, X, Y)

    def join_back(self, g, X, Y):
        """gb(x) = min over y of W(x, y) + g(y)"""
        F, h, K, D = self.F, self.T.h, self.T.K, self.D
        gy = g + D[Y]
        out = np.full(len(X), gy.min() + 2 * h, np.int64)
        if len(X) * len(Y) <= 400000:
            for k in range(1, K + 1):
                eq = F.suf[k][X][:, None] == F.pre[k][Y][None, :]
                if eq.any():
                    out = np.minimum(out, np.where(eq, gy[None, :], fdp.BIG).min(1) + 2 * (h - k))
            return out + D[X]
        for k in range(1, K + 1):
            a = F.suf[k][X]; b = F.pre[k][Y]
            u, inv = np.unique(np.concatenate([a, b]), return_inverse=True)
            tab = np.full(len(u), fdp.BIG, np.int64)
            np.minimum.at(tab, inv[len(a):], gy)
            out = np.minimum(out, tab[inv[:len(a)]] + 2 * (h - k))
        return out + D[X]

    # ---- forward programme over an order of objects
    def forward(self, order, f0=None):
        """returns the list of (g_in, f_out) per object; f_out over the cuts of the object"""
        vecs = []
        prevX, f = None, None
        for i, o in enumerate(order):
            X = self.cuts[o]
            if i == 0:
                gin = self.D[X].astype(np.int64) if f0 is None else f0
            else:
                gin = self.join(f, prevX, X)
            if o < self.NG:
                fo = (gin[:, None] + self.M[o]).min(0)
            else:
                fo = gin
            vecs.append((gin, fo))
            prevX, f = X, fo
        return vecs

    def evaluate(self, order, trace=False):
        """2 cost of the best word with this order of objects.  With trace=True also the list of (entry, exit) for
        every object, as indices into its cuts: equal for a big trail and for a group in loop mode."""
        vecs = self.forward(order)
        X = self.cuts[order[-1]]
        fin = vecs[-1][1] + self.D[X]
        j = int(np.argmin(fin))
        val = int(fin[j])
        if not trace:
            return val
        states = [None] * len(order)
        xj = j
        for i in range(len(order) - 1, -1, -1):
            o = order[i]
            gin, fo = vecs[i]
            if o < self.NG:
                yj = int(np.argmin(gin + self.M[o][:, xj]))
                states[i] = (yj, xj)
            else:
                yj = xj
                states[i] = (xj, xj)
            if i > 0:
                Xp = self.cuts[order[i - 1]]
                w = self.P.wcol(Xp, int(self.cuts[o][yj]))
                xj = int(np.argmin(vecs[i - 1][1] + w))
        return val, states

    # ---- events of a solution
    def events(self, order, states):
        """list of ('O', cut) / ('S', cut_from, cut_to): a segment from the S window of cut_from to the E window of cut_to"""
        ev = []
        for o, (yj, xj) in zip(order, states):
            if o >= self.NG:
                ev.append(("O", int(self.cuts[o][xj])))
                continue
            G = self.groups[o]
            if yj != xj:
                ei = np.full(G.m, 10 ** 9, np.int64); eo = np.full(G.m, 10 ** 9, np.int64)
                ei[yj] = 0; eo[xj] = 0
                v, runs = G.solve(ei, eo)
                assert len(runs) == 1 and int(v) == int(self.Tt[o][yj, xj]), (v, self.Tt[o][yj, xj])
                for c in runs[0]:
                    ev.append(("O", int(G.cuts[c])))
            else:
                p = yj
                q = int(self.loopq[o][p])
                # closed tour through q: q -> ... -> x7 -> q
                Wm = np.full(G.m, BIGT, np.int64)
                for t in range(G.k):
                    at, bt, wt, st, ub = G.arcs[t]
                    s = bt == q
                    Wm[at[s]] = np.minimum(Wm[at[s]], wt[s])
                tot = self.Tt[o][q] + Wm
                x7 = int(np.argmin(tot))
                assert int(tot[x7]) == int(self.closed[o][q])
                ei = np.full(G.m, 10 ** 9, np.int64); eo = np.full(G.m, 10 ** 9, np.int64)
                ei[q] = 0; eo[x7] = 0
                v, runs = G.solve(ei, eo)
                assert len(runs) == 1 and runs[0][0] == q
                ev.append(("S", int(G.cuts[p]), int(G.cuts[q])))
                for c in runs[0][1:]:
                    ev.append(("O", int(G.cuts[c])))
                ev.append(("S", int(G.cuts[q]), int(G.cuts[p])))
        return ev

    def cost_of_events(self, ev):
        """2 cost of a list of events by the identity (independent of the programme)"""
        F = self.F
        ent = [e[1] for e in ev]; ext = [e[1] if e[0] == "O" else e[2] for e in ev]
        tot = int(self.D[ent[0]] + self.D[ext[-1]])
        for i in range(len(ev) - 1):
            tot += self.T.W(ext[i], ent[i + 1])
        return tot

    def write_plan(self, ev, path, baselen):
        """write the events as a plan: "O t start g g1" for a whole trail (g1 > 0: a repeated permutation is
        dropped), "S t start len" for a segment of a trail written in two"""
        B, F = self.B, self.F
        n = B.n
        lines = []
        for e in ev:
            if e[0] == "O":
                c = e[1]
                t = int(F.ct[c]); S = int(F.S[c]); E = int(F.E[c])
                start = int(B.pos[S] - B.ps[t])
                g = 3 - int(self.D[c])
                g1 = int(B.gap[E]) if F.SK[c] >= 0 else 0
                lines.append("O %d %d %d %d" % (t, start, g, g1))
            else:
                p, q = e[1], e[2]
                assert F.SK[p] < 0 and F.SK[q] < 0
                t = int(F.ct[p]); R = int(B.R[t])
                st = int(B.pos[int(F.S[p])] - B.ps[t])
                en = int(B.pos[int(F.E[q])] - B.ps[t]) + n
                ln = (en - st) % R
                if ln < n:
                    ln += R
                lines.append("S %d %d %d" % (t, st, ln))
        with open(path, "w", newline="\n") as f:
            f.write("TRAILSEARCH-PLAN %d %d %d\n" % (n, baselen, len(lines)))
            f.write("\n".join(lines) + "\n")

    def spell_len(self, ev):
        """length of the word of the events (segments spelled, largest overlaps up to n - 1)"""
        B, F = self.B, self.F
        evs = []
        for e in ev:
            if e[0] == "O":
                evs.append((int(F.S[e[1]]), int(F.E[e[1]])))
            else:
                evs.append((int(F.S[e[1]]), int(F.E[e[2]])))
        return B.length(evs), evs


def trail_keys(T):
    """for every small trail the sorted tuple of its 8 vertex words: the same on every base with these small trails"""
    F = T.F; B = F.B
    keys = {}
    sm = np.nonzero(T.is_small & (T.D == 0))[0]
    L = B.letters(F.S[sm], 0, T.h)
    for c, row in zip(sm.tolist(), L.tolist()):
        keys.setdefault(int(F.ct[c]), []).append(tuple(row))
    return {t: tuple(sorted(v)) for t, v in keys.items()}
