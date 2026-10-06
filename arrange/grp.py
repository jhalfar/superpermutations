#!/usr/bin/env python
"""grp.py - exact dynamic programme inside one group of small trails.  A module.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

A group is one object of top.py: at n = 10 the 7 small trails that belong together (in Pantone's construction the 7
full 3-cycles of a 4-cycle).

Single-port: every trail of the group is written once, entered and left at one cut.  The word visits the group in
one or more RUNS (maximal sequences of consecutive trails of the group).  For prices ei (a run enters at a cut) and
eo (a run leaves at a cut) the programme returns
        min over orders, cuts and splittings into runs of   sum over runs [ ei(first) + joins inside + eo(last) ]
with the minimiser (a list of runs, each a list of cuts).  Joins inside a run: the listed joins between cuts of
different trails of the group (W < wcap).  A join that is not listed has W >= wcap and is never better than ending
the run and starting another one as long as eo(x) + ei(y) <= wcap for all x, y of the group (the caller checks it).
The programme runs over the subsets of the trails of the group (128 for 7 trails) with one value per cut.

Needs: Python 3, numpy, top.py.
"""
import numpy as np


class Group:
    """group g of a top.Top: cuts (their numbers in the base word), m cuts on k trails, cuts_of[t] = the cuts of
    its t-th trail, arcs[t] = the listed joins into trail t as (from, to, W, starts of the runs of equal `to`,
    the distinct `to`), all in numbers local to the group"""

    def __init__(self, T, g):
        F = T.F
        self.g = g
        cuts = np.nonzero(T.obj == g)[0]
        self.cuts = cuts
        m = len(cuts)
        self.m = m
        trails = np.unique(F.ct[cuts])
        self.trails = trails
        self.k = len(trails)
        lt = np.searchsorted(trails, F.ct[cuts])
        self.lt = lt
        self.cuts_of = [np.nonzero(lt == t)[0] for t in range(self.k)]
        loc = np.full(T.V, -1, np.int64); loc[cuts] = np.arange(m)
        dm = ~F.same
        A, Bn, Wv = loc[F.pa[dm]], loc[F.pb[dm]], F.pw[dm]
        sel = (A >= 0) & (Bn >= 0)
        a, b, w = A[sel], Bn[sel], Wv[sel].astype(np.int64)
        self.wcap = F.wcap
        self.arcs = []
        for t in range(self.k):
            s = lt[b] == t
            at, bt, wt = a[s], b[s], w[s]
            o = np.argsort(bt, kind="stable")
            at, bt, wt = at[o], bt[o], wt[o]
            st = np.nonzero(np.concatenate([[True], bt[1:] != bt[:-1]]))[0]
            self.arcs.append((at, bt, wt, st, bt[st]))
        self.D = T.D[cuts]

    def solve(self, ei, eo, trace=True):
        """the programme of the header.  g[S][x] = the cheapest way to have written exactly the trails of the set S,
        the last one cut at x.  Returns (value, runs) with the runs as lists of local cut numbers in the order they
        are written; runs is None with trace=False."""
        k, m = self.k, self.m
        BIG = np.asarray(10 ** 12, ei.dtype)
        full = (1 << k) - 1
        g = [None] * (1 << k)
        for t in range(k):
            v = np.full(m, BIG, ei.dtype)
            v[self.cuts_of[t]] = ei[self.cuts_of[t]]
            g[1 << t] = v
        for S in range(1, full):
            cur = g[S]
            if cur is None:
                continue
            base = (cur + eo).min()
            for t in range(k):
                if (S >> t) & 1:
                    continue
                at, bt, wt, st, ub = self.arcs[t]
                ct = self.cuts_of[t]
                Tm = S | (1 << t)
                if g[Tm] is None:
                    g[Tm] = np.full(m, BIG, ei.dtype)
                ent = base + ei[ct]
                g[Tm][ct] = ent
                if len(at):
                    vals = np.minimum.reduceat(cur[at] + wt, st)
                    g[Tm][ub] = np.minimum(g[Tm][ub], vals)
        fin = g[full] + eo
        y = int(np.argmin(fin))
        val = fin[y]
        if not trace:
            return val, None
        runs = [[y]]
        S = full
        while True:
            t = int(self.lt[y])
            P = S & ~(1 << t)
            if P == 0:
                break
            cur = g[P]
            at, bt, wt, st, ub = self.arcs[t]
            s = bt == y
            best_arc = None
            if s.any():
                vals = cur[at[s]] + wt[s]
                j = int(np.argmin(vals))
                best_arc = (vals[j], int(at[s][j]))
            if best_arc is not None and best_arc[0] <= g[S][y]:
                x = best_arc[1]
                runs[-1].append(x)
            else:
                x = int(np.argmin(cur + eo))
                runs.append([x])
            y, S = x, P
        runs = [r[::-1] for r in runs[::-1]]
        return val, runs

    def run_cost(self, T, run):
        """exact W-sum of the joins inside a run (global join weights)"""
        return sum(T.W(self.cuts[run[i]], self.cuts[run[i + 1]]) for i in range(len(run) - 1))
