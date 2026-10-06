#!/usr/bin/env python
"""top.py - the top-level objects of a base word of Pantone's form, and min-plus steps that leave out the own
object.  A module.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

Objects.  Take the largest level v at which the graph "two small trails have a join with W < v" does not connect
all small trails.  Its components are the groups: at n = 10, 48 groups of 7 small trails; at n = 11, 48 classes of
56.  Every big trail is an object of its own.  obj[c] is the object of cut c.

Half letters.  W(x, y) = 2 c(x, y) + D_x + D_y for a cut x written before a cut y: c = h - (largest overlap of the
end of x with the start of y), D = cost of a cut.  For a word, 2 cost = D(first) + sum of W over its joins + D(last),
cost = cuts + joins, length = h + sum R + cost.

  out_best   g(x) = min over cuts y of another object of scale * W(x, y) + val(y)
  in_best    g(y) = min over cuts x of another object of val(x) + scale * W(x, y)
  pairs      all joins (x, y, W) with W <= wmax between cuts of different objects
The two minima are computed for all cuts at once: for every overlap k and every string of k letters the best value
and the best value of a second object are kept, so the own object can be left out.  t_minplus.py tests them
against the direct formula.

Needs: Python 3, numpy, countn.py, tm.py.
"""
import time
import numpy as np
import countn

BIGN = 10 ** 9


class Top:
    """a base word (countn.Fam, with the joins of the small trails up to cost cmax) and its objects: NG groups of
    small trails, then the big trails; NO objects in all.  tobj[t] = object of trail t, obj[c] = object of cut c,
    is_small[c] = cut c lies on a small trail."""

    def __init__(self, base, cmax=4, wide=False, log=print):
        F = countn.Fam(base, wide=wide, cmax=cmax, log=log)
        F.small_joins(); F.big(); F.capacities(min(F.beta, F.wcap))
        self.F, self.log = F, log
        self.h, self.K, self.V, self.D = F.h, F.K, F.V, F.D
        lev_top = max(v for v in F.Lt if F.Lt[v] < F.NS)
        cls = F.tlab[lev_top]
        gids = np.unique(cls[F.small_t])
        self.NG = len(gids)
        tobj = np.full(F.NT, -1, np.int64)
        tobj[F.small_t] = np.searchsorted(gids, cls[F.small_t])
        tobj[F.big_t] = self.NG + np.arange(len(F.big_t))
        self.tobj = tobj
        self.NO = self.NG + len(F.big_t)
        self.obj = tobj[F.ct]                       # object of every cut
        self.is_small = F.is_small_trail[F.ct]
        self.lev_top = lev_top
        log("objects: %d groups + %d big trails" % (self.NG, len(F.big_t)))

    def _tables(self, ids, v, lab, cuts, k, want_arg):
        """per string of level k: best value, its label, best value among the other labels (and the cuts)"""
        F = self.F
        order = np.lexsort((v, ids))
        si, sv, sl = ids[order], v[order], lab[order]
        st = np.nonzero(np.concatenate([[True], si[1:] != si[:-1]]))[0]
        cnt = np.diff(np.concatenate([st, [len(si)]]))
        l1 = sl[st]
        v2 = np.where(sl == np.repeat(l1, cnt), BIGN, sv)
        m2 = np.minimum.reduceat(v2, st)
        t1 = np.full(F.nstr[k], BIGN, v.dtype); t2 = np.full(F.nstr[k], BIGN, v.dtype); tl = np.full(F.nstr[k], -1,
            np.int64)
        t1[si[st]] = sv[st]; t2[si[st]] = m2; tl[si[st]] = l1
        a1 = a2 = None
        if want_arg:
            a1 = np.full(F.nstr[k], -1, np.int64); a1[si[st]] = cuts[order[st]]
            o2 = np.lexsort((v2, si))
            s2 = si[o2]
            st2 = np.nonzero(np.concatenate([[True], s2[1:] != s2[:-1]]))[0]
            a2 = np.full(F.nstr[k], -1, np.int64); a2[s2[st2]] = cuts[order[o2[st2]]]
        return t1, t2, tl, a1, a2

    # g(x) = min over y in Y, lab(y) != lab(x), of W(x,y) * scale + val(y)
    def out_best(self, val, X=None, Y=None, lab=None, scale=1, want_arg=False):
        F = self.F
        X = np.arange(self.V) if X is None else X
        Y = np.arange(self.V) if Y is None else Y
        lab = self.obj if lab is None else lab
        v = val + scale * self.D[Y]
        g = np.full(len(X), BIGN, v.dtype)
        arg = np.full(len(X), -1, np.int64)
        ly = lab[Y]; lx = lab[X]
        for k in range(self.K + 1):
            t1, t2, tl, a1, a2 = self._tables(F.pre[k][Y], v, ly, Y, k, want_arg)
            q = F.suf[k][X]
            own = tl[q] == lx
            cand = np.where(own, t2[q], t1[q]) + 2 * scale * (self.h - k)
            if want_arg:
                arg = np.where(cand < g, np.where(own, a2[q], a1[q]), arg)
            g = np.minimum(g, cand)
        g = g + scale * self.D[X]
        return (g, arg) if want_arg else g

    # g(y) = min over x in X, lab(x) != lab(y), of val(x) + W(x,y) * scale
    def in_best(self, val, X=None, Y=None, lab=None, scale=1, want_arg=False):
        F = self.F
        X = np.arange(self.V) if X is None else X
        Y = np.arange(self.V) if Y is None else Y
        lab = self.obj if lab is None else lab
        v = val + scale * self.D[X]
        g = np.full(len(Y), BIGN, v.dtype)
        arg = np.full(len(Y), -1, np.int64)
        lx = lab[X]; ly = lab[Y]
        for k in range(self.K + 1):
            t1, t2, tl, a1, a2 = self._tables(F.suf[k][X], v, lx, X, k, want_arg)
            q = F.pre[k][Y]
            own = tl[q] == ly
            cand = np.where(own, t2[q], t1[q]) + 2 * scale * (self.h - k)
            if want_arg:
                arg = np.where(cand < g, np.where(own, a2[q], a1[q]), arg)
            g = np.minimum(g, cand)
        g = g + scale * self.D[Y]
        return (g, arg) if want_arg else g

    def pairs(self, X, Y, wmax, lab=None):
        """all joins (x, y, W) with W <= wmax, x in X, y in Y, lab(x) != lab(y); W uses the largest overlap"""
        F = self.F
        lab = self.obj if lab is None else lab
        V = self.V
        seen = np.zeros(0, np.int64)
        pa, pb, pw = [], [], []
        kmin = max(0, self.h - wmax // 2)
        for k in range(self.K, kmin - 1, -1):
            a, b = F.join_pairs(X, Y, k)
            key = a * V + b
            if len(seen):
                new = ~np.isin(key, seen)
                a, b, key = a[new], b[new], key[new]
            seen = np.concatenate([seen, key])
            w = 2 * (self.h - k) + self.D[a] + self.D[b]
            ok = (w <= wmax) & (lab[a] != lab[b])
            pa.append(a[ok]); pb.append(b[ok]); pw.append(w[ok])
        return np.concatenate(pa), np.concatenate(pb), np.concatenate(pw)

    def W(self, a, b):
        """W of the join from cut a to cut b"""
        return self.F.W(int(a), int(b))
