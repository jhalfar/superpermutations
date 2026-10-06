#!/usr/bin/env python
"""countn.py - the cuts and joins of a base word of Pantone's form (class Fam), and a counting bound built on them.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: countn.py BASE_WORD.txt [WORD.txt] [--wide] [--single] [--cmax C]

What the other scripts here use is the class Fam: all cuts of the trails, the tables of the k-letter ends and
starts of their words (suf, pre), the joins between cuts of small trails up to a cost (small_joins), the components
of the join graph by level (capacities) and the number beta with its function f on the big cuts (big).
Run as a program it prints a counting bound for the family and, for a word given as second argument, how the word
sits against it.  That bound is an earlier and weaker one than cert10.py and cert11.py; it is kept because the
quantities a, w3, beta, Lc, Lt that it defines are the ones the later programs start from.

--wide: joins of up to n - 1 letters and cuts at steps of weight 1.
--single: the function f on the big cuts is only required between cuts of different big trails (enough for the
single-port family; needed in the wide family, where joins inside one big trail can have negative W)

SMALL trails: those with the fewest cuts (the full 3-cycles), BIG trails: the others.  Half letters:
W(x,y) = 2 c(x,y) + D_x + D_y;  for a word  2 cost = sum of W over its joins + D of its first and last cut.
What is computed (every number is exact, the search for the joins is by the tries of the join words):
 a      = smallest W between cuts of two different small trails
 Lc_v   = largest number of trails met by a connected component of the graph on the small CUTS whose edges are the
          joins with W < v between different small trails;   Lt_v = the same for the graph on the small TRAILS
 w3     = smallest W between two different cuts of one small trail
 beta, f = a number and a function on the big cuts with, for big cuts c, d and small cuts a, b,
              W(a,c) >= beta - f(c),   W(c,b) >= f(c),   W(c,d) >= f(c) - f(d),   0 <= f(c) <= beta + D_c
          (f = fixed point of f(c) = min(min_b W(c,b), beta + D_c, min_d W(c,d) + f(d)), found by Bellman-Ford over the
          tries, then all four conditions are checked; beta = 8 is tried first, then smaller values).
          Then a block of big segments between two small cuts weighs at least beta + sum over its segments of
          f(exit) - f(entry), a block at an end of the word (with the D of the end cut) at least 0 + the same sum, and
          these sums cancel over a word (every used cut is once an entry and once an exit).
          With --single the third condition is only required for cuts of different big trails.
THE BOUND (levels).  A CONNECTION is what stands between two consecutive small UNITS of the word: one join, weight
W >= a, or a block of big segments, weight >= beta after the correction above.  A unit is a small trail
(single-port) or a maximal group of consecutive segments of one small trail held together by joins with W <= 7
(multi-port; these joins cost >= w3 each and are counted apart).  For a level v <= beta the connections of weight < v
are joins with W < v between different small trails; the units between two connections of weight >= v form a RUN.
 single-port: a run lies in one component of cuts, so it has at most Lc_v trails: r_v >= ceil(NS / Lc_v) runs.
 multi-port:  a run lies in one component of trails: r_v >= ceil(NS / Lt_v).  Sharper, for the levels with Lc_v < Lt_v:
   take the graph whose nodes are the components of cuts that hold an entry or an exit of a unit and whose edges join
   the component of the entry of a unit to that of its exit.  Every run is connected in it, so it has at most r_v
   connected parts, hence at most r_v + rank nodes, and the nodes hold all small trails: NS <= Lc_v (r_v + rank).
   The edges of a trail with s units and j joins inside its units have rank <= (s - 1) + floor(j / 2) (with j <= 1 the
   edges contain a cycle or a loop).  So r_v >= ceil(NS / Lc_v) - sum over trails of ((s_T - 1) + floor(j_T / 2)), while
   the s_T - 1 additional units cost a each (one more connection) and the j_T joins w3 each: if the number of such
   levels is at most a and at most 2 w3, the losses are paid and Lc_v may be used for them.
 At least r_v - 1 connections have weight >= v, and a connection of weight w counts in w - a levels:
     2 cost >= a (NS - 1) + sum over v = a+1 .. beta of (ceil(NS / L_v) - 1).                (D >= 0, joins >= 0)

Needs: Python 3, numpy, tm.py.  Integers only, no solver.  n <= 11.  At n = 11 on Pantone's word the set-up of Fam
with the joins and the function f takes about 50 s.
"""
import sys
import time

import numpy as np

import tm

BIGN = 10 ** 9


class Fam:
    """a base word with all its cuts: E, S (windows), D (cost), SK (the window dropped, or -1), ct (trail of a
    cut); V cuts on NT trails.  The small trails are those with the fewest cuts (small_t, sc = their cuts), the
    others are big (big_t, BC).  suf[k][c] / pre[k][c]: number of the string of the last k letters of the end word
    / the first k letters of the start word of cut c, k = 0 .. K (K = h, or n - 1 when wide)."""

    def __init__(self, path, wide=False, cmax=4, log=print):
        t0 = time.time()
        self.log = log
        B = tm.Base(path, log=log)
        self.B = B
        n, h = B.n, B.h
        self.n, self.h = n, h
        K = n - 1 if wide else h
        self.K, self.wide = K, wide
        E, S, D, SK = B.all_cuts(gap1=wide, skip=True)
        o = np.lexsort((S, E))
        self.E, self.S, self.D, self.SK = E[o], S[o], D[o].astype(np.int64), SK[o]
        E, S, D = self.E, self.S, self.D
        self.ct = B.trail_of(E).astype(np.int64)
        V = len(E)
        self.V = V
        NT = B.NT
        self.NT = NT
        self.ncut = np.bincount(self.ct, minlength=NT)
        LE = B.letters(E, n - K, n); LS = B.letters(S, 0, K)
        self.suf, self.pre, self.nstr = [], [], []
        for k in range(K + 1):
            a = np.zeros(V, np.int64); b = np.zeros(V, np.int64)
            for j in range(k):
                a = (a << 4) | LE[:, K - k + j]
                b = (b << 4) | LS[:, j]
            codes = np.unique(np.concatenate([a, b]))
            self.suf.append(np.searchsorted(codes, a).astype(np.int32)); self.pre.append(np.searchsorted(codes,
                b).astype(np.int32))
            self.nstr.append(len(codes))
            del a, b, codes
        del LE, LS
        small_n = int(self.ncut.min())
        self.small_t = np.nonzero(self.ncut == small_n)[0]
        self.big_t = np.nonzero(self.ncut != small_n)[0]
        self.NS = len(self.small_t)
        self.is_small_trail = self.ncut == small_n
        is_small_cut = self.is_small_trail[self.ct]
        self.sc = np.nonzero(is_small_cut)[0]
        self.BC = np.nonzero(~is_small_cut)[0]
        log("n=%d %s: trails %d = %d small (%d cuts each) + %d big (%d..%d cuts); cuts %d (small %d, big %d); D values %s; h + sum R = %d  (%.0fs)" % (
            n, "WIDE" if wide else "narrow", NT, self.NS, small_n, len(self.big_t),
            int(self.ncut[self.big_t].min()) if len(self.big_t) else 0,
            int(self.ncut[self.big_t].max()) if len(self.big_t) else 0, V, len(self.sc), len(self.BC),
            sorted(set(D.tolist())), B.base_const,
            time.time() - t0))
        self.cmax = cmax
        self.t0 = t0
        self.single_only = False       # True: f only has to hold between big cuts of different trails (single-port)

    # ------------------------------------------------------------ joins
    def cost(self, a, b):
        """cost of the join from cut a to cut b: h - the largest overlap"""
        for k in range(self.K, -1, -1):
            if self.suf[k][a] == self.pre[k][b]:
                return self.h - k

    def W(self, a, b):
        """W(a, b) = 2 cost + D_a + D_b"""
        return 2 * self.cost(a, b) + int(self.D[a] + self.D[b])

    def join_pairs(self, A, Bc, k):
        """all pairs (a in A, b in Bc) whose words overlap in exactly the k-letter string compared (suffix of a =
        prefix of b)"""
        kb = self.pre[k][Bc]
        order = np.argsort(kb, kind="stable")
        kbs = kb[order]
        ka = self.suf[k][A]
        lo = np.searchsorted(kbs, ka, "left"); hi = np.searchsorted(kbs, ka, "right")
        cnt = (hi - lo).astype(np.int64)
        tot = int(cnt.sum())
        if tot == 0:
            return np.zeros(0, np.int64), np.zeros(0, np.int64)
        ii = np.repeat(np.arange(len(A)), cnt)
        off = np.arange(tot) - np.repeat(np.cumsum(cnt) - cnt, cnt)
        jj = order[np.repeat(lo, cnt) + off]
        return A[ii], Bc[jj]

    def minplus(self, f, A, Bc):
        """g(b) = min over a in A of f(a) + W(a,b)"""
        g = np.full(len(Bc), BIGN, np.int64)
        val = f + self.D[A]
        for k in range(self.K + 1):
            tab = np.full(self.nstr[k], BIGN, np.int64)
            np.minimum.at(tab, self.suf[k][A], val)
            g = np.minimum(g, tab[self.pre[k][Bc]] + 2 * (self.h - k))
        return g + self.D[Bc]

    def minplus_rev(self, f, A, Bc):
        """g(a) = min over b in Bc of W(a,b) + f(b)"""
        g = np.full(len(A), BIGN, np.int64)
        val = f + self.D[Bc]
        for k in range(self.K + 1):
            tab = np.full(self.nstr[k], BIGN, np.int64)
            np.minimum.at(tab, self.pre[k][Bc], val)
            g = np.minimum(g, tab[self.suf[k][A]] + 2 * (self.h - k))
        return g + self.D[A]

    def minplus_rev_excl(self, f, A, Bc):
        """g(a) = min over b in Bc on ANOTHER trail than a of W(a,b) + f(b), a in A  (best and second-best trail per string)"""
        g = np.full(len(A), BIGN, np.int64)
        val = f + self.D[Bc]
        lab = self.ct[Bc]
        la = self.ct[A]
        for k in range(self.K + 1):
            ids = self.pre[k][Bc]
            order = np.lexsort((val, ids))
            si, sv, sl = ids[order], val[order], lab[order]
            st = np.nonzero(np.concatenate([[True], si[1:] != si[:-1]]))[0]
            cnt = np.diff(np.concatenate([st, [len(si)]]))
            m1 = sv[st]; l1 = sl[st]
            v2 = np.where(sl == np.repeat(l1, cnt), BIGN, sv)
            m2 = np.minimum.reduceat(v2, st)
            t1 = np.full(self.nstr[k], BIGN, np.int64); t2 = np.full(self.nstr[k], BIGN,
                np.int64); tl = np.full(self.nstr[k], -1, np.int64)
            t1[si[st]] = m1; t2[si[st]] = m2; tl[si[st]] = l1
            q = self.suf[k][A]
            cand = np.where(tl[q] == la, t2[q], t1[q])
            g = np.minimum(g, cand + 2 * (self.h - k))
        return g + self.D[A]

    # ------------------------------------------------------------ the small trails
    def small_joins(self):
        """all joins between small cuts with c <= cmax: arrays (a, b, W); complete for W < 2 cmax + 2"""
        log, h, K, V, sc, D = self.log, self.h, self.K, self.V, self.sc, self.D
        seen = np.zeros(0, np.int64)
        pa, pb, pc = [], [], []
        for k in range(K, h - self.cmax - 1, -1):
            a, b = self.join_pairs(sc, sc, k)
            key = a * V + b
            if len(seen):
                new = ~np.isin(key, seen)
                a, b, key = a[new], b[new], key[new]
            seen = np.concatenate([seen, key])
            pa.append(a); pb.append(b); pc.append(np.full(len(a), h - k, np.int64))
        del seen
        pa = np.concatenate(pa); pb = np.concatenate(pb); pc = np.concatenate(pc)
        self.pa, self.pb = pa, pb
        self.pw = 2 * pc + D[pa] + D[pb]
        self.wcap = 2 * (self.cmax + 1)
        same = self.ct[pa] == self.ct[pb]
        deg = pa == pb
        self.same, self.deg = same, deg
        dm = ~same
        self.a = int(self.pw[dm].min())
        hd = np.unique(self.pw[dm], return_counts=True)
        log("joins between cuts of DIFFERENT small trails, W: count (complete for W < %d): %s" % (
            self.wcap, {int(v): int(c) for v, c in zip(*hd) if v < self.wcap}))
        sd = same & ~deg
        self.w3 = int(self.pw[sd].min()) if sd.any() else self.wcap
        hs = np.unique(self.pw[sd], return_counts=True)
        log("joins between two different cuts of the SAME small trail, W: count: %s" % ({int(v): int(c) for v,
            c in zip(*hs) if v < self.wcap}))
        log("a = %d, w3 = %d   (%.0fs)" % (self.a, self.w3, time.time() - self.t0))

    @staticmethod
    def components(nn, a_, b_):
        """labels of the connected components of the graph on nn nodes with the edges (a_[i], b_[i])"""
        lab = np.arange(nn)
        while True:
            mn = np.minimum(lab[a_], lab[b_])
            new = lab.copy()
            np.minimum.at(new, a_, mn); np.minimum.at(new, b_, mn)
            new = new[new]
            if (new == lab).all():
                return lab
            lab = new

    def capacities(self, vmax):
        """Lc_v and Lt_v for v = a+1 .. vmax; also the trail-level labels per level (self.tlab[v])"""
        NT, sc = self.NT, self.sc
        loc = np.full(self.V, -1, np.int64); loc[sc] = np.arange(len(sc))
        dm = ~self.same
        da, db, dw = loc[self.pa[dm]], loc[self.pb[dm]], self.pw[dm]
        tr_s = self.ct[sc]
        self.Lc, self.Lt, self.tlab = {}, {}, {}
        for v in range(self.a + 1, vmax + 1):
            assert v <= self.wcap, "raise --cmax: joins with W < %d are not all listed" % v
            m = dw < v
            lab = self.components(len(sc), da[m], db[m])
            pair = np.unique(lab * NT + tr_s)
            self.Lc[v] = int(np.bincount(pair // NT, minlength=len(sc)).max())
            tl = self.components(NT, tr_s[da[m]], tr_s[db[m]])
            self.tlab[v] = tl
            self.Lt[v] = int(np.bincount(tl[self.small_t], minlength=NT).max())
            self.log("  level %d: joins with W < %d between different small trails: %d; a component of cuts meets at most %d trails, "
                     "a component of trails has at most %d trails" % (v, v, int(m.sum()), self.Lc[v], self.Lt[v]))

    # ------------------------------------------------------------ the big trails
    def big(self):
        """the largest beta <= 8 with a function f on the big cuts that satisfies the four conditions of the header
        (found by Bellman-Ford over the join tables, then checked); sets beta, f, in1, out1"""
        log, BC, sc, D = self.log, self.BC, self.sc, self.D
        if not len(BC):
            self.beta = BIGN
            return
        zs = np.zeros(len(sc), np.int64)
        self.in1 = self.minplus(zs, sc, BC); self.out1 = self.minplus_rev(zs, BC, sc)
        step = self.minplus_rev_excl if self.single_only else self.minplus_rev
        loc = np.full(self.V, -1, np.int64); loc[BC] = np.arange(len(BC))
        self.bloc = loc
        self.beta = None
        for beta in range(8, 0, -1):
            f = np.minimum(self.out1, beta + D[BC])
            ok = True
            for it in range(400):
                g = np.minimum(f, step(f, BC, BC))
                if (g == f).all():
                    break
                f = g
                if f.min() < -200:
                    ok = False
                    break
            if not ok:
                break
            # the four conditions, checked on the final f
            c1 = bool((self.in1 + f >= beta).all())
            c2 = bool((f <= self.out1).all())
            c3 = bool((step(f, BC, BC) >= f).all())
            c4 = bool((f >= 0).all() and (f <= beta + D[BC]).all())
            log("big cuts: beta = %d: f after %d Bellman-Ford rounds; W(a,c) >= beta - f(c): %s; W(c,b) >= f(c): %s; W(c,d) >= f(c) - f(d)%s: %s; "
                "0 <= f <= beta + D: %s   (%.0fs)" % (beta, it, c1, c2,
                " (different trails)" if self.single_only else "", c3, c4, time.time() - self.t0))
            if c1 and c2 and c3 and c4:
                self.beta, self.f = beta, f
                break
        if self.beta is None:
            log("big cuts: no function f (cycles of joins between big cuts with negative W-sum): the bound has no term for blocks")

    def bound(self):
        """the counting bound of the header, single-port and multi-port; returns {name: (2 cost, cost)}"""
        a, NS = self.a, self.NS
        top = min(self.beta if self.beta is not None else a, self.wcap)
        self.capacities(top)
        out = {}
        nvc = sum(1 for v in range(a + 1, top + 1) if self.Lc[v] < self.Lt[v])
        sharp = nvc <= a and nvc <= 2 * self.w3
        Lm = {v: (self.Lc[v] if sharp else self.Lt[v]) for v in range(a + 1, top + 1)}
        self.log("multi-port: %d levels with Lc < Lt; a = %d, w3 = %d: %s" % (
            nvc, a, self.w3,
            "the components of cuts may be used" if sharp else "only the components of trails are used"))
        for name, L in (("single-port", self.Lc), ("multi-port", Lm)):
            if name == "multi-port" and (self.single_only or self.w3 < 0):
                self.log("BOUND multi-port: not valid here (%s)" % (
                    "f was only checked between different big trails" if self.single_only
                                                                    else "joins inside a small trail with W < 0"))
                continue
            tot = a * (NS - 1)
            terms = []
            for v in range(a + 1, top + 1):
                r = -(-NS // L[v])
                tot += r - 1
                terms.append("%d" % (r - 1))
            cost = (tot + 1) // 2
            out[name] = (tot, cost)
            self.log("BOUND %s %s: 2 cost >= %d (%d - 1) + %s = %d  ->  cost >= %d, length >= %d" % (
                name, "wide" if self.wide else "narrow", a, NS, " + ".join(terms) if terms else "0", tot, cost,
                self.B.base_const + cost))
        return out

    # ------------------------------------------------------------ anatomy of a word
    def anatomy(self, path):
        """how a word of the family sits against the bound: its joins between small trails by W, its blocks of big
        segments with their corrected weight, and the number of connections of weight >= v for every level v"""
        log, B = self.log, self.B
        P = tm.Plan(B, path, log=log)
        vid = {(int(e), int(s)): i for i, (e, s) in enumerate(zip(self.E.tolist(), self.S.tolist()))}
        byE, byS = {}, {}
        for (E, S, k) in P.cuts:
            c = vid.get((int(E), int(S)))
            if c is None:
                log("the word uses a cut that is not in this family (E %d, S %d): no anatomy" % (E, S))
                return
            byE[int(E)] = c; byS[int(S)] = c
        ev = P.events
        ent = [byS[a] for a, _ in ev]; ext = [byE[b] for _, b in ev]
        small = self.is_small_trail[self.ct[np.array(ent)]]
        Wj = []
        for i in range(len(ev) - 1):
            ov = P.ovs[i]
            if ov > self.K:
                log("the word has a join overlapping %d letters, more than this family allows: no anatomy" % ov)
                return
            Wj.append(2 * (self.h - ov) + int(self.D[ext[i]] + self.D[ent[i + 1]]))
        tot = sum(Wj) + int(self.D[ent[0]] + self.D[ext[-1]])
        log("word %s: %d segments (%d small, %d big), 2 cost = %d (cost %d, length %d)" % (
            path.replace("\\", "/").split("/")[-1], len(ev), int(small.sum()), int((~small).sum()), tot, tot // 2,
            B.base_const + tot // 2))
        # connections between consecutive small segments
        f = getattr(self, "f", None)
        conn = []          # (weight, kind, number of big segments)
        i = 0
        N = len(ev)
        first_small = int(np.argmax(small)); last_small = N - 1 - int(np.argmax(small[::-1]))
        ends = sum(Wj[:first_small]) + sum(Wj[last_small:]) + int(self.D[ent[0]] + self.D[ext[-1]])
        i = first_small
        hist_same = {}
        while i < last_small:
            j = i + 1
            while not small[j]:
                j += 1
            wsum = sum(Wj[i:j])
            if j == i + 1:
                if self.ct[ext[i]] == self.ct[ent[j]]:
                    hist_same[wsum] = hist_same.get(wsum, 0) + 1
                    conn.append((wsum, "same", 0))
                else:
                    conn.append((wsum, "join", 0))
            else:
                corr = 0
                if f is not None and self.beta is not None:
                    corr = sum(int(f[self.bloc[ext[k]]] - f[self.bloc[ent[k]]]) for k in range(i + 1, j))
                conn.append((wsum - corr, "block", j - i - 1))
            i = j
        hj = {}
        for wv, kind, nb in conn:
            if kind == "join":
                hj[wv] = hj.get(wv, 0) + 1
        hb = {}
        for wv, kind, nb in conn:
            if kind == "block":
                hb[(nb, wv)] = hb.get((nb, wv), 0) + 1
        log("  joins between different small trails, W: count %s" % dict(sorted(hj.items())))
        log("  joins between two segments of one small trail, W: count %s" % dict(sorted(hist_same.items())))
        log("  blocks of big segments between small ones, (segments, corrected weight): count %s" % dict(sorted(hb.items())))
        log("  blocks at the ends and D of the end cuts: %d half letters" % ends)
        ws = sorted(wv for wv, kind, nb in conn if kind != "same")
        a = self.a
        top = max(ws) if ws else a
        line = []
        for v in range(a + 1, min(top, 14) + 1):
            line.append("%d: %d" % (v, sum(1 for x in ws if x >= v)))
        log("  connections %d; with weight >= v, v: count  %s" % (len(ws), ", ".join(line)))
        return conn


def main():
    args = [x for x in sys.argv[1:] if not x.startswith("--")]
    wide = "--wide" in sys.argv
    cmax = 4
    if "--cmax" in sys.argv:
        cmax = int(sys.argv[sys.argv.index("--cmax") + 1])
        args = [x for x in args if x != str(cmax)]
    log = lambda *x: print(*x, flush=True)
    F = Fam(args[0], wide=wide, cmax=cmax, log=log)
    F.single_only = "--single" in sys.argv
    if F.single_only:
        log("big cuts: f is only required between cuts of DIFFERENT big trails: the bound printed for multi-port is not valid")
    F.small_joins()
    F.big()
    F.bound()
    for wpath in args[1:]:
        F.anatomy(wpath)
    log("total %.0fs" % (time.time() - F.t0))


if __name__ == "__main__":
    main()
