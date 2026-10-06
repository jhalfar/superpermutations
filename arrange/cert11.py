#!/usr/bin/env python
"""cert11.py - a lower bound for single-port narrow words made of Pantone's pieces at n = 11, in exact integers.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: cert11.py BASE.txt [--kmax K] [--slack CAP [--full]]

  BASE.txt     Pantone's n = 11 word (2,800 closed trails: 2,688 small, 112 big)
  --kmax K     compute the block values Y_k exactly up to k = K and bound longer blocks from them (default: all 112)
  --slack CAP  lower the prices of the E ends where the run table has slack, by at most CAP (see below)
  --full       with --slack: use the whole slack of a run with two E ends instead of half of it

Families of words.  "Single-port": every closed trail is written once, from one cut.  "Multi-port": a trail may
be written in several segments.  "Narrow": consecutive pieces overlap in at most h = n - 3 letters.  A bound proved
for a family says nothing about words outside it, and nothing about other piece sets.
Here: single-port narrow (cuts at steps of weight 2 or 3 and cuts that drop a repeated permutation; h = 8).

The run and class programme with a term for the blocks of big trails (doubled half letters).
A RUN is a maximal sequence of consecutive small trails joined by joins with W < LOW; the connection before / after
a run has type I (a join with W >= LOW inside the same top class) or E (a join to another top class, or a block of
big trails).  lb(x, I), lb(x, E): lower bounds of such a connection at the cut x;
val(run) = lb_in(first cut, type) + 2 (joins inside) + lb_out(last cut, type);
V[k][t_in][t_out] = smallest val of a run with k trails (exact, all components at once).
(a) The cover of a class is computed for every NUMBER of E ends: Cx[e] = cheapest cover of the 56 trails of a class
    by runs with exactly e E ends.
(b) For an E connection that is a block of k big cuts between small cuts x, y
        2 w - lb_out(x, E) - lb_in(y, E) >= Y_k
    (min-plus over the join tables, consecutive big cuts in different trails; a block may visit a big trail twice,
    which is a relaxation), Ys_k / Ye_k for a block at the start / end.
THEN   4 cost = sum over runs val + sum over connections (2 w - lb_out - lb_in) + end terms
            >= min over the numbers of E ends n_c >= 2 of the classes and the splits of the big trails into q inner
               blocks, q <= (sum n_c - 2) / 2:   sum_c Cx[n_c] + sum of Y_k + start term + end term.
--slack: for every cut the smallest (val - V) over the runs that end (start) there with an E end is computed, and
the price of the E end at that cut is lowered by it (halved for runs with two E ends unless --full), at most by CAP.
The run table is computed again with the lower prices and printed as "unchanged" or "LOWER"; the block values
gain from the lower prices.  The bound is valid for any prices.

Results on Pantone's n = 11 word (the last line printed is the bound):
  no option                   4 cost >= 12,688    length >= 43,930,476
  --slack 4 --kmax 40         4 cost >= 12,706    length >= 43,930,481
Status: exhaustive integer computation.  Cross-checks: the min-plus steps against the direct formula (t_minplus.py);
the identity and its terms on a real word (check11.py on my word of 43,930,614 letters: 4 cost = 13,240 on both
sides).  The parser, the run table and the cover of a class are taken over from an earlier program of this project,
so they are not an independent check.  There is one implementation of the block programme.  Not refereed.

Needs: Python 3, numpy, top.py, countn.py, tm.py.  No solver.
Time and memory: measured, one thread: 830 s and 3.08 GB without options; 560 s and 3.11 GB with --slack 4 --kmax 40.
"""
import sys
import time
import numpy as np
import top

BIG = 10 ** 9


def main():
    log = lambda *x: print(*x, flush=True)
    base = sys.argv[1]
    opt = lambda k, d: type(d)(sys.argv[sys.argv.index(k) + 1]) if k in sys.argv else d
    T = top.Top(base, cmax=4, log=log)
    F = T.F
    t0 = time.time()
    sc = F.sc
    NC = len(sc)
    loc = np.full(F.V, -1, np.int64); loc[sc] = np.arange(NC)
    tr = F.ct[sc]
    lev_top = max(v for v in F.Lt if F.Lt[v] < F.NS)
    cls = F.tlab[lev_top]
    csize = int(np.bincount(cls[F.small_t]).max())
    LOW = max(v for v in F.Lc if F.Lc[v] < csize)
    ncls = len(np.unique(cls[F.small_t]))
    dm = ~F.same
    A, Bn, Wv = loc[F.pa[dm]], loc[F.pb[dm]], F.pw[dm]
    low = Wv < LOW
    comp = F.components(NC, A[low], Bn[low])
    key = comp * F.NT + tr
    uk = np.unique(key)
    ucomp = uk // F.NT
    first = np.searchsorted(ucomp, ucomp, "left")
    rank_u = np.arange(len(uk)) - first
    lt = rank_u[np.searchsorted(uk, key)]
    kmax = int(lt.max()) + 1
    assert kmax <= 8
    same_cls = cls[tr[A]] == cls[tr[Bn]]
    assert not (low & ~same_cls).any()
    CAP = F.wcap
    beta = F.beta
    lbI_in = np.full(NC, CAP, np.int64); lbI_out = np.full(NC, CAP, np.int64)
    mI = same_cls & ~low
    np.minimum.at(lbI_in, Bn[mI], Wv[mI]); np.minimum.at(lbI_out, A[mI], Wv[mI])
    E_in = np.full(NC, min(CAP, beta), np.int64); E_out = np.full(NC, min(CAP, beta), np.int64)
    mE = ~same_cls
    np.minimum.at(E_in, Bn[mE], np.minimum(Wv[mE], beta)); np.minimum.at(E_out, A[mE], np.minimum(Wv[mE], beta))
    H = lambda a: {int(k): int(v) for k, v in zip(*np.unique(a, return_counts=True))}
    log("top classes %d of %d trails; LOW = %d; prices of an E end: in %s out %s" % (ncls, csize, LOW, H(E_in),
        H(E_out)))
    a_, b_, w2 = A[low], Bn[low], (2 * Wv[low]).astype(np.int32)
    bitb = (1 << lt[b_]).astype(np.int64); bita = (1 << lt[a_]).astype(np.int64)
    BIGV = np.int32(30000)
    nm = 1 << kmax
    pop = np.array([bin(S).count("1") for S in range(nm)])

    def vtables(E_in, E_out, slack=False):
        """V[k][t_in][t_out] for given prices of the E ends, by a programme over the subsets of the at most 8
        trails of every component of the joins with W < LOW, all components at once.  With slack=True also, for
        every cut, the smallest (val - V) over the runs that end (s_out) or start (s_in) there with an E end at
        that cut, by the type of the other end; the runs that start at a cut come from the same programme run
        backwards, and the two programmes are asserted to agree."""
        V = {}
        s_out = {}
        for tin, lbin in (("I", lbI_in), ("E", E_in)):
            g = np.full((nm, NC), BIGV, np.int32)
            g[1 << lt, np.arange(NC)] = lbin.astype(np.int32)
            for S in range(1, nm):
                cur = g[S]
                if int(cur.min()) >= BIGV:
                    continue
                ok = (bitb & S) == 0
                ok &= cur[a_] < BIGV
                if not ok.any():
                    continue
                aa, bb, ww = a_[ok], b_[ok], w2[ok]
                tgt = S | bitb[ok]
                for Tm in np.unique(tgt).tolist():
                    s_ = tgt == Tm
                    np.minimum.at(g[Tm], bb[s_], cur[aa[s_]] + ww[s_])
            for tout, lbout in (("I", lbI_out), ("E", E_out)):
                best = np.full(nm, BIG, np.int64)
                for S in range(1, nm):
                    m_ = g[S] < BIGV
                    if m_.any():
                        best[S] = int((g[S][m_].astype(np.int64) + lbout[m_]).min())
                for k in range(1, kmax + 1):
                    V[(k, tin, tout)] = int(best[pop == k].min())
            if slack:
                so = np.full(NC, BIG, np.int64)
                for S in range(1, nm):
                    m_ = g[S] < BIGV
                    if m_.any():
                        so[m_] = np.minimum(so[m_], g[S][m_].astype(np.int64) + E_out[m_] - V[(int(pop[S]), tin, "E")])
                s_out[tin] = so
            del g
        if not slack:
            return V
        s_in = {}
        for tout, lbout in (("I", lbI_out), ("E", E_out)):
            g = np.full((nm, NC), BIGV, np.int32)                  # runs that START at the cut
            g[1 << lt, np.arange(NC)] = lbout.astype(np.int32)
            for S in range(1, nm):
                cur = g[S]
                if int(cur.min()) >= BIGV:
                    continue
                ok = (bita & S) == 0
                ok &= cur[b_] < BIGV
                if not ok.any():
                    continue
                aa, bb, ww = a_[ok], b_[ok], w2[ok]
                tgt = S | bita[ok]
                for Tm in np.unique(tgt).tolist():
                    s_ = tgt == Tm
                    np.minimum.at(g[Tm], aa[s_], cur[bb[s_]] + ww[s_])
            si = np.full(NC, BIG, np.int64)
            for S in range(1, nm):
                m_ = g[S] < BIGV
                if m_.any():
                    val = g[S][m_].astype(np.int64) + E_in[m_]
                    assert int(val.min()) >= V[(int(pop[S]), "E", tout)], "backward and forward programme disagree"
                    si[m_] = np.minimum(si[m_], val - V[(int(pop[S]), "E", tout)])
            s_in[tout] = si
            del g
        return V, s_in, s_out

    cap = opt("--slack", 0)
    if cap > 0:
        V, s_in, s_out = vtables(E_in, E_out, slack=True)
        div = 1 if "--full" in sys.argv else 2
        d_in = np.minimum(np.minimum(s_in["I"], s_in["E"] // div), cap)
        d_out = np.minimum(np.minimum(s_out["I"], s_out["E"] // div), cap)
        log("slack of the E ends: lowering e_in by %s, e_out by %s" % (H(d_in), H(d_out)))
        E_in = E_in - d_in; E_out = E_out - d_out
        V2 = vtables(E_in, E_out)
        worse = {k_: (V[k_], V2[k_]) for k_ in V if V2[k_] < V[k_]}
        log("run table with the lower prices: %s" % ("unchanged" if not worse else "LOWER at %s" % worse))
        V = V2
    else:
        V = vtables(E_in, E_out)
    for k in range(1, kmax + 1):
        log("   V[k = %d]:  I,I %d   I,E %d   E,I %d   E,E %d" % (k, V[(k, "I", "I")], V[(k, "I", "E")], V[(k, "E",
            "I")], V[(k, "E", "E")]))
    NBT = len(F.big_t)
    EMAX = 2 * (ncls + NBT) + 4
    Cx = np.full((csize + 1, EMAX + 1), BIG, np.int64)
    Cx[0, 0] = 0
    for j in range(1, csize + 1):
        for k in range(1, min(kmax, j) + 1):
            for ti in "IE":
                for to in "IE":
                    ne = (ti == "E") + (to == "E")
                    v = V[(k, ti, to)]
                    prev = Cx[j - k]
                    cand = np.full(EMAX + 1, BIG, np.int64)
                    cand[ne:] = prev[:EMAX + 1 - ne] + v
                    Cx[j] = np.minimum(Cx[j], cand)
    Cc = Cx[csize]
    log("cover of a class of %d trails with exactly e E ends, e = 0..12: %s" % (csize, Cc[:13].tolist()))
    # f(N): the classes together have N E ends, every class at least 2
    NMAX = 2 * (ncls + NBT) + 2
    f = np.full(NMAX + 1, BIG, np.int64)
    f[0] = 0
    for c in range(ncls):
        nf = np.full(NMAX + 1, BIG, np.int64)
        for e in range(2, min(EMAX, NMAX) + 1):
            if Cc[e] >= BIG:
                continue
            nf[e:] = np.minimum(nf[e:], f[:NMAX + 1 - e] + Cc[e])
        f = nf
    log("classes with N E ends in all: f(96) = %d, f(98) = %d, f(100) = %d, f(120) = %d" % (int(f[96]), int(f[98]),
        int(f[100]), int(f[120])))
    # blocks
    sm = sc; bg = F.BC
    ein = np.zeros(T.V, np.int64); eout = np.zeros(T.V, np.int64)
    ein[sm] = E_in; eout[sm] = E_out
    lab_sb = T.is_small.astype(np.int64)
    o_end = T.out_best(-ein[sm], X=bg, Y=sm, lab=lab_sb, scale=2)
    v = T.in_best(-eout[sm], X=sm, Y=bg, lab=lab_sb, scale=2)
    vs = 2 * T.D[bg].astype(np.int64)
    kmaxb = opt("--kmax", NBT)
    Y, Ys, Ye = [None], [None], [None]
    for k in range(1, kmaxb + 1):
        Y.append(int((v + o_end).min())); Ys.append(int((vs + o_end).min())); Ye.append(int((v + 2 * T.D[bg]).min()))
        if k % 8 == 0:
            log("   blocks up to %d big cuts done: Y %s  (%.0fs)" % (k, Y[max(1, k - 7):k + 1], time.time() - t0))
        if k < kmaxb:
            v = T.in_best(v, X=bg, Y=bg, scale=2)
            vs = T.in_best(vs, X=bg, Y=bg, scale=2)
    mv, mvs, mo = int(v.min()), int(vs.min()), int(o_end.min())
    S0 = int((2 * T.D[sm] - ein[sm]).min()); E0 = int((2 * T.D[sm] - eout[sm]).min())
    log("Y_k: %s" % Y[1:])
    log("Ys_k: %s ; no block %d" % (Ys[1:], S0))
    log("Ye_k: %s ; no block %d" % (Ye[1:], E0))
    if kmaxb < NBT:
        # longer blocks: a block of k > kmaxb cuts holds a block of kmaxb cuts and joins of W >= 1 (2 doubled)
        # every join between big cuts of different trails has W >= 1: the k-th cut is reached at >= mv + 2 (k - kmaxb)
        assert int(T.in_best(np.zeros(len(bg), np.int64), X=bg, Y=bg, scale=2).min()) >= 2
        for k in range(kmaxb + 1, NBT + 1):
            Y.append(mv + 2 * (k - kmaxb) + mo); Ys.append(mvs + 2 * (k - kmaxb) + mo); Ye.append(mv + 2 * (k - kmaxb))
        log("blocks of more than %d cuts: Y_k >= %d + 2 (k - %d) + %d, Ys_k >= %d + 2 (k - %d) + %d, Ye_k >= %d + 2 (k - %d)" % (
            kmaxb, mv, kmaxb, mo, mvs, kmaxb, mo, mv, kmaxb))
    # inner[q][j]: cheapest way to put j big trails into exactly q inner blocks
    INF = BIG
    inner = np.full((NBT + 1, NBT + 1), INF, np.int64)
    inner[0, 0] = 0
    Yarr = np.array([INF] + Y[1:], np.int64)
    for q in range(1, NBT + 1):
        for j in range(q, NBT + 1):
            ks = np.arange(1, j - (q - 1) + 1)
            inner[q, j] = int((inner[q - 1, j - ks] + Yarr[ks]).min())
    best = INF
    arg = None
    for ks in range(0, NBT + 1):
        for ke in range(0, NBT + 1 - ks):
            j = NBT - ks - ke
            st = (S0 if ks == 0 else Ys[ks]) + (E0 if ke == 0 else Ye[ke])
            for q in range(0 if j == 0 else 1, j + 1):
                N = 2 * max(ncls - 1, q) + 2
                val = st + int(inner[q, j]) + int(f[N:].min())
                if val < best:
                    best, arg = val, (ks, ke, q, N)
    two = -(-best // 2)
    cost = (two + 1) // 2
    log("cheapest: %d big trails in a start block, %d in an end block, %d inner blocks, %d E ends" % arg)
    old = ncls * int(Cc[2:].min()) - 2 * beta
    log("BOUND single-port narrow (run, class and block programme): 4 cost >= %d  ->  2 cost >= %d, cost >= %d, length >= %d   (run and class programme alone: 4 cost >= %d)  (%.0fs)" % (
        best, two, cost, F.B.base_const + cost, old, time.time() - t0))


if __name__ == "__main__":
    main()
