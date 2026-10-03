#!/usr/bin/env python
"""Trail-level re-joining of Pantone-type superpermutation words with non-vertex openings
(the operation behind rumstd's n=10 word 4,034,873; see the README).

Model.  A Pantone-type word is a concatenation of closed trails T (cyclic words of length R_T whose consecutive
permutation windows are 1, 2 or 3 apart), each written once (or in a few segments), joined with overlaps.
Opening T at the cut between consecutive windows p_i -> p_{i+1} (gap g) writes T as a piece of length R + n - g,
starting with the h-word s = first h letters of window p_{i+1} and ending with e = last h letters of window p_i
(h = n-3).  g = 3: a row vertex (s == e, extra cost 0).  g = 2: the boundary between two 2-cycles inside a row
(e = s shifted by one letter, extra cost 1 -- it acts as a connector step that also absorbs T).  If the window
between two cuts is a duplicate covered elsewhere, it can be skipped ("dup-skip" option, extra cost 3 - g1 - g2).
Joining piece A to piece B with the maximal suffix/prefix overlap of their h-words costs d(e_A, s_B) = h - overlap
letters.  Hence
    L = h + sum R_T + sum(extra opening costs) + sum_joins d(e_A, s_B).
This is a generalised TSP over trails (one option per trail); Pantone only uses g = 3 openings.  The script
extracts the trails and all openings from a word, reads the current sequence, and runs a destroy/repair local
search (remove k trails, reinsert each with the best option and position).

usage: connector_splice.py WORD.txt OUT.txt [--time SEC] [--seed S] [--kmax K] [--T0 TEMP] [--noskip]
                           [--start WORD2.txt] [--chunk A:B] [--attach] [--rlns SEC]
OUT.txt.ckpt holds the best word found so far (rewritten at most once a minute).

WORD must split into whole trails at its steps of weight >= 4, as Pantone's words do.  A word produced by this
search usually does not (zero-cost joins merge neighbouring pieces), so to continue from one pass the original word
as WORD and the improved word with --start.
"""
import argparse
import random
import sys
import time

import numpy as np

ALPH = "0123456789ABCDEF"


def load(path):
    s = open(path, "rb").read().strip()
    a = np.frombuffer(s, dtype=np.uint8).copy()
    lut = np.full(256, 255, np.uint8)
    for i, c in enumerate(ALPH.encode()):
        lut[c] = i
    a = lut[a]
    assert (a != 255).all()
    return a


def perm_positions(w, n, chunk=1 << 22):
    """start positions of windows that are permutations (chunked to keep memory low)"""
    L = len(w)
    out = []
    full = (1 << n) - 1
    for a in range(0, L - n + 1, chunk):
        b = min(L - n + 1, a + chunk)
        m = np.zeros(b - a, np.int32)
        for k in range(n):
            m |= (np.int32(1) << w[a + k:b + k].astype(np.int32))
        out.append(np.nonzero(m == full)[0].astype(np.int64) + a)
    return np.concatenate(out)


def hcodes(arr, n, h):
    """code of every h-gram of arr (base n)"""
    m = len(arr) - h + 1
    c = np.zeros(m, np.int64)
    for k in range(h):
        c = c * n + arr[k:k + m]
    return c


def perm_rank_keys(arr, pos, n):
    """injective int64 key of the n-letter window at each pos (base-n digits)"""
    c = np.zeros(len(pos), np.int64)
    for k in range(n):
        c = c * n + arr[pos + k]
    return c


class Model:
    def __init__(self, w, use_skip=True, log=print):
        self.w = w
        n = int(w.max()) + 1
        h = n - 3
        self.n, self.h = n, h
        self.pw = [n ** k for k in range(h + 1)]
        t0 = time.time()
        pos = perm_positions(w, n)
        gaps = np.diff(pos)
        cut = np.nonzero(gaps >= 4)[0]
        first = np.concatenate([[0], cut + 1])
        last = np.concatenate([cut, [len(pos) - 1]])
        ps = pos[first]
        pl = pos[last] + n - ps
        log("n=%d L=%d perm windows %d pieces %d (%.1fs)" % (n, len(w), len(pos), len(ps), time.time() - t0))
        self.piece_start, self.piece_len = ps, pl
        # closed pieces and chains of open pieces -> trails
        closed = np.zeros(len(ps), bool)
        extra = np.zeros(len(ps), np.int64)   # piece written from a gap-(3-extra) opening: length R + h + extra
        for k in range(len(ps)):
            s, l = int(ps[k]), int(pl[k])
            for ex in (0, 1, 2):
                R = l - h - ex
                if R > 2 * n and (w[s + R:s + l] == w[s:s + h + ex]).all():
                    closed[k] = True; extra[k] = ex; break
        self.trail_of_piece = np.full(len(ps), -1, np.int64)
        trails = []  # list of (list of (piece, len_contrib))
        for k in np.nonzero(closed)[0]:
            self.trail_of_piece[k] = len(trails)
            trails.append([int(k)])
        openp = [int(k) for k in np.nonzero(~closed)[0]]
        code = lambda a: int(sum(int(x) * self.pw[h - 1 - i] for i, x in enumerate(a)))
        head = {}
        for k in openp:
            head.setdefault(code(w[ps[k]:ps[k] + h]), []).append(k)
        used = set()
        for k in openp:
            if k in used:
                continue
            chain = [k]
            used.add(k)
            hw = code(w[ps[k]:ps[k] + h])
            while True:
                tw = code(w[ps[chain[-1]] + pl[chain[-1]] - h:ps[chain[-1]] + pl[chain[-1]]])
                if tw == hw:
                    break
                nx = [j for j in head.get(tw, []) if j not in used]
                if not nx:
                    raise RuntimeError("open piece %d cannot be chained into a closed trail" % k)
                chain.append(nx[0])
                used.add(nx[0])
            for j in chain:
                self.trail_of_piece[j] = len(trails)
            trails.append(chain)
        self.trails_pieces = trails
        self.cyc = []
        for ch in trails:
            parts = [w[ps[j]:ps[j] + pl[j] - h - extra[j]] for j in ch]
            self.cyc.append(np.concatenate(parts) if len(parts) > 1 else parts[0])
        self.R = np.array([len(c) for c in self.cyc], np.int64)
        log("trails %d (closed pieces %d, chained open pieces %d), sum R %d" % (len(trails), closed.sum(), len(openp), self.R.sum()))
        # duplicate windows (global)
        allkeys = []
        tw_pos = []
        for t, c in enumerate(self.cyc):
            R = len(c)
            ext = np.concatenate([c, c[:n]])
            p = perm_positions(ext, n)
            p = p[p < R]
            tw_pos.append(p)
            allkeys.append(perm_rank_keys(ext, p, n))
        ak = np.concatenate(allkeys)
        u, cnt = np.unique(ak, return_counts=True)
        log("trail windows %d distinct %d (n! check: %s)" % (len(ak), len(u), len(u) == int(np.prod(np.arange(1, n + 1)))))
        dupkeys = u[cnt > 1]
        # options
        S, E, D, T, C, SK = [], [], [], [], [], []
        nskip = {}
        for t, c in enumerate(self.cyc):
            R = len(c)
            ext = np.concatenate([c, c[:n + h]])
            hc = hcodes(ext, n, h)
            p = tw_pos[t]
            m = len(p)
            g = np.diff(np.append(p, p[0] + R))
            nxt = np.roll(p, -1)
            # plain cuts with g in {2,3}
            sel = np.nonzero(g >= 2)[0]
            S.append(hc[nxt[sel]]); E.append(hc[p[sel] + 3]); D.append(3 - g[sel]); T.append(np.full(len(sel), t))
            C.append(sel * 4 + 0); SK.append(np.full(len(sel), -1, np.int64))
            if use_skip:
                isdup = np.isin(allkeys[t], dupkeys)
                # skip window i+1 (dup): cut from window i to window i+2
                i1 = np.nonzero(np.roll(isdup, -1))[0]
                g2 = g[i1] + g[(i1 + 1) % m]
                ok = g2 >= 2
                i1, g2 = i1[ok], g2[ok]
                S.append(hc[p[(i1 + 2) % m]]); E.append(hc[p[i1] + 3]); D.append(3 - g2); T.append(np.full(len(i1), t))
                C.append(i1 * 4 + 1); SK.append(allkeys[t][(i1 + 1) % m])
                for x in (3 - g2).tolist():
                    nskip[x] = nskip.get(x, 0) + 1
        self.S = np.concatenate(S); self.E = np.concatenate(E); self.D = np.concatenate(D).astype(np.int64)
        self.T = np.concatenate(T); self.C = np.concatenate(C); self.SK = np.concatenate(SK)
        self.tw_pos = tw_pos
        order = np.argsort(self.T, kind="stable")
        for a in ("S", "E", "D", "T", "C", "SK"):
            setattr(self, a, getattr(self, a)[order])
        self.opt_lo = np.searchsorted(self.T, np.arange(len(trails)), "left")
        self.opt_hi = np.searchsorted(self.T, np.arange(len(trails)), "right")
        vals, cnts = np.unique(self.D, return_counts=True)
        log("options %d by extra cost %s; dup-skip options by extra cost %s" % (len(self.S), dict(zip(vals.tolist(), cnts.tolist())), dict(sorted(nskip.items()))))
        # current sequence of events (one per piece)
        self.events = []
        for k in range(len(ps)):
            s, l = int(ps[k]), int(pl[k])
            self.events.append(dict(t=int(self.trail_of_piece[k]), s=code(w[s:s + h]), e=code(w[s + l - h:s + l]), l=l, piece=k, opt=None, skip=-1))

    # ---- costs
    def dist(self, e, s):
        """h - max overlap of h-words e (suffix) and s (prefix); arrays allowed"""
        h, pw = self.h, self.pw
        e = np.asarray(e); s = np.asarray(s)
        d = np.full(np.broadcast(e, s).shape, h, np.int64)
        for k in range(1, h + 1):
            m = (e % pw[k]) == (s // pw[h - k])
            d = np.where(m, h - k, d)
        return d

    def length(self, ev):
        L = sum(x["l"] for x in ev)
        es = np.array([x["e"] for x in ev[:-1]]); ss = np.array([x["s"] for x in ev[1:]])
        return int(L - (self.h - self.dist(es, ss)).sum())

    # ---- spelling
    def option_piece(self, o):
        t = int(self.T[o]); c = self.cyc[t]; R = len(c); p = self.tw_pos[t]; m = len(p)
        i, kind = divmod(int(self.C[o]), 4)
        start = p[(i + 1 + kind) % m]
        ln = R + self.n - (3 - int(self.D[o]))
        idx = (start + np.arange(ln)) % R
        return c[idx]

    def spell(self, ev):
        out = []
        tail = None
        for x in ev:
            if x.get("seg") is not None:
                t, st, ln = x["seg"]
                c = self.cyc[t]
                pc = c[(st + np.arange(ln)) % len(c)]
            elif x["opt"] is None:
                k = x["piece"]
                pc = self.w[self.piece_start[k]:self.piece_start[k] + self.piece_len[k]]
            else:
                pc = self.option_piece(x["opt"])
            if tail is not None:
                ov = self.h - int(self.dist(int(tail), x["s"]))
                out.append(pc[ov:])
            else:
                out.append(pc)
            tail = x["e"]
        return np.concatenate(out)


def _ranges(a, b):
    """indices concatenating ranges [a_i, b_i) and the owner i of each"""
    cnt = b - a
    own = np.repeat(np.arange(len(a)), cnt)
    start = np.repeat(a - np.concatenate([[0], np.cumsum(cnt)[:-1]]), cnt)
    return own, start + np.arange(cnt.sum())


def best_insertion(M, ev, t, skipped, K=3, arrays=None, rng=None, noise=0.0):
    """best (delta, position, option) to insert trail t into event list ev (insert before index pos).
    delta = extra letters (opening cost + new joins - old join), R_t excluded."""
    h, pw = M.h, M.pw
    lo, hi = M.opt_lo[t], M.opt_hi[t]
    S, E, D, SK = M.S[lo:hi], M.E[lo:hi], M.D[lo:hi], M.SK[lo:hi]
    if arrays is None:
        eA = np.array([x["e"] for x in ev], np.int64)
        sB = np.array([x["s"] for x in ev], np.int64)
        Dj = M.dist(eA[:-1], sB[1:])
    else:
        eA, sB, Dj = arrays
    cache = getattr(M, "_sortcache", None)
    if cache is None:
        cache = M._sortcache = {}
    JJ, OI = [], []
    for j in range(0, K + 1):
        key = ("s", t, j)
        if key not in cache:
            ks = S // pw[j]
            o = np.argsort(ks, kind="stable")
            cache[key] = (ks[o], o)
        ks, o = cache[key]
        q = eA[:-1] % pw[h - j]
        a = np.searchsorted(ks, q, "left"); b = np.searchsorted(ks, q, "right")
        own, ii = _ranges(a, b)
        JJ.append(own); OI.append(o[ii])
        key = ("e", t, j)
        if key not in cache:
            ke = E % pw[h - j]
            o = np.argsort(ke, kind="stable")
            cache[key] = (ke[o], o)
        ke, o = cache[key]
        q = sB[1:] // pw[j]
        a = np.searchsorted(ke, q, "left"); b = np.searchsorted(ke, q, "right")
        own, ii = _ranges(a, b)
        JJ.append(own); OI.append(o[ii])
    jj = np.concatenate(JJ); oi = np.concatenate(OI)
    if skipped and len(oi):
        ok = (SK[oi] < 0) | ~np.isin(SK[oi], np.fromiter(skipped, np.int64))
        jj, oi = jj[ok], oi[ok]
    if not len(oi):
        k = int(np.argmin(D))
        return (int(M.dist(eA[-1], S[k]) + D[k]), len(ev), int(lo + k))
    val = M.dist(eA[jj], S[oi]) + D[oi] + M.dist(E[oi], sB[jj + 1]) - Dj[jj]
    if noise and rng is not None:
        if len(val) < 2000:
            val = val + noise * np.array([rng.random() for _ in range(len(val))])
        else:
            val = val + noise * np.random.default_rng(rng.randrange(1 << 30)).random(len(val))
    k = int(np.argmin(val))
    return (int(round(float(val[k]))), int(jj[k]) + 1, int(lo + oi[k]))


def seg_events(M, c1, c2):
    """two events for trail T split at plain cuts c1 (start of seg1) and c2 (end of seg1)"""
    t = int(M.T[c1]); R = int(M.R[t]); p = M.tw_pos[t]; m = len(p); n = M.n
    i1 = int(M.C[c1]) // 4; i2 = int(M.C[c2]) // 4
    st1 = int(p[(i1 + 1) % m]); en1 = int(p[i2]); l1 = (en1 - st1) % R + n
    st2 = int(p[(i2 + 1) % m]); en2 = int(p[i1]); l2 = (en2 - st2) % R + n
    e1 = dict(t=t, s=int(M.S[c1]), e=int(M.E[c2]), l=l1, piece=None, opt=None, skip=-1, seg=(t, st1, l1))
    e2 = dict(t=t, s=int(M.S[c2]), e=int(M.E[c1]), l=l2, piece=None, opt=None, skip=-1, seg=(t, st2, l2))
    return e1, e2


def best_split_insertion(M, ev, t, arrays, maxv=400, rng=None):
    """insert trail t as two segments wrapped around a block ev[i..j-1]: ..., ev[i-1], seg1, ev[i..j-1], seg2, ev[j], ...
    seg1 ends and seg2 starts at a vertex v of t (plain gap-3 cut c2); seg1 starts / seg2 ends at any plain cut c1.
    returns (delta, i, j, c1, c2) or None"""
    h, pw = M.h, M.pw
    eA, sB, Dj = arrays
    lo, hi = M.opt_lo[t], M.opt_hi[t]
    vid = np.nonzero((M.D[lo:hi] == 0) & (M.C[lo:hi] % 4 == 0))[0] + lo
    if len(vid) > maxv:
        vid = np.array(sorted((rng or random).sample(list(vid), maxv)))
    N = len(ev)
    pairs = []   # (c2, i, j, const)
    # i: d(v, s_i) <= 1 ; j: d(e_{j-1}, v) <= 1
    kS = {}
    for idx in range(1, N - 1):
        kS.setdefault(int(sB[idx]) // pw[1], []).append(idx)
        kS.setdefault(("x", int(sB[idx])), []).append(idx)
    kE = {}
    for idx in range(0, N - 1):
        kE.setdefault(int(eA[idx]) % pw[h - 1], []).append(idx)
        kE.setdefault(("x", int(eA[idx])), []).append(idx)
    for c2 in vid.tolist():
        v = int(M.S[c2])
        I = set(kS.get(("x", v), [])) | set(kS.get(v % pw[h - 1], []))
        if not I:
            continue
        J = set(kE.get(("x", v), [])) | set(kE.get(v // pw[1], []))
        if not J:
            continue
        for i in I:
            dvi = int(M.dist(v, sB[i]))
            for jm in J:
                j = jm + 1
                if j <= i or j >= N:
                    continue
                const = dvi + int(M.dist(eA[jm], v)) - int(Dj[i - 1]) - int(Dj[jm])
                pairs.append((c2, i, j, const))
    if not pairs:
        return None
    pairs.sort(key=lambda z: z[3])
    pairs = pairs[:64]
    P = len(pairs)
    eA2 = np.zeros(2 * P + 1, np.int64); sB2 = np.zeros(2 * P + 1, np.int64); Dj2 = np.full(2 * P, -10 ** 6, np.int64)
    for k, (c2, i, j, const) in enumerate(pairs):
        eA2[2 * k] = eA[i - 1]; sB2[2 * k + 1] = sB[j]; Dj2[2 * k] = -const
    val, pos, c1 = best_insertion(M, [None] * (2 * P + 1), t, None, arrays=(eA2, sB2, Dj2))
    if val > 10 ** 5:
        return None
    k = (pos - 1) // 2
    if (pos - 1) % 2 or k >= P:
        return None
    c2, i, j, const = pairs[k]
    if c1 == c2 or M.C[c1] % 4 != 0:
        return None
    return (val, i, j, c1, c2)


def make_event(M, o):
    t = int(M.T[o])
    return dict(t=t, s=int(M.S[o]), e=int(M.E[o]), l=int(M.R[t] + M.h + M.D[o]), piece=None, opt=o, skip=int(M.SK[o]))


def lns(M, ev, tlimit, seed=1, kmax=6, log=print, T0=1.5, big=None, split=True, splitmax=3000, prel=0.4, ckpt=None, fixed=()):
    """destroy/repair local search with simulated-annealing acceptance.
    destroy: (a) consecutive events around an expensive join, (b) random trails, (c) trails related by words."""
    rng = random.Random(seed)
    cur = M.length(ev)
    best_len = cur
    best_ev = list(ev)
    t0 = time.time()
    it = acc = 0
    h = M.h
    last_ck = 0.0
    while time.time() - t0 < tlimit:
        it += 1
        frac = (time.time() - t0) / tlimit
        temp = T0 * (1 - frac) + 0.05
        es = np.array([x["e"] for x in ev[:-1]]); ss = np.array([x["s"] for x in ev[1:]])
        dj = M.dist(es, ss)
        k = rng.randint(1, kmax)
        rem = set()
        mode = rng.random()
        if mode < prel:
            # related-run removal: a seed run plus up to two runs whose end/start words are within d<=1 of
            # options of the seed run's trails (lets groups be merged into other runs, with re-chosen ends)
            rid = np.concatenate([[0], np.cumsum(dj >= 2)])
            nrun = int(rid[-1]) + 1
            sizes = np.bincount(rid, minlength=nrun)
            small_runs = np.nonzero(sizes <= 5)[0]
            X = int(small_runs[rng.randrange(len(small_runs))]) if (len(small_runs) and rng.random() < 0.7) else rng.randrange(nrun)
            xt = {ev[i]["t"] for i in np.nonzero(rid == X)[0].tolist()}
            Sx = np.concatenate([M.S[M.opt_lo[t]:M.opt_hi[t]] for t in xt]); Ex = np.concatenate([M.E[M.opt_lo[t]:M.opt_hi[t]] for t in xt])
            sset = set(Sx.tolist()) | set((Sx // M.pw[1]).tolist())
            eset = set(Ex.tolist()) | set((Ex % M.pw[h - 1]).tolist())
            ends = np.nonzero(np.diff(np.concatenate([rid, [nrun]])) != 0)[0]    # last event index of each run
            starts = np.concatenate([[0], ends[:-1] + 1])
            rel = []
            for r in range(nrun):
                if r == X:
                    continue
                e_end = ev[ends[r]]["e"]; s_st = ev[starts[r]]["s"]
                if e_end in sset or (e_end % M.pw[h - 1]) in sset or s_st in eset or (s_st // M.pw[1]) in eset:
                    rel.append(r)
            rng.shuffle(rel)
            pick = [X] + rel[:rng.randint(1, 2)]
            for r in pick:
                for i in range(starts[r], ends[r] + 1):
                    rem.add(ev[i]["t"])
        elif mode < 0.5 + prel / 2:
            cand = np.nonzero(dj >= 2)[0]
            j = int(cand[rng.randrange(len(cand))]) if len(cand) else rng.randrange(len(dj))
            lo = max(0, j - rng.randint(0, k))
            for i in range(lo, min(len(ev), lo + k)):
                rem.add(ev[i]["t"])
        elif mode < 0.75:
            for _ in range(k):
                rem.add(ev[rng.randrange(len(ev))]["t"])
        else:
            # two or three short segments at different places
            for _ in range(rng.randint(2, 3)):
                j = rng.randrange(len(ev))
                for i in range(j, min(len(ev), j + max(1, k // 2))):
                    rem.add(ev[i]["t"])
        if big is not None and rng.random() < 0.3:
            rem.add(big[rng.randrange(len(big))])
        rem -= set(fixed)
        if not rem:
            continue
        new = [x for x in ev if x["t"] not in rem]
        skipped = {x["skip"] for x in new if x["skip"] >= 0}
        pending = list(rem)
        rng.shuffle(pending)
        greedy = rng.random() < 0.5
        noise = 0.0 if rng.random() < 0.5 else 0.6
        while pending:
            eA = np.array([x["e"] for x in new], np.int64); sB = np.array([x["s"] for x in new], np.int64)
            arr = (eA, sB, M.dist(eA[:-1], sB[1:]))
            if greedy:
                bests = [(best_insertion(M, new, t, skipped, arrays=arr, rng=rng, noise=noise), t) for t in pending]
                (dv, p, o), t = min(bests, key=lambda z: (z[0][0], rng.random()))
            else:
                t = pending[0]
                dv, p, o = best_insertion(M, new, t, skipped, arrays=arr, rng=rng, noise=noise)
            sp = best_split_insertion(M, new, t, arr, rng=rng) if (split and M.opt_hi[t] - M.opt_lo[t] <= splitmax) else None
            if sp is not None and sp[0] < dv:
                _, i, j, c1, c2 = sp
                e1, e2 = seg_events(M, c1, c2)
                new.insert(j, e2)
                new.insert(i, e1)
            else:
                if fixed and (p == 0 or p >= len(new)):
                    p = 1
                x = make_event(M, o)
                new.insert(p, x)
                if x["skip"] >= 0:
                    skipped.add(x["skip"])
            pending.remove(t)
        nl = M.length(new)
        d = nl - cur
        if d <= 0 or rng.random() < np.exp(-d / temp):
            if nl < best_len:
                log("it %d t=%.0fs: best %d -> %d (removed %d trails)" % (it, time.time() - t0, best_len, nl, len(rem)))
            ev = new
            cur = nl
            acc += 1
            if cur < best_len:
                best_len, best_ev = cur, list(ev)
                if ckpt is not None and time.time() - last_ck > 60:
                    write_word(M, best_ev, ckpt, best_len); last_ck = time.time()
        if it % 200 == 0:
            log("it %d t=%.0fs cur %d best %d acc %d" % (it, time.time() - t0, cur, best_len, acc))
    log("LNS done: %d iterations, %d accepted, best %d" % (it, acc, best_len))
    return best_ev, best_len


def run_bounds(M, ev):
    es = np.array([x["e"] for x in ev[:-1]]); ss = np.array([x["s"] for x in ev[1:]])
    dj = M.dist(es, ss)
    cut = np.nonzero(dj >= 2)[0]
    st = np.concatenate([[0], cut + 1]); en = np.concatenate([cut, [len(ev) - 1]])
    return list(zip(st.tolist(), en.tolist()))


def chain_search(M, opts, start_word, need, forward=True, maxd=2, budget=None, nodes_cap=20000):
    """cheapest chain of options (one per trail in need) starting after word start_word (forward) or ending
    before it (backward). opts: dict with arrays S,E,D,T and lookup dicts. returns (cost, [option ids])"""
    h, pw = M.h, M.pw
    best = [budget if budget is not None else 10 ** 9, None]
    cnt = [0]
    def cands(word):
        out = []
        for d in range(0, maxd + 1):
            key = (word % pw[h - d]) if forward else (word // pw[d])
            for o in opts["fw" if forward else "bw"][d].get(key, ()):
                out.append((d, o))
        return out
    def rec(word, left, cost, path):
        cnt[0] += 1
        if cnt[0] > nodes_cap:
            return
        if not left:
            if cost < best[0]:
                best[0], best[1] = cost, list(path)
            return
        if cost + len(left) >= best[0]:
            return
        cs_ = sorted(((d + int(opts["D"][o]), o) for d, o in cands(word) if int(opts["T"][o]) in left), key=lambda z: z[0])
        for c, o in cs_:
            t = int(opts["T"][o])
            path.append(o)
            rec(int(opts["E"][o]) if forward else int(opts["S"][o]), left - {t}, cost + c, path)
            path.pop()
    rec(start_word, frozenset(need), 0, [])
    if best[1] is None:
        return None
    return best[0], (best[1] if forward else best[1][::-1])


def group_opts(M, trails, maxd=2):
    h, pw = M.h, M.pw
    ids = np.concatenate([np.arange(M.opt_lo[t], M.opt_hi[t]) for t in trails])
    ids = ids[(M.C[ids] % 4) == 0]
    S, E, D, T = M.S[ids], M.E[ids], M.D[ids], M.T[ids]
    fw = [dict() for _ in range(maxd + 1)]; bw = [dict() for _ in range(maxd + 1)]
    for k in range(len(ids)):
        s_, e_ = int(S[k]), int(E[k])
        for d in range(maxd + 1):
            fw[d].setdefault(s_ // pw[d], []).append(k)        # word w reaches k with d steps if w % pw[h-d] == S//pw[d]
            bw[d].setdefault(e_ % pw[h - d], []).append(k)     # k reaches word w with d steps if E % pw[h-d] == w//pw[d]
    return dict(ids=ids, S=S, E=E, D=D, T=T, fw=fw, bw=bw)


def attach_pass(M, ev, log=print, maxgroup=8, rng=None):
    """dissolve standalone big-trail runs: attach them as a cheap chain to a closed small-trail run that is
    re-opened ("wrapped") at a cut c1 of one of its trails (rumstd's n=10 move). Applies improving moves."""
    h, pw = M.h, M.pw
    cur = M.length(ev)
    improved = True
    total_gain = 0
    while improved:
        improved = False
        rb = run_bounds(M, ev)
        cnt = {}
        for x in ev:
            cnt[x["t"]] = cnt.get(x["t"], 0) + 1
        # closed small runs usable for wrapping
        wraps = []   # (run index, event index p, c1 array, c2)
        for ri, (a_, b_) in enumerate(rb):
            blk = ev[a_:b_ + 1]
            if len(blk) < 3 or any(cnt[x["t"]] != 1 for x in blk):
                continue
            if int(M.dist(blk[-1]["e"], blk[0]["s"])) != 1:
                continue
            for p_, x in enumerate(blk):
                c2 = x["opt"] if x["opt"] is not None else match_option(M, x)
                if c2 is None or M.D[c2] != 0:
                    continue
                t = x["t"]
                ids = np.arange(M.opt_lo[t], M.opt_hi[t])
                ids = ids[((M.C[ids] % 4) == 0) & (ids != c2)]
                wraps.append((ri, p_, ids, c2))
        if not wraps:
            break
        allc1 = np.concatenate([w_[2] for w_ in wraps]); owner = np.concatenate([np.full(len(w_[2]), k) for k, w_ in enumerate(wraps)])
        groups = [ri for ri, (a_, b_) in enumerate(rb) if b_ - a_ + 1 <= maxgroup and all(M.R[x["t"]] > 5000 for x in ev[a_:b_ + 1])]
        if rng is not None:
            rng.shuffle(groups)
        best = (0, None)
        stat = [0, 0, 10 ** 9]
        for gi in groups:
            a_, b_ = rb[gi]
            if any(cnt[x["t"]] != 1 for x in ev[a_:b_ + 1]):
                continue
            gtr = [x["t"] for x in ev[a_:b_ + 1]]
            go = group_opts(M, gtr)
            keysS0 = set(go["S"].tolist()); keysS1 = set((go["S"] // pw[1]).tolist())
            keysE0 = set(go["E"].tolist()); keysE1 = set((go["E"] % pw[h - 1]).tolist())
            Ew = M.E[allc1]; Sw = M.S[allc1]
            okE = np.isin(Ew, list(keysS0)) | np.isin(Ew % pw[h - 1], list(keysS1))
            okS = np.isin(Sw, list(keysE0)) | np.isin(Sw // pw[1], list(keysE1))
            for k in np.nonzero(okE | okS)[0].tolist():
                ri, p_, _, c2 = wraps[owner[k]]
                if ri == gi:
                    continue
                c1 = int(allc1[k])
                for fwd in ((True,) if okE[k] and not okS[k] else (False,) if not okE[k] else (True, False)):
                    res = chain_search(M, go, int(M.E[c1]) if fwd else int(M.S[c1]), set(gtr), forward=fwd, budget=len(gtr) + 3)
                    stat[0] += 1
                    if res is None:
                        continue
                    stat[1] += 1
                    ccost, chain = res
                    ra, rb_ = rb[ri]
                    blk = ev[ra:rb_ + 1]
                    after = blk[p_ + 1:] + blk[:p_]
                    e1, e2 = seg_events(M, c1, c2)
                    chain_ev = [make_event(M, int(go["ids"][o])) for o in chain]
                    newblk = ([e1] + after + [e2] + chain_ev) if fwd else (chain_ev + [e1] + after + [e2])
                    new = []
                    for i, x in enumerate(ev):
                        if a_ <= i <= b_:
                            continue
                        if i == ra:
                            new.extend(newblk)
                        if ra <= i <= rb_:
                            continue
                        new.append(x)
                    nl = M.length(new)
                    stat[2] = min(stat[2], nl - cur)
                    if nl - cur < best[0]:
                        best = (nl - cur, new, (gi, ri, len(gtr), fwd, ccost))
        log("attach scan: %d groups, %d chain searches, %d chains, best delta %s" % (len(groups), stat[0], stat[1], stat[2]))
        if best[1] is not None:
            ev = best[1]; cur += best[0]; total_gain += -best[0]; improved = True
            log("attach: group run %d (%d trails) -> run %d (%s), chain cost %d, gain %d, now %d" % (best[2][0], best[2][2], best[2][1], "end" if best[2][3] else "start", best[2][4], -best[0], cur))
    return ev, cur


def blocklen(M, blk):
    L = sum(x["l"] for x in blk)
    for x, y in zip(blk[:-1], blk[1:]):
        L -= M.h - int(M.dist(x["e"], y["s"]))
    return L


class Unit:
    """a run (block of events) with alternative realizations: rotations and wraps of a closed run"""
    def __init__(self, M, blk, wraps=True, maxwrap=None):
        self.blk = blk
        self.base = blocklen(M, blk)
        S, E, X, K = [blk[0]["s"]], [blk[-1]["e"]], [0], [("base",)]
        cnt = {}
        for x in blk:
            cnt[x["t"]] = cnt.get(x["t"], 0) + 1
        k = len(blk)
        closed = k >= 2 and all(c == 1 for c in cnt.values()) and int(M.dist(blk[-1]["e"], blk[0]["s"])) <= 1
        if closed:
            cl = int(M.dist(blk[-1]["e"], blk[0]["s"]))
            for p_ in range(1, k):
                S.append(blk[p_]["s"]); E.append(blk[p_ - 1]["e"]); X.append(cl - int(M.dist(blk[p_ - 1]["e"], blk[p_]["s"]))); K.append(("rot", p_))
            if wraps:
                for p_, x in enumerate(blk):
                    c2 = x["opt"] if x["opt"] is not None else match_option(M, x)
                    if c2 is None or M.D[c2] != 0:
                        continue
                    t = x["t"]
                    ids = np.arange(M.opt_lo[t], M.opt_hi[t])
                    ids = ids[((M.C[ids] % 4) == 0) & (ids != c2)]
                    if maxwrap is not None and len(ids) > maxwrap:
                        continue
                    after = blk[p_ + 1:] + blk[:p_]
                    inner = blocklen(M, after) if after else 0
                    for c1 in ids.tolist():
                        e1, e2 = seg_events(M, c1, c2)
                        # e1 -> after[0] -> ... -> after[-1] -> e2
                        if after:
                            L = e1["l"] + inner + e2["l"] - (M.h - int(M.dist(e1["e"], after[0]["s"]))) - (M.h - int(M.dist(after[-1]["e"], e2["s"])))
                        else:
                            L = e1["l"] + e2["l"] - (M.h - int(M.dist(e1["e"], e2["s"])))
                        S.append(int(M.S[c1])); E.append(int(M.E[c1])); X.append(L - self.base); K.append(("wrap", p_, c1, c2))
        self.S = np.array(S, np.int64); self.E = np.array(E, np.int64); self.X = np.array(X, np.int64); self.K = K

    def realize(self, M, r):
        kind = self.K[r]
        blk = self.blk
        if kind[0] == "base":
            return list(blk)
        if kind[0] == "rot":
            return blk[kind[1]:] + blk[:kind[1]]
        _, p_, c1, c2 = kind
        e1, e2 = seg_events(M, c1, c2)
        return [e1] + blk[p_ + 1:] + blk[:p_] + [e2]


def rlns(M, units, seq, tlimit, seed=1, kmax=6, T0=0.3, log=print):
    """run-level destroy/repair: seq = list of (unit index, realization index)"""
    rng = random.Random(seed)
    h = M.h
    def total(sq):
        L = sum(units[u].base + int(units[u].X[r]) for u, r in sq)
        for (u1, r1), (u2, r2) in zip(sq[:-1], sq[1:]):
            L -= h - int(M.dist(units[u1].E[r1], units[u2].S[r2]))
        return L
    cur = total(seq); best = cur; best_seq = list(seq)
    t0 = time.time(); it = 0
    while time.time() - t0 < tlimit:
        it += 1
        temp = T0 * (1 - (time.time() - t0) / tlimit) + 0.02
        k = rng.randint(1, kmax)
        if rng.random() < 0.5:
            i0 = rng.randrange(len(seq)); idx = set(range(i0, min(len(seq), i0 + k)))
        else:
            idx = set(rng.sample(range(len(seq)), min(k, len(seq))))
        rem = [seq[i][0] for i in sorted(idx)]
        new = [x for i, x in enumerate(seq) if i not in idx]
        rng.shuffle(rem)
        for u in rem:
            U = units[u]
            eA = np.array([units[a].E[r] for a, r in new], np.int64)
            sB = np.array([units[a].S[r] for a, r in new], np.int64)
            # positions 0..len(new): before first, between, after last
            ePrev = np.concatenate([[-1], eA]); sNext = np.concatenate([sB, [-1]])
            dOld = np.concatenate([[h], M.dist(eA[:-1], sB[1:]) if len(new) > 1 else np.zeros(0, np.int64), [h]])
            d1 = np.where(ePrev[:, None] < 0, h, M.dist(np.where(ePrev < 0, 0, ePrev)[:, None], U.S[None, :]))
            d2 = np.where(sNext[:, None] < 0, h, M.dist(U.E[None, :], np.where(sNext < 0, 0, sNext)[:, None]))
            val = d1 + d2 + U.X[None, :] - dOld[:, None]
            if len(new) == 0:
                val = U.X[None, :] + 0 * d1
            val = val + rng.random() * 0.01
            pos, r = np.unravel_index(int(np.argmin(val)), val.shape)
            new.insert(int(pos), (u, int(r)))
        nl = total(new)
        d = nl - cur
        if d <= 0 or rng.random() < np.exp(-d / temp):
            seq = new; cur = nl
            if cur < best:
                best = cur; best_seq = list(seq)
                log("rlns it %d t=%.0fs best %d" % (it, time.time() - t0, best))
    log("rlns done: %d iterations, best %d" % (it, best))
    return best_seq, best


def to_units(M, ev, wraps=True, maxwrap=None, log=print):
    rb = run_bounds(M, ev)
    units = [Unit(M, ev[a_:b_ + 1], wraps=wraps, maxwrap=maxwrap) for a_, b_ in rb]
    log("units %d, realizations %d" % (len(units), sum(len(u.K) for u in units)))
    return units, [(i, 0) for i in range(len(units))]


def from_units(M, units, seq):
    ev = []
    for u, r in seq:
        ev.extend(units[u].realize(M, r))
    return ev


def events_from_word(M, w2, log=print):
    """express another word built from the same trails (e.g. rumstd's) as a sequence of trail segments"""
    n, h = M.n, M.h
    keys, tid, off = [], [], []
    for t, c in enumerate(M.cyc):
        ext = np.concatenate([c, c[:n]])
        p = M.tw_pos[t]
        keys.append(perm_rank_keys(ext, p, n)); tid.append(np.full(len(p), t)); off.append(p)
    keys = np.concatenate(keys); tid = np.concatenate(tid); off = np.concatenate(off)
    o = np.argsort(keys, kind="stable"); sk = keys[o]
    pos = perm_positions(w2, n)
    kk = perm_rank_keys(w2, pos, n)
    a = np.searchsorted(sk, kk, "left"); b = np.searchsorted(sk, kk, "right")
    assert (b > a).all() and ((b - a) <= 2).all()
    c1 = o[a]; c2 = np.where(b - a > 1, o[np.minimum(a + 1, len(o) - 1)], -1)
    d = np.diff(pos)
    Rr = M.R
    # choose for each window an occurrence consistent with the previous one when possible
    ch = np.empty(len(pos), np.int64)
    ch[0] = c1[0]
    for i in range(1, len(pos)):
        x = ch[i - 1]
        ok = False
        for y in (c1[i], c2[i]):
            if y >= 0 and tid[y] == tid[x] and (off[x] + d[i - 1]) % Rr[tid[x]] == off[y] and d[i - 1] <= 3:
                ch[i] = y; ok = True; break
        if not ok:
            ch[i] = c1[i]
    x = ch[:-1]; y = ch[1:]
    cont = (tid[x] == tid[y]) & (((off[x] + d) % Rr[tid[x]]) == off[y]) & (d <= 3)
    br = np.nonzero(~cont)[0]
    starts = np.concatenate([[0], br + 1]); ends = np.concatenate([br, [len(pos) - 1]])
    ev = []
    hc = lambda arr: int(sum(int(v) * M.pw[h - 1 - i] for i, v in enumerate(arr)))
    for st, en in zip(starts.tolist(), ends.tolist()):
        t = int(tid[ch[st]]); p0 = int(off[ch[st]]); p1 = int(off[ch[en]])
        ln = (p1 - p0) % int(Rr[t]) + n
        if st != en and p1 == p0:
            ln += int(Rr[t])
        ws, we = pos[st], pos[en] + n
        ev.append(dict(t=t, s=hc(w2[ws:ws + h]), e=hc(w2[we - h:we]), l=ln, piece=None, opt=None, skip=-1, seg=(t, p0, ln)))
    log("segments %d (trails %d)" % (len(ev), len({x['t'] for x in ev})))
    return ev


def match_option(M, x):
    """option id of an event that is a single-segment opening of its trail (or None)"""
    t = x["t"]
    lo, hi = M.opt_lo[t], M.opt_hi[t]
    m = np.nonzero((M.S[lo:hi] == x["s"]) & (M.E[lo:hi] == x["e"]) & (M.R[t] + M.h + M.D[lo:hi] == x["l"]))[0]
    return int(lo + m[0]) if len(m) else None


def write_word(M, ev, path, L=None):
    word = M.spell(ev)
    if L is not None:
        assert len(word) == L, (len(word), L)
    with open(path, "wb") as f:
        f.write(np.frombuffer(ALPH.encode(), np.uint8)[word].tobytes())
        f.write(bytes([10]))
    return len(word)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("word")
    ap.add_argument("out")
    ap.add_argument("--time", type=float, default=600)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--kmax", type=int, default=6)
    ap.add_argument("--noskip", action="store_true")
    ap.add_argument("--T0", type=float, default=1.5)
    ap.add_argument("--chunk", help="A:B byte range of WORD (piece-aligned); first/last pieces are kept fixed")
    ap.add_argument("--attach", action="store_true", help="run the group-attach pass before the LNS")
    ap.add_argument("--rlns", type=float, default=0, help="seconds of run-level LNS (rotations/wraps of closed runs) before the event LNS")
    ap.add_argument("--start", help="start from this word (same trails) instead of WORD's own sequence")
    a = ap.parse_args()
    if a.chunk:
        lo_, hi_ = map(int, a.chunk.split(":"))
        with open(a.word, "rb") as f:
            f.seek(lo_); raw = f.read(hi_ - lo_)
        lut = np.full(256, 255, np.uint8)
        for i, c in enumerate(ALPH.encode()):
            lut[c] = i
        w = lut[np.frombuffer(raw, np.uint8)]
        assert (w != 255).all()
    else:
        w = load(a.word)
    M = Model(w, use_skip=not a.noskip)
    fixed = (M.events[0]["t"], M.events[-1]["t"]) if a.chunk else ()
    L0 = M.length(M.events)
    print("model length of the input sequence: %d (word %d)" % (L0, len(w)))
    if a.start:
        M.events = events_from_word(M, load(a.start))
        print("model length of the start word: %d" % M.length(M.events))
    if a.attach:
        M.events, La = attach_pass(M, M.events)
        print("after attach pass: %d" % La)
    if a.rlns > 0:
        units, seq = to_units(M, M.events)
        seq, Lr = rlns(M, units, seq, a.rlns, a.seed)
        M.events = from_units(M, units, seq)
        print("after run-level LNS: %d (check %d)" % (Lr, M.length(M.events)))
    ev, L = lns(M, M.events, a.time, a.seed, a.kmax, T0=a.T0, ckpt=a.out + ".ckpt", fixed=fixed)
    write_word(M, ev, a.out, L)
    print("wrote %s length %d" % (a.out, L))


if __name__ == "__main__":
    main()
