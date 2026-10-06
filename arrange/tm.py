#!/usr/bin/env python
"""tm.py - the closed trails of a base word at the level of permutation windows, and any other word built from
the same trails read as a sequence of events.  A module; run as a program it reads words against a base word.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: tm.py BASE.txt [WORD.txt ...]
  BASE.txt  a base word in which every closed trail is one piece (or a chain of open pieces that closes): Pantone's
            words, and the base words of the generators
  WORD.txt  words made of the same trails; for each the events, the model length and whether spelling the events
            again gives the word are printed

Coordinates.  Trail t is the closed piece t of the base word (R_t letters, cyclic).  Its permutation windows are
numbered globally ("gi", in the order of the base word).  nxt(gi) / prv(gi) are the cyclic neighbours in the trail,
gap[gi] in {1, 2, 3} is the distance in letters from window gi to nxt(gi).
A cut is (E, S): the word leaves the trail after window E and enters it again at window S; S = nxt(E) for a plain
cut, S = nxt(nxt(E)) when the window between them (a permutation that occurs twice, covered elsewhere) is dropped.
Cost of a cut: D = 3 - (letters from E to S along the trail).  Join of an event ending with window p to an event
starting with window q: h - ov(p, q), ov = the longest suffix of p that is a prefix of q (0 .. n-1), h = n - 3.
    length = h + sum R_t + sum D + sum over joins of (h - ov).

  Base   the trails of a base word: windows, gaps, repeated permutations, all cuts, spelling of events
  Plan   another word as events on those trails, with its cuts and its model length

Needs: Python 3, numpy.  Memory: 4 n! bytes for the table of permutation ranks (160 MB at n = 11), plus the words
and their windows.  Used at n = 10 and n = 11.  With the tables of joins that countn.py and top.py add, a program
on Pantone's n = 11 word needs 2.9 to 3.8 GB (measured).
"""
import sys
import time

import numpy as np

ALPH = b"0123456789ABCDEF"


def load_word(path):
    """the word in a file as an array of letter values (0-9, A-F); white space at the end is dropped"""
    s = np.fromfile(path, dtype=np.uint8)
    e = len(s)
    while e > 0 and s[e - 1] in (10, 13, 32):
        e -= 1
    lut = np.full(256, 255, np.uint8)
    lut[np.frombuffer(ALPH, np.uint8)] = np.arange(16, dtype=np.uint8)
    a = lut[s[:e]]
    assert (a != 255).all(), "bad symbol in " + path
    return a


def save_word(path, w):
    """write an array of letter values as one line of text"""
    with open(path, "wb") as f:
        f.write(np.frombuffer(ALPH, np.uint8)[w].tobytes())
        f.write(b"\n")


def perm_positions(w, n, chunk=1 << 22):
    """the positions at which n consecutive letters of w are a permutation (bit mask of the letters is full)"""
    L = len(w)
    out = []
    full = (1 << n) - 1
    for a in range(0, L - n + 1, chunk):
        b = min(L - n + 1, a + chunk)
        m = np.zeros(b - a, np.int32)
        for k in range(n):
            m |= np.left_shift(np.int32(1), w[a + k:b + k].astype(np.int32))
        out.append((np.nonzero(m == full)[0] + a).astype(np.int32))
    return np.concatenate(out) if out else np.zeros(0, np.int32)


def perm_ranks(w, pos, n, chunk=1 << 21):
    """the lexicographic rank (0 .. n! - 1) of the permutation at every position of pos"""
    fact = [1] * (n + 1)
    for i in range(1, n + 1):
        fact[i] = fact[i - 1] * i
    r = np.empty(len(pos), np.int32)
    for a in range(0, len(pos), chunk):
        p = pos[a:a + chunk].astype(np.int64)
        cols = [w[p + k] for k in range(n)]
        acc = np.zeros(len(p), np.int64)
        for k in range(n):
            c = cols[k].astype(np.int64)
            for j in range(k):
                c -= (cols[j] < cols[k])
            acc += c * fact[n - 1 - k]
        r[a:a + chunk] = acc
    return r


class Base:
    """the closed trails of a base word.  Pieces are the maximal runs of windows at most 3 letters apart; a piece
    whose first h letters come again after R letters is a closed trail; open pieces are chained by their end words
    into closed trails.  The trails are stored one after the other, each followed by its first n - 1 letters.
    Fields: NT trails with start ps and length R; M windows with pos (start), gap, isdup (the permutation occurs
    twice) and twin (the other occurrence); tab: rank of a permutation -> its first window."""

    def __init__(self, path, log=print):
        t0 = time.time()
        w = load_word(path)
        self.path = path
        self.w = w
        n = int(w.max()) + 1
        h = n - 3
        self.n, self.h = n, h
        pos = perm_positions(w, n)
        gaps = np.diff(pos)
        cut = np.nonzero(gaps >= 4)[0]
        first = np.r_[0, cut + 1].astype(np.int64)
        last = np.r_[cut, len(pos) - 1].astype(np.int64)
        ps = pos[first].astype(np.int64)
        pl = pos[last].astype(np.int64) + n - ps
        NP = len(ps)
        # closed pieces (a whole trail written from a gap-3, gap-2 or gap-1 cut) and chains of open pieces
        def closes(ex):
            """which pieces are a closed trail written from a cut with ex extra letters (ex = 3 - weight of the
            step that was cut), and the R they would have"""
            Rx = pl - h - ex
            ok = Rx > 2 * n
            for k in range(h + ex):
                ok &= w[np.minimum(ps + Rx + k, len(w) - 1)] == w[ps + k]
            return ok, Rx
        Rp = np.zeros(NP, np.int64)
        ok, Rx = closes(0)
        Rp[ok] = Rx[ok]
        trails = [[k] for k in np.nonzero(Rp > 0)[0].tolist()]
        openp = np.nonzero(Rp == 0)[0].tolist()
        code = lambda a: bytes(a.tolist())
        head = {}
        for k in openp:
            head.setdefault(code(w[ps[k]:ps[k] + h]), []).append(k)
        used = set()
        single = []
        nchained = 0
        for k in openp:
            if k in used:
                continue
            chain = [k]; used.add(k)
            hw = code(w[ps[k]:ps[k] + h])
            while True:
                j = chain[-1]
                tw = code(w[ps[j] + pl[j] - h:ps[j] + pl[j]])
                if tw == hw:
                    break
                nx = [j2 for j2 in head.get(tw, []) if j2 not in used]
                if not nx:
                    break
                chain.append(nx[0]); used.add(nx[0])
            if tw != hw:
                used.difference_update(chain[1:])
                single.append(k)
                continue
            nchained += len(chain)
            trails.append(chain)
        for ex in (1, 2):
            ok, Rx = closes(ex)
            for k in list(single):
                if ok[k]:
                    Rp[k] = Rx[k]; trails.append([k]); single.remove(k)
        assert not single, "piece %d is not part of a closed trail: use a Pantone-form word" % single[0]
        NT = len(trails)
        self.npieces, self.nchained = NP, nchained
        parts = []
        R = np.zeros(NT, np.int64)
        file_ps = ps.copy()                              # piece starts in the word file
        part_len = []
        for t, ch in enumerate(trails):
            cyc = [w[ps[j]:ps[j] + (Rp[j] if Rp[j] > 0 else pl[j] - h)] for j in ch]
            R[t] = sum(len(c_) for c_ in cyc)
            part_len.append([len(c_) for c_ in cyc])
            parts.extend(cyc)
            parts.append(np.concatenate(cyc)[:h + 2] if len(cyc) > 1 else cyc[0][:h + 2])
        del pos, gaps
        w = np.concatenate(parts)                       # own storage: every trail followed by its first n-1 letters
        del parts
        self.w = w
        ps = np.r_[0, np.cumsum(R + h + 2)[:-1]].astype(np.int64)
        pos = perm_positions(w, n)
        tt = np.searchsorted(ps, pos, "right") - 1
        pos = pos[(pos - ps[tt]) < R[tt]]
        tt = np.searchsorted(ps, pos, "right") - 1
        first = np.searchsorted(tt, np.arange(NT), "left").astype(np.int64)
        last = (np.searchsorted(tt, np.arange(NT), "right") - 1).astype(np.int64)
        del tt
        gaps = np.diff(pos)
        self.NT, self.ps, self.R = NT, ps, R
        self.wfirst, self.wlast = first, last
        self.wcnt = last - first + 1
        # position of every trail window in the word file
        fp = np.zeros(len(pos), np.int64)
        for t_, ch in enumerate(trails):
            starts = np.r_[0, np.cumsum(part_len[t_])[:-1]]
            off = pos[first[t_]:last[t_] + 1].astype(np.int64) - ps[t_]
            j = np.searchsorted(starts, off, "right") - 1
            fp[first[t_]:last[t_] + 1] = file_ps[np.array(ch)[j]] + off - starts[j]
        self.file_pos = fp
        self.pos = pos                                    # start of every window in w
        M = len(pos)
        self.M = M
        gap = np.empty(M, np.uint8)
        gap[:-1] = np.minimum(gaps, 255)
        gap[last] = (ps + R - pos[last]).astype(np.uint8)
        assert gap.max() <= 3 and gap.min() >= 1
        self.gap = gap
        self.sumR = int(R.sum())
        self.base_const = h + self.sumR
        rk = perm_ranks(w, pos, n)
        nf = 1
        for i in range(2, n + 1):
            nf *= i
        tab = np.full(nf, -1, np.int32)
        ar = np.arange(M, dtype=np.int32)
        tab[rk[::-1]] = ar[::-1]                          # first occurrence wins
        assert (tab >= 0).all(), "the trails do not hold every permutation"
        second = np.nonzero(tab[rk] != ar)[0]
        twin = {}
        self.triple = 0
        for g2 in second.tolist():
            g1 = int(tab[rk[g2]])
            if g1 in twin:                                # third occurrence: chain the occurrences in a ring
                self.triple += 1
                twin[g2] = twin[g1]
                twin[g1] = g2
            else:
                twin[g1] = g2
                twin[g2] = g1
        self.tab, self.twin = tab, twin
        isdup = np.zeros(M, bool)
        if twin:
            isdup[np.fromiter(twin.keys(), np.int64)] = True
        self.isdup = isdup
        log("base %s: n=%d windows %d pieces %d (in chains %d) trails %d sum R %d duplicated windows %d (%.1fs)" % (
            path.replace("\\", "/").split("/")[-1], n, M, self.npieces, self.nchained, NT, self.sumR, len(second),
            time.time() - t0))

    # ---- neighbours (scalars or arrays)
    def trail_of(self, gi):
        """the trail of window gi (scalar or array)"""
        return np.searchsorted(self.wfirst, gi, "right") - 1

    def nxt(self, gi):
        """the next window in the same trail, cyclically"""
        gi = np.asarray(gi, np.int64)
        t = self.trail_of(gi)
        return np.where(gi == self.wlast[t], self.wfirst[t], gi + 1)

    def prv(self, gi):
        """the previous window in the same trail, cyclically"""
        gi = np.asarray(gi, np.int64)
        t = self.trail_of(gi)
        return np.where(gi == self.wfirst[t], self.wlast[t], gi - 1)

    def letters(self, gi, a, b):
        """letters a..b-1 of windows gi (array) as a (len, b-a) matrix"""
        p = self.pos[np.asarray(gi, np.int64)].astype(np.int64)
        return self.w[p[:, None] + np.arange(a, b)[None, :]]

    def cut_cost(self, E, S):
        """3 - letters from window E to window S along the trail (S is nxt(E) or nxt(nxt(E)))"""
        E = np.asarray(E, np.int64); S = np.asarray(S, np.int64)
        t = self.trail_of(E)
        d = (self.pos[S].astype(np.int64) - self.pos[E].astype(np.int64)) % self.R[t]
        d = np.where(d == 0, self.R[t], d)
        return 3 - d

    def overlap(self, p, q, K=None):
        """largest k <= K with suffix_k(window p) == prefix_k(window q)"""
        n = self.n
        K = n - 1 if K is None else K
        a = self.w[int(self.pos[p]):int(self.pos[p]) + n]
        b = self.w[int(self.pos[q]):int(self.pos[q]) + n]
        for k in range(K, 0, -1):
            if (a[n - k:] == b[:k]).all():
                return k
        return 0

    # ---- all cuts of a model
    def all_cuts(self, gap1=False, skip=True, trails=None):
        """(E, S, D, skipped) arrays: plain cuts at gap >= 2 (gap >= 1 with gap1), duplicate-skip cuts"""
        gi = np.arange(self.M, dtype=np.int64)
        if trails is not None:
            sel = np.zeros(self.NT, bool); sel[np.asarray(list(trails), np.int64)] = True
            gi = gi[sel[self.trail_of(gi)]]
        g = self.gap[gi]
        keep = gi if gap1 else gi[g >= 2]
        E = [keep]; S = [self.nxt(keep)]; K = [np.full(len(keep), -1, np.int64)]
        if skip:
            d = gi[self.isdup[gi]]
            if len(d):
                e = self.prv(d); s = self.nxt(d)
                g2 = self.gap[e].astype(np.int64) + self.gap[d]
                ok = (g2 >= 2) if not gap1 else np.ones(len(d), bool)
                ok &= (e != d) & (s != d) & (e != s)
                E.append(e[ok]); S.append(s[ok]); K.append(d[ok])
        E = np.concatenate(E); S = np.concatenate(S); K = np.concatenate(K)
        return E, S, self.cut_cost(E, S), K

    # ---- spelling
    def seg_letters(self, a, b):
        """letters of the event that runs from window a to window b of one trail"""
        t = int(self.trail_of(a))
        pa, pb = int(self.pos[a]), int(self.pos[b])
        n = self.n
        if a <= b:
            return self.w[pa:pb + n]
        return np.concatenate([self.w[pa:int(self.ps[t] + self.R[t])], self.w[int(self.ps[t]):pb + n]])

    def spell(self, events):
        """events: list of (a, b); joined with the largest overlap of the neighbouring windows"""
        n = self.n
        out = []
        prev = None
        for a, b in events:
            pc = self.seg_letters(a, b)
            if prev is None:
                out.append(pc)
            else:
                out.append(pc[self.overlap(prev, a):])
            prev = b
        return np.concatenate(out)

    def length(self, events):
        """length of the word of the events (a, b), joined with the largest overlaps, without spelling it"""
        L = 0
        prev = None
        n = self.n
        for a, b in events:
            t = int(self.trail_of(a))
            ln = (int(self.pos[b]) - int(self.pos[a])) % int(self.R[t]) + n
            if a != b and self.pos[a] > self.pos[b] and False:
                pass
            L += ln if prev is None else ln - self.overlap(prev, a)
            prev = b
        return L


class Plan:
    """a word read as events on the trails of a base"""

    def __init__(self, B, path, log=print, name=None):
        t0 = time.time()
        self.name = name or path.replace("\\", "/").split("/")[-1]
        w2 = load_word(path)
        n = B.n
        self.L = len(w2)
        pos2 = perm_positions(w2, n)
        rk2 = perm_ranks(w2, pos2, n)
        c = B.tab[rk2].astype(np.int64)
        del rk2
        d2 = np.diff(pos2)
        twin = B.twin
        dupk = np.nonzero(B.isdup[c])[0]
        gap = B.gap

        def nx1(g):
            """the next window of the trail, for one window"""
            t = int(np.searchsorted(B.wfirst, g, "right")) - 1
            return int(B.wfirst[t]) if g == B.wlast[t] else g + 1

        K = len(c)
        for k in dupk.tolist():
            cands = (int(c[k]), twin[int(c[k])])
            best = None
            for x in cands:
                sc = 0
                if k > 0 and nx1(int(c[k - 1])) == x and d2[k - 1] == gap[int(c[k - 1])]:
                    sc += 2
                if k + 1 < K and d2[k] == gap[x]:
                    y = nx1(x)
                    z = int(c[k + 1])
                    if y == z or twin.get(z, -1) == y:
                        sc += 1
                if best is None or sc > best[0]:
                    best = (sc, x)
            c[k] = best[1]
        cont = (c[1:] == B.nxt(c[:-1])) & (d2 == gap[c[:-1]])
        br = np.nonzero(~cont)[0]
        st = np.r_[0, br + 1]; en = np.r_[br, K - 1]
        runs = [(int(c[a]), int(c[b]), int(b - a + 1)) for a, b in zip(st.tolist(), en.tolist())]
        nraw = len(runs)
        # coverage of trail windows; drop runs whose windows are all covered by other runs (incidental windows)
        cov = np.zeros(B.M, np.int32)
        np.add.at(cov, c, 1)
        self.dropped = 0
        order = sorted(range(len(runs)), key=lambda i: runs[i][2])
        alive = [True] * len(runs)
        for i in order:
            a, b, cnt = runs[i]
            if cnt > 3:
                break
            ws = self._windows(B, a, cnt)
            if all(cov[x] >= 2 for x in ws):
                # only if the neighbours join at least as well without it
                alive[i] = False
                for x in ws:
                    cov[x] -= 1
                self.dropped += 1
        runs = [r for r, al in zip(runs, alive) if al]
        self.events = [(a, b) for a, b, _ in runs]
        self.cnt = [cnt for _, _, cnt in runs]
        self.twice = int((cov >= 2).sum())
        unc = np.nonzero(cov == 0)[0]
        self.skipped = unc
        bad = [int(x) for x in unc.tolist() if not (int(x) in twin and cov[twin[int(x)]] >= 1)]
        assert not bad, "windows not covered: %s" % bad[:5]
        # cuts of every trail
        tr = B.trail_of(np.array([a for a, _ in self.events], np.int64))
        per = {}
        for i, t in enumerate(tr.tolist()):
            per.setdefault(t, []).append(i)
        cuts = []         # (E, S, skipped window or -1)
        self.odd = 0
        for t, lst in per.items():
            f = int(B.wfirst[t]); m = int(B.wcnt[t])
            lst.sort(key=lambda i: self.events[i][0])
            for j, i in enumerate(lst):
                i2 = lst[(j + 1) % len(lst)]
                E = self.events[i][1]; S = self.events[i2][0]
                s = (S - E - 1) % m
                if s == 0:
                    cuts.append((E, S, -1))
                elif s == 1:
                    cuts.append((E, S, nx1(E)))
                else:
                    self.odd += 1
                    cuts.append((E, S, -2))
        assert len(per) == B.NT, "a trail is absent"
        self.cuts = cuts
        self.ntrails_multi = sum(1 for lst in per.values() if len(lst) > 1)
        # model length
        Dsum = 0
        for E, S, k in cuts:
            Dsum += int(B.cut_cost(E, S))
        ovs = [B.overlap(self.events[i][1], self.events[i + 1][0]) for i in range(len(self.events) - 1)]
        self.ovs = ovs
        self.cost = Dsum + sum(B.h - o for o in ovs)
        self.model_len = B.base_const + self.cost
        self.wide = sum(1 for o in ovs if o > B.h)
        self.gap1 = sum(1 for E, S, k in cuts if k == -1 and B.gap[E] == 1)
        log("plan %s: L=%d model %d (cost %d) events %d (raw runs %d, incidental %d) multi-segment trails %d skips %d "
            "gap-1 cuts %d joins>h %d odd %d twice %d (%.1fs)" % (
                self.name, self.L, self.model_len, self.cost, len(self.events), nraw, self.dropped, self.ntrails_multi,
                sum(1 for c_ in cuts if c_[2] >= 0), self.gap1, self.wide, self.odd, self.twice, time.time() - t0))

    @staticmethod
    def _windows(B, a, cnt):
        """the cnt consecutive windows of a trail from window a"""
        out = []
        t = int(np.searchsorted(B.wfirst, a, "right")) - 1
        g = a
        for _ in range(cnt):
            out.append(g)
            g = int(B.wfirst[t]) if g == B.wlast[t] else g + 1
        return out

    def join_hist(self, B):
        """{cost of a join: number of joins} of the word"""
        hst = {}
        for o in self.ovs:
            hst[B.h - o] = hst.get(B.h - o, 0) + 1
        return dict(sorted(hst.items()))


def check_word(w, n):
    """number of distinct permutations among the windows of w"""
    pos = perm_positions(w, n)
    rk = perm_ranks(w, pos, n)
    return len(np.unique(rk))


if __name__ == "__main__":
    B = Base(sys.argv[1])
    for p in sys.argv[2:]:
        P = Plan(B, p)
        print("   joins by cost", P.join_hist(B))
        ww = B.spell(P.events)
        print("   respelled length", len(ww), "equal to the word:", len(ww) == P.L and bool((ww == load_word(p)).all()))
