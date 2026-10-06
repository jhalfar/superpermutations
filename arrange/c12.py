#!/usr/bin/env python
"""c12.py - the file of cuts written by cuts12.c, and min-plus steps over the costs of joins.  A module.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

The file of cuts lists every cut of every closed trail of a base word.  A cut is one word w and the number of its
trail.  At n = 12 the word has 9 letters for a cut at a vertex (D = 0) and 10 letters for a cut at a step of weight
2 (D = 1); the piece written from that cut starts with the first h = 9 letters of w and ends with the last 9.  A
word is stored as a number, 4 bits per letter, the first letter highest.

Half letters.  For a cut x written before a cut y, W(x, y) = 2 (h - k) + D_x + D_y, where k is the largest number of
letters (at most h = 9) in which the end of the piece cut at x agrees with the start of the piece cut at y, and D is
the cost of a cut (0 at a vertex, 1 at a step of weight 2).  A join of cost c between two vertices has W = 2 c.
For a word, 2 (cuts + joins) = D(first cut) + sum of W over its joins + D(last cut).

  Cuts              the file as arrays: trail and D of every cut in memory, the words mapped from the file
  suffix, prefix    the last / first k letters of a 9-letter code
  minplus           g(y) = min over x of val(x) + 2 (h - k(x, y))
  minplus_rev       g(x) = min over y of 2 (h - k(x, y)) + val(y)
The two min-plus steps go through the overlaps k = kmin .. h with sorted tables of k-letter codes, never through
pairs of cuts.  The D terms are added by the caller.  The defaults h = 9 are those of n = 12.

Needs: Python 3, numpy.  Memory: Cuts keeps 5 bytes per cut (0.2 GB for the 40 million cuts of the n = 12 piece
set) and 8 more per cut once all words are asked for (the property w).
"""
import sys
import time
import numpy as np

REC = np.dtype([("w", "<u8"), ("c", "<u8"), ("D", "u1"), ("sk", "u1"), ("t", "<u2")])


class Cuts:
    """the file of cuts: n, NT trails, nc cuts; per trail R, the number of windows, the number of cuts and the index
    of its kind (kinds numbered in the order in which they first appear in the table); per cut the trail t and the
    cost D in memory, everything else through col() or w.  The cuts of a trail are consecutive; first[t] is the first
    cut of trail t."""

    def __init__(self, path, log=print):
        t0 = time.time()
        with open(path, "rb") as f:
            n, NT = np.fromfile(f, np.int32, 2)
            nc = int(np.fromfile(f, np.int64, 1)[0])
            th = np.fromfile(f, np.int32, 4 * NT).reshape(NT, 4)
            off = f.tell()
        self.n, self.NT, self.nc = int(n), int(NT), nc
        self.h = self.n - 3
        self.R, self.nwin, self.ncut_t, self.kind = th[:, 0].copy(), th[:, 1].copy(), th[:, 2].copy(), th[:, 3].copy()
        self.mm = np.memmap(path, REC, "r", offset=off, shape=(nc,))
        self.t = np.array(self.mm["t"]).astype(np.int32)
        self.D = np.array(self.mm["D"]).astype(np.int8)
        self.first = np.searchsorted(self.t, np.arange(NT), "left")
        assert (np.diff(self.t) >= 0).all()
        self._w = None
        log("cuts %d on %d trails, n = %d (%.0fs)" % (nc, NT, n, time.time() - t0))

    @property
    def w(self):
        """the words of all cuts as 64-bit numbers (read on first use, then kept)"""
        if self._w is None:
            self._w = np.array(self.mm["w"]).astype(np.int64)
        return self._w

    def col(self, name, lo=0, hi=None):
        """one field of the cuts lo .. hi-1: "w" word, "c" word with the old letters renamed in order of first
        appearance, "D" cost, "sk" 1 for a cut that drops a repeated permutation, "t" trail"""
        return np.array(self.mm[name][lo:hi])


def suffix(code9, k):
    """code of the last k letters"""
    return code9 & ((np.int64(1) << (4 * k)) - 1)


def prefix(code9, k, h=9):
    """code of the first k letters of an h-letter word"""
    return code9 >> (4 * (h - k))


def minplus(src_exit, src_val, qry_entry, h=9, chunk=6_000_000, kmin=1):
    """g(y) = min over sources x of val(x) + 2 (h - k), k = largest overlap <= h of exit(x) with entry(y)  (W without
    the D terms; add them outside).  The table is built on the smaller side; the larger side is streamed in chunks.
    Overlaps below kmin are charged as overlap kmin - 1 (a lower bound)."""
    ns, nq = len(src_exit), len(qry_entry)
    g = np.full(nq, int(src_val.min()) + 2 * (h - (kmin - 1)), np.int64)
    for k in range(kmin, h + 1):
        if ns <= nq:
            a = suffix(src_exit, k)
            o = np.argsort(a, kind="stable")
            a_s = a[o]
            v_s = src_val[o]
            st = np.nonzero(np.concatenate([[True], a_s[1:] != a_s[:-1]]))[0]
            u = a_s[st]
            mv = np.minimum.reduceat(v_s, st)
            for lo in range(0, nq, chunk):
                q = prefix(qry_entry[lo:lo + chunk], k, h)
                p = np.searchsorted(u, q)
                p = np.minimum(p, len(u) - 1)
                ok = u[p] == q
                gg = g[lo:lo + chunk]
                g[lo:lo + chunk] = np.where(ok, np.minimum(gg, mv[p] + 2 * (h - k)), gg)
        else:
            q = prefix(qry_entry, k, h)
            uq, inv = np.unique(q, return_inverse=True)
            tab = np.full(len(uq), 10 ** 9, np.int64)
            for lo in range(0, ns, chunk):
                a = suffix(src_exit[lo:lo + chunk], k)
                p = np.searchsorted(uq, a)
                p = np.minimum(p, len(uq) - 1)
                ok = uq[p] == a
                if ok.any():
                    np.minimum.at(tab, p[ok], src_val[lo:lo + chunk][ok])
            g = np.minimum(g, tab[inv] + 2 * (h - k))
    return g


def minplus_rev(src_entry, src_val, qry_exit, h=9, chunk=6_000_000, kmin=1):
    """g(x) = min over sources y of 2 (h - k) + val(y), k = largest overlap of exit(x) with entry(y)"""
    ns, nq = len(src_entry), len(qry_exit)
    g = np.full(nq, int(src_val.min()) + 2 * (h - (kmin - 1)), np.int64)
    for k in range(kmin, h + 1):
        if ns <= nq:
            a = prefix(src_entry, k, h)
            o = np.argsort(a, kind="stable")
            a_s = a[o]
            v_s = src_val[o]
            st = np.nonzero(np.concatenate([[True], a_s[1:] != a_s[:-1]]))[0]
            u = a_s[st]
            mv = np.minimum.reduceat(v_s, st)
            for lo in range(0, nq, chunk):
                q = suffix(qry_exit[lo:lo + chunk], k)
                p = np.searchsorted(u, q)
                p = np.minimum(p, len(u) - 1)
                ok = u[p] == q
                gg = g[lo:lo + chunk]
                g[lo:lo + chunk] = np.where(ok, np.minimum(gg, mv[p] + 2 * (h - k)), gg)
        else:
            q = suffix(qry_exit, k)
            uq, inv = np.unique(q, return_inverse=True)
            tab = np.full(len(uq), 10 ** 9, np.int64)
            for lo in range(0, ns, chunk):
                a = prefix(src_entry[lo:lo + chunk], k, h)
                p = np.searchsorted(uq, a)
                p = np.minimum(p, len(uq) - 1)
                ok = uq[p] == a
                if ok.any():
                    np.minimum.at(tab, p[ok], src_val[lo:lo + chunk][ok])
            g = np.minimum(g, tab[inv] + 2 * (h - k))
    return g
