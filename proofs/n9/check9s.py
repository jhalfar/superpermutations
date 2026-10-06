#!/usr/bin/env python
"""check9s.py - a self-contained proof check: in the single-port family on the trails of Pantone's n = 9 word no word
is shorter than h + sum R + 149 letters (= 408,731 for superpermutation-9-408732.txt).
No solver, no project code, integers only (numpy int64 / Python int).  About 2 minutes (narrow), 6 minutes (--wide).

usage: check9s.py BASE_WORD.txt [WORD_OF_THE_FAMILY.txt] [--wide]

THE FAMILY.  Windows of the base word W0 = positions where n letters form a permutation; pieces = maximal runs of
windows at most 3 apart; every piece is a closed trail (its last window overlaps its first in n-g letters, g = 3, 2
or 1); a trail is the cyclic sequence of its windows with gaps g_i, R = sum of its gaps.
CUTS of a trail: (E = window i, S = window i+1) if g_i >= 2 [--wide: any g_i], cost D = 3 - g_i;
                 (E = window i-1, S = window i+1) if window i is a duplicate, cost D = 3 - g_{i-1} - g_i.
The piece of a cut runs from the first letter of window S cyclically to the last letter of window E
(R + h + D letters, h = n-3).  A WORD OF THE FAMILY: one cut for every trail, the pieces in some order, consecutive
pieces overlapping in k agreeing letters, k <= h [--wide: k <= n-1].  Its length is
    h + sum R + sum D + sum (h - k)  >=  h + sum R + cost,   cost = sum D + sum over consecutive pieces of c(a,b),
    c(a,b) = h - (largest k allowed such that the last k letters of piece a are the first k letters of piece b).
(c depends only on the last / first K letters, K = h or n-1: the "words" e_a, s_b of the cuts.)

THE ARGUMENT, in half letters.  W(x,y) = 2 c(x,y) + D_x + D_y for cuts of different trails.  For the cuts a_1..a_N
of a word in its order:        2 cost = sum_i W(a_i, a_{i+1}) + D_{a_1} + D_{a_N}.                         (0)
Split the trails into SMALL (the 48 with the fewest cuts) and BIG (the other 4).  Checked below:
 (1) all D >= 0; W(x,y) >= 6 for cuts of two different small trails.
 (2) A sequence of cuts of pairwise different small trails with W <= 7 between neighbours has at most 6 cuts.
 (3) For cuts o_1..o_k of k >= 1 different big trails and small cuts a, b:
         W(a,o_1) + W(o_1,o_2) + .. + W(o_k,b) >= 8                                  (block between small trails)
         D_{o_1} + W(o_1,o_2) + .. + W(o_k,b) >= 1,   W(a,o_1) + .. + W(o_{k-1},o_k) + D_{o_k} >= 1   (block at an end)
 COUNTING.  In a word the big trails form q >= 1 maximal blocks, e of them at an end; the small trails form
 s = q + 1 - e blocks, cut further into r maximal runs whose joins have W <= 7; r >= 8 by (2).  Joins inside runs:
 48 - r, each >= 6 by (1).  Joins between two runs of one small block: r - s, each >= 8.  Joins at a big block
 between small trails: >= 8 in total; block at an end (with the D of the end piece): >= 1.  With (0):
         2 cost >= 6 (48 - r) + 8 (r - s) + 8 (q - e) + e = 280 + 2 r + e >= 296,     hence cost >= 148.
 EQUALITY 2 cost = 296 needs e = 0, r = 8, W = 6 at every join inside a run, W = 8 between runs, W-sum 8 at every
 big block.  Then every run has exactly 6 trails.
 (4a) All sequences of 6 cuts of different small trails with W = 6 between neighbours ("chains") are listed.
 (4b) Exhaustive search: no 8 chains on disjoint trails covering all small trails can be put in an order with
      W = 8 from the end of a chain to the start of the next, or a block of big trails with W-sum 8 between them,
      such that every big trail is used.
 Hence 2 cost >= 297; cost is an integer, so cost >= 149.
"""
import hashlib
import itertools
import sys
import time

import numpy as np

ALPH = "0123456789ABCDEF"
t00 = time.time()
args = [a for a in sys.argv[1:] if not a.startswith("--")]
WIDE = "--wide" in sys.argv


def say(*x):
    print(*x, flush=True)


def read_word(path):
    raw = open(path, "rb").read()
    return [ALPH.index(ch) for ch in raw.decode("ascii").strip()], hashlib.sha256(raw).hexdigest()


# ------------------------------------------------------------------ the family
w, sha = read_word(args[0])
n = max(w) + 1
h = n - 3
K = n - 1 if WIDE else h
full = set(range(n))
pos = [p for p in range(len(w) - n + 1) if set(w[p:p + n]) == full]
pieces = [[pos[0]]]
for p, q in zip(pos[:-1], pos[1:]):
    if q - p >= 4:
        pieces.append([q])
    else:
        pieces[-1].append(q)
trails = []
for pc in pieces:
    a, b = pc[-1], pc[0]
    g = next((g for g in (3, 2, 1) if w[a + g:a + n] == w[b:b + n - g]), None)
    assert g is not None, "a piece is not a closed trail"
    trails.append((pc, [q - p for p, q in zip(pc[:-1], pc[1:])] + [g]))
NT = len(trails)
sumR = sum(sum(g) for _, g in trails)
cnt = {}
for pc, _ in trails:
    for p in pc:
        key = tuple(w[p:p + n])
        cnt[key] = cnt.get(key, 0) + 1
nfact = 1
for i in range(2, n + 1):
    nfact *= i
assert len(cnt) == nfact, "the trails do not hold every permutation"
cuts = []            # (trail, index of window E, index of window S, D)
for t, (pc, gaps) in enumerate(trails):
    m = len(pc)
    for i in range(m):
        if gaps[i] >= (1 if WIDE else 2):
            cuts.append((t, i, (i + 1) % m, 3 - gaps[i]))
        if cnt[tuple(w[pc[i]:pc[i] + n])] >= 2 and m > 2:
            cuts.append((t, (i - 1) % m, (i + 1) % m, 3 - gaps[(i - 1) % m] - gaps[i]))
V = len(cuts)
ct = np.array([c[0] for c in cuts], np.int64)
D = np.array([c[3] for c in cuts], np.int64)
wa = np.array(w + [0] * n, np.int64)
pE = np.array([trails[c[0]][0][c[1]] for c in cuts], np.int64)
pS = np.array([trails[c[0]][0][c[2]] for c in cuts], np.int64)
ew = wa[pE[:, None] + np.arange(n - K, n)[None, :]]           # last K letters of window E
sw = wa[pS[:, None] + np.arange(K)[None, :]]                  # first K letters of window S
suf, pre, nstr = [], [], []                                   # per level k: id of the k-letter end of e / start of s
for k in range(K + 1):
    a = np.zeros(V, np.int64); b = np.zeros(V, np.int64)
    for j in range(k):
        a = a * 16 + ew[:, K - k + j]
        b = b * 16 + sw[:, j]
    codes = np.unique(np.concatenate([a, b]))
    suf.append(np.searchsorted(codes, a)); pre.append(np.searchsorted(codes, b)); nstr.append(len(codes))
say("base word: n=%d, %d letters, sha256 %s" % (n, len(w), sha))
say("family: single-port, %s" % ("WIDE (cuts at every gap, overlaps up to n-1)" if WIDE else "narrow (cuts at gaps 2 and 3, overlaps up to n-3)"))
say("trails %d, sum R = %d, h + sum R = %d, cuts %d (D values %s)" % (NT, sumR, h + sumR, V, sorted(set(D.tolist()))))
BIGN = 10 ** 9


def Wm(A, Bc):
    """matrix W(a, b), a in A, b in Bc"""
    C = np.full((len(A), len(Bc)), h, np.int64)
    for k in range(1, K + 1):
        C[suf[k][A][:, None] == pre[k][Bc][None, :]] = h - k
    return 2 * C + D[A][:, None] + D[Bc][None, :]


def minplus(f, A, Bc):
    """g(b) = min over a in A of f(a) + W(a, b) for b in Bc: for every level k the smallest f(a) + D_a among the a
    whose word ends with a given k-letter string, looked up with the k-letter start of b"""
    g = np.full(len(Bc), BIGN, np.int64)
    val = f + D[A]
    for k in range(K + 1):
        tab = np.full(nstr[k], BIGN, np.int64)
        np.minimum.at(tab, suf[k][A], val)
        g = np.minimum(g, tab[pre[k][Bc]] + 2 * (h - k))
    return g + D[Bc]


def minplus_rev(f, A, Bc):
    """g(a) = min over b in Bc of W(a, b) + f(b) for a in A"""
    g = np.full(len(A), BIGN, np.int64)
    val = f + D[Bc]
    for k in range(K + 1):
        tab = np.full(nstr[k], BIGN, np.int64)
        np.minimum.at(tab, pre[k][Bc], val)
        g = np.minimum(g, tab[suf[k][A]] + 2 * (h - k))
    return g + D[A]


ncut = np.bincount(ct, minlength=NT)
order_t = np.argsort(ncut, kind="stable")
big_t = sorted(order_t[-4:].tolist())
small_t = sorted(order_t[:-4].tolist())
NS = len(small_t)
sc = np.nonzero(np.isin(ct, small_t))[0]
bc = {t: np.nonzero(ct == t)[0] for t in big_t}
say("small trails %d (%s cuts each), big trails %s (%s cuts)" % (NS, sorted(set(ncut[small_t].tolist())), big_t, [int(ncut[t]) for t in big_t]))
assert NS % 6 == 0
need_runs = NS // 6
# ------------------------------------------------------------------ (1)
assert D.min() >= 0
wmin = BIGN
hist = {}
arcs = {6: [], 7: [], 8: []}
for c0 in range(0, len(sc), 500):
    Wc = Wm(sc[c0:c0 + 500], sc)
    Wc[ct[sc[c0:c0 + 500]][:, None] == ct[sc][None, :]] = BIGN
    wmin = min(wmin, int(Wc.min()))
    for v in (6, 7, 8):
        i, j = np.nonzero(Wc == v)
        arcs[v].append(np.stack([i + c0, j], 1))
    assert not (Wc < 6).any()
arcs = {v: np.concatenate(x) for v, x in arcs.items()}
say("(1) all D >= 0; joins between cuts of different small trails: smallest W = %d  [W = 6: %d, W = 7: %d, W = 8: %d]" % (
    wmin, len(arcs[6]), len(arcs[7]), len(arcs[8])))
assert wmin == 6
# ------------------------------------------------------------------ (2), (4a)
tr = ct[sc].tolist()
succ7, succ6 = {}, {}
for v in (6, 7):
    for i, j in arcs[v].tolist():
        succ7.setdefault(i, []).append(j)
        if v == 6:
            succ6.setdefault(i, []).append(j)
sys.setrecursionlimit(100000)
longest = 0
chains = []


def dfs(path, used, succ, collect):
    global longest
    longest = max(longest, len(path))
    if collect and len(path) == 6:
        chains.append((path[0], path[-1], frozenset(used)))
    for j in succ.get(path[-1], ()):
        if tr[j] not in used:
            used.add(tr[j]); path.append(j)
            dfs(path, used, succ, collect)
            path.pop(); used.discard(tr[j])


for i in range(len(sc)):
    dfs([i], {tr[i]}, succ7, False)
say("(2) longest sequence of cuts of different small trails with W <= 7 between neighbours: %d" % longest)
assert longest == 6
for i in range(len(sc)):
    dfs([i], {tr[i]}, succ6, True)
sets = sorted(set(c[2] for c in chains), key=sorted)
say("(4a) sequences of 6 cuts of different small trails with W = 6 between neighbours: %d, on %d different sets of 6 trails" % (len(chains), len(sets)))
# ------------------------------------------------------------------ (3)
zs = np.zeros(len(sc), np.int64)
in1 = {t: minplus(zs, sc, bc[t]) for t in big_t}              # min over small a of W(a, o)
out1 = {t: minplus_rev(zs, bc[t], sc) for t in big_t}         # min over small b of W(o, b)
Tmid, Tfirst, Tlast = {}, {}, {}
fmid, ffirst = {}, {}
for k in range(1, len(big_t) + 1):
    for seq in itertools.permutations(big_t, k):
        fmid[seq] = in1[seq[0]] if k == 1 else minplus(fmid[seq[:-1]], bc[seq[-2]], bc[seq[-1]])
        ffirst[seq] = D[bc[seq[0]]].copy() if k == 1 else minplus(ffirst[seq[:-1]], bc[seq[-2]], bc[seq[-1]])
        Tmid[seq] = int((fmid[seq] + out1[seq[-1]]).min())
        Tfirst[seq] = int((ffirst[seq] + out1[seq[-1]]).min())
        Tlast[seq] = int((fmid[seq] + D[bc[seq[-1]]]).min())
    say("(3) blocks of %d big trails: smallest W-sum between two small cuts %d (W-sum 8 for: %s); at the start of the word "
        "%d, at the end %d" % (k, min(v for s_, v in Tmid.items() if len(s_) == k),
                               ", ".join("-".join(map(str, s_)) for s_, v in sorted(Tmid.items()) if len(s_) == k and v == 8) or "none",
                               min(v for s_, v in Tfirst.items() if len(s_) == k), min(v for s_, v in Tlast.items() if len(s_) == k)))
assert min(Tmid.values()) >= 8 and min(Tfirst.values()) >= 1 and min(Tlast.values()) >= 1
bound2 = 6 * NS - 8 + 2 * need_runs
say("COUNTING: 2 cost >= 6 (%d - r) + 8 (r - s) + 8 (q - e) + e = %d + 2 r + e, r >= %d:  cost >= %d, every word of the "
    "family has at least %d letters" % (NS, 6 * NS - 8, need_runs, (bound2 + 1) // 2, h + sumR + (bound2 + 1) // 2))
# ------------------------------------------------------------------ (4b)
starts = sorted(set(c[0] for c in chains)); ends = sorted(set(c[1] for c in chains))
sidx = {c: i for i, c in enumerate(starts)}; eidx = {c: i for i, c in enumerate(ends)}
sC = sc[np.array(starts)]; eC = sc[np.array(ends)]
L8 = np.zeros((len(ends), len(starts)), bool)
for i, j in arcs[8].tolist():
    if i in eidx and j in sidx:
        L8[eidx[i], sidx[j]] = True
bridges = []
for seq, v in sorted(Tmid.items()):
    if v != 8:
        continue                                   # W-sum >= 9: cannot occur in an equality word
    M = np.zeros((len(ends), len(starts)), bool)
    W0 = Wm(eC, bc[seq[0]])                         # W(e, o_1), one row per chain end
    for i in range(len(ends)):
        f = W0[i]
        for a, b in zip(seq[:-1], seq[1:]):
            f = minplus(f, bc[a], bc[b])
        M[i] = minplus(f, bc[seq[-1]], sC) == 8
    say("    block %s: pairs (end of a chain, start of a chain) with W-sum exactly 8: %d" % ("-".join(map(str, seq)), int(M.sum())))
    bridges.append((sum(1 << big_t.index(t) for t in seq), M))
by_trail = {t: [i for i, s_ in enumerate(sets) if t in s_] for t in small_t}
covers = []


def cover(chosen, covered):
    rest = [t for t in small_t if t not in covered]
    if not rest:
        covers.append(tuple(chosen)); return
    t = min(rest, key=lambda x: sum(1 for i in by_trail[x] if not (sets[i] & covered)))
    for i in by_trail[t]:
        if not (sets[i] & covered):
            cover(chosen + [i], covered | sets[i])


cover([], frozenset())
rot = {}
for c in chains:
    rot.setdefault(sets.index(c[2]), []).append((sidx[c[0]], eidx[c[1]]))
nb = len(big_t)
ALLB = (1 << nb) - 1
found = 0
for cov in covers:
    Kc = len(cov)
    st = [np.array([r_[0] for r_ in rot[i]]) for i in cov]
    en = [np.array([r_[1] for r_ in rot[i]]) for i in cov]
    reach = {(1 << i, 0): {i: np.ones(len(st[i]), bool)} for i in range(Kc)}
    for mask in range(1, 1 << Kc):
        for bm in range(1 << nb):
            cur = reach.get((mask, bm))
            if cur is None:
                continue
            for i, alive in cur.items():
                for j in range(Kc):
                    if (mask >> j) & 1:
                        continue
                    for bmask, M in [(0, L8)] + bridges:
                        if bm & bmask:
                            continue
                        ok = (alive[:, None] & M[np.ix_(en[i], st[j])]).any(0)
                        if ok.any():
                            d = reach.setdefault((mask | (1 << j), bm | bmask), {})
                            d[j] = d.get(j, np.zeros(len(st[j]), bool)) | ok
    if (((1 << Kc) - 1), ALLB) in reach:
        found += 1
say("(4b) families of %d chains on disjoint trails covering all small trails: %d; those that can be ordered with W = 8 "
    "links and W-sum-8 blocks using every big trail: %d" % (need_runs, len(covers), found))
best = (bound2 + 2) // 2 if found == 0 else (bound2 + 1) // 2
if found == 0:
    say("THEOREM (checked): every word of this family has cost >= %d, i.e. at least %d letters.  (%.0f s)" % (best, h + sumR + best, time.time() - t00))
else:
    say("only cost >= %d is proven: at least %d letters  (%.0f s)" % (best, h + sumR + best, time.time() - t00))
# ------------------------------------------------------------------ optional: a word of the family that attains it
if len(args) > 1:
    ww, sha2 = read_word(args[1])
    place = {}
    for t, (pc, gaps) in enumerate(trails):
        for i, p in enumerate(pc):
            place.setdefault(tuple(w[p:p + n]), []).append((t, i))
    wp = [p for p in range(len(ww) - n + 1) if set(ww[p:p + n]) == full]
    runs = []                                    # [trail, first window index, last window index]
    for k, p in enumerate(wp):
        cands = place[tuple(ww[p:p + n])]
        ok = None
        if runs:
            t, i0, i1 = runs[-1]
            m = len(trails[t][0])
            if (t, (i1 + 1) % m) in cands and p - wp[k - 1] == trails[t][1][i1]:
                ok = (t, (i1 + 1) % m)
        if ok is not None:
            runs[-1][2] = ok[1]
        else:
            c = cands[0]
            if len(cands) > 1 and k + 1 < len(wp):
                nxt = tuple(ww[wp[k + 1]:wp[k + 1] + n])
                for (t, i) in cands:
                    if (t, (i + 1) % len(trails[t][0])) in place[nxt]:
                        c = (t, i)
            runs.append([c[0], c[1], c[1]])
    assert sorted(r_[0] for r_ in runs) == list(range(NT)), "the word does not write every trail once in one piece"
    lookup = {(c[0], c[1], c[2]): i for i, c in enumerate(cuts)}
    order = [lookup[(t, i1, i0)] for t, i0, i1 in runs]
    cst = int(D[order].sum()) + sum(int((Wm(np.array([a]), np.array([b]))[0, 0] - D[a] - D[b]) // 2) for a, b in zip(order[:-1], order[1:]))
    say("%s (sha256 %s..): %d letters; a word of the family (one piece per trail), cost %d, h + sum R + cost = %d%s" % (
        args[1].replace("\\\\", "/").split("/")[-1], sha2[:16], len(ww), cst, h + sumR + cst,
        ": the bound is attained, the word is optimal in this family" if h + sumR + cst == len(ww) == h + sumR + best else ""))
