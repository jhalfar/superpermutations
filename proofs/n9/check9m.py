#!/usr/bin/env python
"""check9m.py - a self-contained proof check for the MULTI-PORT narrow family on the trails of Pantone's n = 9 word:
no word of the family is shorter than h + sum R + 149 letters (= 408,731 for superpermutation-9-408732.txt).
No solver, no project code, integers only (numpy int64 / Python int).  About half a minute.

usage: check9m.py BASE_WORD.txt [WORD_OF_THE_FAMILY.txt]

THE FAMILY.  Windows, pieces, closed trails, gaps g_i, R and the CUTS (E, S, D) of a trail exactly as in check9s.py:
(E = window i, S = window i+1) if g_i >= 2, D = 3 - g_i;  (E = window i-1, S = window i+1) if window i is a duplicate,
D = 3 - g_{i-1} - g_i.  A WORD OF THE MULTI-PORT FAMILY: for every trail a set of k >= 1 of its cuts; they split the
trail into k SEGMENTS, each running from the window S of one cut (its ENTRY) to the window E of the next cut along the
trail (its EXIT); all segments of all trails are written in some order, consecutive ones overlapping in j agreeing
letters, j <= h = n-3.  A trail with k cuts has k h + R + sum D letters in its segments, so the word has
    h + sum R + sum D + sum (h - j)  >=  h + sum R + cost   letters,
    cost = sum of D over the used cuts + sum over consecutive segments of c(x, y),
    c(x, y) = h - (largest j <= h such that the last j letters of window E of x are the first j letters of window S of y),
x = exit of the earlier segment, y = entry of the later one (a JOIN).  One cut per trail is the single-port family.
The proof uses only this much of the family:
 (F1) every used cut is the entry of exactly one segment and the exit of exactly one segment, both of its trail;
 (F2) a trail with one used cut c has the segment (c, c); with two used cuts c, d the segments (c, d) and (d, c).
A join from the exit c of a segment to the entry c of the next one (same cut) is DEGENERATE: dropping the cut c merges
the two segments and does not increase the cost (D >= 0, c >= 0).  So it is enough to bound words without them.

THE ARGUMENT, in half letters.  W(x,y) = 2 c(x,y) + D_x + D_y for any two cuts.  By (F1), for the segments
s_1..s_M of a word:      2 cost = sum_i W(exit s_i, entry s_{i+1}) + D_{entry s_1} + D_{exit s_M}.             (0)
SMALL trails: the NS = 48 with the fewest cuts; BIG trails: the other 4.  Checked below:
 (m1) all D >= 0;  W(x,y) >= 6 for cuts of two different small trails.
 (m2) In the graph on the small cuts whose edges are the pairs of cuts of different small trails with W <= 7, every
      connected component has cuts of at most 6 trails.
 (m3) W(x,y) >= 1 for two different cuts of one small trail.
 (b)  Two functions f = f_out and f = 8 - f_in on the big cuts, each with, for big cuts c, d and small cuts a, b:
        W(a,c) >= 8 - f(c),   W(c,b) >= f(c),   W(c,d) >= f(c) - f(d),   1 - D_c <= f(c) <= 7 + D_c.
 COUNTING.  Take a word without degenerate joins.  A join between two segments of one small trail with W <= 7 is
 CONTRACTED (W >= 1 by (m3)); a SUPER-SEGMENT is a maximal group of consecutive segments of one small trail held
 together by contracted joins (entry = entry of its first segment, exit = exit of its last).  Let m be the number of
 small super-segments, j the number of contracted joins.  The big segments form maximal BLOCKS; e of them stand at an
 end of the word.  The small super-segments, in their order, are split into r maximal RUNS: neighbours in a run are
 joined directly with W <= 7 (hence they belong to different trails and W >= 6 by (m1)).  Between two runs stands a
 direct join with W >= 8 or a block.  With phi = f - 4, a block c_1 ~> c_1', .., c_k ~> c_k' (entries c_i, exits
 c_i') between small cuts a, b has
     W(a,c_1) + sum W(c_i',c_{i+1}) + W(c_k',b) >= 8 + sum_i (phi(c_i') - phi(c_i)),
 a block at an end, with the D of the end cut of the word, >= 1 + sum_i (phi(c_i') - phi(c_i)); over all big
 segments the sums of phi(exit) - phi(entry) cancel by (F1).  So with (0):
     2 cost >= j + 6 (m - r) + 8 (r - 1) + e.                                                               (1)
 RUNS.  Call a super-segment of a run a JUMP if entry != exit and it is neither first nor last in its run; J = number
 of jumps.  Cut every run at its jumps (the jump belongs to both parts): r + J STRETCHES.  Inside a stretch all joins
 are edges of the graph of (m2) and consecutive ones share a cut, so a stretch lies in one component: at most 6
 trails.  Every small trail is in a stretch, a trail with a jump in two; with Q = number of trails with a jump:
     NS + Q <= 6 (r + J),    i.e.    2 r >= NS/3 - 2 J + Q/3.                                                (2)
 (1), (2):  2 cost >= 6 NS - 8 + NS/3 + e + sum over small trails T of
     theta_T = j_T + 6 (sigma_T - 1) - 2 J_T + [J_T >= 1]/3     (sigma_T super-segments, j_T contracted joins, J_T jumps).
 A trail with one cut has theta = 0.  A trail with k >= 2 cuts: if sigma_T >= 2 then theta >= 4 sigma_T - 6 >= 2;
 if sigma_T = 1 then k >= 3 (two segments (c,d), (d,c) in a row would make a degenerate join, (F2)), j_T = k - 1 >= 2,
 J_T <= 1, theta >= 1/3.  Hence   2 cost >= 6 NS - 8 + NS/3 = 296,   cost >= 148,
 and cost = 148 forces: every small trail has ONE cut, e = 0, r = NS/6 = 8 runs of exactly 6 cuts with W = 6 inside
 (CHAINS), W = 8 at the direct joins between runs, and every join at a big segment tight for both functions of (b).
 EQUALITY.  psi = f_in + f_out - 8 >= 0.  Tight joins: small a -> big c needs psi(c) = 0, W(a,c) = f_in(c);
 big c -> small b needs psi(c) = 0, W(c,b) = f_out(c); big c -> big d needs psi(c) = psi(d), W(c,d) = f_out(c) - f_out(d).
 Checked below:
 (e1) all chains are listed; different chains have different first cuts and different last cuts.
 (e2) every tight join between two different big cuts with psi = 0 has W > 0, and its first cut c has no chain end a
      with W(a,c) = f_in(c).   [Then no such join is used: going backwards along used joins of this kind f_out grows, so
      one arrives at a cut entered from a small cut, i.e. from the end of a chain: excluded.]
 (e3) every tight join with W = 0 between two different big cuts joins cuts of the same trail.   [Used cuts with
      psi > 0 are joined to big cuts with the same psi only; following the joins forwards one returns (F1), the W
      along the cycle sum to 0, so all are 0.]
 So in a word of cost 148 every block lies on one big trail, is entered at a cut c with psi = 0 from the chain end
 e(c) with W = f_in(c), and left at a cut c' of the same trail with psi = 0 to the chain start s(c') with
 W = f_out(c'); the set U of entry cuts equals the set of exit cuts (F1); every big trail has a cut in U (otherwise
 its segments are joined to segments of the same trail only, and the word would never reach a small trail).
 (e4) Exhaustive search of this relaxed problem: families of 8 chains on disjoint trails covering all small trails,
      a set U with a cut on every big trail, an order of the chains in which a chain whose end is e(c), c in U, is
      followed by a chain whose start is s(c'), c' in U on the same big trail as c, and all other neighbours have
      W = 8 from end to start; the first chain does not start at an s(c), the last does not end at an e(c), c in U.
      (How the big trails are cut between c and c' is not looked at: the search covers more than the family.)
 If the search finds nothing, cost >= 149.
"""
import hashlib
import itertools
import sys
import time

import numpy as np

ALPH = "0123456789ABCDEF"
t00 = time.time()
args = [a for a in sys.argv[1:] if not a.startswith("--")]
WIDE = "--wide" in sys.argv          # only to show where the argument stops in the wide family


def say(*x):
    print(*x, flush=True)


def read_word(path):
    raw = open(path, "rb").read()
    return [ALPH.index(ch) for ch in raw.decode("ascii").strip()], hashlib.sha256(raw).hexdigest()


def fail(msg):
    say("NOT PROVEN: " + msg)
    sys.exit(1)


# ------------------------------------------------------------------ the family (as in check9s.py)
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
say("family: MULTI-port, %s" % ("WIDE (cuts at every gap, overlaps up to n-1)" if WIDE else "narrow (cuts at gaps 2 and 3, overlaps up to n-3)"))
say("trails %d, sum R = %d, h + sum R = %d, cuts %d (D values %s)" % (NT, sumR, h + sumR, V, sorted(set(D.tolist()))))
BIGN = 10 ** 9


def Wm(A, Bc):
    """matrix W(a, b), a in A, b in Bc"""
    C = np.full((len(A), len(Bc)), h, np.int64)
    for k in range(1, K + 1):
        C[suf[k][A][:, None] == pre[k][Bc][None, :]] = h - k
    return 2 * C + D[A][:, None] + D[Bc][None, :]


def minplus(f, A, Bc):
    """g(b) = min over a in A of f(a) + W(a, b) for b in Bc (exact: per level k the smallest f(a) + D_a among the a
    whose word ends with a given k-letter string, looked up with the k-letter start of b)"""
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
BC = np.nonzero(np.isin(ct, big_t))[0]
say("small trails %d (%s cuts each), big trails %s (%s cuts)" % (NS, sorted(set(ncut[small_t].tolist())), big_t, [int(ncut[t]) for t in big_t]))
assert NS % 6 == 0
need_runs = NS // 6
# ------------------------------------------------------------------ (m1), (m2)
if D.min() < 0:
    fail("a cut with D < 0")
wmin = BIGN
arcs = {6: [], 7: [], 8: []}
for c0 in range(0, len(sc), 500):
    Wc = Wm(sc[c0:c0 + 500], sc)
    Wc[ct[sc[c0:c0 + 500]][:, None] == ct[sc][None, :]] = BIGN
    wmin = min(wmin, int(Wc.min()))
    for v in (6, 7, 8):
        i, j = np.nonzero(Wc == v)
        arcs[v].append(np.stack([i + c0, j], 1))
arcs = {v: np.concatenate(x) for v, x in arcs.items()}
say("(m1) all D >= 0; joins between cuts of different small trails: smallest W = %d  [W = 6: %d, W = 7: %d, W = 8: %d]" % (
    wmin, len(arcs[6]), len(arcs[7]), len(arcs[8])))
if wmin < 6:
    fail("(m1) fails")
tr = ct[sc].tolist()
par = list(range(len(sc)))


def find(x):
    while par[x] != x:
        par[x] = par[par[x]]
        x = par[x]
    return x


for v in (6, 7):
    for i, j in arcs[v].tolist():
        a, b = find(i), find(j)
        if a != b:
            par[a] = b
comp = {}
for i in range(len(sc)):
    comp.setdefault(find(i), set()).add(tr[i])
most = max(len(v) for v in comp.values())
say("(m2) components of the graph of joins with W <= 7 between different small trails: %d, with at most %d trails" % (len(comp), most))
if most > 6:
    fail("(m2) fails")
# ------------------------------------------------------------------ (m3)
w3 = BIGN
for t in small_t:
    A = np.nonzero(ct == t)[0]
    Wc = Wm(A, A)
    Wc[np.arange(len(A)), np.arange(len(A))] = BIGN
    w3 = min(w3, int(Wc.min()))
say("(m3) joins between two different cuts of one small trail: smallest W = %d" % w3)
if w3 < 1:
    fail("(m3) fails: a join between two cuts of one small trail with W <= 0 (the counting argument needs W >= 1)")
# ------------------------------------------------------------------ (b)
zs = np.zeros(len(sc), np.int64)
in1 = minplus(zs, sc, BC)                        # min over small a of W(a, c)
out1 = minplus_rev(zs, BC, sc)                   # min over small b of W(c, b)
fo = np.minimum(out1, 7 + D[BC])
fi = np.minimum(in1, 7 + D[BC])
ok_b = [bool((in1 + fo >= 8).all()), bool((fo + D[BC] >= 1).all()), bool((minplus_rev(fo, BC, BC) >= fo).all()),
        bool((fi + out1 >= 8).all()), bool((fi + D[BC] >= 1).all()), bool((minplus(fi, BC, BC) >= fi).all())]
say("(b) f_out = min(min_b W(c,b), 7 + D_c):  min_a W(a,c) + f_out(c) >= 8: %s;  f_out + D >= 1: %s;  W(c,d) >= f_out(c) - f_out(d) "
    "for all %d x %d pairs: %s" % (ok_b[0], ok_b[1], len(BC), len(BC), ok_b[2]))
say("    f_in = min(min_a W(a,c), 7 + D_c):  f_in(c) + min_b W(c,b) >= 8: %s;  f_in + D >= 1: %s;  W(c,d) >= f_in(d) - f_in(c): %s" % (
    ok_b[3], ok_b[4], ok_b[5]))
if not all(ok_b):
    fail("(b) fails: no such functions on the big cuts (joins between big cuts that are cheaper than the detour over small trails)")
bound2 = 6 * NS - 8 + 2 * need_runs
say("COUNTING: 2 cost >= 6 NS - 8 + NS/3 = %d: cost >= %d, every word of the family has at least %d letters" % (
    bound2, (bound2 + 1) // 2, h + sumR + (bound2 + 1) // 2))
# ------------------------------------------------------------------ (e1) chains
succ6 = {}
for i, j in arcs[6].tolist():
    succ6.setdefault(i, []).append(j)
chains = []
sys.setrecursionlimit(100000)


def dfs(path, used):
    if len(path) == 6:
        chains.append((path[0], path[-1], frozenset(used)))
        return
    for j in succ6.get(path[-1], ()):
        if tr[j] not in used:
            used.add(tr[j]); path.append(j)
            dfs(path, used)
            path.pop(); used.discard(tr[j])


for i in range(len(sc)):
    dfs([i], {tr[i]})
sets = sorted(set(c[2] for c in chains), key=sorted)
starts = [c[0] for c in chains]; ends = [c[1] for c in chains]
say("(e1) chains (6 cuts of different small trails, W = 6 between neighbours): %d on %d sets of 6 trails; first cuts all "
    "different: %s, last cuts all different: %s" % (len(chains), len(sets), len(set(starts)) == len(chains), len(set(ends)) == len(chains)))
if len(set(starts)) != len(chains) or len(set(ends)) != len(chains):
    fail("(e1): two chains with the same first or last cut (the search below assumes they differ)")
# ------------------------------------------------------------------ tight joins of the big cuts
psi = fi + fo - 8
assert psi.min() >= 0
Z = np.nonzero(psi == 0)[0]                      # positions in BC
eC = sc[np.array(sorted(set(ends)))]; sC = sc[np.array(sorted(set(starts)))]
eL = sorted(set(ends)); sL = sorted(set(starts))
tin = Wm(eC, BC[Z]) == fi[Z][None, :]            # chain end a before c with W(a,c) = f_in(c)
tout = Wm(BC[Z], sC) == fo[Z][:, None]           # chain start b after c with W(c,b) = f_out(c)
nin = tin.sum(0); nout = tout.sum(1)
say("big cuts with psi = 0: %d; of these with a tight chain end before: %d, a tight chain start after: %d, both: %d" % (
    len(Z), int((nin > 0).sum()), int((nout > 0).sum()), int(((nin > 0) & (nout > 0)).sum())))
has_in = np.zeros(len(BC), bool)
has_in[Z[nin > 0]] = True
pairs = []                                       # tight joins big c -> big d: (c, d, W), positions in BC
for k in range(K + 1):
    cst = 2 * (h - k)
    ka = suf[k][BC] * 4096 + (fo - D[BC] - cst + 64) * 32 + psi
    kb = pre[k][BC] * 4096 + (fo + D[BC] + 64) * 32 + psi
    assert psi.max() < 32 and (fo - D[BC] - cst + 64).min() >= 0 and (fo + D[BC] + 64).max() < 128
    order = np.argsort(kb, kind="stable")
    kbs = kb[order]
    lo = np.searchsorted(kbs, ka, "left"); hi = np.searchsorted(kbs, ka, "right")
    assert int((hi - lo).sum()) < 5000000
    for i in np.nonzero(hi > lo)[0].tolist():
        for j in order[lo[i]:hi[i]].tolist():
            if i != j:
                pairs.append((i, j, cst + int(D[BC[i]] + D[BC[j]])))
P = np.array(pairs, np.int64).reshape(-1, 3)
p0 = P[psi[P[:, 0]] == 0]
bad2 = int((p0[:, 2] <= 0).sum()) + int(has_in[p0[:, 0]].sum())
say("(e2) tight joins between two different big cuts with psi = 0: %d (W values %s); with W <= 0 or a tight chain end "
    "before their first cut: %d" % (len(p0), sorted(set(p0[:, 2].tolist())), bad2))
z0 = P[P[:, 2] == 0]
bad3 = int((ct[BC[z0[:, 0]]] != ct[BC[z0[:, 1]]]).sum())
say("(e3) tight joins with W = 0 between two different big cuts: %d; joining different trails: %d" % (len(z0), bad3))
# ------------------------------------------------------------------ (e4) the relaxed equality problem
solutions = 0
cases = 0
if bad2 == 0 and bad3 == 0:
    if int(nin.max()) > 1 or int(nout.max()) > 1:
        fail("a big cut with two tight chain ends or chain starts (the search below assumes at most one)")
    rows = []                                    # (big trail, chain end e(c), chain start s(c)) for the cuts usable in a block
    for z in np.nonzero((nin > 0) & (nout > 0))[0].tolist():
        rows.append((int(ct[BC[Z[z]]]), eL[int(np.nonzero(tin[:, z])[0][0])], sL[int(np.nonzero(tout[z])[0][0])], int(BC[Z[z]])))
    set_of_start = {c[0]: sets.index(c[2]) for c in chains}
    set_of_end = {c[1]: sets.index(c[2]) for c in chains}
    rot = {}
    for c in chains:
        rot.setdefault(sets.index(c[2]), []).append((c[0], c[1]))
    link = set()
    for i, j in arcs[8].tolist():
        if i in set_of_end and j in set_of_start:
            link.add((i, j))
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
    ncand = {}
    for cov in covers:
        Kc = len(cov)
        loc = {s_: i for i, s_ in enumerate(cov)}
        cand = [r for r in rows if set_of_end[r[1]] in loc and set_of_start[r[2]] in loc]
        ncand[len(cand)] = ncand.get(len(cand), 0) + 1
        assert len(cand) <= 20
        if len(set(r[0] for r in cand)) < len(big_t):
            continue
        for size in range(len(big_t), Kc):
            for U in itertools.combinations(cand, size):
                if len(set(r[0] for r in U)) < len(big_t):
                    continue
                tail, head = {}, {}              # chain (position in the cover) -> cut of U entered after it / left before it
                good = True
                for r in U:
                    a, b = loc[set_of_end[r[1]]], loc[set_of_start[r[2]]]
                    if a in tail or b in head:
                        good = False; break
                    tail[a] = r; head[b] = r
                if not good:
                    continue
                opts = []                        # the chains (start, end) each set may use
                for i, s_ in enumerate(cov):
                    opts.append([c for c in rot[s_] if (i not in tail or c[1] == tail[i][1]) and (i not in head or c[0] == head[i][2])])
                if any(not o for o in opts):
                    continue
                cases += 1
                reach = set((1 << i, i, c) for i in range(Kc) if i not in head for c in opts[i])
                for mask in range(1, 1 << Kc):
                    for i in range(Kc):
                        if not (mask >> i) & 1:
                            continue
                        for c in opts[i]:
                            if (mask, i, c) not in reach:
                                continue
                            for j in range(Kc):
                                if (mask >> j) & 1 or (i in tail) != (j in head):
                                    continue
                                for c2 in opts[j]:
                                    if (tail[i][0] == head[j][0]) if i in tail else ((c[1], c2[0]) in link):
                                        reach.add((mask | (1 << j), j, c2))
                if any(k[0] == (1 << Kc) - 1 and k[1] not in tail for k in reach):
                    solutions += 1
                    say("    a solution of the relaxed problem: sets %s, big cuts %s" % (cov, [r[3] for r in U]))
    say("(e4) families of %d chains covering all small trails: %d (by number of usable big cuts: %s); cases (family, set U "
        "with consistent chains): %d; with an admissible order: %d" % (need_runs, len(covers), dict(sorted(ncand.items())), cases, solutions))
proved = bad2 == 0 and bad3 == 0 and solutions == 0
best = (bound2 + 2) // 2 if proved else (bound2 + 1) // 2
if proved:
    say("THEOREM (checked): every word of the multi-port family has cost >= %d, i.e. at least %d letters.  (%.0f s)" % (best, h + sumR + best, time.time() - t00))
else:
    say("only cost >= %d is proven: at least %d letters  (%.0f s)" % (best, h + sumR + best, time.time() - t00))
# ------------------------------------------------------------------ optional: a single-port word of the family that attains it
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
    say("%s (sha256 %s..): %d letters; a word of the family (one segment per trail), cost %d, h + sum R + cost = %d%s" % (
        args[1].replace("\\\\", "/").split("/")[-1], sha2[:16], len(ww), cst, h + sumR + cst,
        ": the bound is attained, the word is optimal in this family" if h + sumR + cst == len(ww) == h + sumR + best else ""))
