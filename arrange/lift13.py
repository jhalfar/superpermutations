#!/usr/bin/env python
"""lift13.py - lift of any n = 12 plan on the pieces of the transported selection to a plan on its n = 13 pieces.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: lift13.py PLAN12 OUT13.plan SEL [BASE13.txt BASE13.tsv] [--dp-only]
       needs cuts12c.bin

  PLAN12      a plan at n = 12 that writes every one of the 7,200 closed trails once.  Only its ORDER is used.
  OUT13.plan  the lifted plan (not written with --dp-only)
  SEL         the 11-symbol selection with full and short rows that both piece sets come from
  BASE13.txt, BASE13.tsv   the n = 13 base word written by gen13.py from SEL, and its table.  The word is mapped,
              and only the first words of the small pieces are read from it.
  --dp-only   stop after step 1: print what the order costs at n = 12 with every trail cut at a vertex

The piece set.  These scripts were written for one piece set at n = 12, the first one that beat Pantone's pieces:
the 11-symbol selection with full and short rows only (Q = 178,080).  Its numbers are fixed in the code: 7,200
closed trails, of which the first 6,048 of the table are small trails with 110 cuts each (100 at steps of weight 2,
10 at vertices); then 144 trails of the three short walks of every block (63, 133 and 182 loops, one trail each;
kinds 1 to 3 of the table, "short-walk trails" below); then 1,008 big trails.  Letters: 0 .. 6 are the old letters,
7, 8, 9 the added letters, A the distinguished letter, B the completion letter.
At n = 13 the same selection, transported once more by gen13.py, gives 72,000 closed trails in 7,200 units: 6,048
chains of 10 small trails and 1,152 chains of 10 walk trails.

The correspondence (asserted on the words while the script runs):
  a small trail of n = 12 (loop x)   <->  the chain of the 10 small trails above x at n = 13 (trails 10 k .. 10 k + 9
                                          of the base word; joins of cost 1 inside)
  any other trail of n = 12          <->  one chain of 10 walk trails of n = 13 (cut at a full row b of the
                                          transported walk, in one of two ways; ten cuts at steps of weight 2,
                                          joins of cost 0 inside), 1,152 to 1,152
  a cut of the n = 12 trail at a vertex u (9 letters)  <->  the unit written so that its first word is u m and its
                                          last word m' u for some letters m, m' (the letter A of the transported
                                          rows stands for the letter B of n = 12)
So the largest overlap of two units at n = 13 is the overlap of the two vertices at n = 12:
    a join of cost c between two vertices at n = 12 is a join of cost c + 1 between the units at n = 13,
    length13 = 10 + sum R13 + 9 x 6,048 + 10 x 1,152 + 7,199 + (joins of the n = 12 order cut at vertices),
with sum R13 = 6,747,720,000.

What lifts: the order of the trails, with every trail cut at a vertex; for a walk trail, at one of the vertices
that are candidate cuts of its chain (first words at the full rows of the transported walk).
What does not lift: cuts at steps of weight 2 and cuts that drop a repeated permutation.  A plan that uses them is
cut again at vertices in step 1 and loses what they gained (1,463 letters on the plan of 522,740,945 letters).
Not settled: the candidates are 3,282,720 of the 3,628,800 vertices of n = 12.  The other 346,080 are first words
at short rows and repair slices of the transported walks; I did not examine whether a unit can end there.

Steps.
  1. The order of PLAN12 is kept, and every trail gets its best vertex by an exact dynamic programme over the
     allowed vertices (the fixed-order pass, restricted to vertices).
  2. The events of n = 13 are written: the chains of small trails from the base word, the walk chains as in
     order13.py.
Prints the n = 12 cost of the order at vertices, the joins of the n = 13 plan by cost, and its length computed
twice: from the events, and from the formula above.  The line ends with AGREE or DIFFER.

The words of the two plans I lifted were rebuilt and checked: 6,747,810,685 and 6,747,810,280 letters.

Needs: Python 3, numpy; c12.py; gen12.py and gen13.py next to this file or on PYTHONPATH.
All files are read from and written to the working directory.
Time and memory: measured on the plan of 522,740,945 letters: 120 s and 0.89 GB for the whole lift (35 s
for the candidates, a few seconds for the pass over the vertices, the rest for the n = 13 events).
"""
import sys, os, math, time, mmap, collections
import numpy as np
import gen12 as G
import gen13 as G13
import c12

log = lambda *x: print(*x, flush=True)
plan12, out13 = sys.argv[1:3]
SEL = sys.argv[3]
B13, T13 = (sys.argv[4:6] + ["", ""])[:2]
NS12 = 6048
h12, h13, n13 = 9, 10, 13
K, K2, z13 = 10, 11, 12
t0 = time.time()
# ------------------------------------------------------------ n = 12 vertices: the cuts with D = 0 that drop nothing
C = c12.Cuts("cuts12c.bin", log=log)
ns = NS12 * 110
D = C.D
skc = C.col("sk", 0, None)
wall = C.w
v0 = np.nonzero((D == 0) & (skc == 0))[0]  # plain weight-3 cuts
wv = wall[v0].copy()
tv = C.t[v0].copy()
del wall, skc
C._w = None
log("n = 12: %d vertices (plain weight-3 cuts); small %d" % (len(v0), int((tv < NS12).sum())))
# ------------------------------------------------------------ walk chains of n = 13 and their candidates.
# The walks of SEL are transported as gen13.py does it; every full row b of a transported walk gives two candidate
# cuts of its chain, with first words b[:9] and b[1:10], coded in the letters of n = 12.
rows = G.read_sel(SEL)
walks = sorted(G.sel_walks([r for r in rows if r[2] >= 0]), key=len)
cc_code, cc_ci, cc_i0, cc_opt = [], [], [], []
chains = []
RELAB = list(range(16))
RELAB[10] = 11
for wi, wk in enumerate(walks):
    for li, W2 in enumerate(G13.transport_walk(wk)):
        ci = len(chains)
        chains.append((wi, li))
        for i0, r in enumerate(W2):
            if r[2] == K2:
                bb = r[0]
                for opt, S in ((0, bb[:9]), (1, bb[1:10])):
                    c = 0
                    for a in S:
                        c = (c << 4) | RELAB[a]
                    cc_code.append(c)
                    cc_ci.append(ci)
                    cc_i0.append(i0)
                    cc_opt.append(opt)
cc_code = np.array(cc_code, np.int64)
cc_ci = np.array(cc_ci, np.int32)
cc_i0 = np.array(cc_i0, np.int32)
cc_opt = np.array(cc_opt, np.int8)
NCH = len(chains)
log("n = 13: %d walk chains, %d candidate cuts (%.0fs)" % (NCH, len(cc_code), time.time() - t0))
# chain <-> n = 12 trail: every candidate word must be a vertex of n = 12, and all candidates of one chain must
# lie on one trail
o = np.argsort(wv, kind="stable")
wvs = wv[o]
tvs = tv[o]
p = np.searchsorted(wvs, cc_code)
p = np.minimum(p, len(wvs) - 1)
assert (wvs[p] == cc_code).all(), "a candidate of a walk chain is not a vertex of n = 12"
ctrail = tvs[p]
tr_of_chain = np.full(NCH, -1, np.int64)
tr_of_chain[cc_ci] = ctrail
assert (tr_of_chain[cc_ci] == ctrail).all(), "the candidates of one walk chain lie on several trails of n = 12"
assert len(set(tr_of_chain.tolist())) == NCH == C.NT - NS12 and tr_of_chain.min() >= NS12
chain_of_trail = np.full(C.NT, -1, np.int64)
chain_of_trail[tr_of_chain] = np.arange(NCH)
log("every walk chain is one walk trail of n = 12 and conversely; candidate vertices per trail: %d .. %d of %d .. %d vertices" % (
    min(len(set(cc_code[cc_ci == ci].tolist())) for ci in range(0, NCH, 97)),
    max(len(set(cc_code[cc_ci == ci].tolist())) for ci in range(0, NCH, 97)),
    int(np.bincount(tv[tv >= NS12] - NS12).min()), int(np.bincount(tv[tv >= NS12] - NS12).max())))
# states of every trail in step 1: the codes of its allowed vertices (small trails: all 10; walk trails: the
# candidates of its chain)
oc = np.argsort(cc_ci, kind="stable")
cst = np.searchsorted(cc_ci[oc], np.arange(NCH), "left")
cen = np.searchsorted(cc_ci[oc], np.arange(NCH), "right")
states = [None] * C.NT
sm_first = np.searchsorted(tv, np.arange(NS12), "left")
for t in range(NS12):
    states[t] = wv[sm_first[t]:sm_first[t] + 10]
for ci in range(NCH):
    states[int(tr_of_chain[ci])] = np.unique(cc_code[oc[cst[ci]:cen[ci]]])
# ------------------------------------------------------------ step 1: fixed-order pass over the vertices.
# f[y] = the cheapest way to write the trails up to this one with this one cut at vertex y (W = 2 (h - overlap));
# then the vertices are read off backwards.
lines = [l.split() for l in open(plan12).read().split("\n") if l.strip()]
order = [int(e[1]) for e in lines[1:]]
assert sorted(order) == list(range(C.NT)), "the n = 12 plan must write every trail once"
fs = []
f = np.zeros(len(states[order[0]]), np.int64)
fs.append(f)
for i in range(1, len(order)):
    X = states[order[i - 1]]
    Y = states[order[i]]
    f = c12.minplus(X, f, Y, h=h12) // 1
    fs.append(f)
val2 = int(f.min())
cost12 = val2 // 2
assert val2 % 2 == 0
sel = [None] * len(order)
j = int(np.argmin(f))
sel[-1] = int(states[order[-1]][j])
for i in range(len(order) - 2, -1, -1):
    X = states[order[i]]
    y = np.array([sel[i + 1]], np.int64)
    # W(x, y) for all x: via minplus with one query per source is wasteful; direct:
    wcol = np.full(len(X), 2 * h12, np.int64)
    for k in range(1, h12 + 1):
        eq = c12.suffix(X, k) == c12.prefix(y, k, h12)[0]
        wcol = np.where(eq, 2 * (h12 - k), wcol)
    j = int(np.argmin(fs[i] + wcol))
    sel[i] = int(X[j])
log("n = 12, the order of %s re-opened at vertices: joins cost %d letters (length %d as a plan of n = 12)  (%.0fs)" % (
    plan12.replace("\\", "/").split("/")[-1], cost12, 522725280 + 9 + cost12, time.time() - t0))
if "--dp-only" in sys.argv:
    sys.exit(0)
# ------------------------------------------------------------ step 2: n = 13 events
tab = [l.split("\t") for l in open(T13)]
kind = [t[0] for t in tab]
Rt = [int(t[2]) for t in tab]
st13 = [int(t[3]) for t in tab]
NS13 = sum(1 for k in kind if k == "D")
fb = open(B13, "rb")
W = mmap.mmap(fb.fileno(), 0, access=mmap.ACCESS_READ)
FROM = bytes(("0123456789ABCDEF".index(chr(c)) if chr(c) in "0123456789ABCDEF" else 255) for c in range(256))


def cyc(t, pos, ln):
    """ln letters of trail t of the n = 13 base word from offset pos of its piece, read around the closed trail"""
    r = Rt[t]
    pos %= r
    a = st13[t]
    if pos + ln <= r:
        return W[a + pos:a + pos + ln].translate(FROM)
    return (W[a + pos:a + r] + W[a:a + ln - (r - pos)]).translate(FROM)


def canon(x):
    """the cyclic word x read from its smallest letter"""
    i = x.index(min(x))
    return x[i:] + x[:i]


def letters(code, L=9):
    """the L letters of a code (4 bits per letter, first letter highest)"""
    return tuple(int((code >> (4 * (L - 1 - i))) & 15) for i in range(L))


V = [tuple(cyc(t, 0, h13)) for t in range(NS13)]
chain_of_loop = {}
for k in range(NS12):
    vs = V[10 * k:10 * k + 10]
    assert all(vs[j][1:] == vs[(j + 1) % 10][:9] for j in range(10)), "trails 10k .. 10k+9 are not an orbit chain"
    chain_of_loop[canon(vs[0])] = k
ev_of = {}  # position in the order -> list of (event text, first word, last word)
want = {}  # walk chain -> (position, code)
for pos, t in enumerate(order):
    u = letters(sel[pos])
    if t < NS12:
        miss = [x for x in range(10) if x not in u]
        k = chain_of_loop[canon(u + (miss[0],))]
        js = [j for j in range(10) if V[10 * k + j][:9] == u]
        assert len(js) == 1
        tr = [10 * k + (js[0] + s) % 10 for s in range(10)]
        ev_of[pos] = [("O %d 0 3 0" % x, bytes(V[x]), bytes(V[x])) for x in tr]
    else:
        want[int(chain_of_trail[t])] = (pos, sel[pos])
assert len(want) == NCH
# the candidate (row i0, way) of every walk chain whose first word begins with the chosen vertex
chosen = {}
for ci in range(NCH):
    pos, code = want[ci]
    idx = oc[cst[ci]:cen[ci]]
    m = idx[cc_code[idx] == code]
    assert len(m) >= 1
    chosen[ci] = (int(cc_i0[m[0]]), int(cc_opt[m[0]]))
rot, ins = G.rot, G.ins
tidx = NS13
cnum = 0
n, h = n13, h13
for wi, wk in enumerate(walks):
    for li, W2 in enumerate(G13.transport_walk(wk)):
        ci = cnum
        cnum += 1
        i0, opt = chosen[ci]
        b = W2[i0][0]
        assert W2[i0][2] == K2
        nf = sum(1 for r in W2 if r[2] == K2)
        g = math.gcd(K2 - 1, nf - (len(W2) - nf))
        trs = []
        for sl, at in G13.complete_detail(W2, z13, i0):
            offs = [0]
            for (bb, s, v) in sl:
                offs.append(offs[-1] + (n + 1) * v + 1)
            R = offs[-1]
            assert R == Rt[tidx], "R differs from the table"
            hw = cyc(tidx, 0, h)
            r = None
            for q, (bb, s, v) in enumerate(sl):
                if bytes(bb[:h]) == hw:
                    r = offs[q]
                    break
            assert r is not None, "written vertex not found"
            trs.append((tidx, R, offs, at, r))
            tidx += 1
        byport = {}
        for tr in trs:
            for q in tr[3]:
                byport[q] = tr
        bt = tuple(b)
        evs = []
        prevE = None
        lifts = range(0, g) if opt == 0 else range(1, g + 1)
        for q in lifts:
            port = q if q < K2 - 1 else 0
            t, R, offs, at, r = byport[port]
            si = at[port] + (1 if q == K2 - 1 else 0)
            Bq = ins(bt, z13, q)
            S = bytes(rot(Bq, q + 1)[:h])
            E = bytes(rot(Bq, q + 2)[:h])
            assert prevE is None or prevE == S
            prevE = E
            start = (offs[si] + (q + 1) * (n + 1) - r) % R
            evs.append(("O %d %d 2 0" % (t, start), S, E))
        assert len({e[0].split()[1] for e in evs}) == g == 10
        pos, code = want[ci]
        u = letters(code)
        fw = tuple(RELAB[a] for a in evs[0][1][:9])
        lw = tuple(RELAB[a] for a in evs[-1][2][1:])
        assert fw == u and lw == u, "first / last word of the walk chain do not carry the vertex"
        ev_of[pos] = evs
assert tidx == len(tab)


def ov(e, s):
    """largest overlap of the end of word e with the start of word s (n = 13 words, 10 letters)"""
    for q in range(h13, 0, -1):
        if e[-q:] == s[:q]:
            return q
    return 0


out = [e for pos in range(len(order)) for e in ev_of[pos]]
assert len(out) == len(tab) and len({int(e[0].split()[1]) for e in out}) == len(tab)
length = h13 + sum(Rt)
joins = collections.Counter()
for e in out:
    g_ = int(e[0].split()[3])
    length += 3 - g_
for i in range(len(out) - 1):
    c = h13 - ov(out[i][2], out[i + 1][1])
    length += c
    joins[c] += 1
blen = len(W) - (1 if W[len(W) - 1:len(W)] == b"\n" else 0)
with open(out13, "w", newline="\n") as fo:
    fo.write("TRAILSEARCH-PLAN 13 %d %d\n" % (blen, len(out)))
    for e in out:
        fo.write(e[0] + "\n")
pred = h13 + sum(Rt) + 9 * NS12 + 10 * NCH + cost12 + (len(order) - 1)
log("n = 13 plan %s: %d events; joins by cost %s" % (out13, len(out), dict(sorted(joins.items()))))
log("predicted length %d (formula from the n = 12 cost: %d)  %s  (%.0fs)" % (length, pred,
    "AGREE" if length == pred else "DIFFER", time.time() - t0))
