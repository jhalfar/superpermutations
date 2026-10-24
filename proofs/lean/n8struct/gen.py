"""Computes the finite data for the Lean files of n8struct and prints it (Lean syntax) to gen_out.txt and
gen_out2.txt.

Uses the model of the n = 8 tool (words/n8/tools/n8lib/model.py of this repository), read only.  Run:
  python3 gen.py [OUTDIR]          (default: this directory; build.sh writes into the build directory)
"""
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
N8 = os.path.join(ROOT, "words", "n8")
OUT = sys.argv[1] if len(sys.argv) > 1 else HERE
sys.path.insert(0, os.path.join(N8, "tools"))
from n8lib import model as M  # noqa: E402

VS = [int(c) for c in "266646664666466466646664666"]
ID = tuple(range(6))
STATES = M.STATES
out = []


def L(x):
    return "[" + ",".join(map(str, x)) + "]"


def relabel(s, x):
    return tuple(s[a] for a in x)


def inv(s):
    r = [0] * 6
    for i, a in enumerate(s):
        r[a] = i
    return tuple(r)


def walk(g):
    rows = []
    x = g
    for v in VS:
        rows.append((x, v))
        x = M.gstep(x, v)
    return rows, x


def loops(g):
    return [M.canon(x) for x, v in walk(g)[0]]


def disj(g, h):
    return not (set(loops(g)) & set(loops(h)))


# ---- walk: slices and a trail order
rows, end = walk(ID)
assert end == ID and len(set(loops(ID))) == 27


def complete_rows(x, v):
    """Pantone's Completion.completeRows <x, 6, v> 7 as (base, satellite, visible)."""
    lift = [(x[:j] + (7,) + x[j:], 6, v + (1 if j < v else 0)) for j in range(6)]
    rep = [(x[j:] + x[:j] + (6,), 7, 7) for j in range(v, 6)]
    return lift + rep


def head(r):
    return r[0][:5]


def tail(r):
    b, s, vis = r
    k = (vis + 1) % len(b)
    return (b[k:] + b[:k])[:5]


sl = [r for x, v in rows for r in complete_rows(x, v)]
assert len(sl) == 178
hidx = {head(r): i for i, r in enumerate(sl)}
assert len(hidx) == 178
order = [0]
while True:
    j = hidx[tail(sl[order[-1]])]
    if j == 0:
        break
    order.append(j)
assert len(order) == 178
# cross-check against the tool's slice strings
strs = [s for x, v in rows for _, s in M.option_slices(x, v)]
cyc, succ = M.trail_cycles(strs)
assert len(cyc) == 1
out.append("-- walk27 trail order (indices into packingRows walk27 7)")
out.append("def trailOrder : List Nat := " + L(order))

# ---- packings
C = [h for h in STATES if h != ID and disj(ID, h)]
out.append("-- partners of the identity placement: %d" % len(C))
out.append("def partners : List State := [" + ", ".join(L(h) for h in C) + "]")
triples = []
for a, b, c in itertools.permutations(C, 3):
    if disj(a, b) and disj(a, c) and disj(b, c):
        triples.append((a, b, c))
out.append("-- ordered triples completing the identity: %d" % len(triples))
packs_id = sorted(set(tuple(sorted((ID,) + t)) for t in triples))
assert len(packs_id) == 2
for k, p in enumerate(packs_id):
    out.append("def K%d : List State := [" % k + ", ".join(L(g) for g in p) + "]")
out.append("def completingTriples : List (List State) := [" + ", ".join(
    "[" + ", ".join(L(g) for g in t) + "]" for t in triples) + "]")


def key(p):
    return tuple(sorted(p))


def act(s, p):
    return key(relabel(s, g) for g in p)


K0, K1 = packs_id
stab0 = [s for s in STATES if act(s, K0) == key(K0)]
stab1 = [s for s in STATES if act(s, K1) == key(K1)]
out.append("-- stabiliser of K0: " + " ".join(map(L, stab0)))
out.append("-- stabiliser of K1: " + " ".join(map(L, stab1)))
assert not any(act(s, K0) == key(K1) for s in STATES)

# count of all packings (cross-check)
allp = set()
for s in STATES:
    allp.add(act(s, K0))
    allp.add(act(s, K1))
out.append("-- all packings: %d" % len(allp))
pairs = sum(1 for g in STATES for h in STATES if g < h and disj(g, h))
out.append("-- compatible pairs: %d" % pairs)

# ---- published selection
sel = M.read_selection(os.path.join(N8, "selection-46174.txt"))
starts = sorted(x for L_, (x, v) in sel.items() if v == 2)
assert len(starts) == 4
for g in starts:
    r, e = walk(g)
    assert e == g and all(sel[M.canon(x)] == (x, v) for x, v in r)
Pstar = key(starts)
out.append("def Pstar : List State := [" + ", ".join(L(g) for g in Pstar) + "]")
for k, K in enumerate((K0, K1)):
    ts = [s for s in STATES if act(s, K) == Pstar]
    if ts:
        out.append("-- Pstar = relabel %s of K%d" % (L(ts[0]), k))
rowless = sorted(L_ for L_, (x, v) in sel.items() if v == 0)
out.append("def leftover : List State := [" + ", ".join(L(x) for x in rowless) + "]")
V4 = [ID, (0, 1, 5, 4, 3, 2), (1, 0, 2, 4, 3, 5), (1, 0, 5, 3, 4, 2)]
for s in V4:
    perm = [Pstar.index(relabel(s, g)) if relabel(s, g) in Pstar else None for g in Pstar]
    fixed = all(M.canon(relabel(s, x)) == x for x in rowless)
    out.append("-- V4 %s: walk permutation %s, leftover loops fixed pointwise %s, stabilises %s" % (
        L(s), perm, fixed, act(s, Pstar) == Pstar))


# ---- reversal
def rev_row(x, v):
    y = tuple(reversed(x))
    k = (7 - v) % 6
    return (y[k:] + y[:k], v)


def word(r):
    b, d, vis = r
    s = b + (d,) + b
    for t in range(vis - 1):
        bt = b[t:] + b[:t]
        bt1 = b[t + 1:] + b[:t + 1]
        s += bt[:1] + (d,) + bt1
    return s


for x in STATES:
    for v in (2, 4, 6):
        y, v2 = rev_row(x, v)
        a = sorted(tuple(reversed(word(r))) for r in complete_rows(x, v))
        b = sorted(word(r) for r in complete_rows(y, v2))
        assert a == b, (x, v)
revrows = [rev_row(x, v) for x, v in sel.values() if v]
# the reversed packing: its start states are the states of its rows with v = 2
rstarts = key(x for x, v in revrows if v == 2)
for g in rstarts:
    r, e = walk(g)
    assert e == g
assert sorted(revrows) == sorted(rv for g in rstarts for rv in walk(g)[0])
out.append("def PstarRev : List State := [" + ", ".join(L(g) for g in rstarts) + "]")
for k, K in enumerate((K0, K1)):
    ts = [s for s in STATES if act(s, K) == rstarts]
    if ts:
        out.append("-- PstarRev = relabel %s of K%d" % (L(ts[0]), k))
    ts = [s for s in STATES if act(s, K) == Pstar]
# rowless loops under reversal: loop L -> canon(reverse L)
for x in rowless:
    a = sorted(tuple(reversed(word((x[j:] + x[:j] + (6,), 7, 7)))) for j in range(6))
    y = M.canon(tuple(reversed(x)))
    b = sorted(word((y[j:] + y[:j] + (6,), 7, 7)) for j in range(6))
    assert a == b
with open(os.path.join(OUT, "gen_out.txt"), "w", encoding="utf-8", newline="\n") as f:
    f.write("\n".join(out) + "\n")
print("\n".join(o for o in out if o.startswith("--")))
for s in V4[1:]:
    imgs = [rowless.index(M.canon(relabel(s, x))) for x in rowless]
    print("V4", L(s), "on leftover loops:", imgs)
selrows = sorted((x, v) for L_, (x, v) in sel.items() if v)
with open(os.path.join(OUT, "gen_out.txt"), "a", encoding="utf-8", newline="\n") as f:
    f.write("def selectionRows : List (State × Nat) := [" + ", ".join("(%s, %d)" % (L(x), v) for x, v in selrows) + "]\n")
extra = []
extra.append("def basesId : List State := [" + ", ".join(L(x) for x, v in walk(ID)[0]) + "]")
extra.append("def loopsId : List State := [" + ", ".join(L(x) for x in loops(ID)) + "]")
extra.append("def partnerTable : List (State × List State) := [" + ", ".join(
    "(%s, [%s])" % (L(h), ", ".join(L(x) for x in loops(h))) for h in C) + "]")
cov = [M.canon(x) for g in Pstar for x, v in walk(g)[0]]
extra.append("def coveredLoops : List State := [" + ", ".join(L(x) for x in cov) + "]")
with open(os.path.join(OUT, "gen_out2.txt"), "w", encoding="utf-8", newline="\n") as f:
    f.write("\n".join(extra) + "\n")
