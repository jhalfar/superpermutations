"""Cut the search `S.search k A q2 C1 C2 bn fuel` (LowerBounds/SSearch.lean) into parts that the Lean kernel can
evaluate one at a time, and write the Lean files (adapted from the generator of an earlier search on eight
symbols).

The search tree is computed here with s_ksim.py (the Python mirror of SSearch.lean).  Nothing computed here is
trusted by Lean: every generated lemma is checked by `decide +kernel`, and a wrong plan makes a lemma fail.

A plan node is a state X of the search with fuel F.
* If the subtree below X is small, one lemma checks it:   goK ... F X [] = false.
* Otherwise the plan picks a depth `a`, lists the paths of length `a` that the search reaches below X (the
  cover), and proves
      cover lemma:   goK (leafCover cover) a X [] = false                 (the search reaches no other path)
      for the end Y of every path:   Ref (F - a) Y                         (groups of small subtrees by one lemma,
                                                                            a large subtree by its own plan node)
  `S.ref_of_cover` (SCut.lean) puts them together; `S.search_false` joins the states after the first piece.

usage: s_plan.py k cn bn q NAME [--fuel F] [--leaf N] [--band N] [--per-file N] [--maxh H]
  writes LowerBounds/SGen/<NAME>Defs.lean, <NAME>P<i>.lean (the lemmas), <NAME>.lean (the assembly) and
  s_gen_<NAME>.txt (module names in build order; the part files are independent of each other).
"""
import sys, os, argparse
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import s_ksim as ks
sys.setrecursionlimit(1000000)

ap = argparse.ArgumentParser()
ap.add_argument("k", type=int); ap.add_argument("cn", type=int); ap.add_argument("bn", type=int)
ap.add_argument("q", type=int); ap.add_argument("name")
ap.add_argument("--fuel", type=int, default=0, help="fuel of the search (default: deepest prefix in pieces)")
ap.add_argument("--leaf", type=int, default=1000, help="largest subtree checked by one lemma")
ap.add_argument("--band", type=int, default=500, help="largest number of states expanded by one cover lemma")
ap.add_argument("--per-file", type=int, default=6000, help="states per generated file (approximate)")
ap.add_argument("--maxh", type=int, default=150, help="largest height of a subtree checked by one lemma")
ap.add_argument("--dry", action="store_true", help="print the plan only")
args = ap.parse_args()
K, CN, BN, Q, NAME = args.k, args.cn, args.bn, args.q, args.name
A, Q2, C1, C2 = ks.params(K, CN, BN, Q)

# ---------------------------------------------------------------- the tree (structure only)
class Node:
    __slots__ = ("kids", "size", "h")
    def __init__(self): self.kids = []; self.size = 1; self.h = 1

seen = set()
def build(st):
    n = Node()
    if ks.viol(C1, BN, st):
        raise SystemExit("the search returns true (a violating window is found); nothing to prove")
    for ch, added in ks.children(K, A, Q2, C2, st, seen):
        seen.update(added)
        kd = build(ch)
        seen.difference_update(added)
        n.kids.append(kd); n.size += kd.size
        if kd.h + 1 > n.h: n.h = kd.h + 1
    return n

roots = []
for ch, added in ks.root_children(K, A, Q2, C2):
    seen.update(added)
    roots.append(build(ch))
    seen.difference_update(added)
total = sum(r.size for r in roots)
height = max(r.h for r in roots)
FUEL = args.fuel if args.fuel else height
if FUEL < height:
    raise SystemExit(f"fuel {FUEL} is less than the deepest prefix {height}")
print(f"search {K} {A} {Q2} {C1} {C2} {BN} {FUEL}: {len(roots)} states after the first piece, {total} calls of goK, "
      f"deepest prefix {height} pieces")

def level(node, a):
    """paths (lists of child indices) of the nodes at depth a below node, with the nodes, in search order"""
    out = []
    def go(n, d, path):
        if d == a:
            out.append((list(path), n)); return
        for i, kd in enumerate(n.kids):
            path.append(i); go(kd, d + 1, path); path.pop()
    go(node, 0, [])
    return out

def band(node, a, cap):
    """number of states at depth < a below node (the states a cover lemma expands), stopped above cap"""
    cnt = 0
    stack = [(node, 0)]
    while stack:
        n, d = stack.pop()
        if d >= a: continue
        cnt += 1
        if cnt > cap: return cnt
        for kd in n.kids: stack.append((kd, d + 1))
    return cnt

# ---------------------------------------------------------------- the plan
class Plan:
    def __init__(self, ident, fuel, node, parent, path):
        self.id = ident; self.fuel = fuel; self.node = node; self.parent = parent; self.path = path
        self.a = None; self.groups = []     # groups: ("leafgroup", [paths], states) or ("child", path, Plan)

plans = []          # all plan nodes, parents before children
lemmas = []         # (kind, plan, group index, cost)

def small(node):
    return node.size <= args.leaf and node.h <= args.maxh

def make(ident, fuel, node, parent, path):
    P = Plan(ident, fuel, node, parent, path)
    plans.append(P)
    if small(node):
        P.a = 0
        lemmas.append(("leaf", P, None, node.size))
        return P
    h = node.h
    amax = 1
    for a in range(1, min(h, args.maxh + 1)):
        if band(node, a, args.band) > args.band: break
        amax = a
    cands = range(max(1, amax - 4), amax + 1)
    best = min(cands, key=lambda a: (len(level(node, a)), -a))
    lv = level(node, best)
    if lv and max(n.size for _, n in lv) >= node.size - 1 and best < amax:
        best = amax; lv = level(node, best)
    P.a = best
    lemmas.append(("cover", P, None, band(node, best, 10 ** 9)))
    cur, cur_size = [], 0
    def flush():
        nonlocal cur, cur_size
        if cur:
            P.groups.append(("leafgroup", cur, cur_size))
            lemmas.append(("group", P, len(P.groups) - 1, cur_size))
            cur, cur_size = [], 0
    for pth, n in lv:
        if not small(n):
            flush()
            child = make(f"{ident}_{len(P.groups)}", fuel - best, n, P, pth)
            P.groups.append(("child", pth, child))
        else:
            # a group lemma walks to the end of each path (`best` states) and then searches below it
            if cur and cur_size + n.size + best > args.leaf: flush()
            cur.append(pth); cur_size += n.size + best
    flush()
    return P

tops = [make(f"r{i}", FUEL, r, None, None) for i, r in enumerate(roots)]
print(f"plan: {len(plans)} plan nodes, {len(lemmas)} lemmas for the kernel;",
      f"largest lemma about {max(l[3] for l in lemmas)} states; total {sum(l[3] for l in lemmas)} states")
if args.dry:
    sys.exit(0)

# ---------------------------------------------------------------- Lean
def lst(xs): return "[" + ", ".join(str(x) for x in xs) + "]"
def rp(path): return lst(list(reversed(path)))            # paths are stored last step first
P4 = f"{K} {A} {Q2} {C2}"
P6 = f"{K} {A} {Q2} {C1} {C2} {BN}"
NS = NAME
D0 = "⟨0, Tr.leaf, 0, 0, 0⟩"
HEAD = f"s_plan.py {K} {CN} {BN} {Q} {NAME} (fuel {FUEL}, leaf {args.leaf}, band {args.band}, maxh {args.maxh})"

def st_name(P): return f"{P.id}_st"
defs = [f"""/-
Generated by {HEAD}.  Do not edit.
The states and path lists of the plan that cuts `S.search {P6} {FUEL}` into parts.
Nothing here is trusted: the lemmas of the files {NS}P*.lean are checked by the kernel.
-/
import LowerBounds.SSearch

namespace SuperpermLowerBounds
namespace SGen
namespace {NS}
open S
"""]
for P in plans:
    if P.parent is None:
        i = tops.index(P)
        defs.append(f"/-- State number {i} after the first piece. -/\nnoncomputable def {st_name(P)} : St :=\n"
                    f"  nthD (rootChildren {P4}) {i} {D0}\n")
    else:
        defs.append(f"noncomputable def {st_name(P)} : St :=\n"
                    f"  stepPath {P4} {st_name(P.parent)} ({rp(P.path)} : List Nat).reverse\n")
    for gi, g in enumerate(P.groups):
        if g[0] == "leafgroup":
            defs.append(f"def {P.id}_g{gi} : List (List Nat) :=\n  [" + ",\n   ".join(rp(p) for p in g[1]) + "]\n")
        else:
            defs.append(f"def {P.id}_g{gi} : List (List Nat) := [{rp(g[1])}]\n")
    if P.a:
        if P.groups:
            cover = " ++ (".join(f"{P.id}_g{gi}" for gi in range(len(P.groups))) + " ++ []" + ")" * (len(P.groups) - 1)
        else:
            cover = "[]"
        defs.append(f"def {P.id}_cover : List (List Nat) := {cover}\n")
defs.append(f"end {NS}\nend SGen\nend SuperpermLowerBounds\n")

def lemma_text(kind, P, gi):
    T = "(fun _ _ => true)"
    if kind == "leaf":
        return (f"theorem {P.id}_ref : Ref {P6} {P.fuel} {st_name(P)} := by\n"
                f"  show goK {P6} {T} {P.fuel} {st_name(P)} [] = false\n  decide +kernel\n")
    if kind == "cover":
        return (f"theorem {P.id}_cov : goK {P6} (leafCover {P.id}_cover) {P.a} {st_name(P)} [] = false := by\n"
                f"  decide +kernel\n")
    b = P.fuel - P.a
    return (f"theorem {P.id}_g{gi}_ok : ({P.id}_g{gi}).all (fun rp =>\n"
            f"    !goK {P6} {T} {b} (stepPath {P4} {st_name(P)} rp.reverse) []) = true := by\n"
            f"  decide +kernel\n")

files, cur, cur_cost = [], [], 0
for (kind, P, gi, cost) in lemmas:
    if cur and cur_cost + cost > args.per_file:
        files.append(cur); cur, cur_cost = [], 0
    cur.append((kind, P, gi, cost)); cur_cost += cost
if cur: files.append(cur)

outdir = os.path.join(HERE, "LowerBounds", "SGen")
os.makedirs(outdir, exist_ok=True)
def write(name, text):
    with open(os.path.join(outdir, name), "w", encoding="utf-8", newline="\n") as f: f.write(text)

write(f"{NS}Defs.lean", "\n".join(defs))
mods = [f"{NS}Defs"]
ndig = max(2, len(str(len(files) - 1)))
for i, fl in enumerate(files):
    body = [f"""/-
Generated by {HEAD}.  Do not edit.
Part {i + 1} of {len(files)} of the kernel evaluation of `S.search {P6} {FUEL}` (about {sum(l[3] for l in fl)} states).
-/
import LowerBounds.SGen.{NS}Defs

namespace SuperpermLowerBounds
namespace SGen
namespace {NS}
open S
set_option maxRecDepth 100000
"""]
    for (kind, P, gi, cost) in fl:
        body.append(f"-- about {cost} states\n" + lemma_text(kind, P, gi))
    body.append(f"end {NS}\nend SGen\nend SuperpermLowerBounds\n")
    pn = f"{NS}P{i:0{ndig}d}"
    write(f"{pn}.lean", "\n".join(body))
    mods.append(pn)

# assembly
asm = [f"""/-
Generated by {HEAD}.  Do not edit.
`S.search {P6} {FUEL} = false`, put together from the parts {mods[1]} … {mods[-1]} with `S.ref_of_cover`
and `S.search_false`.
-/
import LowerBounds.SCut
""" + "".join(f"import LowerBounds.SGen.{m}\n" for m in mods[1:]) + f"""
namespace SuperpermLowerBounds
namespace SGen
namespace {NS}
open S
set_option maxRecDepth 100000
"""]
for P in reversed(plans):               # children before parents
    if P.a == 0: continue               # leaf: its lemma is `{id}_ref`
    b = P.fuel - P.a
    terms = []
    for gi, g in enumerate(P.groups):
        if g[0] == "leafgroup":
            terms.append(f"(refs_of_all {P6} {b} {st_name(P)} {P.id}_g{gi} {P.id}_g{gi}_ok)")
        else:
            terms.append(f"(forall_cons (P := fun rp => Ref {P6} {b} (stepPath {P4} {st_name(P)} rp.reverse))\n"
                         f"      {g[2].id}_ref forall_nil)")
    proof = "forall_nil"
    for t in reversed(terms):
        proof = f"(forall_append {t}\n    {proof})"
    asm.append(f"theorem {P.id}_ref : Ref {P6} {P.fuel} {st_name(P)} :=\n"
               f"  ref_of_cover {P6} {P.a} {b} {st_name(P)} {P.id}_cover {P.id}_cov\n    {proof}\n")
allp = "S.forall_lt_zero"
PP = (f"(P := fun i => S.Ref {P6} {FUEL} (S.nthD (S.rootChildren {P4}) i "
      f"{D0.replace('Tr.leaf', 'S.Tr.leaf')}))")
for P in tops:
    allp = f"(S.forall_lt_succ {PP}\n      {allp} {NS}.{P.id}_ref)"
asm.append(f"""theorem rootChildren_length : (rootChildren {P4}).length = {len(tops)} := by decide +kernel

end {NS}

/-- The search on numbers finds nothing: evaluated by the kernel in {len(lemmas)} parts. -/
theorem search_{NS} : S.search {P6} {FUEL} = false :=
  S.search_false {P6} {FUEL} {len(tops)} {D0.replace('Tr.leaf', 'S.Tr.leaf')} {NS}.rootChildren_length
    {allp}

end SGen
end SuperpermLowerBounds
""")
write(f"{NS}.lean", "\n".join(asm))
mods.append(NS)
with open(os.path.join(HERE, f"s_gen_{NAME}.txt"), "w", newline="\n") as f:
    f.write("\n".join(mods) + "\n")
print(f"wrote {len(files)} part files, {NS}Defs.lean, {NS}.lean; modules in s_gen_{NAME}.txt")
for i, fl in enumerate(files):
    print(f"  {mods[1 + i]}: {len(fl)} lemmas, about {sum(l[3] for l in fl)} states")
