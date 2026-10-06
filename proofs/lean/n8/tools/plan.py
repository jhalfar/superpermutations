"""Cut the search `K.fsearch A Cc Bd fuel` into parts that the Lean kernel can evaluate one at a time, and write
the Lean files.

The search tree is computed here with ksim.py (the Python mirror of KSearch.lean).  Nothing computed here is
trusted by Lean: every generated lemma is checked by `decide +kernel`, and a wrong plan makes a lemma fail.

A plan node is a state X of the search with fuel F.
* If the subtree below X is small, one lemma checks it:   fsearchK … F X [] = false.
* Otherwise the plan picks a depth `a`, lists the paths of length `a` that the search reaches below X (the
  cover), and proves
      cover lemma:   fsearchK (leafCover cover) a X [] = false          (the search reaches no other path)
      for the end Y of every path:   Ref (F - a) Y                       (groups of small subtrees by one lemma,
                                                                          a large subtree by its own plan node)
  `K.ref_of_cover` (KSound.lean) puts them together.

usage: plan.py A Cc Bd fuel NAME OUTDIR [--leaf N] [--band N] [--per-file N]
  writes OUTDIR/K<NAME>Defs.lean, OUTDIR/K<NAME>S<i>.lean (the lemmas), OUTDIR/K<NAME>.lean (the assembly) and
  OUTDIR/../modules_<NAME>.txt (module names in build order).
"""
import sys, os, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ksim
sys.setrecursionlimit(1000000)

ap = argparse.ArgumentParser()
ap.add_argument("A", type=int); ap.add_argument("Cc", type=int); ap.add_argument("Bd", type=int)
ap.add_argument("fuel", type=int); ap.add_argument("name"); ap.add_argument("outdir")
ap.add_argument("--leaf", type=int, default=5000, help="largest subtree checked by one lemma")
ap.add_argument("--band", type=int, default=2500, help="largest number of states expanded by one cover lemma")
ap.add_argument("--per-file", type=int, default=20000, help="states per generated file (approximate)")
args = ap.parse_args()
A, Cc, Bd, FUEL, NAME = args.A, args.Cc, args.Bd, args.fuel, args.name

# ---------------------------------------------------------------- the tree (structure only)
class Node:
    __slots__ = ("kids", "size", "h")
    def __init__(self): self.kids = []; self.size = 1; self.h = 1

def build(st, fuel):
    n = Node()
    if fuel == 0 or Bd < st[3]:
        raise SystemExit("the search returns true (fuel exhausted or a trail found); nothing to prove")
    for c in ksim.children(A, Cc, st):
        k = build(c, fuel - 1)
        n.kids.append(k); n.size += k.size
        if k.h + 1 > n.h: n.h = k.h + 1
    return n

roots = ksim.rootChildren(A, Cc)
if len(roots) != 1:
    raise SystemExit(f"{len(roots)} states after the first row; this generator handles one")
root = build(roots[0], FUEL)
print(f"fsearch {A} {Cc} {Bd} {FUEL}: {root.size} calls of fsearchK")

def level(node, a):
    """paths (lists of child indices) of the nodes at depth a below node, with the nodes, in search order"""
    out = []
    def go(n, d, path):
        if d == a:
            out.append((list(path), n)); return
        for i, k in enumerate(n.kids):
            path.append(i); go(k, d + 1, path); path.pop()
    go(node, 0, [])
    return out

def band(node, a):
    """number of states at depth < a below node (the states a cover lemma expands)"""
    if a == 0: return 0
    return 1 + sum(band(k, a - 1) for k in node.kids)

# ---------------------------------------------------------------- the plan
class Plan:
    def __init__(self, ident, path_chain, fuel, node):
        self.id = ident; self.chain = path_chain; self.fuel = fuel; self.node = node
        self.a = None; self.groups = []     # groups: ("leafgroup", [paths], states) or ("child", path, Plan)

plans = []          # all internal plan nodes, parents before children
lemmas = []         # (kind, plan, group index, cost)

def make(ident, chain, fuel, node):
    P = Plan(ident, chain, fuel, node)
    plans.append(P)
    if node.size <= args.leaf:
        P.a = 0
        lemmas.append(("leaf", P, None, node.size))
        return P
    h = node.h
    # deepest cut whose band fits; then the narrowest level among the last five
    amax = 1
    for a in range(1, h):
        if band(node, a) > args.band: break
        amax = a
    best = min(range(max(1, amax - 4), amax + 1), key=lambda a: (len(level(node, a)), -a))
    lv = level(node, best)
    if max(n.size for _, n in lv) >= node.size - 1 and best < amax:
        best = amax; lv = level(node, best)
    P.a = best
    lemmas.append(("cover", P, None, band(node, best)))
    cur, cur_size = [], 0
    def flush():
        nonlocal cur, cur_size
        if cur:
            P.groups.append(("leafgroup", cur, cur_size))
            lemmas.append(("group", P, len(P.groups) - 1, cur_size + best * len(cur)))
            cur, cur_size = [], 0
    for path, n in lv:
        if n.size > args.leaf:
            flush()
            child = make(f"{ident}_{len(P.groups)}", chain + [path], fuel - best, n)
            P.groups.append(("child", path, child))
        else:
            if cur and cur_size + n.size > args.leaf: flush()
            cur.append(path); cur_size += n.size
    flush()
    return P

top = make("n", [], FUEL, root)
print(f"plan: {len(plans)} plan nodes, {len(lemmas)} lemmas for the kernel;",
      f"largest lemma about {max(l[3] for l in lemmas)} states; total {sum(l[3] for l in lemmas)} states")

# ---------------------------------------------------------------- Lean
def lst(xs): return "[" + ", ".join(str(x) for x in xs) + "]"
def rp(path): return lst(list(reversed(path)))            # paths are stored last step first
P5 = f"{A} {Cc}"
P6 = f"{A} {Cc} {Bd}"
NS = f"K{NAME}"

def st_name(P): return f"{P.id}_st"
defs = [f"""/-
Generated by tools/plan.py {A} {Cc} {Bd} {FUEL} {NAME} (leaf {args.leaf}, band {args.band}).  Do not edit.
The states and path lists of the plan that cuts `K.fsearch {P6} {FUEL}` into parts.
Nothing here is trusted: the lemmas of the files {NS}S*.lean are checked by the kernel.
-/
import Superperm8.KSearch

namespace Superperm8
namespace {NS}
open K
"""]
for P in plans:
    for g in P.groups:
        if g[0] == "child": g[2].parent = P
for P in plans:
    if not P.chain:
        defs.append(f"/-- The state after the first row. -/\ndef {st_name(P)} : St := rootSt {P5}\n")
    else:
        defs.append(f"def {st_name(P)} : St :=\n  stepPath {P5} {st_name(P.parent)} ({rp(P.chain[-1])} : List Nat).reverse\n")
    for gi, g in enumerate(P.groups):
        if g[0] == "leafgroup":
            defs.append(f"def {P.id}_g{gi} : List (List Nat) :=\n  [" + ",\n   ".join(rp(p) for p in g[1]) + "]\n")
        else:
            defs.append(f"def {P.id}_g{gi} : List (List Nat) := [{rp(g[1])}]\n")
    if P.groups:
        cover = " ++ (".join(f"{P.id}_g{gi}" for gi in range(len(P.groups))) + " ++ []" + ")" * (len(P.groups) - 1)
        defs.append(f"def {P.id}_cover : List (List Nat) := {cover}\n")
defs.append(f"end {NS}\nend Superperm8\n")

def lemma_text(kind, P, gi):
    T = "(fun _ _ => true)"
    if kind == "leaf":
        return (f"theorem {P.id}_ref : Ref {P6} {P.fuel} {st_name(P)} := by\n"
                f"  show fsearchK {P6} {T} {P.fuel} {st_name(P)} [] = false\n  decide +kernel\n")
    if kind == "cover":
        return (f"theorem {P.id}_cov : fsearchK {P6} (leafCover {P.id}_cover) {P.a} {st_name(P)} [] = false := by\n"
                f"  decide +kernel\n")
    b = P.fuel - P.a
    return (f"theorem {P.id}_g{gi}_ok : ({P.id}_g{gi}).all (fun rp =>\n"
            f"    !fsearchK {P6} {T} {b} (stepPath {P5} {st_name(P)} rp.reverse) []) = true := by\n"
            f"  decide +kernel\n")

files, cur, cur_cost = [], [], 0
for (kind, P, gi, cost) in lemmas:
    if cur and cur_cost + cost > args.per_file:
        files.append(cur); cur, cur_cost = [], 0
    cur.append((kind, P, gi, cost)); cur_cost += cost
if cur: files.append(cur)

os.makedirs(args.outdir, exist_ok=True)
def write(name, text):
    with open(os.path.join(args.outdir, name), "w", encoding="utf-8", newline="\n") as f: f.write(text)

write(f"{NS}Defs.lean", "\n".join(defs))
mods = [f"{NS}Defs"]
for i, fl in enumerate(files):
    body = [f"""/-
Generated by tools/plan.py {A} {Cc} {Bd} {FUEL} {NAME}.  Do not edit.
Part {i + 1} of {len(files)} of the kernel evaluation of `K.fsearch {P6} {FUEL}` (about {sum(l[3] for l in fl)} states).
-/
import Superperm8.{NS}Defs

namespace Superperm8
namespace {NS}
open K
set_option maxRecDepth 100000
"""]
    for (kind, P, gi, cost) in fl:
        body.append(f"-- about {cost} states\n" + lemma_text(kind, P, gi))
    body.append(f"end {NS}\nend Superperm8\n")
    write(f"{NS}S{i:02d}.lean", "\n".join(body))
    mods.append(f"{NS}S{i:02d}")

# assembly
asm = [f"""/-
Generated by tools/plan.py {A} {Cc} {Bd} {FUEL} {NAME}.  Do not edit.
`K.fsearch {P6} {FUEL} = false`, put together from the parts {NS}S00 … {NS}S{len(files) - 1:02d} with `K.ref_of_cover`.
-/
import Superperm8.KSound
""" + "".join(f"import Superperm8.{m}\n" for m in mods[1:]) + f"""
namespace Superperm8
namespace {NS}
open K
"""]
for P in reversed(plans):               # children before parents
    if P.a == 0: continue               # leaf: its lemma is `{id}_ref`
    b = P.fuel - P.a
    terms = []
    for gi, g in enumerate(P.groups):
        if g[0] == "leafgroup":
            terms.append(f"(refs_of_all {P6} {b} {st_name(P)} {P.id}_g{gi} {P.id}_g{gi}_ok)")
        else:
            terms.append(f"(forall_cons (P := fun rp => Ref {P6} {b} (stepPath {P5} {st_name(P)} rp.reverse))\n"
                         f"      {g[2].id}_ref forall_nil)")
    proof = "forall_nil"
    for t in reversed(terms):
        proof = f"(forall_append {t}\n    {proof})"
    asm.append(f"theorem {P.id}_ref : Ref {P6} {P.fuel} {st_name(P)} :=\n"
               f"  ref_of_cover {P6} {P.a} {b} {st_name(P)} {P.id}_cover {P.id}_cov\n    {proof}\n")
asm.append(f"""theorem rootChildren_length : (rootChildren {P5}).length = 1 := by decide +kernel

end {NS}

/-- The search on numbers finds nothing: evaluated by the kernel in {len(lemmas)} parts. -/
theorem fsearch_{A}_{Cc}_{Bd} : K.fsearch {P6} {FUEL} = false :=
  K.fsearch_false {P6} {FUEL} {NS}.rootChildren_length {NS}.n_ref

end Superperm8
""")
write(f"{NS}.lean", "\n".join(asm))
mods.append(NS)
with open(os.path.join(args.outdir, "..", f"modules_{NAME}.txt"), "w", newline="\n") as f:
    f.write("\n".join(mods) + "\n")
print(f"wrote {len(files)} part files, {NS}Defs.lean, {NS}.lean; modules in modules_{NAME}.txt")
for i, fl in enumerate(files):
    print(f"  {NS}S{i:02d}: {len(fl)} lemmas, about {sum(l[3] for l in fl)} states")
