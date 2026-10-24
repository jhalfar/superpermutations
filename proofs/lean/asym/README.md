# The shortest superpermutation: (L(n) - F3(n)) / (n-3)! tends to 0

Let L(n) be the length of the shortest superpermutation on n symbols and F3(n) = n! + (n-1)! + (n-2)!. This
directory proves in Lean, in namespace `ConstAsym`:

```lean
theorem shortest_superpermutation_coefficient :
    (forall n, 0 < n -> L n = Hunter.Ssuper n) /\
    (forall n, 6 <= n -> F3 n <= (L n : Rat)) /\
    Tendsto (fun n : Nat => ((L n : Real) - (F3 n : Real)) / ((n - 3).factorial : Real)) atTop (nhds 0)

theorem two_sided : forall eps : Rat, 0 < eps -> exists N : Nat, forall n : Nat, N <= n ->
    F3 n <= (L n : Rat) /\ (L n : Rat) <= F3 n + eps * ((n - 3).factorial : Rat)
```

(copied from `ConstAsym/Main.lean` with the symbols spelled in ASCII; `L n` is the least length of a word over
`Fin n` that `Covers` every permutation). The same file has `coefficient_limit_rat`, `L_eq_ssuper` and
`hunter_lower_L`. In words: the shortest superpermutation is at least F3(n) for n >= 6, and for every eps > 0 it is
at most F3(n) + eps (n-3)! from some n on.

* The lower side is `Hunter.Paper.factorial_clean` of the Hunter-Raudvere library: for n >= 6 the shortest
  superpermutation has at least n! + (n-1)! + (n-2)! + (n-4)! - 2 (n-5)! letters.
* The upper side is `Uniform.coefficient_tends_to_zero` of [`../constant43586371/`](../constant43586371/README.md).
* `Bridge.lean` states `Covers` (Pantone's definition) for `Hunter.IsPermWord`, `Hunter.IsSuperperm` and
  `Hunter.Ssuper` by shifting letters by one each way: `ssuper_le_length`, `ssuper_eq_sInf`.

Every statement depends on `propext`, `Classical.choice` and `Quot.sound` only. There is no `sorry` and no
`native_decide`.

## The order of the remainder

`ConstAsym/Remainder.lean` combines the lower bound with `UniR.rate_R` of `../constant43586371/` and shows that
the remainder L(n) - F3(n) is of the order (n-4)!:

```lean
theorem remainder_order (n : Nat) (hn : 2 ^ 14 <= n) :
    ((n - 4).factorial : Rat) - 2 * ((n - 5).factorial : Rat) <= (L n : Rat) - F3 n /\
    (L n : Rat) - F3 n <= 9 * ((n - 4).factorial : Rat)
```

For n >= 2^14 the ratio (L(n) - F3(n)) / (n-4)! lies between 1/2 and 9 (`remainder_ratio_half`; `remainder_ratio`
has the lower end 1 - 2/(n-4)). The comparator that checks a statement against its source was run on the first two
theorems of this directory, not on the theorems of `Remainder.lean`.

### The constant lies in [2, 8]

`ConstAsym/Remainder8.lean` takes the lower side from Theorem B of [`../lower/`](../lower/README.md) (n >= 7) and
the upper side from `UniR.rate_R8` of `../constant43586371/`, and proves

```lean
theorem remainder_limit8 (eps : Rat) (heps : 0 < eps) : exists N : Nat, forall n : Nat, N <= n ->
    2 - eps <= ((L n : Rat) - F3 n) / ((n - 4).factorial : Rat) /\
    ((L n : Rat) - F3 n) / ((n - 4).factorial : Rat) <= 8 + eps
```

so in Lean the limit inferior of (L(n) - F3(n)) / (n-4)! is at least 2 and the limit superior at most 8. The finite
forms are `lower2_L` (2 (n-4)! - 2 (n-5)! <= L(n) - F3(n) for n >= 7), `remainder_order8` and `remainder_ratio8` (for
n >= 2^14 the remainder is at most 41/5 (n-4)!). `UniR.rate_R8` gives F3(n) + (41/5)(n-4)! for n >= 2^14 and
`rate_R8_eventually` gives F3(n) + (8 + eps)(n-4)!. The comparator was not run on these theorems.

`Remainder8` also needs Theorem B of `../lower/` and `Superperm.Bridge` of `../words/` (both in this directory
tree) and Liu's preimage-chain library, github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds, used
unchanged (set `PREIMAGE_DIR`; `../words/preimage-sources.sha256` lists the files and their hashes).

## The Hunter-Raudvere library

It is not copied here. It is github.com/urdvr/superpermutations-hunter at commit `d4522219`, used unchanged. The
75 modules behind `Hunter.Paper` are compiled by `build.sh` from a checkout of it (set `HUNTER_DIR`). Two of its
files, `ProofsMeta9` and `Refutations`, mention `native_decide` in comments only; the axiom lines show that it is
not used. The library and this development use the Lean and Mathlib versions of `../lean-toolchain`.

## Building

```sh
git clone https://github.com/urdvr/superpermutations-hunter deps/superpermutations-hunter
git -C deps/superpermutations-hunter checkout d4522219
HUNTER_DIR=$PWD/deps/superpermutations-hunter ./build.sh
```

`build.sh` follows the other builds of `proofs/lean`: it compiles Pantone's library (with the patched file of
`../constant/patches/`), the 75 Hunter modules, the modules of `../constant43586371/` up to `Uniform.Main`, and
the four files here, and prints the `#print axioms` lines. The settings are those of `../tools/common.sh`.

I compiled the four files here against the 75 Hunter modules built afresh from the checkout above, with the compiled
`Uniform` modules of my working directory: 27 minutes of wall time, 3.9 GB of working set at most. I have not run
`build.sh` in this layout.

## Axiom audit

From my build log:

    'ConstAsym.shortest_superpermutation_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ConstAsym.two_sided' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ConstAsym.L_eq_ssuper' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ConstAsym.hunter_lower_L' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ConstAsym.coefficient_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ConstAsym.coefficient_limit_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ConstAsym.remainder_order' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ConstAsym.remainder_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ConstAsym.remainder_ratio_half' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ConstAsym.lower2_L' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ConstAsym.remainder_order8' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ConstAsym.remainder_ratio8' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ConstAsym.remainder_limit8' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.UniR.rate_R8' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.UniR.rate_R8_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
