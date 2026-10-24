# The coefficient 305989/604800 in Lean

This directory builds on [`../constant61937/`](../constant61937/README.md) (the coefficient 61937/120960) and
proves, for superpermutations on n symbols,

    S(n) <= F3(n) + (305989/604800 + o(1)) (n-3)!        F3(n) = n! + (n-1)! + (n-2)!
    305989/604800 = 0.505934...

for every n >= 16. The coefficient of `../constant61937/` is 0.512045..., the one of `../constant/` is 0.512442...
and Pantone's is 0.5375. The construction is Pantone's. The change from `../constant61937/` is the block step: from
15 symbols on, the loops above each of the 6,048 loops without a row on 11 symbols are not taken from the selection
transported up but from one block, solved once on 14 symbols and carried to every position by a relabelling.

* The block (`data/s103_old2_0.txt`) has 6 closed walks of full and short rows (880 rows, total charge 370) and 440
  loops without a row. On 15 symbols the six walks are written 3, 6, 6, 6, 6 and 6 times and transported from
  their start ports, which gives 14 closed trails (1,235 / 715 / 385 / 395 rows). The 440 loops become full
  charts. Over all 6,048 positions this gives 13! = 6,227,020,800 rows with charge 3,084,943,680
  (= 11771/23760 of 13!) and 5,039,928 connector cycles on 15 symbols.
* The connector cycles of the block are chosen again for 16 symbols: 26 cycles (`data/cyc_t_s103_old2_0_n16.txt`),
  each with a pointer certificate on the canonical trails. The cost of the cycles is 23333/2217600 of
  (n-3)!/(n-3), against 859/40320 in `../constant61937/`.
* The block lemma needs no hypothesis about "old letters". The construction in Lean needs only closed trails, a
  winding divisible by the number of ports, rows over the alphabet, and that every 2-loop has some row. The checks
  on the canonical block (`BlockOK`) and a relabelling lemma (`Relabel.lean`) give the block above every loop.

The Lean kernel checks every proof. There is no `native_decide` and no `sorry`. The theorems below depend on
the axioms `propext`, `Classical.choice` and `Quot.sound` only.

## The theorems

```lean
-- SuperpermutationUpperBound305989/MainB.lean
theorem finite_bound16 (m : Nat) (hm : 14 <= m) (a : Nat) (ha : 2 <= a) (ham : a <= m) :
    exists w : List (Fin (m + 2)), SuperpermutationBounds.Covers w /\
      (w.length : Rat) <=
        (((m + 2).factorial + (m + 1).factorial + m.factorial : Nat) : Rat)
          + (305989 / 604800 : Rat) * ((m - 1).factorial : Rat)
          + ((a - 2 : Nat) : Rat) * (23333 / 2217600 : Rat) * ((m - 1).factorial : Rat) / ((m - 1 : Nat) : Rat)
          + ((m - a : Nat) : Rat) *
              min ((23333 / 2217600 : Rat) * ((m - 1).factorial : Rat) / ((m - 1 : Nat) : Rat))
                (((m + 1).factorial : Rat) / ((a + 1).factorial : Rat))

theorem eventual_bound16 :
    forall eps : Rat, 0 < eps -> exists N : Nat, 16 <= N /\
      forall K : Nat, N <= K -> exists w : List (Fin K), SuperpermutationBounds.Covers w /\
        (w.length : Rat) <= SuperpermutationBounds.F3 K +
          ((305989 / 604800 : Rat) + eps) * (Nat.factorial (K - 3) : Rat)
```

(The statement is copied from `MainB.lean` with the symbols spelled in ASCII.) `CorollariesB.lean` adds the
bound in the shape of Pantone's `Finite` and `FiniteInteger` from m = 14 (`Cost305989`, `finite_305989`,
`finiteInteger_305989`) and two values:

| symbols | statement | parameters |
|---|---|---|
| 16 | `hasWord_sixteen_B : HasWord 16 22320830091240` | m = 14, a = 9 |
| 17 | `hasWord_seventeen_B : HasWord 17 377962492058424` | m = 15, a = 9 |

At 16 symbols this is about 74 million below the value of `../constant61937/` (22,320,904,300,200). These are
values of the general formula, not words.

## The files

`SuperpermutationUpperBound305989/` contains the files of `../constant61937/SuperpermutationUpperBound61937/` that
step (B) needs (`Repeat`, `Levels`, `WordOfLevel`, `Hybrid`, `Thirteen`, `AllSizes`, `Certificate/`), with the
namespace renamed and no other change, and these new files:

| file | content |
|---|---|
| `Relabel.lean` | a relabelling lemma for transport, completion, ports, charts and cycle covers; `relab d0 d` sends the letters of one loop to those of another and fixes the rest. Builds on Pantone's `Foundation/RowRelabeling.lean` |
| `BlockB.lean` | `above3 d` (the 1,320 loops on 14 symbols above `d`); an inventory lemma for a walk written several times and transported from several start ports; `BlockData` and `BlockOK` (the decidable checks); the block on every loop `d` by relabelling |
| `Fifteen.lean` | the level on 15 symbols: the long and short walks transported, plus the block above each of the 6,048 loops; the counts (13! rows, charge 3,084,943,680, 5,039,928 cycles) |
| `AllSizesB.lean`, `GenericBoundsB.lean` | the level on k + 16 symbols for every k, and the rational bound with the new constants |
| `MainB.lean`, `CorollariesB.lean` | the statements above |
| `Certificate/Block*.lean` (generated) | `BlockData` (the block, 1,320 pointers, 26 cycles), `BlockChecks` (`BlockOK`, four `decide +kernel`), `BlockPorts16a/b` (182 pointers), `BlockCert` |

The generated files of `Certificate/` come from two scripts: `gen_cert.py` (as in `../constant61937/`, for the
files that are shared) and `gen_blockB.py` with `block_checks_body.lean` (for the `Block*` files; it reads the
three files in `data/`). Both check every fact before they write it. `build.sh` builds everything.

## Inputs

* `arrange/data/n12t-selection.txt.xz` and `selection/data/zcycles_n12.txt` of the repository, for `gen_cert.py`
  (hashes in `../constant61937/README.md`). It needs numpy and scipy.
* `data/s103_old2_0.txt` (the block on 14 symbols), `data/cyc_s103_old2_0.txt` (its cycles on 15 symbols, checked
  by the script only) and `data/cyc_t_s103_old2_0_n16.txt` (the cycles on 16 symbols). Their SHA-256 are in the
  header of `Certificate/BlockData.lean`.

## Building

```sh
./build.sh
```

`build.sh` follows `../constant61937/build.sh`: it checks Pantone's sources, runs the two generators and requires
identical output, compiles his library (with the patched file of `../constant/patches/`) and the modules of this
directory, and prints the `#print axioms` lines. Settings are those of `../tools/common.sh`.

I ran both generators in this layout and compared the output with the files here: all 53 generated files are
identical. I built the 66 modules of the development with one Lean process on one thread, in my working
directory and with the compiled library of `../constant/` on the module path: 38 minutes, 2,222 s of Lean time.
The new modules take at most 33 s each; `BlockChecks` needs 5.0 GB of working set, `BlockPorts16a` 4.4 GB. On
2026-10-24 I ran `build.sh` from an empty build directory, on the files of this repository as `git archive`
writes them, with five Lean processes: 161 modules, 12 minutes, exit 0.

## Axiom audit

The `#print axioms` lines of the final statements, from my build log:

    'SuperpermutationUpperBound305989.finite_bound16' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound305989.eventual_bound16' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound305989.finite_305989' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound305989.finiteInteger_305989' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound305989.hasWord_sixteen_B' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound305989.hasWord_seventeen_B' depends on axioms: [propext, Classical.choice, Quot.sound]

All 98 `#print axioms` lines of that build: 59 with `[propext, Classical.choice, Quot.sound]`, 35 with
`[propext, Quot.sound]`, 2 with `[propext]` and 2 without axioms. `build.sh` prints these counts at the end.
