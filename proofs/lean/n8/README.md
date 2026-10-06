# n = 8 in Echols's framework, without native_decide

William Echols's Lean project (github.com/williamechols/superperm8-ge-46130, commit
`893ab2d92669ea56d012ceca626bf01ca631e920`, Apache License 2.0) proves that a superpermutation on 8 symbols
has at least 46,130 letters. His proof uses `native_decide`: besides the three standard axioms it rests on six
axioms that trust the Lean compiler.

This directory holds what turns his project into three variants that need no `native_decide`:

| variant | bound | inequality for every trail of marked rows | whose |
|---|---|---|---|
| `v46130k` | 46,130 <= L(8) | 20 rows - 49 charge <= 136 | his bound and his inequality |
| `v46131k` | 46,131 <= L(8) | 5 rows - 12 charge <= 38 | new |
| `v46132bk` | 46,132 <= L(8) | 20 rows - 47 charge <= 172 | new |

His reduction from words to trails of marked rows is used as it is, with the defect budget raised from 44 to
45 and 46 for the two new bounds. What is new: the two inequalities, and the way all three are proven. The
search behind an inequality is written on natural numbers, cut into parts, and evaluated by the Lean kernel
(`decide +kernel`); a soundness proof carries its result to all trails.

`../lower` proves 46,131, 46,132 and 46,133 for n = 8 by another route (Theorem C, on Liu's library). The two
proofs share nothing but Mathlib, so this directory is a second, independent proof of 46,131 and 46,132, and
it gives Echols's 46,130 without `native_decide`. This part stops at 46,132 and will not be taken further:
the route of `../lower` gives 46,133, also without `native_decide`.

His repository is not copied here. You clone it; `build.sh` reads his files, applies the changes in a build
directory and compiles the result.

## The statements

The same in the three variants, with N = 46130, 46131, 46132. They are copied from the Lean files with the
symbols spelled in ASCII. Every one depends on the axioms `propext`, `Classical.choice` and `Quot.sound` only.

```lean
-- Superperm8/Main.lean: his statement.  Word := List (Fin 8),
-- IsSuperpermutation w := forall p : Equiv.Perm (Fin 8), List.ofFn p <:+: w
theorem Superperm8.superpermutation_length_ge_46132 (w : Word) (hw : IsSuperpermutation w) :
    46132 <= w.length

-- Challenge.lean, Solution.lean: his statement layer
def Statement.ContainsAllEightPermutations (w : List (Fin 8)) : Prop :=
  forall p : Equiv.Perm (Fin 8), exists before after : List (Fin 8), w = before ++ List.ofFn p ++ after
def Statement.Challenge : Prop :=
  forall w : List (Fin 8), ContainsAllEightPermutations w -> 46132 <= w.length
theorem solution : Statement.Challenge

-- Plain.lean: new, a bridge of four lines from `solution`
theorem covering_word_length_ge_46132 :
    forall w : List (Fin 8),
      (forall p : List (Fin 8), p.length = 8 -> p.Nodup -> exists u v, w = u ++ p ++ v) -> 46132 <= w.length

-- Superperm8/Main.lean: the inequality of the variant
theorem Superperm8.row_affine_bound (rows : List MarkedRow) (h : ModelTrail rows) :
    20 * rows.length <= 172 + 47 * chargeSum rows
```

The hypothesis of `covering_word_length_ge_46132` is `Covers w` of Pantone's `Challenge.lean` written out, so
the statement is the lower-bound half of the two-sided statements of `../words` and `../lower` for n = 8.

## What replaces his native_decide

His sources use `native_decide` in eight proofs. Six of them reach his final theorem: the search, four
tables and a count.

* The search (`AffineCheck.lean`, `Affine.search 68 = false`). Here the search is `K.fsearch A Cc Bd fuel` on
  numbers (`KSearch.lean`): a permutation is its word read as eight octal digits, and the used insertion blocks
  and rotation classes are bit sets. `tools/plan.py` cuts the search tree into parts, each a lemma that the
  kernel evaluates, and `K.ref_of_cover` joins them to `K.fsearch A Cc Bd fuel = false`. `K.affine_bound_nat`
  (`KSound.lean`) proves from that the inequality for all trails; its last step follows the proof of
  `affine_bound_of_search_false` in his `AffineSound.lean`.
* Four tables over the 40,320 permutations (`classCode_attained`, `blockCode_attained`, `freezePerm_eq`,
  `nextStarts_complete`). They are not needed: `KCode.lean` proves the corresponding facts about the codes,
  with two tests over all 40,320 codes that the kernel evaluates in eight parts each.
* Two invariance lemmas (`classCode_R`, `blockCode_F`) are not used by his final theorem and are removed.
* A count over `Fin 7` in `CoarsenAccounting.lean`: `decide` does it.

| variant | states of the search | lemmas by `decide +kernel` | part files |
|---|---|---|---|
| `v46130k` | 8,009 | 3 | 1 |
| `v46131k` | 41,005 | 17 | 3 |
| `v46132bk` | 1,632,486 | 787 | 94 |

Nothing that Python computes is trusted. `plan.py` and its mirror of the search, `ksim.py`, only choose where
to cut; a wrong cut makes a lemma fail. With the right-hand side lowered by one (`5 12 37`, `20 49 135`) the
search finds a trail, so it is not vacuous.

## The files

* `echols-sources.sha256`: SHA-256 of his 36 Lean files at the commit named above.
* `variants/VARIANT/changes.diff`: the changes to his files, as a unified diff against that commit (9 files
  for `v46130k`, 20 for the other two). Three kinds of change are in it: the port from his Lean 4.30.0 and
  Mathlib `c5ea0035` to the Lean 4.31.0 and the Mathlib used in the rest of this repository (11 lines in 9
  files); the defect budget and the inequality of the variant; the passage from his search to the K files.
  Every changed file begins with a notice of modification.
* `variants/VARIANT/Plain.lean`: the new top file.
* `variants/VARIANT/files.sha256`: SHA-256 of the 38 hand-written Lean files of the variant (his 34 with the
  changes, `Plain.lean`, the three K files), by which `build.sh` checks what it has put together.
* `variants/VARIANT/generated.sha256`: SHA-256 of the parts of the search that `plan.py` writes (3, 5 and 96
  files).
* `kernel/Superperm8/KSearch.lean`, `KCode.lean`, `KSound.lean`: the new hand-written files, the same in every
  variant (1,621 lines).
* `tools/plan.py`, `tools/ksim.py`: the generator of the search parts (`Superperm8/K<NAME>Defs.lean`,
  `K<NAME>S<i>.lean`, `K<NAME>.lean`) and the Python mirror of the search it uses. The parts are not in the
  repository; `build.sh` generates them.
* `NOTICE.echols`: the `NOTICE` file of his repository, unchanged.
* `build.sh`: see below.

Two files of his are not used by the variants: `Superperm8/AffineSound.lean` and `AffineCheck.lean`.

## Licences

His project is under the Apache License 2.0 and carries a `NOTICE` that names the projects it is derived from:
Justin Lebar's superperm7-ge-5898 (Copyright 2026 Anthropic, PBC; Apache License 2.0) and Benjamin Grayzel's
superperm6 (MIT License). `changes.diff` contains lines of his files, and the variants that `build.sh` puts
together are modified copies of his work. So: every modified file says at its top that it was changed, by
whom and how; his header comments stay below that notice; `NOTICE.echols` is his `NOTICE`, and the licence
text is the `LICENSE` at the top of this repository. The new files are under the same licence.

The words "when and by whom" of these notices are written in one place, the variable `ATTRIBUTION` in
`build.sh`. The diffs and the `Plain.lean` files have the placeholder `@ATTRIBUTION@` where they belong, and
`build.sh` fills it in after it has compared the files with `files.sha256`.

## Building

```sh
git clone https://github.com/williamechols/superperm8-ge-46130 ../deps/superperm8-ge-46130
git -C ../deps/superperm8-ge-46130 checkout 893ab2d92669ea56d012ceca626bf01ca631e920
./build.sh                 # all three variants
./build.sh v46131k         # or one
```

`build.sh` needs Lean 4.31.0, the compiled Mathlib (the scripts take it from Pantone's checkout, see
`../README.md`), Python 3 and the program `patch`. It does not use lake and fetches nothing. For each variant
it compares his files with `echols-sources.sha256`, copies them into `../build/n8/VARIANT/src` with LF line
ends, leaves out the two unused files, applies `changes.diff`, adds the new files and compares the result
with `files.sha256`; then it fills in the notices, runs `plan.py` and compares the parts with
`generated.sha256`. Then Lean compiles `Solution`, `Plain`, `AxiomAudit` and what they import. The script
fails if any `#print axioms` line of the variant names an axiom other than the three. A second run compiles
only what has changed.

Measured on my machine (Ryzen 9 5950X, 32 GB, Windows 11 with Git Bash; one thread per Lean process, other
work running beside it), each variant from an empty directory:

| variant | modules | sum of Lean process time | of which the parts of the search | largest working set |
|---|---|---|---|---|
| `v46130k` | 40 | 14 minutes | 37 s (3 modules) | 1.8 GB |
| `v46131k` | 42 | 16 minutes | 166 s (5 modules) | 1.9 GB |
| `v46132bk` | 133 | 119 minutes | 105 minutes (96 modules, at most 80 s each) | 2.6 GB |

His 30 modules take 11 minutes in each variant (`PermutationMap` 3 minutes), the three K files a minute and
a half. `plan.py` needs under two minutes for `v46132bk` and seconds for the others. With `JOBS=4` the third
variant took 51 minutes by the clock. `build.sh` printed 7 `#print axioms` lines for each variant, all of
them `[propext, Classical.choice, Quot.sound]`.

## What is trusted

The Lean kernel, including its arithmetic on natural numbers, Mathlib, the three axioms, and the statement
layer: his `Challenge.lean`, or `Plain.lean`. His reduction (the files derived from Lebar's and Grayzel's
projects, and his own) is compiled here from his sources with the changes named above; I did not review it
beyond that.

## What is not here

* 46,133 in this framework. It would need a search of 76 million states or more, which was not built;
  `../lower` proves 46,133 by the other route.
* The variants that keep his `native_decide` (his layout with the new constants), which I built on the way.
* A lake project. His `lakefile.toml` with the newer toolchain should build the variants; I did not try.
