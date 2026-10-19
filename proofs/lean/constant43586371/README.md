# Nested block levels in Lean: the coefficients down to 11117297/27675648, and the limit 0

This directory builds on [`../constant305989/`](../constant305989/README.md). It proves, for superpermutations on
n symbols,

    S(n) <= F3(n) + (c + o(1)) (n-3)!        F3(n) = n! + (n-1)! + (n-2)!

for eight coefficients c, and in `Uniform/` that the best coefficient tends to 0. The construction is Pantone's.
The change from `../constant305989/` is the block step applied again, one level up, and in the last three
constants also the removal of the selection on 11 symbols.

## The coefficients

The coefficients that the Lean proofs in this repository reach, with the first n from which each holds:

| c | decimal | from n | directory |
|---|---:|---:|---|
| 43/80, Pantone | 0.537500 | 11 | his repository |
| 1771/3456 | 0.512442 | 13 | [`../constant/`](../constant/README.md) |
| 61937/120960 | 0.512045 | 13 | [`../constant61937/`](../constant61937/README.md) |
| 305989/604800 | 0.505934 | 16 | [`../constant305989/`](../constant305989/README.md) |
| 43586371/86486400 | 0.503968 | 19 | here |
| 3961457/7862400 | 0.503848 | 19 | here |
| 8711159/17297280 | 0.503614 | 19 | here |
| 21751799/43243200 | 0.503011 | 22 | here |
| 21736511/43243200 | 0.502657 | 22 | here |
| 629507/1441440 | 0.436721 | 22 | here |
| 3853/8736 | 0.441049 | 19 | here |
| 11117297/27675648 | 0.401700 | 22 | here |

Each row proves the same four things, with the first n written n0 (19 or 22) and m = n - 2: a `finite_bound` for
every m >= n0 - 2 and every 2 <= a <= m (a word on m + 2 symbols of length at most
(m+2)! + (m+1)! + m! + c (m-1)! + (a-2) d + (m-a) min(d, (m+1)!/(a+1)!), with d a multiple of (m-1)!/(m-1)); an
`eventual_bound` (for every rational eps > 0 there is an N >= n0 such that every K >= N has a covering word of
length at most F3 K + (c + eps)(K-3)!); the same in the shape of Pantone's `Finite` and `FiniteInteger`; and two
`HasWord` values of the finite bound. They are values of a formula, not words.

| name | selection and blocks | c | d / ((m-1)!/(m-1)) | n0 | names in the Lean files |
|---|---|---|---|---:|---|
| C | selection on 11 symbols; blocks W103, S133 | 43586371/86486400 | 654131/86486400 | 19 | `finite_bound19`, `finite_43586371` |
| E | same; S103 with cycles chosen on 16 symbols, S133 | 3961457/7862400 | 121207/17297280 | 19 | `finite_bound19_3961457` |
| F | same; W103 with cycles on 16 symbols, S133 | 8711159/17297280 | 124711/17297280 | 19 | `finite_bound19_8711159` |
| D | same; X103, W133, S163 | 21751799/43243200 | 297743/43243200 | 22 | `finite_bound22`, `finite_21751799` |
| G | same; X103 with cycles on 16 symbols, W133, S163 | 21736511/43243200 | 56491/8648640 | 22 | `finite_bound22_21736511` |
| H | no selection; X103 on 16 symbols, W133, S163 | 629507/1441440 | 32759/288288 | 22 | `finite_bound22_629507` |
| I | no selection; D73, W103, S133 | 3853/8736 | 6113/96096 | 19 | `finite_bound19_3853` |
| J | no selection; B73, X103, W133, S163 | 11117297/27675648 | 1769507/19768320 | 22 | `finite_bound22_11117297` |

The block names are those of the files in `data/`: W103 = `w103_0.6245_1`, X103 = `w103_0.4795_0`,
S103 = `s103_old2_0`, S133 = `s133_0`, W133 = `w133_0`, S163 = `s163_old2_0`, D73 = `block_7_3_enum14_0`,
B73 = `b73_dw_0`. A block (p, 3) sits above the loops without a row, on p + 4 symbols. "Cycles on 16 symbols" means
the connector cycles of the block are chosen on the completion one level up (files `cyc_t_*` and `cyc_up_*` in
`data/`) instead of on its own level.

### What changes from one level to the next

* Two or three block levels (C to G): a second block sits above each loop without a row of the first, and for D
  and G a third above those of the second. The selection on 11 symbols and the first block are as in
  `../constant305989/`.
* No selection (H, I, J): the proof starts on 12 symbols with no rows at all (`Stage.noSeed`, `NoSeed.lean`). The
  loops above the first letters are `a` followed by every arrangement of the others, one per cyclic order, and the
  first block goes above those. Everything after that is as before.
* Every proof is checked by the Lean kernel. There is no `native_decide` and no `sorry`.

## The limit: the coefficient tends to 0

`SuperpermutationUpperBound43586371/Uniform/` (11 files, 2,489 lines) proves

```lean
theorem coefficient_tends_to_zero :
    forall eps : Rat, 0 < eps -> exists N : Nat, forall K : Nat, N <= K ->
      exists w : List (Fin K), SuperpermutationBounds.Covers w /\
        (w.length : Rat) <= SuperpermutationBounds.F3 K + eps * (Nat.factorial (K - 3) : Rat)
```

(copied from `Uniform/Main.lean` with the symbols spelled in ASCII). It depends on `propext`, `Classical.choice` and
`Quot.sound` only; every block property is proved for all odd m >= 5, with no `decide` on anything that depends on
m. The family is the simplest one that works: no selection, and above every loop without a row on m old letters (m
odd) one walk of m(m+12) rows, a "caterpillar", met by one connector cycle; at even levels the empty block. The
proof gives N of the order of 2 * 10^6 / eps^7, so this is a statement about the limit, far from the best finite
constants above. `PROOF.md` is the proof on paper, `REFEREE.md` the report of an independent check of it (a build
of the 23 files it needs straight from Pantone's sources).

### A rate

`SuperpermutationUpperBound43586371/UniR/` (11 files, 2,399 lines) uses a block at every level, not only at odd
ones, and proves two things (`PROOF_R.md` has the proof on paper):

```lean
-- UniR/RRate.lean
theorem rate_R (n : Nat) (hn : 2 ^ 14 <= n) :
    exists w : List (Fin n), SuperpermutationBounds.Covers w /      (w.length : Rat) <= SuperpermutationBounds.F3 n + (9 / n : Rat) * (Nat.factorial (n - 3) : Rat)
```

and `finite_boundR m0 K n a` in `UniR/RMain.lean`, an explicit bound for every n >= m0 + 3K + 3, with the
parameters m0 >= 11, K levels and 2 <= a <= n - 2. `python bound_R.py N` prints its exact value at N, minimised over
m0, K and a. In units of (N-3)! above F3(N) it is 0.3059 at N = 40, 0.2015 at N = 60, 0.1103 at N = 100 and 0.1031
at N = 106. The constant 9 in `rate_R` is not sharp (the proof gives 8.69; numerically about 8.6).

`UniR/RRate8.lean` states the rate in units of (n-4)!: `rate_R8` gives F3(n) + (41/5)(n-4)! for n >= 2^14 and
`rate_R8_eventually` gives F3(n) + (8 + eps)(n-4)! for every eps > 0 from some n on. Both print the three axioms;
the comparator was not run on them.

Together with the lower bound of the Hunter-Raudvere library, [`../asym/`](../asym/README.md) concludes that
(L(n) - F3(n)) / (n-3)! tends to 0, where L(n) is the length of the shortest superpermutation on n symbols.

## The files

`SuperpermutationUpperBound43586371/` contains the files of `../constant305989/` with the namespace renamed
(`Repeat`, `Levels`, `WordOfLevel`, `Hybrid`, `Thirteen`, `AllSizes`, `Relabel`, `Certificate/`) and these new
files:

| file | content |
|---|---|
| `BlockG.lean`, `BlockUp.lean` | the block lemma with the frame as a parameter (blocks on 10, 13, 16 or 7 old letters); `BlockData`, `BlockOK`, `BlockPorts`, `BlockCert`; the block relabelled onto any loop; the variant whose cycles are chosen one level up |
| `Stage.lean`, `NoSeed.lean`, `PortsSplit.lean` | `Stage`: a level whose missing 2-loops lie above pending loops; `Stage.advance`, `Stage.close`, `Stage.noSeed` |
| `AllSizesG.lean` | a closed level to every size, counts as ratios to factorials, and the word with the finite-bound ledger |
| `Nested*.lean` | the selections of the eight constants; the counts are checked by `decide +kernel` |
| `GenericBounds*.lean`, `Main*.lean`, `Corollaries*.lean` | the arithmetic and the statements, one letter C to J per constant, written by `gen_bounds.py` from the files of `../constant305989/` by text substitution (the result is compiled like every other file) |
| `Certificate/Block*.lean` (generated) | per block: `Data`, `Walks`, `Cover`, `Ports` and the assembled block, written by `gen_blocks.py` |
| `Uniform/*.lean` | the limit theorem (above) |
| `UniR/*.lean` | the rate (above) |

`ledgerC.py` writes the ledger of the counts with exact fractions (charge, cycles, charts, finite values), so that
the numbers in the Lean files can be compared with an independent computation. `gen_cert.py` writes the shared
certificate files (as in `../constant61937/`), `gen_blocks.py` the `Block*` files from the blocks in `data/` (block
files `*.txt`, lines `x T`; connector cycle files `cyc_*.txt`), `gen_bounds.py` the arithmetic files. Every
generator checks all facts that Lean will check before it writes.

## Inputs

* `arrange/data/n12t-selection.txt.xz` and `selection/data/zcycles_n12.txt` of the repository, for `gen_cert.py`
  (hashes in `../constant61937/README.md`). It needs numpy and scipy.
* the files in `data/`; their SHA-256 are in the header of each `Certificate/Block*Data.lean`.

## Building

```sh
./build.sh
```

`build.sh` follows `../constant305989/build.sh`: it checks Pantone's sources, runs the generators and requires
identical output, compiles his library (with the patched file of `../constant/patches/`) and this directory
(including `Uniform/`), and prints the `#print axioms` lines. Settings are those of `../tools/common.sh`.

I ran all three generators in this layout and compared the output with the files here. I built the new modules
with one Lean process on one thread, in my working directory and with the compiled library of `../constant/` on the
module path: the 149 modules for the eight constants took 45.5 minutes (2,564 s of Lean time, at most 6.1 GB of
working set, in `BlockW133UUp0_1` and `BlockS133UUp0_1`), and the 11 modules of `Uniform/` 3.7 minutes (1.9 GB). The 11 modules of `UniR/` with the 9 `Uniform/` modules
they need and the 13 base modules took 6 minutes (23 s of it for `RRate`), 1.9 GB at most.
I have not run `build.sh` from an empty build directory in this layout.

## Axiom audit

The `#print axioms` lines of all 48 final statements of the eight constants (six each), from my build log, and a
separate audit module that printed the same for each of the eight main theorems:

    'SuperpermutationUpperBound43586371.eventual_bound19' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.eventual_bound19_3853' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.eventual_bound19_3961457' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.eventual_bound19_8711159' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.eventual_bound22' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.eventual_bound22_11117297' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.eventual_bound22_21736511' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.eventual_bound22_629507' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finiteInteger_11117297' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finiteInteger_21736511' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finiteInteger_21751799' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finiteInteger_3853' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finiteInteger_3961457' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finiteInteger_43586371' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finiteInteger_629507' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finiteInteger_8711159' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_11117297' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_21736511' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_21751799' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_3853' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_3961457' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_43586371' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_629507' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_8711159' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_bound19' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_bound19_3853' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_bound19_3961457' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_bound19_8711159' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_bound22' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_bound22_11117297' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_bound22_21736511' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.finite_bound22_629507' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_nineteen_C' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_nineteen_E' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_nineteen_F' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_nineteen_I' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_twenty_C' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_twenty_E' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_twenty_F' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_twenty_I' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_twentythree_D' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_twentythree_G' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_twentythree_H' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_twentythree_J' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_twentytwo_D' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_twentytwo_G' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_twentytwo_H' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.hasWord_twentytwo_J' depends on axioms: [propext, Classical.choice, Quot.sound]

For the rate (`UniR/RAudit.lean` prints 12 lines, one per main lemma):

    'SuperpermutationUpperBound43586371.UniR.rate_R' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.UniR.finite_boundR' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.UniR.rate_R8' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.UniR.rate_R8_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]

For the limit theorem (`Uniform/Audit.lean` prints 17 lines, one per main lemma):

    'SuperpermutationUpperBound43586371.Uniform.coefficient_tends_to_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound43586371.Uniform.small_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound]

The other `#print axioms` lines of the builds show `[propext, Classical.choice, Quot.sound]`, `[propext, Quot.sound]`,
`[propext]` or no axioms; `build.sh` prints the counts at the end.
