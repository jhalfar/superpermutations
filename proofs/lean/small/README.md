# L(1) to L(6) in Lean, checked by the kernel alone

The shortest superpermutation on n symbols has 1, 3, 9, 33, 153 and 872 letters for n = 1, 2, 3, 4, 5 and 6.
This directory proves the six values in Lean 4. Each value is one theorem with both halves: a word of that length
contains every permutation of the n symbols as a contiguous part, and no shorter word does. Every theorem depends on
the axioms `propext`, `Classical.choice` and `Quot.sound` only: there is no `native_decide`, no `Lean.ofReduceBool`
and no compiled code, and every finite search is evaluated by the kernel (`decide +kernel`). `build.sh` builds
everything from sources into an empty build directory.

For n = 6 this is, as far as I know, the first proof of 872 that the kernel checks alone. Benjamin Grayzel's Lean
proof of $`s(6) = 872`$ (github.com/BGray-wrl/superperm6) uses `native_decide` in its finite searches. The lower bound
here is proven in the model of standard configurations of the proof of 5,899 in `../n7`, not in Grayzel's framework;
his word and his statement are used for the upper bound and for the second form of the theorem.

## The statements

Copied from the Lean files with the symbols spelled in ASCII (`forall`, `exists`, `<=`, `->`, `/\`). `Covers` is the
definition of Jay Pantone's `Challenge.lean` (github.com/jaypantone/superperm-upper-43-80): `Covers w` says that
every list of n different letters of `Fin n` is `w = u ++ p ++ v` for some `u` and `v`.

```lean
-- Small/Upto5.lean, Small/Exact.lean                                     (namespace SmallSuperperm)
theorem exact_one :
    (exists w : List (Fin 1), Covers w /\ w.length = 1) /\ forall w : List (Fin 1), Covers w -> 1 <= w.length
theorem exact_two :
    (exists w : List (Fin 2), Covers w /\ w.length = 3) /\ forall w : List (Fin 2), Covers w -> 3 <= w.length
theorem exact_three :
    (exists w : List (Fin 3), Covers w /\ w.length = 9) /\ forall w : List (Fin 3), Covers w -> 9 <= w.length
theorem exact_four :
    (exists w : List (Fin 4), Covers w /\ w.length = 33) /\ forall w : List (Fin 4), Covers w -> 33 <= w.length
theorem exact_five :
    (exists w : List (Fin 5), Covers w /\ w.length = 153) /\ forall w : List (Fin 5), Covers w -> 153 <= w.length
theorem exact_six :
    (exists w : List (Fin 6), Covers w /\ w.length = 872) /\ forall w : List (Fin 6), Covers w -> 872 <= w.length

-- Grayzel's formulation of s(6) = 872
theorem grayzel_six : Superperm6.IsMinimumLength 872

-- the same values for the least length of the Hunter-Raudvere library
theorem ssuper_values :
    Hunter.Ssuper 1 = 1 /\ Hunter.Ssuper 2 = 3 /\ Hunter.Ssuper 3 = 9 /\ Hunter.Ssuper 4 = 33 /\
      Hunter.Ssuper 5 = 153 /\ Hunter.Ssuper 6 = 872
```

Grayzel's definitions (`superperm6/Superperm6/Basic.lean`) are `Word := List (Fin 6)`, `IsSuperpermutation w :=
forall p : Equiv.Perm (Fin 6), List.ofFn p <:+: w` and `IsMinimumLength n := (exists w, IsSuperpermutation w /\
w.length = n) /\ (forall w, IsSuperpermutation w -> n <= w.length)`. `K6.isSuperpermutation_iff_covers` proves that
his `IsSuperpermutation` and `Covers` agree. `AuditSmall.lean` states the six `exact_` theorems once more with
`Covers` written out, so that nothing of this repository has to be read to know what is claimed.

The axioms, as `build.sh` prints them:

```
'SmallSuperperm.exact_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'SmallSuperperm.exact_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'SmallSuperperm.exact_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'SmallSuperperm.exact_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'SmallSuperperm.exact_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'SmallSuperperm.exact_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'SmallSuperperm.grayzel_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'SmallSuperperm.ssuper_values' depends on axioms: [propext, Classical.choice, Quot.sound]
'audit_six' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Where each value comes from

| n | upper bound: a word checked by the kernel | lower bound |
|---|---|---|
| 1 | `1` | `lower_one`: the word contains `[0]` |
| 2 | `121` | `lower_two`: a word of two letters cannot contain both `[0, 1]` and `[1, 0]` |
| 3 | `123121321` | `pointwise_3` of the Hunter-Raudvere library |
| 4 | 33 letters | `pointwise_4` of the Hunter-Raudvere library |
| 5 | 153 letters | Theorem A of `../lower` at k = 5 |
| 6 | Robin Houston's word of 872 letters, from Grayzel's repository | `K6.covers_872`, the search of `K6/` in the model of `../n7` |

The words for $`n \le 5`$ are those of the recursive construction (the word on k symbols is built from the word on
k - 1 symbols, and has $`1! + 2! + \cdots + k!`$ letters); they are written out in `Small/Words.lean`. `check K w` runs
through Mathlib's list `permutations'` of `0, ..., K-1` and asks whether each occurs in `w`, and `covers_of_check`
proves that a word that passes has `Covers`. For n = 6 the word and its check are Grayzel's `Witness.lean` in the
kernel-only version of `superperm6/`.

The lower bounds do not all take the same route. The model of `../n7` (Theorems W and N,
`covers_length_gt_of_no_stdConfig`) is stated for $`k \ge 5`$, so it does not reach n = 3 and 4. Zach Hunter and Uku
Raudvere's library proves `9 <= Ssuper 3` and `33 <= Ssuper 4` (Corollary 28 of their paper, kernel-only), and the
bridge of `../words` (`hunter_le_ssuper_iff`) turns them into statements about `Covers`. At n = 5 Theorem A of
`../lower` already gives 153: $`\mathrm{hpv}(5) + \lceil 2\,(3! - 3) / (5 \cdot 2) \rceil = 152 + 1`$, with $`\mathrm{hpv}(k) = k! + (k-1)! + (k-2)! + k - 3`$. So no search is needed below n = 6; the Hunter-Raudvere library gives 153 at n = 5 as well
(`superperm_length_ge_5_153`). At n = 6 Theorem A gives 870 and the Hunter-Raudvere bound 869, and the last two
letters need the search.

## How the proof at n = 6 goes

1. The model (`../n7`, reused unchanged). A standard configuration on k symbols is a kernel (a list of rows)
   and hanging components (lists of rows attached at one vertex); its cost is rows + seam excess + attachment
   costs. Theorems W and N (`covers_length_gt_of_no_stdConfig`, `../n7/LowerBounds/NTheorem.lean`): if no valid
   configuration has cost at most $`(k-2)! + D`$, every superpermutation has at least $`\mathrm{hpv}(k) + D + 1`$ letters,
   $`\mathrm{hpv}(6) = 867`$. So 871 is "no configuration of cost $`\le 27`$" and 872 "of cost $`\le 28`$".
2. The family (`K6/Family.lean`, `K6/FamilyC.lean`). A valid configuration on 6 symbols falls into open trails
   (the kernel cut at its seams of weight other than 3; hanging components with a paid attachment cut the same
   way; hanging components with a free attachment and a heavy seam, cut and read cyclically), closed trails (free
   attachment, no heavy seam, at least two rows) and loops (free attachment, one row, which has 4 blocks).
   Counting blocks (at least 120, one per rotation class) against the cost gives, for t open trails and defect D:
   the sum over open and closed trails of (rows - holes) is at least $`24 - 4D + 4(t-1)`$, and the sum of their holes
   plus the loops is at most $`5D - 5(t-1)`$.
3. Chain caps (`K6/Cap*.lean`). A chain (rows joined by seams of weight 3, blocks in pairwise different classes)
   with $`x \le 20`$ holes has at most $`W_6[x]`$ rows, $`W_6 =`$ 4 4 7 7 10 10 11 13 14 15 16 17 19 19 22 23 24 25 26 27 28. Up
   to 14 holes these are the true caps; from 15 holes on h + 8 is enough, and the search for these caps has 52,386
   nodes instead of 3.2 million. That the answer of the search proves the caps is the argument of
   `PLevels.lean` and `PRules.lean` of `../n7`, reused unchanged.
4. 871 (`K6/Knap.lean`, `K6/Final871.lean`). An open trail has value $`\text{rows} - \text{holes} \le W_6[h] - h`$; a closed trail
   glues through the class it skips into a trail with one row and 6 holes fewer, so its value is at most
   $`1 + W_6[h - 6] - h`$. Knapsack tables computed by Lean and one check by the kernel (`chk3`) show that no numbers
   of open and closed trails reach the bound of step 2 at defect 3.
5. The tight case, defect 4 (`K6/Tight*.lean`, `K6/TE/`). The same check (`chk4`) leaves only families with no
   closed trail and 1, 2 or 3 open trails. Every class outside the open trails then lies in a loop that avoids
   them. The search enumerates the open trails, the first one from `1 2 3 4 5 6` with the largest rows - holes,
   the others from any word, pruned by the knapsack table of the chain caps; at the end it asks whether some
   class outside the trails is dead, that is, in no row of 4 blocks that avoids them. All 57 families that reach
   the bound (2, 23 and 32 for 1, 2 and 3 trails) have a dead class. The search is cut into 72 parts, one file
   each.
6. The bridge (`K6/A6.lean`): Grayzel's `IsSuperpermutation` and `Covers` agree, and his witness gives the upper
   bound.

The search. `K6/Engine.lean` is one depth-first search over lists of rows on 6 symbols with pairwise different
classes. A word is its index 0..719, the tables (class index, the door to the next block, the five successors of
weight 3) are natural numbers read with shifts, and the set of used classes is a natural number read as bits, so
the kernel does every step with a few operations on big numbers: about 0.4 ms per node. What the search counts and
when it stops is a parameter (`Rules`): counters updated at every row, two rules for continuing with a seam or
with a jump, and a test at the end that also sees the used classes. A search is cut into parts by rules that
remember the entry of a chosen row and refuse all but a share of them.

Why its answer proves the statements. `K6/TabOK.lean` checks the tables against the words by `decide +kernel`.
`K6/Sound.lean` proves `not_kalong`: if the search answers `false`, no list of rows that starts at `1 2 3 4 5 6`
satisfies the rules along it. The search returns its answer and no state, so the proof is a plain induction over
the rows. `K6/Cap.lean` turns this into the statement `PS.PStmt` of `../n7` (relabelling the symbols so that the
first word is `1 2 3 4 5 6`), and `K6/TightAlong.lean` and `K6/TightFinal.lean` prove that the open trails of a
configuration of defect 4, relabelled, satisfy the rules of the tight case along their rows, including the part
they belong to and the leaf test (`deadB_false`: if every class outside lies in a loop that avoids the trails,
the test finds no dead class; the property survives relabelling).

The theorems on the way:

```lean
-- K6/Final871.lean, K6/Final872.lean, K6/A6.lean                                     (namespace K6)
theorem no_config_27 (c : NConfig 6) (hv : c.Valid) : Not (c.cost <= (6 - 2).factorial + 3)
theorem covers_871 : forall w : List (Fin 6), SuperpermutationBounds.Covers w -> 871 <= w.length
theorem no_config_28 (c : NConfig 6) (hv : c.Valid) : Not (c.cost <= (6 - 2).factorial + 4)
theorem covers_872 : forall w : List (Fin 6), SuperpermutationBounds.Covers w -> 872 <= w.length
theorem isSuperpermutation_iff_covers (w : Superperm6.Word) :
    Superperm6.IsSuperpermutation w <-> SuperpermutationBounds.Covers w
theorem a6_eq_872 : Superperm6.IsMinimumLength 872
```

## Whose the parts are

* The model of standard configurations with Theorems W and N, the cut of rows at heavy seams, the geometry of
  attachments and the layer that turns a search statement into chain caps (`PSeq`, `PLevels`, `PRules`) are
  those of the proof of 5,899 (`../n7`), used unchanged. They rest on Zach Hunter and Uku Raudvere's library and
  on Xiaolong Liu's preimage-chain library, both used unchanged.
* `K6/Family.lean` follows `PShapes.lean` and `PHanging.lean` of `../n7`, with 7 replaced by 6 and the closed
  trails and loops kept as objects of their own; the lemmas `RowsOK`, `free_geom` and `glue_ring` are copies.
* The word of 872 letters was found by Robin Houston. The statements `IsSuperpermutation` and `IsMinimumLength`
  and the check of the word are Benjamin Grayzel's (superperm6, MIT License). `superperm6/` holds his
  `Basic.lean` and `Witness.lean`, changed so that the kernel checks them alone, and his data file; each changed
  file says at its top what was changed. The kernel-only proofs in his `Basic.lean` follow William Echols's port
  of the same file to eight symbols (superperm8-ge-46130, Apache License 2.0), which comes from Justin Lebar's
  superperm7-ge-5898; their notice is `superperm6/NOTICE.echols`.
* `Covers` is the definition of Jay Pantone's `Challenge.lean`.
* `pointwise_3` and `pointwise_4` are Hunter and Raudvere's. Theorem A is the Lean proof of `../lower`; its
  formula is Zach Hunter's (see `../lower/README.md`).
* The capacity table, the 2 + 23 + 32 chain sets and the observation that none of them has a loop tiling come
  from an exhaustive enumeration of chains on 6 symbols that I ran before the Lean proof; the enumeration is not
  part of this directory, and nothing in the proof depends on it.
* New here: the kernel search engine at n = 6 and its soundness proof, the family of a configuration on 6 symbols
  with its counting, the knapsack arguments for 871 and for the shape of the tight case, the dead-class test, the
  proof that the rules hold along a family, the bridge between the two definitions, the kernel-only changes to
  Grayzel's two files, and the checker and the small cases of `Small/`.

## The files

* `Small/Words.lean`: `occurs`, `check`, `covers_of_check`, the words for n = 1 to 5, `lower_one`, `lower_two`.
* `Small/Upto5.lean`: `exact_one` to `exact_five`, `ssuper_upto5`.
* `Small/Exact.lean`: `exact_six`, `grayzel_six`, `ssuper_values`.
* `AuditSmall.lean`: the six statements with `Covers` written out.
* `K6/Tab.lean` (written by `gen_k6.py`), `K6/Engine.lean`, `K6/TabOK.lean`, `K6/Sound.lean`: the engine.
* `K6/CapTab.lean` (`gen_cap.py`), `K6/CapRules.lean`, `K6/Cap.lean`, `K6/CapEval.lean`, `K6/CapFinal.lean`: the
  chain caps.
* `K6/Family.lean`, `K6/FamilyC.lean`, `K6/Knap.lean`, `K6/Final871.lean`: 871.
* `K6/TightTab.lean` (`gen_tight.py`), `K6/TightRules.lean`, `K6/TE/*.lean` (72 parts, `gen_teval.py`),
  `K6/TightAll.lean` (`gen_teval.py`), `K6/TightSem.lean`, `K6/TightAlong.lean`, `K6/TightFinal.lean`,
  `K6/TightConf.lean`, `K6/Final872.lean`: 872.
* `K6/A6.lean`: the bridge and Grayzel's formulation.
* `superperm6/Superperm6/Basic.lean`, `superperm6/Superperm6/Witness.lean`: Grayzel's files, changed;
  `superperm6/data/superperm6_872_clean.txt`: his data file, unchanged; `superperm6/LICENSE`: his licence;
  `superperm6/NOTICE.echols`: Echols's notice.
* `gen_k6.py`, `gen_cap.py`, `gen_tight.py`, `gen_teval.py`: the generators of the tables and of the parts.
  Nothing in them is trusted: a wrong table entry makes a kernel check fail.
* `check_witness.py`: compares the word written out in `Witness.lean` with the data file.
* `build.sh`, `sources.sha256`.

## Building

`build.sh` needs what `../n7/build.sh` needs except `leanc`: Lean 4.31.0, the compiled Mathlib, Pantone's
`Challenge.lean`, the Hunter-Raudvere library, Liu's library and Python 3 (`../README.md` says how to fetch them).
Grayzel's repository is not needed: the two files of his that the proof uses are in `superperm6/`.

```sh
JOBS=2 ./build.sh      # everything
./build.sh 5           # n = 1 to 5 only
```

It compares the sources with `sources.sha256` and the lists of the two libraries, runs the four generators into
the build directory and compares their 76 files with those in `K6/`, compares the witness with the data file, and
compiles every module that the theorems import, in dependency order, each as one Lean process with one thread:
the two libraries, `Challenge`, 2 files of `../words`, 18 of `../lower`, 34 of `../n7`, Grayzel's two files and the
98 files of this directory. Nothing compiled elsewhere is read except Mathlib. At the end it prints the axioms and
fails if any `#print axioms` line in the build directory names an axiom other than the three. The settings are at
the top of the script; `LEAN_PREFIX` puts a command in front of each Lean process (I used it for a memory
limit), and a build can be stopped and continued.

## What it costs

Measured on 25 October 2026 with `JOBS=2 ./build.sh` into an empty build directory on Windows 11 under Git Bash,
with other jobs running on the machine. Every Lean process ran on one thread at the lowest priority, each inside a
job object of the operating system that limited its memory and recorded its CPU time and its peak committed memory
(through `LEAN_PREFIX`).

| part | modules | Lean CPU time | peak committed memory of a process |
|---|---|---|---|
| the two libraries and `Challenge` | 151 | 2,639 s | 8.2 GB |
| the files of `../words`, `../lower`, `../n7` | 54 | 903 s | 10.5 GB (`PArith`), else 8.0 GB |
| Grayzel's two files | 2 | 165 s | 15.4 GB (`Witness`) |
| `Small/` | 3 | 39 s | 7.9 GB |
| engine, tables, chain caps, family, 871 | 13 | 296 s | 10.3 GB (`TabOK`) |
| the 72 parts of the tight case | 72 | 3,808 s | 32.9 GB (`T2P2Q6`, alone); the others at most 23.0 GB |
| proofs of the tight case, 872, bridge, `Exact`, `AuditSmall` | 10 | 142 s | 8.0 GB |
| in all | 305 | 7,992 s = 2.2 hours | 32.9 GB |

By the clock the build took 1 hour 34 minutes with two processes at a time. The wall times of the processes add
up to 8,567 s. A part of the tight case takes 4 to 316 s of CPU time; the chain caps (`CapEval`) take 34 s.
`./build.sh 5` compiles 157 of the 305 modules (the libraries, `Challenge`, the bridge, the files of `../lower`
behind Theorem A and `Small/`), which took 2,743 s of CPU time in the same run, with at most 8.2 GB. The build
directory holds 165 MB at the end.

## What is trusted

The Lean kernel with its arithmetic on natural numbers, the three axioms, Mathlib, and the definitions `Covers`
(Pantone), `IsSuperpermutation` and `IsMinimumLength` (Grayzel) and `Hunter.Ssuper` (Hunter and Raudvere). The
lemmas of the two libraries are compiled here from their sources; I did not review their proofs. The generators,
the tables and the part plan are not trusted. That the word in `Witness.lean` is the one in Grayzel's data file is
checked by `check_witness.py` and the hashes, not by the kernel; the theorem says that a word of 872 letters
exists, whichever it is.

## Licences

The new files are under the Apache License 2.0 of this repository. `superperm6/Superperm6/Basic.lean`,
`superperm6/Superperm6/Witness.lean` and `superperm6/data/superperm6_872_clean.txt` come from Grayzel's
superperm6 (github.com/BGray-wrl/superperm6, commit `d8a932d8f61d80b0bcfc737bd0e235a8300449c4`, directory
`formal-verification`) under the MIT License in `superperm6/LICENSE`; the two Lean files are changed, the data
file is not. `superperm6/NOTICE.echols` is the notice of the projects that the changes follow. The reused files
of `../n7`, `../lower` and `../words` and the two libraries keep their licences as stated there.

## What is not here

* Nothing about n = 7.
* The engine of `K6/` is written for 6 symbols. The values for $`n \le 5`$ do not use it.
