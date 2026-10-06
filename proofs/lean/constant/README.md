# The coefficient 1771/3456 in Lean

This directory is a Lean 4 development on top of Jay Pantone's library `SuperpermutationUpperBound`
(github.com/jaypantone/superperm-upper-43-80, commit `c8fb7ffdd69be1375580710ae11b47a295b1f0f6`, Lean 4.31.0,
Mathlib at `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`). It applies his construction to another selection and
proves, for superpermutations on n symbols,

    S(n) <= F3(n) + (1771/3456 + o(1)) (n-3)!        F3(n) = n! + (n-1)! + (n-2)!
    1771/3456 = 53/108 + 25/1152 = 0.512442...

His selection gives 43/80 = 7/15 + 17/240 = 0.5375. The selection used here has 53/108 (n-3)! missed classes
and needs 25/1152 (n-3)!/(n-3) connector cycles. The construction is his; what is new is the selection and the
two points in which it leaves the format of his paper (see "The selection").

Every proof is checked by the Lean kernel. There is no `native_decide` and no `sorry`. Each theorem below
depends on the axioms `propext`, `Classical.choice` and `Quot.sound` only.

## The theorems

`Covers`, `HasWord` and `F3` are the definitions of his `Challenge.lean`. I import them and do not restate
them. The statements below are copied from the Lean files, with the symbols spelled in ASCII (`forall`,
`exists`, `<=`, `/\`, `Nat`, `Rat`, `eps`), which Lean reads as the same statements.

```lean
-- SuperpermutationUpperBound1771/Main13.lean
theorem word_thirteen : SuperpermutationBounds.HasWord 13 6747849960

-- SuperpermutationUpperBound1771/Main.lean
theorem finite_bound (m : Nat) (hm : 11 <= m) (a : Nat) (ha : 2 <= a) (ham : a <= m) :
    exists w : List (Fin (m + 2)), SuperpermutationBounds.Covers w /\
      (w.length : Rat) <=
        (((m + 2).factorial + (m + 1).factorial + m.factorial : Nat) : Rat)
          + (1771 / 3456 : Rat) * ((m - 1).factorial : Rat)
          + ((a - 2 : Nat) : Rat) * (25 / 1152 : Rat) * ((m - 1).factorial : Rat) / ((m - 1 : Nat) : Rat)
          + ((m - a : Nat) : Rat) *
              min ((25 / 1152 : Rat) * ((m - 1).factorial : Rat) / ((m - 1 : Nat) : Rat))
                (((m + 1).factorial : Rat) / ((a + 1).factorial : Rat))

theorem eventual_bound :
    forall eps : Rat, 0 < eps -> exists N : Nat, 13 <= N /\
      forall K : Nat, N <= K -> exists w : List (Fin K), SuperpermutationBounds.Covers w /\
        (w.length : Rat) <= SuperpermutationBounds.F3 K +
          ((1771 / 3456 : Rat) + eps) * (Nat.factorial (K - 3) : Rat)
```

`finite_bound` and `eventual_bound` have the shape of his `finite_bound` and `eventual_bound`, with 1771/3456
in place of 43/80, 25/1152 in place of 17/240, and 13 symbols (m = 11) as the first size.

`SuperpermutationUpperBound1771/Corollaries.lean` adds the same bound in the shape of his `Finite` and
`FiniteInteger` (`Cost1771`, `finite_1771`, `finiteInteger_1771`) and three values of `finite_bound`:

| symbols | statement | parameters | best value of his `finite_bound` |
|---|---|---|---|
| 13 | `word_thirteen : HasWord 13 6747849960` | m = 11, a = 8 | 6,748,047,864 |
| 14 | `hasWord_fourteen : HasWord 14 93905309790` | m = 12, a = 8 | 93,907,379,760 |
| 15 | `hasWord_fifteen : HasWord 15 1401331300446` | m = 13, a = 9 | 1,401,355,309,200 |
| 16 | `hasWord_sixteen : HasWord 16 22320908101800` | m = 14, a = 9 | 22,321,214,768,160 |

In each line `a` is the parameter that makes the formula smallest. These are bounds from the general
formula. The literal words published for 13 symbols are shorter by about 47,000 letters (see `words/` at the
top of this repository).

`Audit1771.lean` restates all of this with the definitions of `Challenge.lean` only and asks Lean to accept the
theorems as proofs of exactly those statements. It is the file to read first.

## The words of his library that I use

* A 2-loop is fixed by a distinguished letter s (the satellite) and a cyclic order x of the other letters.
  It runs through the cyclic classes of the words x' s, for the rotations x' of x.
* A row (`Row`; a slice in his paper) is a piece of a 2-loop: a starting rotation of x (the base), the
  satellite, and the number of consecutive classes it covers (`visible`). A row is full if it covers the whole
  2-loop and short if it leaves out one class.
* A closed trail (`ClosedTrail`) is a cyclic list of rows in which the tail of each row is the head of the
  next. For a closed trail with f full and t short rows, f - t is its signed excess.
* Transport (`Transport.rows`, `transportWalk`) carries a row to rows on one more symbol, and completion
  makes the rows whose words are spelled out. A closed trail whose signed excess is divisible by k - 2 (k the
  number of symbols) is carried to k - 2 closed trails.
* A full chart (`Partition.fullChart`) is the closed trail of full rows above one 2-loop of the level below,
  with the new letter put into each gap in turn.
* A connector cycle is the cycle of the rotations of one endpoint word. It costs n - 3 letters and joins all
  closed trails it meets into one.

## The selection

The selection lives on 11 symbols. Its 2-loops are of three kinds.

* 338,688 loops carry the rows of a selection on 9 symbols transported twice. That selection has two
  closed trails (2,280 and 2,424 rows, both with 7 dividing f - t) and 336 2-loops without a row.
* The other 24,192 loops lie above those 336 loops. They come in 48 groups of 504. In each group 378 loops
  carry rows that form three closed trails of 63, 133 and 182 rows, and 126 loops carry no row.
* So 6,048 loops carry no row at all, and the three short trails of each group have f - t prime to 9.

Two points differ from the selections of the paper. A 2-loop may carry no row, as the 48 unused bases do in
`Certificates/NineRecipe.lean`; one transport later the loops above it form a full chart, exactly as in
`Partition/SprintBase.lean`. And a closed trail may violate the condition that k - 2 divides f - t; I write
such a trail k - 2 times in a row, which is again a `ClosedTrail` and satisfies the condition.
`SafeCircleCover.transport` has no divisibility hypothesis, so connector cycles are carried up as before.

After one transport (12 symbols) the selection has one full or short row in every 2-loop, all closed trails
satisfy the divisibility condition, and it has 7,875 connector cycles on 13 symbols: the 203 cycles found
on 12 symbols with the new letter in each of their nine gaps, and the word of each of the 6,048 loops
without a row. From there on everything is transport and completion as in the paper.

## The files

In `SuperpermutationUpperBound1771/`:

* `Repeat.lean`: a closed trail written m times: `closedTrail_rep`, `transported_rep_closed`,
  `transportWalk_rep_inventory`.
* `Levels.lean`: a level as a list of closed trails (`Level`); transport and completion of the list;
  `SafeComp` (cycle cover of one trail); `PortsCovered` (pointer certificate of one trail).
* `WordOfLevel.lean`: `word_of_level`: one completion and the connector cycles give a word with its ledger.
* `Hybrid.lean`: the certificate as a structure (`Cert`, `GroupFacts`); the levels on 10, 11 and 12 symbols;
  `complete12`.
* `Thirteen.lean`: the counts, the 7,875 cycles, the word on 13 symbols.
* `AllSizes.lean`: the level on k + 12 symbols for every k; `Cert.word_ledger`.
* `GenericBounds.lean`: the rational bound and the epsilon argument.
* `Certificate/Checks.lean`: the statements the kernel evaluates, and what they imply.
* The other files of `Certificate/`: generated data with one `decide +kernel` per check.
* `Main13.lean`, `Main.lean`, `Corollaries.lean`: the statements above.

Next to it:

* `Audit1771.lean`: the statements again, in the words of `Challenge.lean` only.
* `gen_cert.py`: writes the generated certificate files from the two input files.
* `patches/`: the one patched file of his library, as a file and as a diff.
* `pantone-sources.sha256`: SHA-256 of the 94 files of his repository that are compiled unchanged, and of the
  original of the patched one.
* `build.sh`: builds everything from sources (see "Building").

The 11 hand-written Lean files of the development have 1,909 lines; `gen_cert.py` has 360.

### What each certificate file checks

All certificate files except `Checks.lean` are written by `gen_cert.py`. The script follows the Lean
definitions and checks every fact itself before it writes a file.

* `WalkA`, `WalkB` hold the two closed trails on 9 symbols as `List (Row Nat)`. Check `WalkOK`: `BasedOn`,
  `ClosedTrail`, 7 divides `signedExcess`; row and charge counts.
* `Walks9`: the two trails as a `Level`.
* `Circles` holds the 203 connector cycles on 12 symbols. Checks: `CircleFamilyValid 9`, the letters, the
  count.
* `Groups00` to `Groups07` hold the 48 groups: three trails, 126 loops without a row, the seven 9-symbol
  loops below, and pointers. Check `GroupOK`: `BasedOn` and `ClosedTrail` for the three trails; the nine
  passes of each trail start at nine different ports; counts; every loop above the seven loops is a row of
  the group or one of its loops without a row; a `MixedPointer` for every port of each trail written nine
  times.
* `Big00` to `Big13` hold pointers for the 112 long trails on 11 symbols. Check `BigOK`: a valid
  `MixedPointer` for every port. The trails themselves are not listed: the kernel computes them with
  `transportWalk` from `WalkA` and `WalkB`.
* `D9`, `Chunks9`, `Complete9_1` to `Complete9_7` hold the 336 loops without a row, the rows of the two
  trails in chunks of 64, and pointers. Check: every ordering `0 :: a :: t` of the eight letters is, up to
  rotation, the base of a row or one of the 336 loops.
* `Groups`, `Complete9`, `Cert`: assembly into `Certificate.cert : Cert`.

`Certificate/modules.txt` lists the generated modules in the order in which `gen_cert.py` writes them.

### Which of his lemmas carry the proof

* Rows and 2-loops: `BasedOn.transport`, `BlockComplete.transport`,
  `Transport.rows_cyclicEq_iff_inInsertionBlock`, `exists_inInsertionBlock_of_perm_append_satellite`,
  `Transport.packingRows_counts`.
* Loops without a row: `Partition.fullChart_closedTrail`, `fullChartAt_valid`,
  `fullChart_cyclicEq_iff_inInsertionBlock`.
* Closed trails: `transportWalk_closedTrail`, `transportWalk_winding_divisible`, `transportWalk_inventory`,
  `completionWalk_inventory`, `completionExit_eq_self_of_winding`.
* Connector cycles: `SafeCircleCover.transport`, `SafeCircleCover.sound`, `CircleFamilyValid.extend`,
  `extendCircles_length`, `MixedPointer.sound`.
* Completion and the word: `Completion.packingRows_cover`, `packingRows_length`, `packingRows_visible_sum`,
  `packingRows_valid`, `packingRows_word_mem`, `exists_word_of_circle_rows`.
* The epsilon argument: `Bounds.floor_parameter_bounds`, `Bounds.factorial_error_le`.

I do not use `SuperpermutationUpperBound43/` or `CircleTransport/Iterated.lean`. They are written for a
base on 10 symbols with the constants 7/15 and 357. Of the 335 Lean files of his repository the development
imports 95, directly or through other files: `Challenge.lean` and 94 files of `SuperpermutationUpperBound/`.

## One patched file, and four passages that follow his text

`patches/SuperpermutationUpperBound/Assembly/SupportedStates.lean` is a copy of his
`Assembly/SupportedStates.lean` in which the import of `Partition.SprintFamily` is replaced by
`Foundation.SupportedWords` and the section that defines `stateAlphabet` (30 lines) is removed;
`patches/SupportedStates.diff` shows the change. The reason: `SprintFamily` imports the certificate for 9
symbols, `Certificates/NineRecipe.lean`, which did not compile within 13.6 GB on my machine, and the joining
theorem `exists_word_of_circle_rows` does not use that section. Four files of his that import the patched one
(`BalancedCuts/SupportedCutWords`, `Assembly/BalancedCircleWords`, `Assembly/ConnectorWords` and
`Assembly/CircleRows`) are compiled from his unchanged sources against it, like the other 90.

Four passages of mine follow his text closely, because the file that holds the original imports the
10-symbol family:

* `completionWalk_closed` in `Levels.lean` is `Iterated.completionWalk_closed` for an arbitrary completion
  letter.
* `word_of_level` in `WordOfLevel.lean` follows `GenericBounds.family_word_ledger`; `overlap_bound` states
  `Bounds.circle_overlap_length_bound`.
* `GenericBounds.lean` is his `SuperpermutationUpperBound43/GenericBounds.lean`, lines 14 to 220, with the
  constants changed, and `overlap_state_count_rat` from `Bounds/CircleRational.lean`.
* `exists_canonPart` in `Certificate/Checks.lean` follows `Word9.canonicalBases_complete`.

His library is under the Apache License 2.0.

## Inputs

`gen_cert.py` reads two files of the repository github.com/jhalfar/superpermutations and nothing else. The
selection on 9 symbols, its closed trails, the groups and all pointers are derived from them. Both hashes are
written into every generated file.

* `arrange/data/n12t-selection.txt.xz`, the selection on 11 symbols. SHA-256:
  `44f6c51e66b20ce625dc3cfc8d53abce6b2c23984a57608a915ff5209b3c44be`
* `selection/data/zcycles_n12.txt`, the 203 connector cycles on 12 symbols. SHA-256:
  `a38ed3727c69273843f892e6bd72b17fe9117f1d3e8d8fed09e6a745c0501957`

## Building

`build.sh` does everything, from sources, into `../build/constant` (or `BUILD_DIR`). The settings are listed at
the top of the script and in `../tools/common.sh`; `../README.md` says how to fetch what the build needs.

```sh
./build.sh
```

1. It compares the 95 source files of his library with `pantone-sources.sha256`.
2. It runs `gen_cert.py` (5 s) and requires its output to be identical to the files in `Certificate/`.
3. It compiles 145 modules in dependency order: 95 of his library from his sources (one from `patches/`),
   the 49 of this development, and `Audit1771.lean`. It uses nothing that his project has compiled.
4. It prints the `#print axioms` lines.

There is no Lake project here: his project cannot be a plain Lake dependency while one of its files is
replaced. `build.sh` calls `lean` once per module.

Measured on my machine (Ryzen 9 5950X, 32 GB, Windows 11 with Git Bash; one Lean process with one thread,
other jobs running beside it), from an empty build directory:

| modules | count | time each | peak memory |
|---|---|---|---|
| his library | 95 | 1 to 37 s, 10 minutes in all | 3.4 GB |
| `WalkA`, `WalkB` | 2 | 45 s | 3.9 GB |
| `Groups00` to `Groups07` | 8 | 102 to 114 s | 3.7 GB |
| `Big00` to `Big13` | 14 | 82 to 107 s | 3.3 GB |
| `Chunks9` | 1 | 51 s | 2.6 GB |
| `Complete9_1` to `Complete9_7` | 7 | 15 s | 2.3 GB |
| the other 17 modules and the audit file | 18 | at most 16 s | 1.9 GB |

The whole build took 60 minutes (53 minutes of Lean time). Memory is the working set of the Lean process;
the largest process committed 5.6 GB. The build directory has 0.3 GB. The generated sources have 1.6 MB.

With `USE_PATCH=0` the script uses his own `SupportedStates.lean` and then compiles `NineRecipe.lean` and what
lies between as well. I have not been able to run that on my machine (see above).

## What is not covered

* Nothing is proved for 12 symbols or fewer. On 12 symbols the 6,048 loops without a row give closed trails
  of their own that need at least 1,210 further connector cycles, and the bound would be weaker than the
  known words.
* The connector cycles on 13 symbols are the transported ones. I did not choose them again at 13 symbols,
  as Section 6 of the paper does for his selection. 203 cycles on 12 symbols is the best number found; the
  lower bound from the search is 201.
* The selection is not known to be optimal. The rows inside a group are one of 6 optimal solutions among
  those that are invariant under rotation of the seven old letters; without that symmetry 308 missed
  classes and loops per group is the best found, with a lower bound of 270.
* The error term o(1) is the one of his proof. I did not formalise a rate.
