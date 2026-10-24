# L(7) >= 5,900 in Lean

A superpermutation on 7 symbols has at least 5,900 letters, two more than Justin Lebar's 5,898 and one more than
the 5,899 of [`../n7/`](../n7/README.md). The shortest word known has 5,905 letters. This directory proves 5,900 in
Lean 4 on top of the proof of 5,899, at the same two levels of trust:

* Level 1 is checked by the Lean kernel to the end, with the axioms `propext`, `Classical.choice` and
  `Quot.sound` only. It proves the bound from a list of equations, each of which says that a finite search
  defined in Lean finds nothing.
* Level 2 evaluates those equations by compiled code (`native_decide`): the 22 equations of 5,899 and 77 new ones
  in 72 modules, 99 in all. For them the Lean compiler, the C compiler of the toolchain, the Lean runtime and the
  libraries built from the search engines are trusted, as in `../n7/` and in Lebar's proof.

The written proof is [`PROOF_5900.md`](PROOF_5900.md); its section 7.1 says which Lean module proves which step.

## The statements

```lean
-- Audit5900Native.lean: written with no definition of this project, and accepted with
-- covers_lower_bound_7_5900_native as its proof
example : forall w : List (Fin 7),
    (forall p : List (Fin 7), p.length = 7 -> p.Nodup -> exists u v : List (Fin 7), w = u ++ p ++ v) ->
    5900 <= w.length

-- LowerBounds/F5900.lean, level 1: the bound from the search equations (hypotheses h0 .. of the form
-- PS.Covered n (PS.seqSearch ...) and the equations of the kernel and joint searches)
theorem covers_5900_of_search ... : forall w : List (Fin 7), SuperpermutationBounds.Covers w -> 5900 <= w.length

-- LowerBounds/F5900Native.lean, level 2
theorem covers_lower_bound_7_5900_native :
    forall w : List (Fin 7), SuperpermutationBounds.Covers w -> 5900 <= w.length
```

`#print axioms` of my build (2026-10-24, `Audit5900Native.lean`): `covers_5900_of_search` and `covers_5900_of_caps`
depend on `propext`, `Classical.choice` and `Quot.sound` only. `covers_lower_bound_7_5900_native` depends on those
three and on 99 axioms of the form `NAME._native.native_decide.ax_1_1`, one per evaluated equation: 22 of the proof
of 5,899 (`../n7/LowerBounds/P*Native.lean`), 41 of the kernel searches in 36 modules (`LowerBounds/K*Native.lean`)
and 36 of the joint searches in 36 modules (`LowerBounds/J15*Native.lean`). `build.sh full` checks this count.

## The parts

The proof follows the written proof part by part:

| part | what | files |
|---|---|---|
| A | the accounting at defect 15: components, cuts, pieces, the knapsack | `A15Arith`, `A15Core`, `A15Cut`, `A15Pieces`, `A15Tables`, `A15Final` |
| B | the kernel alone: table T', Theorem K, the search engine for sequences and its soundness | `KDefs`, `KTables`, `KSearch`, `KSound`, `KPot`, `KRev`, `KRules`, `KFinal`, `KSmall` |
| C | the joint statements: the joint engine, its soundness, its rules | `J15Search`, `J15Sound`, `J15Rules`, `J15Final` |
| D | the assembly at level 1 | `F5900`, `F5900Joint`, `Audit5900`, `Audit5900Search` |
| E | the evaluations and the theorem at level 2 | `K*Native`, `J15*Native`, `KFinalNative`, `J15FinalNative`, `F5900Native`, `Audit5900Native` |

The files that this proof shares with 5,899 (the model, its level 1, `PSearch`, the 17 evaluation modules of 5,899
and `PFinalNative`) are those of `../n7/LowerBounds/` and are not copied. `KSmallSearch`, `J15SmallSearch` and
`A15Test` are kernel tests; `KTestNative` and `J15TestNative` evaluate small searches by `native_decide` whose
answers are known, some of them also evaluated by the kernel. `evaluations.txt` lists the 72 evaluation modules
in the order of my run. `KTables.lean`, `KTestTables.lean` and the 74 files `K*Native.lean`, `J15*Native.lean`,
`KFinalNative.lean`, `J15FinalNative.lean` were written by the generators in [`tools/`](tools/README.md); they
write the same files again. The generators are not trusted: the kernel checks what they write, except the
equations that level 2 evaluates.

## Building

```sh
cd proofs/lean
JOBS=8 ./n7/build.sh full          # the proof of 5,899 with its 17 evaluations (in the same build directory)
./n7_5900/build.sh                 # level 1, the two engines, the kernel tests and the native tests
JOBS=8 ./n7_5900/build.sh full     # then the 72 evaluations, the theorem and the audit
./n7_5900/build.sh one J15S5Native # instead of "full": the default level and one evaluation, as a test
```

It needs what `../n7/build.sh` needs (Lean 4.31.0, Pantone's repository with Mathlib fetched, the Hunter-Raudvere
and preimage-chain libraries at the commits of `../words/README.md`, and `leanc`). The engines are three files
compiled to C: `../n7/LowerBounds/PSearch.lean`, `LowerBounds/KSearch.lean` and `LowerBounds/J15Search.lean`. The
library `KSearch` is linked from the C files of the first two, `J15Search` from all three; the evaluations load
them with `--load-dynlib`. `build.sh` compares the Lean files with `sources.sha256` first.

What it cost me:

* Level 2: the 72 evaluation modules ran from 2026-10-11 to 2026-10-23, beside other jobs, one Lean process each
  with 1 to 12 threads. The sum of wall time times threads is 4,190 thread-hours (an upper bound of the CPU time),
  the sum of wall times 1,028 hours, the longest module 84.6 hours (`KK0_01Native`). Each process stayed below
  0.55 GB of committed memory. `build.sh full` runs the modules one after the other with `JOBS` threads each.
* The assembly (`KFinalNative`, `J15FinalNative`, `F5900Native`, `Audit5900Native` and the level-1 files) took
  under five minutes on 2026-10-24.
* I have not rebuilt level 2 from an empty directory: it takes days. On 2026-10-24 I rebuilt, from the files of
  the repository as `git archive` writes them and in an empty build directory, with four processes:
  `../n7/build.sh` (default level, the two libraries included) in 47 minutes; then `build.sh one J15S5Native`,
  that is the two engines, level 1, the kernel tests, `KTestNative` (23 s), `J15TestNative` (26 s) and the
  evaluation `J15S5Native` (7 s), in 5 minutes, all exit 0 with the axiom checks passed; then
  `../n7_5901/build.sh` in 5 minutes. The whole run committed at most 31.5 GB.

## What is trusted, and what is not done

Trusted: the Lean kernel, the definitions of `Covers` and `HasWord` (Pantone's `Challenge.lean`), the three
standard axioms, and for the 99 equations the Lean compiler, `leanc` and the Lean runtime. The search programs in
C, C++ and CUDA of the written proof are not needed for the Lean theorem; they are its first evidence and a
cross-check (section 0.3 of `PROOF_5900.md`).

Not done: a rebuild of level 2 from an empty directory; an independent kernel or the comparator on these files.
