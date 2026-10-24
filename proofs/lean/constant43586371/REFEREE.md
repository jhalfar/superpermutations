# Referee report: `Uniform.coefficient_tends_to_zero`

2026-10-19 (00:42 to 01:30). Adversarial check of
`SuperpermutationUpperBound43586371.Uniform.coefficient_tends_to_zero`:

    ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ K : ℕ, N ≤ K → ∃ w : List (Fin K), SuperpermutationBounds.Covers w ∧
      (w.length : ℚ) ≤ SuperpermutationBounds.F3 K + ε * (Nat.factorial (K - 3) : ℚ)

Everything I wrote for this check is in one working folder of mine, not in this repository (sources copied into `src/`, my own build in `build/lib`,
logs in `logs/`, scripts `closure.py`, `build_ref.py`, `run_one.sh`, `leanchecker_all.sh`, `ref_check.py`). Nothing
outside that folder and this file was changed. Every Lean process ran with one thread, at idle priority, under
`guard.py --gb 12`; at most two at a time.

## Verdicts

| check | verdict |
|---|---|
| 1. Statement | pass |
| 2. Kernel replay | pass: leanchecker `--fresh` replays the whole import closure, Mathlib included, through the kernel without error; comparator not runnable here (no binary, no `lean4export`, `landrun` is Linux only); I ran its statement and axiom checks by hand |
| 3. Clean build | pass: all 118 modules rebuilt from source, Pantone's included, only Mathlib precompiled; same audit |
| 4. Paper proof | pass, with two small inaccuracies in the text (below); my own script confirms Lemmas 1 to 6 for every odd m = 5..41 |
| 5. Sanity word | not possible: the smallest instance is far too large (below) |

## 1. Statement

* `Challenge.lean` and the `Challenge.lean` of my clone of github.com/jaypantone/superperm-upper-43-80 have the
  same sha256 `559e5613…3968`. That clone sits at commit `c8fb7ff` (2026-10-01) with a clean working tree. I did not
  compare it with GitHub (no downloads).
* `Covers w` = every list `p : List (Fin K)` with `p.length = K` and `p.Nodup` is a contiguous factor
  (`w = u ++ p ++ v`). That is exactly "every permutation of the K symbols occurs". `F3 K = K! + (K-1)! + (K-2)!`
  in ℚ (natural subtraction inside the factorials, harmless for large K).
* Name resolution, checked in the compiled environment (`src/RefAudit.lean`, output `refaudit.out`):
  - `SuperpermutationBounds.Covers` and `SuperpermutationBounds.F3` are defined in module `Challenge`.
  - The only constants in the whole environment named `*.Covers`, `*.F3` or containing `SuperpermutationBounds`
    are Challenge's ten declarations (plus the equation lemma `F3.eq_1`) and Pantone's own
    `SuperpermutationUpperBound.F3` (a different, ℕ-valued name). No shadowing.
  - The theorem's type is syntactically equal (`Expr ==`) to the same statement typed by me at the root with
    `_root_.` names, and to `ChallengeUniform.statement`, the statement elaborated in a separate file that imports
    nothing but `Challenge` (so no instance or coercion of the big development can have changed its meaning).
  - The constants occurring in the type are only core/Mathlib basics (`Rat`, `Rat.instLT`, `Rat.instLE`,
    `Rat.instAdd`, `Rat.instMul`, `Rat.instNatCast`, `Nat.factorial`, `instSubNat`, `List.length`, `Fin`, …) and the
    two Challenge definitions.
  - `referee_unfolded`, the statement with `Covers` and `F3` written out by hand, is accepted with the same proof term.
* `ε * (K-3)!` is a product in ℚ (`HMul.hMul` with `Rat.instMul`, `ε : ℚ`, `Nat.cast` into ℚ). As intended.
* The statement is not vacuous: the known lower bound K! + (K-1)! + (K-2)! + K - 3 is consistent with it, and it
  is stronger than Challenge's `Eventual` (coefficient 43/80 + ε).

## 2. Kernel replay

* comparator (described in `comparator/README.md` of github.com/jlebar/superperm7-ge-5898): Lean FRO's tool builds a
  trusted Challenge module and the untrusted Solution in a sandbox, exports both with `lean4export`, checks that each
  named theorem and every constant its statement mentions are identical in the two, checks that the axioms are in a
  permitted list, and replays the Solution's proofs in the Lean kernel (optionally also in `nanoda`). It needs the
  `comparator` binary, `lean4export` and `landrun` (a Linux sandbox). None of them is on this machine, so I could not
  run it without downloads. What I did instead covers its first two steps:
  statement identity (section 1: `Expr ==` against a statement elaborated from `Challenge` alone, and every constant
  of the statement resolved to `Challenge` or core/Mathlib) and the axiom list (`[propext, Classical.choice,
  Quot.sound]`, the three standard ones).
* leanchecker (`leanchecker.exe` of toolchain v4.31.0, the successor of `lean4checker`, built into Lean): it
  loads a module's imports and re-adds each of the module's own declarations to a fresh kernel environment
  (`Environment.replay`). With `--fresh` it does this for the module and all its imports from scratch, Mathlib
  included, so no declaration is trusted from an `.olean`.
  - Per module, on all 118 modules of the closure and `ChallengeUniform`: 119/119 exit 0, 01:03:38 to 01:27:46
    (`referee/leanchecker_all.log`).
  - `--fresh SuperpermutationUpperBound43586371.Uniform.Main`: exit 0, 01:03:46 to 01:11:32, peak 6.05 GB
    (`referee/leanchecker_fresh.log`). Every constant in Main's environment (core, the imported part of
    Mathlib, Pantone's 94 modules, our 23, `Challenge`) went through the kernel again.
  - Negative controls, so that a silent exit 0 means something: `src/RefBad.lean` adds `theorem RefBad.bad : False
    := True.intro` with `debug.skipKernelTC` on. It compiles, and `#print axioms RefBad.bad` says "does not depend on
    any axioms", so an axiom audit alone would not notice a forged declaration. leanchecker rejects it ("has type
    True but it is expected to have type False", `leanchecker_negative.log`). `src/RefBad2.lean` only imports it:
    plain leanchecker passes it (it replays the module's own declarations only), `--fresh` rejects it
    (`leanchecker_negative_fresh.log`). So the `--fresh` run on Main is the one that matters, and it passed.
  - Limitation: leanchecker uses the same C++ kernel as `lean` itself, so it guards against corrupted or forged
    `.olean` files and elaborator bugs, not against a kernel bug. An independent kernel (nanoda, lean4lean) is not
    available here.

## 3. Clean build

* `closure.py` follows the imports of `Uniform/Main.lean`: 118 modules, of which 94 are Pantone's
  (`SuperpermutationUpperBound.*`), 23 ours (13 base modules of constant43586371 and the 10 `Uniform/*` files that Main needs)
  and `Challenge`.
* Sources copied into `referee/src/` (hashes in `copies.txt`): Pantone's 93 unchanged files and `Challenge.lean`
  straight from the upstream clone (all 94 also equal the copies in `pantone`); the one patched file
  `Assembly/SupportedStates.lean` from `patches` (the diff only replaces the import of
  `Partition.SprintFamily`, which pulls in the n = 9 certificate needing more than 13.6 GB, by
  `Foundation.SupportedWords`, and deletes the 30-line section `stateAlphabet`; deleting definitions cannot make
  anything downstream unsound); our 23 files from `lean`.
* `build_ref.py`: `LEAN_PATH` = Mathlib and its packages (`packages`, Mathlib at
  `fabf563`, the revision of Pantone's manifest, clean tree) + `referee/build/lib` only. No `lib`,
  no prebuilt module of ours. 118/118 compiled, no error, no `sorry` in any log, 2026-10-19 00:54:19 to 01:02:34
  (8 min 15 s wall, two processes, peak 4.4 GB committed per process). Warnings are only linter noise
  (unused simp arguments, `omega` does nothing, unused variables).
* Audit against this build (`refaudit.out`): `#print axioms coefficient_tends_to_zero` =
  `[propext, Classical.choice, Quot.sound]`, the same for `referee_statement` and `referee_unfolded`.
* Side remark: 95 of the 118 `.olean` files differ byte-wise from the project's (Pantone's were built by `lake` in
  his project, with other options; six of ours, `Walk`, `Distinct`, `WalkLoops`, `Ports`, `BlockG`, `AllSizesG`,
  differ by a few bytes from the same sources). `Main.olean` and `Stage.olean` are byte-identical. This does not
  affect anything: my build stands on its own.
* No grep hit for `sorry`, `admit`, `native_decide`, `axiom`, `implemented_by`, `extern`, `unsafe`,
  `ofReduceBool` or kernel options in our 23 files or `Challenge.lean`, nor `sorry`/`native_decide` in Pantone's 94.

## 4. Paper proof (PROOF.md) as a referee

Each lemma has a Lean counterpart that is proved, not assumed (the axiom list above would show any `axiom` or
`sorry`):

| PROOF.md | Lean |
|---|---|
| Lemma 1 closed trail | `walk_closed` (`Walk.lean`) |
| Lemma 2 alphabet, counts | `walk_basedOn`, `walk_length`, `walk_charge` |
| Lemma 3 loops distinct | `Xinj`, `walk_canon_nodup` (`WalkLoops.lean`), invariants `key1_arr`, `key2_arr` |
| Lemma 4 above3T, loops without a row | `walk_canon_mem`, `walk_dloops_length`, `above3T_nodup`, `above3T_length`, `count_uncovered` |
| Lemma 5 ports | `walk_exit` (shift `(q + 4) mod (m+2)`), `walk_orbit_perm` |
| Lemma 6 one cycle | `walk_safe` (`SafeComp (rep (m+2) W) 10 (m+2) [cycle0]`), `cycle0_valid` |
| block conditions | `walkData_ok`, `walk_safeB`, `emptyData_ok`, `famS` (`Block.lean`) |
| Lemma 7 invariants | `walk_I1`, `walk_I2`, `empty_I1`, `empty_I2`, `step_I3`, `double_step`, `stages`, `closed_level` |
| the limit | `small_coefficient`, `finite_of_closed`, `eventual_of_finite`, `coefficient_tends_to_zero` |

The framework (`Stage.advance`, `Stage.close`, `Stage.noSeed`, `Closed.all`, `Closed.word`) is constant43586371's, and
Pantone's `floor_parameter_bounds`, `factorial_error_le` are his; all compiled from source in check 3.

I re-derived the arithmetic by hand: the walk step of (I1) needs 9m + 2 ≤ 10 m (m+12)/m0, true for m ≥ m0; the
decay (L - N)/L ≤ a/(a+1) is L ≤ N (a+1), i.e. (a+1)(a+2) ≤ (a+12)(a+1), and with a^6 (a+7) ≤ (a+1)^7 it gives (I3);
the port sum is -m(m+8) + 4m = 4 - (m+2)^2 ≡ 4 (mod m+2), invertible since m+2 is odd; the final constants match
Lean (r > 4/(δ/2), M > 1024 r^4/(δ/2), N = (a+1) + 22 + 8r + M).

My own numeric check (`ref_check.py`, written from PROOF.md and Pantone's definitions of `Row.head`,
`Row.tail`, `portPath`, `portTarget`, `liftRow`, `repairRow`, `fullAt`, `completionWalk`, `SafeIncidence`,
before I opened `check_uniform.py`): for every odd m = 5..41, with the old letters avoiding 9 and 10, plus random
relabellings (two for m ≤ 15, one for m ≥ 17): W(m) has m(m+12) rows of length m+3 on the right alphabet, charge 8m
with 4m short rows; it is a closed trail (cyclic tail = head); its m(m+12) loops are distinct; all lie in
`above3T`, which has exactly L = m(m+1)(m+2) pairwise non-rotated entries whose old letters keep the cyclic order of
d0; rows + loops without a row = L; one lap moves port q to q + 4 mod m+2 and m+2 laps from port 0 start at every
port once; `cycle0` = head of `fullAt(first row, 10, 0)` has m+2 distinct letters with 10 and without 9, and from
every port j the literal `completionWalk` of the (m+2)-fold walk has a row whose head is a rotation of it. Logs:
first run in this report's session (m = 5..15), `ref_check_17_41.log`. Mutation tests (a shortened sweep, a swapped
arrangement, a reversed cycle, too few laps) make it fail, so it is not vacuous.

Inaccuracies in the text (no effect on the theorem):
* §0 says "the term a dominates" N. With the least admissible choices, N = 15,796,421 at δ = 1 (a = 2,359,397,
  M = 13,436,929) and N = 618,926,421 at δ = 1/2 (a = 276,824,245, M = 342,102,017): there M dominates. a dominates
  only for δ below about 0.45 (at δ = 0.1: a ≈ 2.0·10^13, M ≈ 8.8·10^11). STATE.md's "N ≈ 2·10^6/δ^7" is right
  for small δ and off by a factor of about 8 at δ = 1.
* Section numbering runs 9, 11, 10.
* The remark "m0 = 11 gives κ ≈ 0.49 after 400 levels (n ≈ 1214)" checks out (κ = 0.4929 at a = 1211).

## 5. A word

No instance is small enough. In the Lean construction m0 ≥ 11 (needed by `rest0`) and m0 = 2(t+6)+1 with
t > 40/δ, so m0 ≥ 95 for any ε ≤ 1; even ignoring ε, the smallest closed level with no walk at all (K' = 0, a = 11)
gives words on K ≥ 14 symbols (14! ≈ 8.7·10^10 letters, and it would test nothing new, only no seed + charts), and
the first level with a walk is a = 17, words on K ≥ 20 symbols (20! ≈ 2.4·10^18 letters). A scaled-down instance
(a walk at a = 7 with words on 13 symbols) is outside the Lean hypotheses (`8 ≤ |A0|`, `11 ≤ m0`) and would need a
re-implementation of the whole transport, completion, closing and cycle-joining pipeline, so it would test my
re-implementation more than this proof. I did not do it. The block-level facts that such a word would exercise
(closed trail, loop exactness, ports, the literal completion meeting the cycle) are checked directly in section 4.

## What an outside checker still has to trust

* The Lean 4 v4.31.0 kernel (leanchecker replays with the same kernel; no second kernel was available).
* Not Mathlib's proofs: the `--fresh` replay re-checked every imported proof in the kernel. What remains is that
  the basic notions in the theorem's type (`Rat` and its order and arithmetic, `Nat.factorial`, `List`, `Fin`,
  `List.Nodup`) are Mathlib's/core's usual ones, read from the prebuilt Mathlib `fabf563`.
* The two definitions of `Challenge.lean` (11 lines, read above) and that the local clone of Pantone's repository is
  his real upstream file (sha256 given; compare with GitHub).
* Nothing else: not PROOF.md, not the numeric checks, not the project's prebuilt `.olean` files, not the patched
  Pantone file (it only removes code; the build from source used it).
