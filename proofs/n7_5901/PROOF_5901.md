# L(7) >= 5,901: the written proof

State of 2026-10-24. A superpermutation on 7 symbols is a word that contains every permutation of the
symbols as a contiguous subword, and L(7) is the least length of one. This document is the written proof of
L(7) >= 5,901. It is a computer-assisted proof, not a Lean theorem. It rests on the Lean theorem L(7) >= 5,899
with its exact model, on the written proof of 5,900 as far as its tables, lemmas and computations are used, on
arguments written out here and on the computations of Table C (section 0.3). Every computation of Table C has
ended and found nothing; every part file is present and agrees with Table C (section 6.3). Most of the
computations have been run by one program only (section 0.4). Lean also proves the reduction to search
equations. Those equations are about the Lean search engines, which are not the programs of Table C. Six of the
thirty equations of defect 16 are proved so far, and a seventh (K6) is being evaluated (section 0.4).

Notation and terms are those of the written proof of 5,899, cited as [P], and of the written proof of 5,900,
cited as [W]. [W] is `proofs/lean/n7_5900/PROOF_5900.md` of this repository. The written text of [P] is not
public; the Lean proof of 5,899 and its description are in `proofs/lean/n7/` (see the README there), and I cite
[P] by the sections of the written text. Formulas are in plain ASCII as there.

Paths in backticks are relative to this folder (`proofs/n7_5901/`) unless they start with `proofs/`; the README
of the folder lists its files. Some sources that I cite are working notes of mine and are not in this
repository. I cite them by name and section: the map of defect 16 (the first form of the accounting, "the map"),
the reports of the referee checks ref16, ref16b, refjs and ref5901 (section 0.2), my notes on the Lean form
(PLAN_5901, STATE_5901A, STATE_5901B, STATE_5901C) and the notes that come with the card programs and their tests
(note gpu, note gpu2, note gkjs, note gpuj, note tune, note krows, note ringcap, note jrev). A program or log that
I name without a path is not in this repository either.

## 0. The theorem and what it rests on

**Theorem.** Every word over 7 symbols that
contains each of the 5,040 permutations of the symbols as a contiguous subword has at least 5,901 letters.

By the exact model ((L1) of [W] 0.1, with k = 7 and D = 16: hpv 7 + D + 1 = 5,884 + 17 = 5,901) the theorem is
equivalent to

    (*)  no valid standard configuration on 7 symbols has cost at most 136,

that is, "no configuration of defect at most 16". The proof does not use that defect 15 is excluded; it treats
cost at most 136 directly. It has four parts.

1. Accounting (section 2). A configuration of cost at most 136 gives components whose values add up to at least
   40 within total weight 96. The excess is now at most 2 (it was at most 1 at defect 15). Every component is
   cut at its dear places into pieces, and every piece of positive value is an item. A finite check over table D
   leaves 131,436 piece profiles in 20 shapes. Each shape is a statement about pieces: the kernel-alone statement
   K or one of nine joint statements T1 to T9, the joint ones only for rings of value at least 7.
2. Kernel alone (section 3). No sequence has value at least 40 within weight 96. This takes eleven statements K0
   to K10 about the rows of a table D16. K3 and K4 rest on K0, K1 and K2.
3. Joint statements (section 4). The nine statements T1 to T9 in their restricted forms, searched in 15 runs
   with rules that the defect-15 search did not have: the reversal cut on one piece (PREV), the order of pieces
   of equal kind by value (ORD), windows of ring holes and the split of a window by the value of the ring (VS).
   A further rule, the order of rings by start vertex (ORDS), was used for faster runs; no counted run uses it
   (section 4.5).
4. Conclusion (section 5).

Why the defect-15 method had to change. At defect 15 one knapsack over single tables left 69 shapes, and the
joint statements were searched with the plain rule of [W] 5.4 (2.9e13 start vertices in all). At defect 16 the
same rule would need about 2.4e18 (estimate of the map, section 5.2, about 60 years of 28 threads). The rules of
section 4 and the graphics card brought the joint runs to about 5.0e15 start vertices in all (the sum of the
column "tried" of Table C).

### 0.1 What it rests on

- Lean, as in [W] 0.1. (L1) the model, level 1 (`covers_length_gt_of_no_stdConfig`, `no_stdConfig_iff`);
  (L2) the tables of set B, level 2; (L3) the lemmas of level 1 that do not mention the cost. Used here:
  `entries_length_ge`, the geometry (G2) to (G7), `famH_spec`, `family_le_49`. `acc_value`, `acc_weight` and
  the other statements for cost at most 134 are repeated on paper at cost 136 (section 2.1).
- From [W], as proved there. Table T and Lemma CL ([W] 2.2); tables D and T' ([W] 2.3); Theorem K and
  Corollary K of defect 15 ([W] 4.1), whose ten statements have ended in two independent programs; Lemma RV,
  Lemma REV, Lemma CUT and the search rule of the kernel-alone statements with its completeness ([W] 4.2 to
  4.5); the lines 1 to 4 of Lemma ITEM and the reductions (G4), (G5) ([W] 3.4, 3.5); the joint search and its
  completeness ([W] 5.4) with the cycle lemma of [P] 8.2. Not used: the joint statements S1 to S5 of defect 15,
  Lemma NCH, the count KN, Lemma SUB.
- The computations of Table C (section 0.3) and the exact ring row RX (section 1.3).

### 0.2 What is proved on paper in this document

| | argument | section |
|---|---|---|
| Q1 | the tables D, D16, RX and the lowered ring rows: what they are and why they are valid | 1.2 to 1.5 |
| Q2 | Lemma ACC16 at cost 136; eps <= 2 | 2.1, 2.2 |
| Q3 | Lemma CUT16: the cut of a component at all its dear places; the items | 2.3, 2.4 |
| Q4 | Proposition PROF16, Lemma PIECE16; every ring piece of a profile has value at least 7 | 2.5 to 2.7 |
| Q5 | the knapsack by pieces and the map from shapes to statements | 2.8, 2.9 |
| Q6 | Theorem K16 from the kernel statements; Rule JS (junction shift) | 3 |
| Q7 | the restricted joint statements; PREV, ORD, ORDS, windows, VS; why each run proves its statement | 4 |
| Q8 | the conclusion | 5 |

Three referee checks went through these arguments as they stood in my working files: ref16 (the accounting,
PREV, ORD, ORDS, the tables), ref16b (the split VS, the restriction to rings with at least 8 holes, the exact
ring row) and refjs (Rule JS). Their reports are working notes and are not in this repository. None found a
step that fails. Each asked for sentences to be added; they are in the text here, not as notes:

| point of the referee | what it says | where |
|---|---|---|
| ref16 M1, ref16b F1 | the programs cut a ring when the value still needed is negative | 4.2 |
| ref16 M2, ref16b L3 | rings with at most 7 holes are not pieces of a profile; T3', T4', T6', T9' | 2.7, 4.8 |
| ref16 M3 | every ring is listed in its own cycle-lemma rotation, which passes the ring rule in every position | 4.2 |
| ref16 M4 | every joint statement rests on Theorem K of defect 15 | 1.2, 5 |
| ref16 M5 | all parts of one statement must have the same statement line | 4.7, 6.3 |
| ref16b L1 | classes of objects defined by a condition on each ring are closed under the normalisations | 4.1 |
| ref16b L2 | in the lower halves of VS the value needed at the ring is positive | 4.6 |
| refjs 1 to 5 | Rule JS: the hypothesis b >= 0, consecutive rows, the cases l' = 1 and l = 6, the reversal, the parts | 3.3 |

A fourth check, ref5901, read the whole written proof as it stood on 2026-10-15, with my list of open questions
and Table C, and found no step that fails and no gap in the mathematics. It asked for one false sentence to be
corrected (Lemma CL is proved on paper, not in Lean; section 0.4), for the rows 9 and 10 of D to be attributed to
Lemma CL (section 3.4) and for sentences in sections 2.3 and 4.2; they are in the text.

### 0.3 The computations (Table C)

Every line is an exhaustive search. "kept" is the number of kept prefixes, "tried" (joint statements) the number
of start vertices tried. All runs are on one CUDA card with 32 GB unless the program column says otherwise. The
programs and the rules are named in section 6.1 and section 4.7. Table C is `table/TABLE_C16.md`, state of
2026-10-18. The runs of 2026-10-16 (T6rp, T9r, T9rs, K7, K10, and the repeats of T7 and T8 by `gj2`) were made
after the host machine was changed; the card is the same. No counted statement rests on the rule ORDS: the
counted runs of T6' and T9' are the plain-rule ones. The second counts in the program column (`k2_s12`, `j2_np5`
and the Lean engines, 2026-10-20 and 2026-10-21) ran on the CPU; section 0.4 describes them.

Joint statements (section 4); every line ended with found 0:

| | statement | rule | kept | tried | program, parts |
|---|---|---|---|---|---|
| T1 | J(S7 S7; 50, 84; 1) | ORD + PREV 10,15,25 | 432,156,242,209,710 | 2,386,049,711,507,025 | `gj2`, 1,024 parts |
| T2 | J(R S7; 46, 89; 1), rings 8..15 | PREV 10,15,40 | 101,123,384,635,543 | 591,203,509,244,515 | `gj2`, 64 |
| T2 | rings 16..23 | PREV 10,15,40 | 129,493,336,379,997 | 664,376,894,711,771 | `gj2`, 64 |
| T2 | rings 24..31 | PREV 10,15,40 | 135,483,427,600,468 | 687,655,387,002,664 | `gj2`, 64 |
| T2 | rings 32..39, value >= 17 | VS, ring first | 151,457,803,584 | 795,609,616,646 | `gj3`, 16 |
| T2 | rings 32..39, value <= 16 | VS, kernel first | 817,008,248,719 | 4,282,237,016,933 | `gj2`, 16 |
| T2 | rings 40..47, value >= 20 | VS | 91,979,996,005 | 476,425,689,572 | `gj3`, 16 |
| T2 | rings 40..47, value <= 19 | VS | 284,267,038,527 | 1,671,708,523,584 | `gj2`, 16 |
| T2 | rings 48..55, value >= 23 | VS | 71,260,814,984 | 365,649,914,334 | `gj3`, 64; equal to `jr6` on the CPU |
| T2 | rings 48..55, value <= 22 | VS | 174,112,070,351 | 957,110,796,225 | `gj2`, 64; equal to `jr6` on the CPU |
| T2 | rings 56..89 | PREV 10,15,40 | 28,953,480,015,964 | 152,453,459,284,641 | `gj2`, 64 |
| T3' | J(R S5 R; 52, 82; 2), rings >= 8 holes | PREV 10,16,43 | 40,196,474,735,125 | 213,550,167,376,609 | `gj2`, 64 |
| T4' | J(R S4 S4; 56, 77; 2), rings >= 8 holes | ORD + PREV 10,16,43 | 1,479,145,818,172 | 7,891,206,447,132 | `gj2`, 64 |
| T5 | J(S3 S3 S3; 60, 72; 2) | plain | 52,379,362,069,149 | 268,009,289,170,899 | `gj`, 16 |
| T6' | J(S2 R R R; 58, 75; 3), rings >= 8 holes | PREV 10,16,25 (tag T6rp) | 112,728,682,360 | 592,623,181,185 | `gj2`, 16 |
| T7 | J(S1 S1 R R; 62, 70; 3) | plain | 1,432,335,917,907 | 7,283,065,963,552 | `gj`; repeated by `gj2`, 1 part (same counts); second count `j2_np5`, 8 parts (same counts) |
| T8 | J(S0 S0 S0 R; 66, 65; 2) | plain | 7,126,584,865 | 36,384,111,126 | `gj`; repeated by `gj2`, 1 part (same counts); second count `j2_np5` and the Lean engine (same counts) |
| T9' | J(S0 R R R R; 64, 68; 4), rings >= 8 holes | plain (tag T9r) | 11,105,597 | 59,706,146 | `gj2`, 8; second count `j2_np5` and the Lean engine (same counts) |

`gj` and `gj2` share `jr_core.h`, so the `gj2` runs of T7 and T8 are repeats, not independent checks.

Extra runs with the rule ORDS, found 0; they are not counted and no statement rests on them:

| | statement | rule | kept | tried | program, parts |
|---|---|---|---|---|---|
| T6' | J(S2 R R R; 58, 75; 3), rings >= 8 holes | ORDS + PREV 10,16,25 (tag T6r) | 98,752,840,534 | 515,328,744,583 | `gj2`, 16 |
| T9' | J(S0 R R R R; 64, 68; 4), rings >= 8 holes | ORDS (tag T9rs) | 4,287,144 | 22,804,444 | `gj2`, 8 |
| T9 | J(S0 R R R R; 64, 68; 4), all rings | ORDS (tag T9s) | 9,560,336,846,694 | 50,933,661,579,615 | `gj2`, 8 |

The two halves of a window of T2 (VS) are run in opposite orders of the pieces, so their kinds are written
R S7 for the upper half and S7 R for the lower half in the commands (section 6.2); the statement does not depend
on the order.

Kernel alone (section 3); "no violation" in every line that has ended:

| | links, levels | potential, rule | kept | program, parts |
|---|---|---|---|---|
| K10 | 10, level 36 | 10,16,25 | 172,577 | `gk4`, 1 part file (`audit/records/K10_p0.txt`); `k2_s12` and the Lean engine (same count) |
| K9 | 9, levels 36 to 42 | 10,16,25 | 384,081,983 | `gk4`, `kfast2`, `k2_s12`, the Lean engine (with Rule JS: 359,998,813, three programs) |
| K8 | 8, levels 36 to 48 | 10,16,25 | 22,732,567,392 | `gk4`, `kfast2`, `k2_s12`, the Lean engine (with Rule JS: 19,526,754,031) |
| K7 | 7, levels 36 to 54 | 10,16,25 | 320,243,136,927 | `gk4`, 1 part file (`audit/records/K7_p0.txt`, 32 card seconds); `k2_s12`, 64 parts (same count); the Lean equation (answer only) |
| K6 | 6, levels 38 to 60 | 10,16,25 | 2,569,985,903,558 | `gk4`, 16 |
| K5 | 5, levels 38 to 66 | 10,16,25 | 23,993,915,746,406 | `gk4`, 64 |
| K4 | 4, levels 42 to 72 | 10,15,25 | 160,141,566,085,840 | `gk4`, 64 |
| K3 | 3, levels 49 to 78 | 10,15,30 | 527,651,578,348,368 | `gk4`, 256 |
| K2 | 2, levels 52 to 84 | 20,29,60, Rule JS | 375,408,252,302,475 (512 of 512 parts, no violation) | `gkjs`, 512 |
| K1 | 1, levels 56 to 90 | 20,29,60, Rule JS | 755,070,879,353,479 (2,048 of 2,048 parts, no violation) | `gkjs`, 2,048 |
| K0 | chains, levels 66 to 96 | 17,24,5, Rule JS | 497,079,750,869,693 (4,096 of 4,096 parts, no violation) | `gkjs`, 4,096 |

K2 ended on 2026-10-16; the change of the host machine on 2026-10-15 interrupted it, and it went on under the
same tag and parameters. K0 ended on 2026-10-17 and K1 on 2026-10-18 at 18:37 (89,682 card seconds). Their part
files are packed in an archive of mine (not in this repository). The part-file audit of section 6.3
(`audit/partaudit.py`) reads every part of every tag of this table. All parts are present, each tag has one
statement line, no part has a violation, and the sums are the kept counts above.

Inputs to the tables (section 1):

| | statement | kept | tried | state |
|---|---|---|---|---|
| RX | ring row by exact holes, 0..63 | 1,588,850,620 | 7,944,253,101 | found 0; three programs with equal counts (`j2` of defect 15 in its mode `ringtab`, `programs/rx/ringx.c`, the referee's `programs/rx/ringchk.c`) |
| defect 15 | Table C of [W] 0.3 | | | all ended, two programs each |

The knapsack (section 2.8): the referee's `programs/knapsack/knap16.py` by pieces, 131,436 piece profiles, all
removed; the map's `programs/knapsack/acc16.py` by items on the same table.

### 0.4 The level of trust

This is a computer-assisted proof. It has three levels, and each one asks the reader to trust something
different and proves something different.

- The computed level: the statements of Table C are true. The card programs searched every statement of
  Table C and found nothing. Together with the rules of sections 3 and 4, which I prove on paper (next item),
  this proves the statements, and the theorem rests on this level and the paper level. The level is C, C++ and
  CUDA code. Here defect 16 is weaker than defect 15, where every statement had two programs with equal counts
  that share no code. At defect 16 the statements fall into three groups.
  - K10, K9, K8, K7, T9', T8 and T7 have independent second counts. The second programs are those of defect 15,
    written from the texts only, which share no code with the card programs: `k2_s12`
    (`programs/second/k2_s12.cpp`, the kernel program k2.cpp of defect 15 built with room for 12 links) and
    `j2_np5` (`programs/second/j2_np5.cpp`, the joint program j2.cpp of defect 15 built for five pieces). The
    audit of 2026-10-20 ran K10, K9, K8, T9' and T8 (`audit/second/`). I ran K7 with the same program in 64
    parts (`audit/k7second/`) and T7 with `j2_np5` in 8 parts (`audit/t7second/`, ended 2026-10-21). Every
    count equals Table C. K9 also has the referee's `ref7` (refjs, also written from the texts) and `kfast2`. K8
    also has `kfast2`, which comes from the card program's lineage. The Lean engines are a third
    implementation; on K10, K9, K8, T9' and T8 they give the same answers and the same counts, and on K7 the
    same answer (third item).
  - Two statements have a second run that is not independent. The window 48..55 of T2 was run on the card and
    by `jr6`, which share `jr_core.h`, so ref16b 4.6 counts them as one program twice. T6' has the plain-rule
    run and the ORDS run of the same program. T7 was also repeated by `gj2`, which shares `jr_core.h` with
    `gj`; its independent second count is the one of `j2_np5` above.
  - K0 to K6 (`gkjs` for K0, K1, K2 and `gk4` for K3 to K6) and T1 to T6' (`gj2`, `gj3`, `gj`) rest on one run
    of one card program each.

  RX has three independent programs and the knapsack two. Section 7.2 gives the state statement by statement.
- The paper level: the arguments of this document and of [W]. The three referee checks of section 0.2 went
  through the arguments of defect 16 as they stood in my working files, and tested them against brute force on
  5 and 6 symbols and in part on 7 (section 6.4). The arguments of [W] that I use here are proved in Lean at
  level 1 ([W] 0.1). On paper I use Lemma CL of [W] 2.2 for the rows 9 to 16 of D, for the rows 0 to 8 beyond
  weight 90, for Corollary K16 at s >= 11, for the row 9 that K10 reads and for KN16. Lean proves the one
  instance that the kernel statements need (the rows 9 and 10 of D16 below LO, `K16.cl16_of`, from Theorem K of
  defect 15) and needs no other, because in the Lean accounting every piece has at most 10 links and is bounded
  by D16 (STATE_5901A 4, item 3).
- The Lean level: the reduction to the Lean search equations. `covers_5901_of_search`
  (`LowerBounds/F5901Search.lean` of the level-1 sources; axioms propext, Classical.choice, Quot.sound; parts
  A16, B16, C16, D16 of PLAN_5901) states: if the search equations of 5,899 and 5,900 hold, together with the
  eleven fields of `K16.Evals` (K0 to K10, engine `K16.seqSearch`) and the nineteen fields of `J16.Evals` (the
  eighteen joint runs and the ring search of RX, engine `J16.jSearch`), then every word that contains all
  permutations of 7 symbols has at least 5,901 letters. Lean proves the accounting, Lemma CUT16, Rule JS, PREV,
  ORD, VS, the ring classes and the completeness of the engines (section 7.3).
  - This level checks every argument of this document that turns "the searches find nothing" into the theorem.
  - The equations are statements about the Lean engines, not about the card programs. The kernel engine walks
    the tree of the card programs: its counting copy gives the kept counts of Table C on K10 (172,577), K9
    (384,081,983, and 359,998,813 with Rule JS, the count of `kjs`) and K8 (22,732,567,392). The joint engine
    differs from the card programs (STATE_5901C 3). It tests the class of every ring, which is an extra cut in
    T3', T6', T7, T8 and T9'. It does not clip the need at 0 in T1, T2 and T4'. Its rule ORD has another form (a
    prefix rule and the jump rule; the programs used the jump rule only, for T4'). It has no ORDS, which no
    counted run uses. So the "found 0" of a card run does not discharge the Lean equation of that run, and each
    equation has to be evaluated on its own.
  - Six equations are evaluated, as Lean theorems proved by `native_decide` with the C code of the engines
    loaded (the mechanism of the level-2 modules of 5,900), in `lean/Audit5901/` and outside the build of the
    level-1 sources. K10, K9, K8: `K16.Audit.k10_native`, `k9_native`, `k8_native` (`NK.lean`, 105 min on 1
    thread). T9', T8: `J16.Audit.t9_native`, `t8_native` (`NJ.lean`, 117 min on 2 threads). K7: the four
    theorems `K16.Audit.k7_0_16`, `k7_16_32`, `k7_32_48` and `k7_48_64` (`NK7_0.lean` to `NK7_3.lean`), each for
    one range of 16 of the 64 hash parts at depth 8, evaluated one after the other on 3 threads from 2026-10-20
    19:15 to 2026-10-21 16:46 (77,433 s of wall time; `lean/nk_queue.log`). `NEv.lean` turns the first five into
    the fields themselves, with the definitions of `K16Final.lean` and `J16Bridge.lean`:
    `Audit5901.k10_ev : K16.Ev Utab10 10 36 36 10 16 25 false`, `k9_ev`, `k8_ev`,
    `t9_ev : J16.Ev DRj [...] J16.rT9 64 68 4` and `t8_ev`. `NEv7.lean` does the same for K7:
    `k7_ev : K16.Ev Utab7 7 36 54 10 16 25 false` from the four theorems, by a case split on the part number of
    the kind that `f1_covered_native` of the proof of 5,899 makes with two ranges. `#print axioms` lists propext
    (and Quot.sound for `t9_ev`) and the `native_decide` axioms of the equations, for example
    `K16.Audit.k8_native._native.native_decide.ax_1_1`, and for `k7_ev` the four axioms of `k7_0_16` to
    `k7_48_64`; `NEv.lean` compiles in 58 s and `NEv7.lean` in 16 s. Before that I evaluated the first
    five equations by `#eval`: K10 in 1 s, K9 in 84 s, K8 in 57 min on 2 threads, T9' in 16 s and T8 in 108 min
    on 2 threads, all with the answer "nothing found". The counting copy of the joint engine gives the counts of
    Table C on T9' (11,105,597 kept, 59,706,146 tried) and on T8 (7,126,584,865 kept, 36,384,111,126 tried, 115
    min on 2 threads). The class cut and the clip do not act in these two runs, so there the Lean engine walks
    the card program's tree. The scripts, logs and the counting copy are in `lean/` (`Eval/*.lean`,
    `logs/*.log`, `Audit5901/J16Count.lean`).
  - K6 is being evaluated in the same way, in 16 files `NK6_00.lean` to `NK6_15.lean`, each for one range of 16
    of the 256 hash parts at depth 10, one file at a time on 4 threads. It started on 2026-10-24 at 03:26. The
    first file (`k6_0_16`) ended at 07:12 after 13,552 s, with the `native_decide` axiom in its log; the second
    was running when I wrote this. When K6 ends, 7 of the 30 equations are evaluated (section 7.2).
  - The other 24 equations of `K16.Evals` and `J16.Evals`, K6 among them until it ends, are not evaluated.
    Evaluating all of them would take about 900 days on 28 threads (section 7.3).

  So the Lean level checks the whole argument, but for 24 of the 30 search equations of defect 16 it does not
  check the searches. Those 24 rest on the computed level.

The first referee set two conditions (ref16 6, items 1 and 2), and both are met. They asked that T9 be run by
the plain rule, and that ORDS be tested on 7 symbols with a positive case before T9 and T6' were counted with
it. No counted statement rests on ORDS now: T6' is counted by the plain-rule run T6rp (PREV only), and T9' (T9
for rings with at least 8 holes, section 4.8) by the plain-rule run T9r. The ORDS runs of both are extra lines
of Table C, marked as not counted. The ORDS run of T9' (T9rs) also found 0.

Section 7 lists what has not been done.

### 0.5 Whose the parts are

As in [W] 0.5. The transform that cuts a path through all permutations into components is Zach Hunter and Uku
Raudvere's. The chains of a component and the lemmas about them are Xiaolong Liu's. The bound 5,898 is Justin
Lebar's; nothing of his proof is used. The model of standard configurations, the proofs of 5,899 and 5,900, the
accounting, the search rules and the programs of defect 16 are mine.

## 1. Objects and tables

### 1.1 Objects

All objects are those of [W] section 1 and nothing changes: words, classes, blocks, rows (e, l) with 6 - l
holes, links of weight 3 or 4, chains, sequences with s links, rings, standard configurations, their cost, the
value v(C) = m - h - 5 (X + a) and the weight w(C) = h + 6 (X + a) of a component. The facts (G4), (G5) and
(G7) are used as there. A sequence with s links and x holes has val = rows - x - 5 s and wt = x + 6 s; a ring with x holes has
val = rows - x and wt = x.

A **piece** is a sequence with at most s links, written S<s>, or a ring, written R ([W] 5.1). "At most" is the
reading of the Lean predicate `KS.IsPiece` and of every program (`t < pS[i]`), so a statement about S7 S7 is
also one about S7 S3 (ref16 2).

### 1.2 Table D

D is the file `table/capD.txt` (identical to the file of the map): rows 0 to 11 of sequences and one ring row, each
for 0 to 96 holes. Its entries are:

- rows 0 to 8 at x + 6 s <= 90: table D of [W] 2.3, that is min(T_s(x), x + 44 + 5 s). The referee's
  `programs/knapsack/knap16.py` compares them with the Lean list `Dtab`: all 603 entries equal;
- rows 0 to 8 beyond weight 90: the entries of T' by the closure of [W] 2.2;
- rows 9, 10, 11: equal at every level to the bound (cl2) of the closure, computed from the rows 0 to 8
  (ref16 2);
- the ring row: TR' of [W] 2.3 for 0 to 76 holes (equal to Lean `TRtab` there); from 77 holes on the chain row,
  because a ring is a chain. The chain row is x + 44 for 77 to 90 holes (Theorem K of defect 15, row 0) and the
  closure beyond.

The knapsack also reads rows 12 to 16, which are not in the file; `knap16.py` takes them as the bound (cl2) of
the rows 0 to 8.

D is valid. Every entry is an upper bound on the rows of a sequence with exactly s links and x holes (of a
ring with x holes for the ring row). For the rows 0 to 8 within weight 90 this is Theorem K of defect 15 and the
validity of T ([W] 2.2, 4.6). For the entries given by the closure it is Lemma CL of [W] 2.2, proved on paper
there (section 0.4 says which instance Lean proves and why the Lean proof needs no other). Its proof shows that
each of the bounds (cl1) and (cl2) is an upper bound once the entries it reads are, and it is written for
x <= 96 and s <= 15; for s = 16 the same proof applies. For the ring row it is the validity of TR' and "a ring is
a chain".

So every statement of this document rests on Theorem K of defect 15 (ref16 M4). Its ten
statements have ended in two programs that share no code, with equal counts ([W] 0.3).

What the runs read. A joint run reads the rows 0 to 7 at weight at most 89 and the ring row at 0 to 89 holes,
because every piece of a joint statement has weight at most 89. The knapsack reads all rows within weight 96.

### 1.3 The exact ring row RX

The ring row of D to 69 holes is the referee's table of [P] for "T rows and at most g holes". Read by the
exact number of holes, as every program reads it, it is loose where it is flat.

**Statement RX.** For 0 <= x <= 63 a ring with exactly x holes has at most RX(x) rows, where

    x  0..15:   5  1  2  1  1  1 10  6 16  3 13 14 15 16 21 22
    x 16..31:  27 25 33 28 35 31 37 33 38 36 40 41 46 43 48 49
    x 32..47:  50 50 56 53 58 58 59 60 65 62 67 67 69 69 71 71
    x 48..63:  76 77 78 78 84 81 82 83 86 87 89 89 91 90 93 92

The entry 1 at x = 1, 3, 4, 5 means that no ring with that number of holes exists (a ring has at least 2 rows).
23 entries are lower than in D, among them 53 to 55 holes (81 82 83 against 84 84 84).

Proof. The ring search of [P] 8.2, which is written for an exact number of holes H: a ring with T rows and
exactly H holes has a rotation in which every prefix of r rows and d holes has d T <= r H, and the rest of the
ring is a chain with exactly H - d holes. The search does not need a table that grows with H. Its inputs are the
chain row on 0 to 63 holes (set B, I1, I2 of [W] 2.2) and the row RX. Three programs that share no code ran it
for 0 to 63 holes and found no ring above RX, with equal counts: kept 1,588,850,620, tried 7,944,253,101
(`j2` of defect 15 in its mode `ringtab`, my `programs/rx/ringx.c` in its mode `prove`, the referee's
`programs/rx/ringchk.c`). `programs/rx/witnesses.txt` holds a ring with exactly RX(x) rows for each of the 60
levels that have a ring, each checked from the definitions by `programs/rx/check_wit.py`. So RX is the exact maximum and cannot be lowered. QED

The file `table/capD_r.txt` is D with the ring row replaced by RX on 0 to 63 holes; the rows 0 to 11 are those
of D. It is read only by the upper halves of the split VS (section 4.6). Every program reads a ring row at the
exact number of holes and forms its own maxima over the weight (the bound Best, the tables of PREV through Best,
the keep tables one number of holes at a time, the knapsack); no place needs "at most x holes"
(ref16b 1). With the exact row a ring of negative value is no longer kept alive by targets that do not
exist; that is the cut M1 of section 4.2, and it acts in no run.

On `table/capD_r.txt` the knapsack of section 2.8 gives 114,745 piece profiles in the same 20 shapes, all removed by the
same statements with the same least slack (`programs/knapsack/knap16_rx.log`, and the referee's
`programs/knapsack/knap_rx.log`). The proof does
not need this; it uses D.

### 1.4 Table D16 for the kernel alone

    D16_s(x) = min(D_s(x), x + 39 + 5 s)        for 0 <= s <= 10 and x + 6 s <= 96.

A sequence with s links and x holes has value at most 39 iff it has at most x + 39 + 5 s rows. The levels where
D16 is below D are, with LO_s the level below the first of them:

    s = 0: 66..96 (31), LO 65         s = 1: 56..90 (35), LO 55         s = 2: 52, 55..84 (31), LO 51
    s = 3: 49..78 (30), LO 48         s = 4: 42..72 (31), LO 41         s = 5: 38, 40..66 (28), LO 37
    s = 6: 38..60 (23), LO 37         s = 7: 36, 38..54 (18), LO 35     s = 8: 36..48 (13), LO 35
    s = 9: 36..42 (7), LO 35          s = 10: 36 (1), LO 35

These are 248 entries. For s >= 11 there is none: the largest value of a row 11 to 16 within weight 96 is 35, 29,
23, 17, 11, 5 (`knap16.py`, by the closure). Theorem K16 of section 3 says that D16 is valid.

Files (`table/`): `capD16_k.txt` has every row from D16; `capD16u_S_k.txt` has the rows below S from D and
the row S from D16. The referee's script chkcaps.py (ref16) checked both against this definition and checked that every
LO used is below the first new level of its row.

A trap that the files avoid. The files of the map (capD16.txt, capD16u_S.txt) end with a line `R: ...` that
holds the ring row. The kernel-alone programs read every line that starts with a number as a row and take
`R:` as row 0, so with those files the ring caps overwrite the chain caps and a run proves nothing
(note gpu2 0.A). The files `*_k.txt` are the same files without that line (12 of 12 compared by the
referee). Every kernel run of Table C used a `_k` file; the counts of K8 and K9 in the map, made with the
old files, are not used.

### 1.5 The lowered ring rows of the split VS

The lower halves of the split VS (section 4.6) read tables in which the ring row is lowered on the window of the
run:

| window | a | file | ring row on the window |
|---|---|---|---|
| 32..39 | 17 | `table/lo_32_39_a17.txt` | min(row, H + 16) |
| 40..47 | 20 | `table/lo_40_47_a20.txt` | min(row, H + 19) |
| 48..55 | 23 | `table/capD_r_rv22.txt` | min(row, H + 22) |

In the rows 0 to 11 they are D (the referee's script chktab.py, ref16b). Outside the window the ring row of all three is that of
RX (for instance 1 at 1 hole and 6 at 7 holes, where D has 5 and 10), and it is not read there. On the window the lowered row is the same whether it is
made from D or from RX, so the lower halves do not rest on RX. They are not valid tables:
they bound the rows of a ring with H holes in the window only if its value is at most a - 1, which is exactly the
class of rings that the lower half is about. A lower half must therefore be run with RLO and RHI equal to the
window of its file, and it is (section 6.2).

## 2. The accounting at defect 16

Throughout, c is a valid configuration with cost at most 136. The steps of [W] section 3 are repeated where they
change; the case split of [W] 3.5 (one dear place) becomes a cut at every dear place (section 2.3), and the
knapsack is made by pieces, not by items (section 2.8).

### 2.1 Lemma ACC16

**Lemma ACC16.** sum over the components of v(C) >= 40 and sum of w(C) <= 96.

Proof, as Lemma ACC15 of [W] 3.1. Let R be the number of rows, h the number of holes and S the sum of X + a over
the components, so cost = R + S <= 136. The number of blocks is 6 R - h, and it is at least 720 by
`entries_length_ge`. Hence sum v = R - h - 5 S >= 720 - 5 (R + S) >= 720 - 680 = 40 and
sum w = h + 6 S <= 6 (R + S) - 720 <= 816 - 720 = 96. QED

### 2.2 The excess is at most 2

Form the family F of c and the excess eps = sum of eps_C as in [W] 3.2: eps_C = X - j for the kernel and an H0a,
(X - j) + (a - 1) for an H1 and 0 for H0b, H0c and H0d. Lemma FAM (`famH_spec` for a hanging component, the identity
for the kernel) holds for every valid configuration, so with Lemma ACC16

    (2.1)    sum over F of e >= 35 + 5 eps        and        sum over F of (holes + 6) <= 102 - 6 eps.

**Lemma EPS16.** eps <= 2.

Proof. If eps >= 3 then F is a family with sum (holes + 6) <= 84 and sum e >= 50. Lemma FF of [P] section 5
(`family_le_49`, stated for weight at most 84) says that such a family has sum e <= 49. QED

eps = 2 is not excluded at the level of families: by (2.1) it needs sum e >= 45 within weight 90, and the tables
allow 53 there. So there are three cases, eps = 0, 1, 2. The proof does not need a bound on the number of chains
of F: the finite check of section 2.8 runs over every number of links that fits into weight 96.

### 2.3 The dear places and Lemma CUT16

A **dear place** of a component is a heavy seam of weight 4 + g with g >= 1 (its excess is g), or, for an H1
with attachment cost a >= 2, the attachment (its excess is a - 1). Since X - j is the sum of (weight - 4) over
the heavy seams, eps_C is the sum of the excesses of the dear places of C, for every kind of component. By Lemma
EPS16 the configuration has at most two dear places, and if it has two, both have excess 1.

For a sequence Q with q links, m rows and y holes and an integer g >= 1 put

    br_g(Q) = m - y - 5 (q + 1 + g),        wb_g(Q) = y + 6 (q + 1 + g).

(This is not the Lemma CUT of [W] 4.4, which is about the reversal cut; that one is used in section 3.)

**Lemma CUT16.** Let C be a component with eps_C >= 1 and r dear seams, of excesses g_1, ..., g_r.

- (lin) C is the kernel (r >= 1). Cut it at its dear seams into K_0, K_1, ..., K_r, where K_i for i >= 1 is the
  part behind the seam of excess g_i. Then
      v(C) = [m_0 - h_0 - 5 s_0] + sum over i >= 1 of br_(g_i)(K_i),
      w(C) = [h_0 + 6 s_0] + sum over i >= 1 of wb_(g_i)(K_i),
  where K_0 has m_0 rows, h_0 holes and s_0 links.
- (lin') C is an H1 with a >= 2 (r >= 0). Cut it at its dear seams into Q_0, Q_1, ..., Q_r and put
  g_0 = a - 1. Then v(C) = sum over i >= 0 of br_(g_i)(Q_i) and w(C) = sum over i >= 0 of wb_(g_i)(Q_i).
- (cyc) C is an H1 with a = 1 or an H0a (r >= 1). Take the cyclic list of rows of (G4) (m rows, h - 1 holes,
  the seams of C and one closing link of weight 3) or of (G5) (m - 1 rows, h - 7 holes, the seams of C as its
  links) and cut it at the r dear seams into Q_1, ..., Q_r, where Q_i is the part behind the seam of excess g_i.
  Then v(C) = sum over i of br_(g_i)(Q_i) - 6 and w(C) = sum over i of wb_(g_i)(Q_i) + 7.

In every case the parts are sequences. The links of a part, which q and s count, are the seams of C of weight 4
that it contains; the seams of weight 3 and, in (cyc), the closing link of weight 3 join rows inside a chain and
do not enter q, s or 5 q. Their classes are pairwise different. In (lin) and (lin') the blocks of the parts are
the blocks of C. In (cyc) they are the blocks of C and one more block, of a class that contains no block of C
(the class of the slot in (G4), the class X in (G5)); this block lies in exactly one part, which I call the
**borrowing part**.

Proof. Every part other than K_0 and Q_0 is preceded by exactly one dear place, and the j - r seams of weight 4
are distributed over the parts as their links: sum of the s_i is j - r, where s_i is the number of links of the
i-th part.
(lin): a = 0 and X = (j - r) + sum over i >= 1 of (1 + g_i), so
5 X = 5 s_0 + sum over i >= 1 of 5 (s_i + 1 + g_i); rows and holes add up over the parts. This gives v and w.
(lin'): X + a = (j - r) + sum over i >= 1 of (1 + g_i) + (1 + g_0) = sum over i >= 0 of (s_i + 1 + g_i).
(cyc), H1 with a = 1: the parts have m rows and h - 1 holes in all, and X + a = sum of (s_i + 1 + g_i) + 1, so
v = m - h - 5 (X + a) = sum br - 1 - 5 and w = h + 6 (X + a) = sum wb + 1 + 6.
(cyc), H0a: the parts have m - 1 rows and h - 7 holes in all, and X = sum of (s_i + 1 + g_i), so
v = sum br + 1 - 7 and w = sum wb + 7.
The classes: the blocks of a valid configuration lie in pairwise different classes, and by (G4), (G5) the added
block is of a class that contains no block of C. A cyclic list with pairwise different classes, read from any of
its rows, is a list of rows with the same links except the one it is cut at, as in [W] 3.5. QED

For r = 1 and g = 1 the four cases are (a) to (d) of [W] 3.5. The identities were recomputed by the referee
(ref16 1). They use (G4), (G5) and the definitions, not the cost.

### 2.4 Items

An **item** is a piece together with a kind. Its value is val(piece) - dv and its weight is wt(piece) + dw, with
the shifts dv, dw of its kind; its **table value** is the same with val(piece) replaced by the bound that table D
gives for a piece of that kind and weight (for S<u> at weight y: D_u(y - 6 u) - (y - 6 u) - 5 u; for R with x
holes: min(TR(x), D_0(x)) - x, TR the ring row of D). The kinds:

| kind | where it comes from | piece | dv | dw | excess g | borrows a class |
|---|---|---|---|---|---|---|
| K | the kernel if eps_K = 0; K_0 in (lin) | S<s> | 0 | 0 | 0 | no |
| R | H0b (item Z of [W]) and H1 with a = 1, j = 0, m >= 2 (item A_1) | R | 6 | 7 | 0 | yes |
| AB | H1 with a = 1, X = j >= 1 (A_q) and H0a with X = j (B_q) | S<j-1> | 11 | 13 | 0 | yes |
| E | a part with g = 1 of (lin) or (lin'), or a part with g = 1 of (cyc) that does not borrow | S<q> | 10 | 12 | 1 | no |
| F | a part with g = 2 of (lin) or (lin') | S<q> | 15 | 18 | 2 | no |
| A' | the borrowing part of (cyc), g = 1 | S<q> | 16 | 19 | 1 | yes |
| A'' | the borrowing part of (cyc), g = 2 | S<q> | 21 | 25 | 2 | yes |

For a part Q with q links and g = 1 or 2: val(Q) - (5 + 5 g) = br_g(Q) and wt(Q) + (6 + 6 g) = wb_g(Q), which
gives the lines E and F; the borrowing part carries the - 6 and + 7 of (cyc) in addition, which gives A' and A''.
In (cyc) the parts that do not borrow have g = 1, because two dear places have excess 1 each. The lines R and AB
are the lines 1 to 4 of Lemma ITEM of [W] 3.4 with the shifts of Lemma PIECE of [W] 5.2.

**Lemma ITEM16.** Every component C of c gives a list of items, empty or not, with these properties.

1. The values of the items of C add up to v(C) and their weights to w(C). If the list is empty, v(C) <= 0.
2. The piece of every item is a sequence (with pairwise different classes) or a ring, with the number of links
   of the table, and the value of an item is at most its table value.
3. The excesses g of the items of C add up to eps_C.
4. The blocks of the pieces of C are blocks of C, and every borrowing item adds one block of a class that contains
   no block of C; the pieces of the items of C are disjoint parts of the rows of C (or of its cyclic list).

Proof. If eps_C = 0: for the kernel, the kernel is a sequence with j links and its item is K. For a hanging
component, [W] 3.4 (Lemma ITEM, lines 1 to 4) and [W] 5.2 give the items R and AB with v(H) = val - dv and
w(H) = wt + dw exactly; the components outside these lines are H0c, H0d and the H1 with a = 1, j = 0, m = 1,
whose v is at most -5, at most 0 and -4 - h ([W] 3.4); their list is empty. If eps_C >= 1, Lemma CUT16 gives
the parts and the identities of 1; for (cyc) the - 6 and + 7 are assigned to the borrowing part. The value of an
item is at most its table value because D is valid (section 1.2) and a ring is a chain. 3 holds because every
part with g takes the excess of the dear place in front of it, and in (lin') g_0 = a - 1 is the excess of the
attachment. 4 is Lemma CUT16 and (G4), (G5). QED

### 2.5 Profiles

**Proposition PROF16.** Take the item K of the kernel and every other item of Lemma ITEM16 whose value is at
least 1. Then the items taken have total value at least 40, total weight at most 96 and total excess at most 2,
and every item other than K has table value at least 1.

Proof. Every item has weight at least 0 (wt >= 0 and dw >= 0), and every component with an empty list has
w(C) >= 0. The items left out have value at most 0, and the components with an empty list have v <= 0. By Lemma
ITEM16 (1) and Lemma ACC16 the values taken add up to at least sum v(C) >= 40 and the weights taken to at most
sum w(C) <= 96. The excesses taken are at most eps <= 2 (Lemma EPS16). The table value of an item is at least its
value. QED

This is where the text differs from the map (section 2 there), which takes the parts of a (cyc) component
together as one item of value (sum of br) - 6. Taking every part as its own item, with the - 6 and + 7 on the
borrowing part, is what the knapsack of section 2.8 enumerates, and it is finer: a (cyc) component with two
parts gives E + A' when both are positive; E alone or A' alone when one is not; nothing when both are not.
(`REFEREE_NOTES.md`, section C, point 1.)

A **piece profile** is a kernel piece S<u> at weight w0 with table value t0, and a multiset of further items of
the kinds R, AB, E, F, A', A'', each with a piece S<u> or R at a weight w and with table value t - dv >= 1, such
that the total excess is at most 2, t0 + sum (t - dv) >= 40 and w0 + sum (w + dw) <= 96. By Proposition PROF16
the configuration c gives a piece profile: the pieces of the items taken, with their kinds. Its **shape** is the
list of its kinds, for example K+E+R.

### 2.6 Lemma PIECE16: from items to pieces

**Lemma PIECE16.** The pieces of the items of Proposition PROF16 have

    sum of val = (sum of the values of the items) + sum of dv  >=  40 + sum of dv,
    sum of wt  = (sum of the weights of the items) - sum of dw  <=  96 - sum of dw,
    shared classes <= number of items that borrow a class.

Proof. The first two lines are the definitions of value and weight of an item and Proposition PROF16. Shared
classes: the blocks of a piece are blocks of its component, plus one borrowed block for a borrowing item (Lemma
ITEM16 (4)). Pieces of different components are disjoint in classes because every class is a block of c exactly
once, and the pieces of one component are disjoint parts of its rows. So a class lies in at most one piece as a
block of c, and otherwise only in pieces that borrow it: (number of pieces that contain the class) - 1 is at most
the number of pieces that borrow it, and the sum over the classes is at most the number of borrowing items. QED

The shifts were recomputed by the referee from the definitions (ref16 1: R 6/7, AB 11/13, E 10/12,
F 15/18, A' 16/19, A'' 21/25).

### 2.7 Every ring piece of a profile has value at least 7

Ring pieces come only from items R (Lemma ITEM16; the parts of Lemma CUT16 are sequences). An item R is taken
only if its value val - 6 is at least 1, so every ring piece of a profile has value at least 7. The ring row
of D gives value at most 5 for 0 to 7 holes (TR(0..7) = 5 5 5 5 5 5 10 10, values 5 4 3 2 1 0 4 3), so every
ring piece of a profile has at least 8 holes. (With RX the values there are smaller still.)

This is what allows the joint statements to be proved for rings of value at least 7 only (section 4.8); without
it the statements T3, T4, T6 would be needed as they stand, and they are not proved (ref16b 2.3).

### 2.8 The knapsack by pieces: a finite check

**Finite statement KN16.** With table D there are exactly 131,436 piece profiles. They have 20 shapes. In every
one the pieces fit the kinds of one of the statements K, T1, ..., T9 of section 2.9, and their V, W and number of
borrowing items meet its V, W and B.

The check is a finite enumeration: kernels S<u> at weights w0 <= 96 (so u <= 16) and multisets of further items of
positive table value within the weight that is left, with total excess at most 2. Program: the referee's
`programs/knapsack/knap16.py` (mode `map`, with positivity), written for this check and sharing no code
with the map's programs. Its log `programs/knapsack/knap16_map.log` has the lines

    profiles (piece level): 131436  by first statement: {'K': 248, ..., 'T1': 24789, 'T4': 45877, 'T5': 43213, ...}
    UNREMOVED: 0
    shapes: 20  with unremoved profiles: []

and it writes the shapes with their counts to `programs/knapsack/knap16_map.shapes.txt`. Every profile is removed whole: the
statement applies to all its pieces, and no sub-multiset (Lemma SUB of the map, section 2) is needed. The least
slack in V and in W of every statement is 0, so no V or W can be raised or lowered.

The 20 shapes, with V = 40 + sum dv, W = 96 - sum dw and B = the number of borrowing items (Lemma PIECE16), the
number of piece profiles and the statement that removes them:

| shape | V | W | B | profiles | statement |
|---|---|---|---|---|---|
| K | 40 | 96 | 0 | 248 | K |
| K+E | 50 | 84 | 0 | 12,686 | T1 |
| K+AB | 51 | 83 | 1 | 9,673 | T1 |
| K+F | 55 | 78 | 0 | 1,561 | T1 |
| K+A' | 56 | 77 | 1 | 869 | T1 |
| K+R | 46 | 89 | 1 | 4,605 | T2 |
| K+R+R | 52 | 82 | 2 | 9,597 | T3 |
| K+E+R | 56 | 77 | 1 | 28,989 | T4 |
| K+AB+R | 57 | 76 | 2 | 16,680 | T4 |
| K+F+R | 61 | 71 | 1 | 185 | T4 |
| K+A'+R | 62 | 70 | 2 | 23 | T4 |
| K+E+E | 60 | 72 | 0 | 19,210 | T5 |
| K+AB+E | 61 | 71 | 1 | 19,546 | T5 |
| K+AB+AB | 62 | 70 | 2 | 4,457 | T5 |
| K+R+R+R | 58 | 75 | 3 | 1,056 | T6 |
| K+E+R+R | 62 | 70 | 2 | 1,418 | T7 |
| K+AB+R+R | 63 | 69 | 3 | 330 | T7 |
| K+E+E+R | 66 | 65 | 1 | 263 | T8 |
| K+AB+E+R | 67 | 64 | 2 | 39 | T8 |
| K+R+R+R+R | 64 | 68 | 4 | 1 | T9 |

The sum is 131,436. By statement: K 248, T1 24,789, T2 4,605, T3 9,597, T4 45,877, T5 43,213, T6 1,056, T7
1,748, T8 302, T9 1. The largest numbers of links of the sequence pieces, sorted, among the profiles of each
statement: K 10; T1 7 and 3; T2 7; T3 5; T4 4 and 2; T5 3, 1 and 1; T6 2; T7 1 and 0; T8 0, 0 and 0; T9 0. No
shape contains an item A'' or two items of excess 1 from one (cyc) component (E + A').

A second count. The map's `programs/knapsack/acc16.py` counts the same configurations by items, not by pieces (it tells Z from
A_1 and A_q from B_q), on the same table: 299,595 item profiles in 361 item shapes (tier D, `programs/knapsack/acc16_D.log`). The counts that can
be compared agree (ref16 1): K 248; K+E 12,686; K+E+E 19,210; K+F 1,561; K+R 4,605 (times 2 for Z
and A_1: 9,210); K+F+R 185 (370); K+E+E+R 263 (526). Without the positivity of the items the referee's program
finds 189,606 profiles, all removed as well, some of them by a sub-multiset (`programs/knapsack/knap16_map_nopos.log`); positivity
is needed for section 2.7, not for the count.

### 2.9 The statements that the accounting needs

For a statement J(k; V, W; B) of [W] 5.1 write **J^7(k; V, W; B)** for the same statement about the objects in
which every ring piece has value at least 7: there are no pieces of the kinds k, every ring among them of value
at least 7, with sum val >= V, sum wt <= W and at most B shared classes. For a kind list without R, J^7 = J.

The accounting needs:

| | statement needed | shapes |
|---|---|---|
| K | Corollary K16: no sequence with weight at most 96 has value at least 40 | K |
| T1 | J(S7 S3; 50, 84; 1) | K+E, K+AB, K+F, K+A' |
| T2 | J^7(S7 R; 46, 89; 1) | K+R |
| T3 | J^7(S5 R R; 52, 82; 2) | K+R+R |
| T4 | J^7(S4 S2 R; 56, 77; 2) | K+E+R, K+AB+R, K+F+R, K+A'+R |
| T5 | J(S3 S1 S1; 60, 72; 2) | K+E+E, K+AB+E, K+AB+AB |
| T6 | J^7(S2 R R R; 58, 75; 3) | K+R+R+R |
| T7 | J^7(S1 S0 R R; 62, 70; 3) | K+E+R+R, K+AB+R+R |
| T8 | J^7(S0 S0 S0 R; 66, 65; 2) | K+E+E+R, K+AB+E+R |
| T9 | J^7(S0 R R R R; 64, 68; 4) | K+R+R+R+R |

Each T of defect 16 is a statement of defect 15 one step further (V - 5, W + 6): S1 -> T1, S2 -> T2, S3 -> T3,
S4 -> T4. T5 to T9 have no statement of defect 15 with the same kinds; they come from the shapes with three
and four extra items that excess 2 and weight 96 make possible.

**Proposition MAP.** If c is a valid configuration with cost at most 136, then the pieces of its profile are a
counterexample to the statement of its shape in this table.

Proof. By KN16 the shape is one of the 20. By Lemma PIECE16 the pieces have sum val >= V, sum wt <= W and at most
B shared classes, with the V, W, B of the shape, and these are at least as strong as those of the statement
(V of the statement <= V of the shape, W >= W, B >= B; read off the two tables). The pieces fit the kinds of
the statement (KN16: the numbers of links, sorted, are at most those of the kinds, and the numbers of rings are
equal). Every ring piece has value at least 7 (section 2.7). For the shape K the profile is the kernel item
alone: its piece is the kernel, or K_0 in case (lin), with val >= 40 and wt <= 96. QED

Two remarks on what is not used.

- The double places (a seam of weight 6, an attachment of cost 3) give the items F and A''. The map reduces them
  to the case eps = 1 of defect 15 (its section 2, Lemma SHIFT (2)). That is not needed: K+F and K+F+R are
  removed by T1 and T4 as they stand, and no profile contains A''.
- The joint statements S1 to S5 of defect 15 are not used. They would remove 5,039 item profiles (the map,
  section 3), all of which T1 to T9 remove as well.

## 3. The kernel alone

### 3.1 The statement

**Theorem K16.** For 0 <= s <= 10 and 0 <= x <= 96 - 6 s, every sequence with exactly s links and x holes has at
most D16_s(x) rows.

**Corollary K16.** No sequence with weight at most 96 has value at least 40.

Proof of the corollary. Let the sequence have s links and x holes, x + 6 s <= 96. If s <= 10 then
rows <= D16_s(x) <= x + 39 + 5 s, so val <= 39. If s >= 11 then val <= D_s(x) - x - 5 s <= 35 (section 1.4). QED

Theorem K16 is the conjunction of the statements K0 to K10 of Table C and of the entries of D below their
levels. Each statement has the form of [W] 4.1,

> F(s; LO, G): every sequence with exactly s links and x holes, LO < x <= G, has at most P_s(x) rows,

for a table P whose rows P_0, ..., P_(s-1) are valid at all holes up to G and whose row P_s is valid at x <= LO.
Here G = 96 - 6 s, LO = LO_s of section 1.4 and P is the table file of section 3.4.

### 3.2 The search rule and Lemma REV

The search rule is that of [W] 4.2 (the plain rule) with the reversal cut of [W] 4.4: Lemma RV, Lemma REV and
the potential phi with integers a > 0, h >= 0 and b, the choice (4.1) of a counterexample pi with the fewest rows
and m + M >= phi_T, Lemma CUT and the rule with the reversal cut. Nothing in them depends on the defect: the
levels go to G = 96 - 6 s instead of 90 - 6 s, and the table is the file of the statement. The completeness
argument is [W] 4.5. Every run of Table C used the reversal cut (`CUT=12` in the programs, as in [W] 7.2), and
K2, K1, K0 add Rule JS (section 3.3).

The potential is free: it changes the tree, not the statement. The potentials used:

| | K10 to K5 | K4 | K3 | K2 | K1 | K0 |
|---|---|---|---|---|---|---|
| a, b, h | 10, 16, 25 | 10, 15, 25 | 10, 15, 30 | 20, 29, 60 | 20, 29, 60 | 17, 24, 5 |

Lemma REV needs a > 0 and h >= 0 and nothing on b; Rule JS needs b >= 0 in addition. The card programs refuse a
potential unless a > 0, b >= a, h >= 0 and 6 (b - a) + 5 a - 2 h >= 0 (note gkjs 2), so every potential
that runs satisfies b >= 0. The potentials of K2, K1, K0 were chosen on the whole tree by sampling
(note krows 3); 20,29,60 against the 10,15,30 of the run book is about 5 times fewer kept prefixes for K2.

The row mask, the gate and the parts are those of [W] 4.5: at a parent no row is placed whose prefix would be
neither a violation nor kept, and a statement is cut at a gate into parts numbered in the order of the search.
A statement holds when every part is present and no part reports a violation.

### 3.3 Rule JS (the junction shift)

A class at the junction of two consecutive rows can be written as the last block of the first row or as the
first block of the second. The two spellings have the same classes, end, rows, holes and links, and the search
of section 3.2 walks both. Rule JS keeps one. It is a canonical form; it changes no table. The text is that of
note krows 2 with the additions of the referee (refjs 5).

For a row (e, l) let q = tau2^(l-1) e be its last entry; its exit is sigma^-1 q.

**Lemma JS1.** For every word q: among the words v with ew(sigma^-1 q, v) = 3 exactly one, j3(q), lies in the
class of tau2 q, and among those with ew(sigma^-1 q, v) = 4 exactly one, j4(q). Moreover
ew(sigma^-1 tau2 q, tau2 j3(q)) = 3, ew(sigma^-1 tau2 q, tau2 j4(q)) = 4, and tau2 j3(q), tau2 j4(q) are not in
the class of tau2 q.

Proof. Write q = q1 q2 q3 q4 q5 q6 m. The exit is m q1 q2 q3 q4 q5 q6 and tau2 q = q2 q3 q4 q5 q6 q1 m. A word
has weight 3 from the exit iff it begins with q3 q4 q5 q6 (it then begins neither with q1 nor with q2, so the
weight is not 1 or 2), and weight 4 iff it begins with q4 q5 q6 (then it begins with none of q1, q2, q3). The
seven words of the class of tau2 q are its rotations, and a rotation is fixed by its first letter. Exactly one
begins with q3, namely j3 = q3 q4 q5 q6 q1 m q2, and it begins with q3 q4 q5 q6; exactly one begins with q4,
namely j4 = q4 q5 q6 q1 m q2 q3, and it begins with q4 q5 q6. The exit of the block of tau2 q is
m q2 q3 q4 q5 q6 q1. tau2 j3 = q4 q5 q6 q1 m q3 q2 begins with the last four letters q4 q5 q6 q1 of that exit,
so the weight is 3 (it begins with q4, hence not with q3, and no longer overlap occurs); tau2 j4 = q5 q6 q1 m q2
q4 q3 begins with its last three letters q5 q6 q1, so the weight is 4 (it begins with q5, hence not with q4). tau2 changes the class, because the six entries of a row lie in six different classes. QED

Lemma JS1 was also checked from the definitions on all words for 5, 6 and 7 symbols (the referee's js1.py), and every
program that applies the rule checks it on the 5,040 words at every start and stops if it fails.

**Lemma JS2 (the shift).** Let R = (e, l) and R' = (e', l') be consecutive rows of a sequence, joined by a link
of weight w in {3, 4}, let q be the last entry of R and let e' = j_w(q) and l' >= 2. Put S = (e, l + 1) and
S' = (tau2 e', l' - 1). Then

- l <= 5, and S is a row whose classes are those of R and the class of tau2 q, which is the class of the first
  block of R'. The classes of S and S' together are those of R and R' together, so they are new to the rest of
  the sequence;
- S has the entry of R; S' has the entries 2 to l' of R', so its last entry and its exit are those of R';
- the link from S to S' has weight w;
- holes: (6 - l) + (6 - l') = (5 - l) + (7 - l').

So replacing R, R' by S, S' gives a sequence with the same classes, the same number of rows and holes, the same
links in the same order, the same first entry and the same last exit. I call a pair R, R' as above a **shiftable
junction**.

Proof. If l = 6 then tau2 q = tau2^6 e = e, so j_w(q) lies in the class of the first block of R, and no other row
of a sequence starts there; hence l <= 5. The class of tau2 q is the class of j_w(q), the first block of R', and
by the pairwise different classes of the sequence it is the class of no other block. So (e, l + 1) has
pairwise different classes, all new except the one taken from R'. S' is a row because l' >= 2. The weight of the
link is Lemma JS1, since the exit of S is sigma^-1 tau2 q and the entry of S' is tau2 j_w(q). The holes are
arithmetic. QED

For l' = 1 there is no shift: R' would vanish and the exit would change (the exit of R' is sigma^-1 j_w(q), that
of S is sigma^-1 tau2 q), so the next link would change. A shifted junction is not shiftable again, but a shift
can make a neighbouring junction shiftable; the measure Psi below handles this.

**Lemma JS3.** After a shift at the rows i, i + 1 of a sequence with T rows, the potential of [W] 4.4 has
phi'_k = phi_k for k != i and phi'_i = phi_i + b.

Proof. The number of rows before every cut is the same. The holes before cut k change only for k = i, by - 1,
because S has one hole less than R and S, S' together have the holes of R, R'. The links and their weights are
the same in the same order, so the terms with h are the same. QED

**Theorem JS.** Let (a, b, h) be the potential of (4.1), with a > 0, h >= 0 and b >= 0. If F(s; LO, G)
fails, there is a counterexample with the fewest rows that starts at 1 2 3 4 5 6 7, satisfies (4.1) and has no
shiftable junction.

Proof. Let X be the set of counterexamples with the fewest rows that start at 1 2 3 4 5 6 7 and satisfy (4.1).
It is finite, and not empty by [W] 4.4. Take pi in X, with rows of l_1, ..., l_T blocks, that maximises
Psi = sum over i of (T - i) l_i. Suppose that the rows i, i + 1 of pi are a shiftable junction and let pi' be pi
after the shift. By Lemma JS2 pi' is a sequence with the rows, holes and links of pi, so it is a counterexample
with the fewest rows at the same level, and it starts at the same word. By Lemma JS3 and b >= 0, m' >= m,
M' >= M and phi'_T = phi_T (i < T), so m' + M' >= phi'_T: pi' satisfies (4.1) and lies in X. And
Psi(pi') = Psi(pi) + (T - i) - (T - i - 1) = Psi(pi) + 1. This contradicts the choice of pi. QED

**Rule JS.** After a row with last entry q, a row that starts at j3(q) behind a link of weight 3, or at j4(q)
behind a link of weight 4, is placed with one block only. With the reversal cut the rule requires b >= 0; with the
plain rule it has no condition on b. It may be applied at any subset of the junctions.

Completeness. Let pi be the counterexample of Theorem JS. Every proper prefix of pi is kept by the plain rule
and by the reversal cut: [W] 4.5 uses only that pi has the fewest rows, starts at 1 2 3 4 5 6 7 and satisfies
(4.1), and Lemma PART and Lemma CUT of [W] 4.4 are applied to parts of pi itself. No row of pi is refused by Rule
JS, because a refused row has at least 2 blocks and is the second row of a shiftable junction. So the search
reaches pi and reports a violation.

Remarks.

- The reversal. Reading a sequence backwards turns a shiftable junction into a shifted one, so the reversal of an
  object without shiftable junction has, in general, shiftable junctions. The proof does not use the reversal of
  the normal object: the choice between pi and its reversal ([W] 4.4) is made first, by (4.1), and the normal
  form is taken inside X afterwards. The opposite normal form (the junction block kept in the second row) would
  need b <= 0, and the referee's brute force sees this (below).
- The parts (refjs 4). The object of Theorem JS passes the plain rule, the reversal cut for the
  potential used and every application of Rule JS. Hence (a) the rule may be applied at any subset of the
  junctions; (b) all parts of one statement must come from one walk above the gate: the same tables, LO,
  potential, CUT, gate depth and number of parts, and the rule either on or off above the gate in all of them;
  (c) below the gate the rule may be on in some parts and off in others; (d) the potential may never differ
  between parts. `gkjs` applies the rule above the gate in the host and below it on the card, in every part, and
  its part runner refuses to continue a tag whose parameters differ (note gkjs 2).
- The links. j3(q) is reached only by a link of weight 3 and j4(q) only by one of weight 4, and the shift keeps
  the weight, so the number of links and the terms with h are unchanged. The row mask is a function of the
  prefix and the length; the programs cap the length before they read the mask.

Tests (section 6.4): Lemma JS1 and JS2 on every shiftable pair for 5, 6 and 7 symbols (246,960 pairs for 7); a
brute force at the level of the proof on 5 and 6 symbols, which finds no failure for eight potentials with
b >= 0 and many failures for b < 0 and for the opposite normal form; random statements on 5 and 6 symbols and
113 statements on 7 symbols with a lowered entry, every counterexample found.

### 3.4 The statements and the order in which they depend on each other

| | statement | table | rule | given |
|---|---|---|---|---|
| K10 | F(10; 35, 36) | `table/capD16u_10_k.txt` | reversal, 10,16,25 | D, rows 0 to 9, weight <= 90 |
| K9 | F(9; 35, 42) | `table/capD16u_9_k.txt` | reversal, 10,16,25 | D, rows 0 to 8, weight <= 90 |
| K8 | F(8; 35, 48) | `table/capD16u_8_k.txt` | reversal, 10,16,25 | D, rows 0 to 7, weight <= 90 |
| K7 | F(7; 35, 54) | `table/capD16u_7_k.txt` | reversal, 10,16,25 | D, rows 0 to 6, weight <= 90 |
| K6 | F(6; 37, 60) | `table/capD16u_6_k.txt` | reversal, 10,16,25 | D, rows 0 to 5, weight <= 90 |
| K5 | F(5; 37, 66) | `table/capD16u_5_k.txt` | reversal, 10,16,25 | D, rows 0 to 4, weight <= 90 |
| K4 | F(4; 41, 72) | `table/capD16_k.txt` | reversal, 10,15,25 | D16 rows 0 to 3; D_4 at x <= 41 |
| K3 | F(3; 48, 78) | `table/capD16_k.txt` | reversal, 10,15,30 | D16 rows 0 to 2; D_3 at x <= 48 |
| K2 | F(2; 51, 84) | `table/capD16_k.txt` | reversal + JS, 20,29,60 | D16 rows 0, 1; D_2 at x <= 51 |
| K1 | F(1; 55, 90) | `table/capD16_k.txt` | reversal + JS, 20,29,60 | D16 row 0; D_1 at x <= 55 |
| K0 | F(0; 65, 96) | `table/capD16_k.txt` | reversal + JS, 17,24,5 | D_0 at x <= 65 |

The files of K3 to K7 and K10 are printed in the parameter files of their parts, and those of K2, K1 and K0 in
the parameter files of their `gkjs` tags (`audit/partaudit.txt` prints all of them; for K7 and K10 see also
`audit/records/`). For K8 and K9 the stored headers (`audit/records/cpu_K8_k.txt`, `cpu_K9_k.txt`) do not name
the table; the scripts name the `u` files (note gpu2 0.A, and the rate script of gpu2/k).

Proof of Theorem K16 from the statements.

- s = 5 to 10. The run reads the rows below s from D. A part with u < s links of a sequence with at most
  96 - 6 s holes has weight at most 96 - 6 s + 6 u <= 90, so only entries of D within weight 90 are read. The
  rows 0 to 8 of them are valid by Theorem K of defect 15 (section 1.2); the row 9, which K10 reads, is a
  closure entry and rests on Lemma CL (in Lean as `K16.cl16_of`, section 0.4). The row s is D below LO_s, and the run proves it
  above. For s = 9 and 10 the entries of D below LO_s (x <= 35, weight up to 95) are closure entries as well, so
  they rest on Lemma CL, not on Theorem K of defect 15, which has s <= 8. So K5 to K10 do not depend on each
  other or on K0 to K4.
- s = 0. Below LO_0 = 65 the row D16_0 is D_0 = T_0, valid by set B, I1 and I2. K0 gives the levels 66 to 96.
- s = 1 to 4. Below LO_s the row D16_s is D_s, valid. Above LO_s it is given by K_s, which reads the rows
  D16_0, ..., D16_(s-1). So K1 needs K0; K2 needs K0 and K1; K3 needs K0, K1 and K2; K4 needs K0 to K3. A part of
  a sequence with at most 96 - 6 s holes has at most that many holes, so the proof of K_s needs the earlier rows
  only up to 96 - 6 s holes.

So K3 and K4 have run, but they are proved as statements only together with K0, K1 and K2: a run of K_s that
finds no violation says nothing if an earlier row is wrong. When K0, K1 and K2 end without violation, K3 and K4
become proved with them, and Theorem K16 holds. QED

## 4. The joint statements

### 4.1 Statements, classes of objects and Lemma L1

The statement J(k; V, W; B) and the shared classes are those of [W] 5.1: there are no pieces p_1, ..., p_n of the
kinds k_1, ..., k_n with sum val >= V, sum wt <= W and at most B shared classes. A counterexample is such a list
of pieces (an **object**); a minimal one has the fewest rows in all. The statement does not depend on the order
in which the kinds are listed: a counterexample for k is one for every permutation of k, with the same rows
(note jrev 0). So every run may list the kinds in the order that suits it.

A **class** of objects is given by one condition on the rows and the holes of a ring, imposed on every ring
piece of the object. The classes used are: every ring has value at least 7 (the statements J^7 of section 2.9);
every ring has value at least 0 (section 4.2); every ring has its number of holes in a window RLO..RHI, or at
least 8 holes (`RLO=8`); every ring has value at least a, or at most a - 1 (section 4.6); and intersections of
these. J restricted to a class C says that no object of C is a counterexample.

**Lemma L1.** A class C of this kind is closed under renaming the symbols, rotating a ring piece, replacing a
sequence piece by a part of it, reading every piece backwards (O -> O^inv of section 4.3) and exchanging two
pieces of the same kind. So if J restricted to C fails, it has a counterexample in C with the fewest rows among
the counterexamples in C, and every normal form of sections 4.2 to 4.5 that is reached from it by these steps
lies in C as well. Two classes may therefore be searched with different rules, and the gate parts of one class
may not (section 4.7).

Proof. None of the steps changes the multiset of the pairs (rows, holes) of the ring pieces: a rotation and
rho (Lemma JRV (b)) keep the rows and the holes of a ring, the other steps do not touch a ring or only move it
to another position, and the condition is the same for every ring. QED

(ref16b L1.) The minimality is taken inside C: steps 2 and 3 of [W] 5.4 replace a sequence piece by a
proper part of it, which gives a counterexample in C with fewer rows.

### 4.2 The base search, the rotation of a ring and the cut at a ring with negative need

Every joint program runs the search of [W] 5.4 (start at 1 2 3 4 5 6 7, record, rest, table bound, ring piece in
the rotation of the cycle lemma, later pieces at every word with shared classes up to B), with table D or one of
the tables of section 1, and with the window of ring holes of the run. Two sentences have to be added to [W] 5.4.

The rotation of a ring (ref16 M3). Every ring piece of the chosen counterexample is listed in a
rotation that satisfies the cycle lemma for its own rows and holes (T, H). Such a rotation passes the ring rule
in every position, because (T, H) itself is a target: H <= left, T <= TR(H) (validity of the table),
T - H + Best_(i+1)(left - H) >= need (the later pieces of the counterexample have values at most Best of their
weight), r < T and d T <= r H for every proper prefix, and T - r <= D_0(H - d) (the rest of the ring is a chain).
A ring may also be kept in other rotations, through other targets, and how many depends on the position: on 5
symbols the referee found 48 objects that the search lists in one order of two rings and not in the other
(ref16 3.4). That does not matter, because completeness needs one listing of one counterexample. So
the cycle-lemma rotation is a property of the ring alone, and the exchanges of ORD and ORDS below may move a ring
with its rotation.

The cut at a ring with negative need (ref16 M1, ref16b F1). In the programs (`getkeep` in
`programs/jr/jr.c` and `programs/gj2/jr5.c`, the keep tables of `programs/gj2/gj2.c` and `programs/gj3/gj3.c`) the value still needed at a ring piece is
replaced by 0 when it is negative, so a target needs T - H + Best >= max(need, 0). The rule of [W] 5.4 compares
with the true need. So a run that finds 0 proves J for the objects in which every ring piece that is entered
with a negative value needed has T - H + Best >= 0 (piece 1 included if V < 0, which no run has).

This class contains every object whose ring pieces all have value at least 0. Proof: the counterexample's later
pieces fit into the weight left, so Best_(i+1) of that weight is at least the table value of putting every later
sequence piece at weight 0 (a chain of full rows, value at least 1) and every later ring at the least number of
holes the run allows (0 holes: value 5; 8 holes with `RLO=8`: value 16 - 8 = 8), which is at least 0. Best is a
maximum over total weight at most w (the Best of no piece is 0 at every weight), so a placement of smaller
weight counts. With `RLO=8`, Best of a later ring is minus infinity below 8 holes of weight left; this does not
matter, because each later ring of a counterexample of the class has at least 8 holes. Hence T - H + Best >= 0
when T - H >= 0. With the exact ring row the cut is sharper than with the old one, because a ring
of negative value is no longer kept by targets that do not exist (F1); this changes no run, because in every run
the rings either are piece 1 with need V > 0, or have positive need (section 4.6, L2), or are only needed with
value at least 7.

### 4.3 Lemma JRV and Rule PREV (the reversal cut on one sequence piece)

Let rho be the involution of Lemma RV ([W] 4.3). For a piece p with rows R_1, ..., R_T let p^rho be the rows
R_T, ..., R_1, each row (e, l) replaced by (rho(tau2^(l-1) e), l).

**Lemma JRV.** (a) If p is a sequence with s links, p^rho is a sequence with the same rows, the same holes row by
row in reverse order and the same link weights in reverse order. (b) If p is a ring, p^rho is a ring with the
same rows and holes. (c) rho maps classes onto classes bijectively, so if the same rho is applied to all pieces,
the number of pieces that contain a class is kept class by class, and the number of shared classes is equal.
Hence O^inv = (p_1^rho, ..., p_n^rho), with the kind list kept, is an object with the same values, weights,
shared classes and rows as O, and a counterexample with the fewest rows goes to one.

Proof. (a) is Corollary RV of [W] 4.3. (b) p^rho is a chain by (a), and the closing link of weight 3 from the
last row of p to its first becomes, by Lemma RV (4), a link of weight 3 from the last row of p^rho to its first.
(c) is Lemma RV (1). Reversing only some of the pieces is not allowed: rho moves the classes, and the shared
classes would change. QED

Fix one sequence piece p_r (the program's `RP`, counted from 0) and integers a > 0, b, h >= 0 with
XL = 6 (b - a) + 5 a - 2 h >= 0. Let phi^r be the potential of [W] 4.4 along p_r alone (its cuts 0 to T_r; the
last carries no link), Phi_r its final value, m and M its least and largest value, and
delta_r(O) = m + M - Phi_r.

**Lemma PREV.** delta_r(O^inv) = - delta_r(O). So if J fails (in a class of section 4.1), there is a
counterexample with the fewest rows (in the class), listed in the same order of kinds, with delta_r >= 0.

Proof. p_r^rho is p_r read backwards, so Lemma REV of [W] 4.4 for the single sequence p_r gives the first claim.
O^inv is a counterexample with the same rows (Lemma JRV), and it lies in the class (Lemma L1). QED

The rule. At a cut j inside piece r let `need` be V less the value of everything placed so far (the earlier pieces
and the rows of p_r up to j, its links counted), `om` W less its weight, tl the number of links that p_r may
still take, f = a i - b d - 2 h t for the i rows, d holes and t links of p_r so far, and m_j, M_j the least and
the largest value of phi^r at the cuts of p_r up to j (cut 0 included, so m_j <= 0; phi at j depends on the link
that follows, as in [W] 4.4). Let Best_(r+1)(w) be the table bound of [W] 5.4 for the pieces after r within
weight w, and

    SEG(tl, w)        = max { a D_u(e) - b e - 2 h u : u <= tl, e + 6 u <= w },
    c(need, om; w)    = a (need - Best_(r+1)(om - w)) - (b - a) w,
    CN1(need, om)     = min over 0 <= w <= om of c(need, om; w),
    A2P(tl, need, om) = min over 0 <= w <= om of ( c(need, om; w) - SEG(tl, w) ).

- (L) A prefix is continued by links of weight 3 only if m_j >= 0, or M_j + m_j - f >= CN1(need, om), or
  m_j >= A2P(tl, need, om).
- (H) It is continued by links of weight 4 only if m_j >= 0, or M_j + m_j - f >= CN1(need + 5, om - 6) - 2 h, or
  m_j >= A2P(tl - 1, need + 5, om - 6). Here phi_j = f - h.
- (T1) A completed piece p_r is followed only if delta_r >= 0, computed exactly. The other pieces have no new
  rule.

Proof of (L). Let O be the counterexample of Lemma PREV and let the rest of p_r after the cut have R rows, E holes
and u links, w = E + 6 u <= om. The later pieces have weight at most om - w and value at most Best_(r+1)(om - w),
so R - E - 5 u >= need - Best_(r+1)(om - w), and

    Phi_r - f = a R - b E - 2 h u = a (R - E - 5 u) - (b - a) w + XL u >= c(need, om; w),

using a > 0 and XL >= 0. Let j* be a cut of p_r with phi^r = M. From delta_r >= 0 and m <= m_j:
M >= Phi_r - m_j. If j* <= j then M = M_j and M_j + m_j - f >= Phi_r - f >= CN1. If j* > j, the rows j + 1 to
j* of p_r are a contiguous part of the rest, a sequence with u' <= tl links and e holes, e + 6 u' <= w, so
M - f <= a D_u'(e) - b e - 2 h u' <= SEG(tl, w) (the link terms at its two ends are at most 0; D is valid for all
sequences). Hence m_j >= Phi_r - M >= c(need, om; w) - SEG(tl, w) >= A2P. The clause m_j >= 0 only keeps more.
(H) is the same with one more link: the rest has R - E - 5 (u + 1) >= need - Best(om - 6 - w), weight
w <= om - 6, Phi_r - f >= c(need + 5, om - 6; w) - 2 h, and M - f <= - 2 h + SEG(tl - 1, w). QED

So a search that applies (L), (H) and (T1) on top of [W] 5.4 reaches the counterexample of Lemma PREV and finds
it. The referee recomputed the rules and read the code (`rev_light`, `rev_heavy`, `CN1t`, `A2Pt`, the exact test
at the end of piece RP), also for RP > 0 (ref16 3.1).

What PREV cannot do: the freedom is one bit (O or O^inv), so only one antisymmetric quantity can be made at least
0, and PREV acts on one piece. The rule JREV of note jrev 2 (a potential along all pieces, the order of the
kinds reversed) is not used in any run, and it cannot be combined with PREV or ORD.

### 4.4 Rule ORD (pieces of equal kind sorted by value)

If two neighbouring pieces p_(i-1), p_i have the same kind (the same S<s>), exchanging them gives a counterexample
with the same rows. So a counterexample with the fewest rows may be listed with val(p_(i-1)) >= val(p_i) for all
such neighbours. The search uses this in two prunings: with two pieces of equal kind, a prefix of piece 1 is kept
only if its value plus the table bound of the rest of this piece alone is at least ceil(V / 2); with more
pieces, if k_(i+1) = k_i and piece i is complete with value v, the jump to piece i + 1 is made only if
2 v + Best_(i+2)(weight left) is at least the value still needed before piece i.

Compatibility. The record and rest rules hold for every minimal counterexample, and sorting keeps it minimal.
With PREV: first sort, then choose O or O^inv; O^inv has the same values piece by piece, so it stays sorted. In a
class of section 4.1 the exchange keeps the class (Lemma L1); a ring is not moved by ORD. (note jrev 7,
ref16 3.2.)

### 4.5 Rule ORDS (rings sorted by start vertex)

ORDS is a rule that was used for faster runs. No counted run of Table C uses it: the counted runs of T6' and T9'
are the plain-rule ones (T6rp with PREV only, T9r), and the ORDS runs (T6r, T9rs, T9s) are extra lines of Table C
that are not counted. The lemma below is the argument that those runs rely on.

Fix a total order of the vertices (the numbering of the card: orbit of the row rotation, then position).

**Lemma ORDS.** If J fails (in a class of section 4.1), it has a counterexample that satisfies every rule of
sections 4.2 to 4.4 used in the run and in addition: for neighbouring pieces i - 1, i that are both rings and both
behind piece 1, start(p_i) >= start(p_(i-1)), where start is the first vertex of the ring as it is listed.

Proof. Take the counterexample O as the earlier rules choose it (fewest rows in the class, delta_r >= 0, runs of
equal sequence kinds sorted by value). Let i - 1, i >= 2 be neighbouring rings with start(p_i) < start(p_(i-1))
and exchange them. The kinds are equal, so the result is a counterexample for the same kind list with the same
rows, and it lies in the class (Lemma L1). Nothing the search relies on changes: piece 1 is not moved, so the
renaming and every start vertex stay; the record rules concern sequence pieces; each ring keeps the rotation of
the cycle lemma for its own (T, H), which passes the ring rule in every position (section 4.2); the tables are
true statements about kinds; the later pieces start at every vertex and the number of shared classes is
symmetric; delta_r depends on the sequence piece r alone, which is not moved; the value order of the sequence
runs is not touched. The keep rules that depend on the position (value needed, weight left, Best of the later
pieces) are necessary for every counterexample listed in the order of the kinds, so also for the new listing.
Finitely many exchanges sort every run of rings behind piece 1. Two rings that begin at the same vertex are
allowed by ">=". QED

Piece 1 is left out because its start is fixed by the renaming. A run has one sort key: with ORDS the value order
is applied to runs of sequence pieces only. In the search, the start frame of such a ring runs over the start
vertices from the start of the ring before it. (note gpu2 5 with ref16 M3.)

### 4.6 Windows of ring holes and the split VS

Windows. A run with `RLO`, `RHI` searches the objects whose ring pieces have a number of holes in the window,
and reads the ring row only inside it ([W] 5.5). This is a class of section 4.1. `RLO=8` with no RHI is the class
"every ring has at least 8 holes".

**Lemma VS.** Let J be a joint statement with one ring piece, a window RLO..RHI and an integer a. Let J[>= a] be J
for rings in the window with rows - holes >= a, and J[< a] be J for rings in the window with rows - holes <= a - 1.
J for the window holds iff both hold, since every ring is in exactly one of the two classes.

- (hi) The search of [W] 5.4 with one more condition on the ring, "a target (T, H) has T - H >= a", and a
  completed ring taken only if rows - holes >= a, finds an object if J[>= a] fails.
- (lo) The search of [W] 5.4 with the ring row replaced by min(TR(H), H + a - 1) on the window finds an object if
  J[< a] fails.

Proof. (hi): take a counterexample of J[>= a] with the fewest rows in the class; by Lemma L1 its normal form,
with PREV, lies in the class. Its ring, in the rotation of the cycle lemma, is its own target (section 4.2), and
T - H >= a. All other conditions are those of [W] 5.4 and section 4.3.
(lo): the same, and the ring row enters the search only as a bound on the rows of a whole ring piece: the row
itself in the ring rule, Best of a ring piece, and the highest target of the keep table. The rest of a ring is
bounded by the chain row, and no sequence piece is bounded by the ring row. This was read in the CPU source
(`programs/jr/jr.c`), in the card host (note tune 4: `programs/gj2/jr_core.h` lines 92, 102, 158, 206 and
`programs/gj2/gj2.c` line 222; line 158 is the table of JREV, which no run uses) and again by the referee in
`programs/gj3/jr_core.h` (the same places are its lines 93, 103, 159, 208) and `gj3.c` (ref16b 1). The ring of a counterexample of J[< a] obeys the lowered row. The programs do not
test a completed ring against its row, so a lower half may also find objects outside its class; that does not
hurt "found 0". QED

**Lemma L2** (ref16b L2). In the three lower halves the value needed at the ring is positive, so the
cut of section 4.2 does not act and each lower half is proved for every ring of its class. The kernel is piece 1
and the ring has at least RLO holes, so the kernel has weight at most 89 - RLO, and its table value there is at
most 37, 36, 31 for RLO = 32, 40, 48; with V = 46 the value needed at the ring is at least 9, 10, 15.

The two halves of a window are searched with different rules (ring first with PREV on the kernel behind it; kernel
first with PREV on the kernel and another potential). This is what M5 of ref16 forbids for gate parts,
and it is sound here because each class is closed under the normalisations (Lemma L1), so each class has its own
counterexample with the fewest rows and delta_r >= 0. Gate parts are not classes of this kind.

The windows and halves of T2 used: 8..15, 16..23, 24..31 and 56..89 whole; 32..39 split at a = 17, 40..47 at
a = 20, 48..55 at a = 23. Together they cover every ring with 8 to 89 holes exactly once.

In `gj3` and `jr6` the switch `RVMIN` acts on every ring piece. That is right for T2, which has one ring;
for several rings it would prove "every ring has value >= a", not the upper class of a split
(ref16b 4.1).

### 4.7 The runs: which rules, and what each run proves

PREV is on the piece named (pieces counted from 1 here; the programs' `RP` counts from 0); the potential is a, b,
h. Every run reads table D except where the table column says otherwise.

| run | kinds as run | V, W, B | class searched | rules | table |
|---|---|---|---|---|---|
| T1 | S7 S7 | 50, 84, 1 | (no ring) | ORD; PREV on piece 1, 10,15,25 | D |
| T2 8..15, 16..23, 24..31, 56..89 | R S7 | 46, 89, 1 | ring holes in the window | PREV on piece 2, 10,15,40 | D |
| T2 32..39, 40..47, 48..55, upper | R S7 | 46, 89, 1 | window; value >= 17, 20, 23 | VS (hi); PREV on piece 2, 10,15,40 | `table/capD_r.txt` (RX) |
| T2 32..39, 40..47, 48..55, lower | S7 R | 46, 89, 1 | window; value <= 16, 19, 22 | VS (lo); PREV on piece 1, 10,15,30 | lowered rows of 1.5 |
| T3' | R S5 R | 52, 82, 2 | every ring >= 8 holes | PREV on piece 2, 10,16,43 | D |
| T4' | R S4 S4 | 56, 77, 2 | every ring >= 8 holes | ORD on pieces 2, 3; PREV on piece 2, 10,16,43 | D |
| T5 | S3 S3 S3 | 60, 72, 2 | (no ring) | plain | D |
| T6' | S2 R R R | 58, 75, 3 | every ring >= 8 holes | PREV on piece 1, 10,16,25 | D |
| T7 | S1 S1 R R | 62, 70, 3 | all | plain | D |
| T8 | S0 S0 S0 R | 66, 65, 2 | all | plain | D |
| T9' | S0 R R R R | 64, 68, 4 | every ring >= 8 holes | plain | D |

Every potential satisfies a > 0, b >= a, h >= 0 and XL >= 0 (10,15,40 and 10,16,43 give XL = 0). The combinations
used are those the referees allowed (ref16 3.3): PREV with ORD, gates and parts by start vertex with
either, windows and VS with either. The extra runs that are not counted add ORDS on pieces 2 to 4 (T6r) and
on pieces 2 to 5 (T9rs, T9s), also with PREV on piece 1 for T6r. Not used: two sort keys on one run, PREV on two
pieces, JREV.

What each run proves. By sections 4.2 to 4.6 a run with found 0 proves its statement for every object of the
class searched whose rings all have value at least 0 (the cut of section 4.2). If the only ring is piece 1 and
V > 0, or in a lower half (Lemma L2), the cut does not act, and the run proves the statement for every object of
the class. From this:

- T1: J(S7 S7; 50, 84; 1), which implies J(S7 S3; 50, 84; 1) because S7 means "at most 7 links".
- T2: the ten runs cover every ring with 8 to 89 holes; a ring piece of T2 has weight at most 89, and a ring of
  value at least 7 has at least 8 holes (section 2.7). In the windows and the upper halves the ring is piece 1
  with need 46 > 0, and in the lower halves Lemma L2 applies. So J^7(S7 R; 46, 89; 1) holds (and even J for every
  ring with at least 8 holes).
- T3': J for the objects with kinds R S5 R whose rings have at least 8 holes and value at least 0. This contains
  J^7(S5 R R; 52, 82; 2).
- T4': J for R S4 S4 with the ring of at least 8 holes (it is piece 1, need 56 > 0). This contains
  J^7(S4 S2 R; 56, 77; 2).
- T5: J(S3 S3 S3; 60, 72; 2), which implies J(S3 S1 S1; 60, 72; 2).
- T6': J for S2 R R R with every ring of at least 8 holes and value at least 0; contains J^7(S2 R R R; 58, 75; 3).
- T7: J for S1 S1 R R with every ring of value at least 0; contains J^7(S1 S0 R R; 62, 70; 3).
- T8: J for every ring of value at least 0; contains J^7(S0 S0 S0 R; 66, 65; 2).
- T9': J for S0 R R R R with every ring of at least 8 holes and value at least 0; contains
  J^7(S0 R R R R; 64, 68; 4).

Parts (ref16 M5). A run in parts is cut at a gate of DEPTH rows of piece 1 (index modulo NPARTS)
and by the start vertices of piece 2 (modulo NPARTS2). Parts made with different rule sets do not add up to a
proof: each rule set keeps its own counterexample, which may lie in a part searched with the other set. So every
part of a statement must have the same statement line (kinds, V, W, B, window, RVMIN, PREV piece, potential,
ORD, ORDS, table) but for the part numbers. This was checked for every tag (section 6.3).

### 4.8 The restricted statements T3', T4', T6', T9' and why they suffice

T3', T4', T6' and T9' are proved for rings with at least 8 holes only (`RLO=8`). This suffices because the
accounting needs J^7 (section 2.9): every ring piece of a profile has value at least 7 and hence at least 8 holes
(section 2.7). The same holds for T2, which was always run from 8 holes on (ref16 M2), and the runs of
T7 and T8 contain J^7 by the cut of section 4.2.

What is not proved: T3, T4 and T6 as statements about all pieces. Their case "one ring with at most 7 holes"
does not follow from the other statements: drop the small ring (value at most 5) and S5 + R is left with
val >= 47, wt <= 82 and up to 2 shared classes, where T2 has B = 1; S4 + S4 is left with 51, 77 and B = 2, where T1
has B = 1; S2 + R + R is left with 53, 75 and B = 3, where T3 has B = 2. Only "every ring small" follows from
Corollary K16 (ref16b 2.3). So T3, T4, T6 must not be cited under those names, and a later use of these
statements (a joint table at a higher defect, a Lean statement `KS.J` about all pieces) needs the restriction
written into it.

## 5. Conclusion

**Theorem.** Given Theorem K16 (the statements K0 to K10 of Table C) and the joint runs of Table C, statement
(*) holds: no valid configuration on 7 symbols has cost at most 136. Hence, by (L1), a superpermutation on 7
symbols has at least 5,901 letters.

Proof. Let c be valid with cost at most 136. By Proposition PROF16 it gives a piece profile, together with its
pieces. By KN16 its shape is one of 20, and by Proposition MAP its pieces are a counterexample to the statement
of its shape in section 2.9.

*Shape K.* The kernel piece has val >= 40 and wt <= 96. This contradicts Corollary K16.

*The other 19 shapes.* The statement is one of T1 to T9 in the form of section 2.9 (J for T1 and T5, J^7 for the
others). By section 4.7 the runs of Table C prove each of them: T1 and T5 as they stand, T2 for every ring with
at least 8 holes, T3', T4', T6', T9' for rings with at least 8 holes and value at least 0, T7 and T8 for rings
of value at least 0, and every ring of a profile has value at least 7 and at least 8 holes (section 2.7).
Contradiction.

So every one of the 131,436 piece profiles is removed and c does not exist. QED

The argument does not use that the cost is exactly 136, and it does not use the theorem of 5,900 as such, only
the tables, lemmas and computations of [W] named in section 0.1. The model is exact (`no_stdConfig_iff`), so (*)
is equivalent to the bound 5,901 and nothing is lost by the reduction.

Dependencies in one picture:

    (L2) set B, I1, I2, C76, I4, Lemma CL  ->  T, T'          defect-15 K0..K8 (two programs)  ->  D
    set B, I1, I2  ->  RX (three programs)
    D  ->  K5, K6, K7, K8, K9, K10
    set B, I1, I2  ->  K0  ->  K1  ->  K2  ->  K3  ->  K4
    K0..K10  ->  Corollary K16  ->  shape K (248 profiles)
    D  ->  T1, T2 windows, T3', T4', T5, T6', T7, T8, T9
    D, lowered rows  ->  T2 lower halves          RX  ->  T2 upper halves
    D  ->  KN16 (the knapsack)

No joint statement depends on a kernel statement of defect 16: the joint runs read table D, which rests on
defect 15. The kernel statements of defect 16 are needed for the shape K alone, and K3 and K4 rest on K0, K1, K2.

## 6. How to check this

### 6.1 The programs

The sources are in `programs/` of this folder unless the table says otherwise. A program is named by the name of
its binary in my runs (`gj2` for the host `gj2.c` with its kernel `gj2.cu`, and so on).

| | program | sources | remark |
|---|---|---|---|
| K3 to K10 | `gk4` with the kernel file of the runs | host `programs/gk4/gk4.c` with `gk_tables.h`; kernel `programs/gk4/gk5.cu`, built with LEARN, RC and NR = 3 | the kernel-alone search of [W] 4 on the card; the host takes the code that builds the tables from kfast.c, the first kernel program of defect 15 |
| K8, K9 again | `kfast2` (CPU) | the first program of defect 15 (not in this repository) | same lineage as `gk4` |
| K9 with Rule JS | `kfast_js`, `ref7`, `gkjs` | `kfast_js.c` = kfast.c + Rule JS (copied as `programs/gkjs/kref.c`); the referee's ref.c, written from the texts (not in this repository) | three programs, one independent |
| K0, K1, K2 | `gkjs` | `programs/gkjs/gkjs.c`, `gkjs.cu` (`mkgkjs.py` is the complete diff against `gk4.c` and `gk5.cu`); `build.sh`, `build_ptx.bat` | Rule JS above the gate in the host, below it on the card |
| T1, T2 windows and lower halves, T3', T4', T6', T9' (also the repeats of T7, T8) | `gj2` | `programs/gj2/gj2.c`, `gj2.cu`, `jr_core.h` (the rules of `programs/jr/jr.c`) | joint search on the card; ORDS is a switch, used only in runs that are not counted |
| T2 upper halves | `gj3` | `programs/gj3/`: `gj2` + RVMIN (`mkgj3.py`) | without RVMIN the counts of `gj2` |
| T5, T7, T8 | `gj` | `programs/gj/gj.c`, `gj.cu`, `jr_core.h` from `jr.c` (`mkcore.py`) | plain rule, PREV, ORD |
| CPU references of the joint rules | `jr3`, `jr5s`, `jr6` | `programs/jr/jr.c`; `programs/gj2/jr5.c` (5 pieces, ORDS); `programs/jr/jr6.c` (RVMIN, made by `mkjr6.py`) | they share the rule code with the card hosts |
| second program of defect 15 with RVMIN | `j2r` | j2.cpp of defect 15 and a patch script (not in this repository) | used for a = 25 on 48..55 only |
| RX | `j2` in its mode `ringtab`, `ringx`, `ringchk` | j2.cpp of defect 15 (it is `programs/second/j2_np5.cpp` with NPMAX = 4), `programs/rx/ringx.c`, `programs/rx/ringchk.c` | three sources |
| knapsack | `programs/knapsack/knap16.py`; `programs/knapsack/acc16.py` (with `tabs15.py`) | | by pieces; by items |
| second counts K7 to K10 | `k2_s12` | `programs/second/k2_s12.cpp`: k2.cpp of defect 15, written from the texts, with SMAX = 12 in place of 9 | K7: `audit/k7second/run_k7.sh`, `summ_k7.py` |
| second counts T7, T8, T9' | `j2_np5` | `programs/second/j2_np5.cpp`: j2.cpp of defect 15, written from the texts, with NPMAX = 5 in place of 4 | T7: `audit/t7second/run_t7.sh` |
| Lean engines, compiled | `K16.seqSearch`, `J16.jSearch` (`LowerBounds/K16Search.lean`, `J16Search.lean` of the level-1 sources) | counting copies `LowerBounds/K16Count.lean`, `lean/Audit5901/J16Count.lean` | `lean/build.sh`, `ev.sh`, `Eval/*.lean`; theorems `lean/Audit5901/NK.lean`, `NJ.lean`, `NEv.lean`, K7 and K6 in `NK7_*.lean`, `NK6_*.lean` (`nat.sh`, `nat2.sh`, `nk_queue.sh`); logs in `lean/logs/` |

The card programs run one depth-first walk per thread with the rule of the CPU program. The switches of `gj2`
(LEARN, EXH, ORB, ROT, RC, NRS) and of `gk5` (LEARN, RC, NR, FC) change the speed, not the counts; ORDS and JS are
rules and change the counts (note gpu2 4.1, 6; note gkjs 2).

### 6.2 The commands

The lines below are the commands of the runs as they were recorded. They ran in my working tree, where every
script changes into its own folder: gpu2/k for `gk4`, gkjs, gpu2 for `gj2`, tune/gj3 for `gj3` and gpuj for
`gj`. On another machine the `cd` lines of the scripts in `programs/` need those paths adapted. The table files
are in `table/`: `../jrev/capD.txt` is `table/capD.txt`, `caps/*_k.txt` are `table/*_k.txt`, and
`../tune/caps/lo_*.txt` and `../ringcap/capD_r*.txt` are the files of the same names in `table/`.

THREADS is not needed on the card. Parts that are present are skipped, so a line can be repeated after a stop.
`MAXSEC` ends a part without a file after that many seconds; a part that hits it is redone finer under a new tag.

Kernel alone, in gpu2/k (arguments: tag, S, LO, parts, gate depth, potential a b h, table):

    ./kparts.sh K6 6 37 16 10 10 16 25 caps/capD16u_6_k.txt     ;  ./ksumm.sh K6 16
    ./kparts.sh K5 5 37 64 12 10 16 25 caps/capD16u_5_k.txt     ;  ./ksumm.sh K5 64
    ./kparts.sh K4 4 41 64 12 10 15 25 caps/capD16_k.txt        ;  ./ksumm.sh K4 64
    ./kparts.sh K3 3 48 256 13 10 15 30 caps/capD16_k.txt       ;  ./ksumm.sh K3 256

K7 and K10 are single parts without a gate (stored as `audit/records/K7_p0.txt` and `K10_p0.txt`, with
`K7_params.txt` and `K10_params.txt` naming `caps/capD16u_7_k.txt` and `caps/capD16u_10_k.txt`, LO 35,
potential 10,16,25); K8 and K9 were single runs. The syntax is that of [W] 7.2 and note gpu, for example
`LO=35 CUT=12 POTA=10 POTB=16 POTH=25 ./run/gk4.exe run 7 96 caps/capD16u_7_k.txt`; the same line with
`kfast2` and S = 8, 9 gives the CPU counts. Rule JS, in gkjs:

    MAXSEC=200000 JS=1 ./kparts.sh K2js 2 51 512 13 20 29 60 caps/capD16_k.txt   ;  ./ksumm.sh K2js 512
    MAXSEC=200000 JS=1 ./kparts.sh K1js 1 55 2048 14 20 29 60 caps/capD16_k.txt  ;  ./ksumm.sh K1js 2048
    MAXSEC=200000 JS=1 ./kparts.sh K0js 0 65 4096 16 17 24 5 caps/capD16_k.txt   ;  ./ksumm.sh K0js 4096
    ./m5check.sh K2js        (and K1js, K0js)

Joint, in gpu2, `D=../jrev/capD.txt` (arguments of `gj2parts.sh`: tag, parts of the gate, gate depth, parts by
start vertex of piece 2, table, V, W, B, pieces; `gj2summ.sh`: tag and the two numbers of parts):

    MAXSEC=7200 ORD=1 REV=1 RMODE=2 RP=0 PB=15 PH=25 ./gj2parts.sh T1 1024 16 1 $D 50 84 1 S7 S7          # T1
    RLO=8 RHI=15 REV=1 RMODE=2 RP=1 PB=15 PH=40 ./gj2parts.sh T2_08 1 0 64 $D 46 89 1 R S7                # T2 8..15
    RLO=16 RHI=23 REV=1 RMODE=2 RP=1 PB=15 PH=40 ./gj2parts.sh T2_16 1 0 64 $D 46 89 1 R S7               # 16..23
    RLO=24 RHI=31 REV=1 RMODE=2 RP=1 PB=15 PH=40 ./gj2parts.sh T2_24 64 18 1 $D 46 89 1 R S7              # 24..31
    RLO=56 RHI=89 REV=1 RMODE=2 RP=1 PB=15 PH=40 ./gj2parts.sh T2_56 64 18 1 $D 46 89 1 R S7              # 56..89
    RLO=32 RHI=39 REV=1 RMODE=2 RP=0 PB=15 PH=30 ./gj2parts.sh T2_32_lo17 16 12 1 ../tune/caps/lo_32_39_a17.txt 46 89 1 S7 R
    RLO=40 RHI=47 REV=1 RMODE=2 RP=0 PB=15 PH=30 ./gj2parts.sh T2_40_lo20 16 12 1 ../tune/caps/lo_40_47_a20.txt 46 89 1 S7 R
    RLO=48 RHI=55 REV=1 RMODE=2 RP=0 PB=15 PH=30 ./gj2parts.sh T2_48_lo23 64 12 1 ../ringcap/capD_r_rv22.txt 46 89 1 S7 R
    RLO=8 REV=1 RMODE=2 RP=1 PB=16 PH=43 ./gj2parts.sh T3r 64 10 1 $D 52 82 2 R S5 R                      # T3'
    RLO=8 ORD=1 REV=1 RMODE=2 RP=1 PB=16 PH=43 ./gj2parts.sh T4r 64 10 1 $D 56 77 2 R S4 S4               # T4'
    RLO=8 REV=1 RMODE=2 RP=0 PB=16 PH=25 ./gj2parts.sh T6rp 16 10 1 $D 58 75 3 S2 R R R                   # T6'
    RLO=8 ./gj2parts.sh T9r 1 0 8 $D 64 68 4 S0 R R R R                                                   # T9'
    ./gj2summ.sh TAG NPARTS NPARTS2 ;  ./m5check.sh TAG       (for every tag above)

The extra runs with ORDS, which are not counted (the same lines with the switch):

    RLO=8 ORDS=1 REV=1 RMODE=2 RP=0 PB=16 PH=25 ./gj2parts.sh T6r 16 10 1 $D 58 75 3 S2 R R R
    RLO=8 ORDS=1 ./gj2parts.sh T9rs 1 0 8 $D 64 68 4 S0 R R R R
    ORDS=1 ./gj2parts.sh T9s 1 0 8 $D 64 68 4 S0 R R R R

Upper halves of VS, in tune/gj3, `R=../../ringcap/capD_r.txt`:

    RVMIN=17 RLO=32 RHI=39 REV=1 RMODE=2 RP=1 PB=15 PH=40 ./gj3parts.sh T2_32_hi17 16 18 1 $R 46 89 1 R S7
    RVMIN=20 RLO=40 RHI=47 REV=1 RMODE=2 RP=1 PB=15 PH=40 ./gj3parts.sh T2_40_hi20 16 18 1 $R 46 89 1 R S7
    RVMIN=23 RLO=48 RHI=55 REV=1 RMODE=2 RP=1 PB=15 PH=40 ./gj3parts.sh T2_48_hi23 64 18 1 $R 46 89 1 R S7
    ./gj3summ.sh TAG NPARTS 1 ;  ./m5check.sh TAG

In gpuj (the first card program of the joint search):

    ./gjparts.sh T5 16 10 1 ../jrev/capD.txt 60 72 2 S3 S3 S3 ;  ./gjsumm.sh T5 16 1                     # T5
    ./gj.exe 7 ../jrev/capD.txt run 62 70 3 S1 S1 R R                                                     # T7
    ./gj.exe 7 ../jrev/capD.txt run 66 65 2 S0 S0 S0 R                                                    # T8

T7 and T8 were repeated by `gj2` as one part each (plain rule, statement line in the first line of the part
file); the counts are those of Table C.

These lines are those recorded in the `command.txt` of every joint tag and the `params.txt` of every kernel tag
(`audit/partaudit.txt` prints them) and in my run book; the `MAXSEC` of a tag is not recorded. The ORDS switch is
not written into `command.txt` by `gj2parts.sh`; it is printed in the first line of every part file
(section 6.3).

The second counts. K10, K9, K8 by `k2_s12` and T9', T8 by `j2_np5` are single runs; their outputs are in
`audit/second/`, and the first line of each output prints the statement. K7 by `k2_s12` in 64 parts:
`audit/k7second/run_k7.sh 2`, then `summ_k7.py`. T7 by `j2_np5` in 8 parts with the gate on piece 2:
`audit/t7second/run_t7.sh 2`; the kept count is the count above the gate (printed in every part, counted once)
plus the sum of the part counts, and the same for tried. Both scripts call the binaries by their paths in my
working tree.

The exact ring row: `j2 ringtab capD_r.txt 0 63 0 1 0 -` and `ringx prove capD_r.txt 0 63`, both on
`table/capD_r.txt`. The knapsack: `python programs/knapsack/knap16.py map`. It reads `capD.txt` and the Lean
table file `KTables.lean` from paths of my research tree (the first lines of the script) and writes its shape
file there, so on another machine it is run from a copy with the paths adapted.

### 6.3 What a result looks like and what to compare

Kernel alone, one line per part (`gkjs`; `gk4` prints the same without `JS=` and `caps=`), and the last line of
`ksumm.sh`:

    gpu run S=2 GTOP=96 (holes <= 84) LO=51 CUT=12 POT=20,29,60 JS=1 caps=12dad743 part 0 of 512 at depth 13:
        violations 0   rows placed 11908085696785   kept 3014120167117   above the gate: rows placed 157331
        kept 55988   prefixes at the gate 101537
    RESULT: no violation, all parts present

Joint, the first lines of a part file (here a part of T6rp) and the last line of `gj2summ.sh`:

    gj K=7 caps=../jrev/capD.txt V=58 W=75 B=3 pieces S2 R R R  NOCUT=0 PART=0/16 DEPTH=10 PART2=0/1 RLO=8
        RHI=128 REV=1 RP=0 potential 10,16,25 ORD=0 ORDS=0 JCAP=-  table bound of the total: 65
    piece 1: kept 14893379  rows tried 74665685   (above the gate: kept 3721  rows tried 18721)
    ...
    RESULT: found 0   kept ...   rows tried ...
    RESULT: all parts present, found 0

Compare with Table C: kept prefixes for the kernel statements; kept and tried for the joint statements. With the
same rule, table and potential these are fixed numbers that do not depend on the gate or on the number of parts.
"Rows placed", the gate counts and "nodes judged" depend on the program. A program with another valid rule only
has to find nothing. A line `FOUND: ...` of a joint run would be an object: the statement is false as a statement
about pieces (for a lower half it must first be classed by hand, since a lower half may find objects outside its
class).

The check of M5. For every tag the first lines of all part files must agree but for the part numbers. In my
working tree every tag of `gj2` (T1, T2_08, T2_16, T2_24, T2_32_lo17, T2_40_lo20, T2_48_lo23, T2_56, T3r, T4r,
T6r) and of `gj3` (the three upper halves) has a file `m5.txt` with one distinct line; T9s was checked by the
referee from its part files (ORDS=1 in all, ref16 M5). The tags of 2026-10-16 (T6rp, T9r, T9rs) have one
statement line each, found 0 in all parts; the statement line of T6rp is the one printed above with the part
numbers masked: `gj K=7 caps=../jrev/capD.txt V=58 W=75 B=3 pieces S2 R R R NOCUT=0 PART=*/16 DEPTH=10
PART2=*/1 RLO=8 RHI=128 REV=1 RP=0 potential 10,16,25 ORD=0 ORDS=0`. For T5 I counted 16 part files with one
statement line and 16 lines "found 0" (2026-10-15). T7 and T8 by `gj` are single runs; their log (rate16.log of
gpuj) keeps the result lines and the table (`D=../jrev/capD.txt` in `programs/gj/rate16.sh`) but not the
statement line; their repeats by `gj2` have the statement line. For the kernel tags the part runner refuses to
continue a tag whose `params.txt` differs.

One script also reads all the part files in one pass: `audit/partaudit.py`. I ran it in my working tree, and its
output of 2026-10-20 is `audit/partaudit.txt`. It reads K0, K1, K2 from their packed archives, K3 to K7 and K10
from their part folders, the single runs of K8 and K9 from their stored headers (`audit/records/cpu_K8_k.txt`,
`cpu_K9_k.txt`), and all joint tags (the 18 counted ones and the three ORDS runs); it also compares T1 with its
archive file by file. For each tag it checks:

- every part index is present, and none lies outside the range of `params.txt` or `command.txt`;
- every part has a complete result;
- all parts have one statement line once the part numbers are masked (M5), and that line names the table, V, W,
  B, the kinds, the window and the switches of section 6.2 (ORDS=0 in every counted joint tag);
- the kept counts above the gate are the same in every part;
- no part reports a violation or an object;
- the sums equal Table C.

For K0, K1, K2 it also recomputes from `table/capD16_k.txt` the table hash that the statement line prints
(`a85830d7`, `a99578e8`, `12dad743`). Every check passes for every tag. The count "rows placed" above the gate
differs by one between some parts of the gated kernel tags; it is not a count of Table C.

The part files of the card runs (about 8,700 small files) are not in this repository. The records of the
single-part runs K7 and K10 and the headers of K8 and K9 are in `audit/records/`, and the part files of the
second counts of K7 and T7 in `audit/k7second/parts/` and `audit/t7second/parts/`.

### 6.4 Tests on file

The tests below are recorded in the notes and referee reports named with them; none of these files is in this
repository.

- Kernel, card. `gk4` gives the reference counts of defect 15 (7 links 29,066,365 and 24,856,368; 6 links
  4,551,813,305; level 76 6,065,162,755; 4 links 45,080,993,091; 3 links 445,234,933,436), also in parts, and
  every kernel variant of `gk5` gives them (note gpu, note gpu2 6).
- Rule JS, program. `gkjs` with `JS=0` gives the production counts (K9 whole, three parts of K6, ten hash
  parts); with `JS=1` it gives the counts of the CPU reference `kfast_js` (K9 359,998,813, K8 19,526,754,031,
  parts of K0, K1, K2 by index and by hash, gates at 1 to 20 rows); 36 cases on 5 and 6 symbols by emulation and
  on the card, 0 different; the referee's 113 statements on 7 symbols with an entry lowered by 1, a violation in
  all 113 with equal counts (note gkjs 3).
- Rule JS, argument. The referee's brute force at the level of the proof (refjs 3.2): on 5 and 6 symbols, for
  eight potentials with b >= 0, no key with (4.1) lacks a normal spelling with (4.1); for b < 0 and for the
  opposite normal form there are many. Random statements (300 on 5 symbols, 350 on 6): 0 wrong answers between
  the referee's own search and `kfast_js`. K9 whole by the referee's own program: equal counts with and without
  the rule.
- Joint, card against CPU. `gj2` against `jr3`: 220 cases on 5 symbols, 187 on 6, 16 on 7, all equal; the
  defect-15 counts of S5, S4, S1 with and without PREV and ORD; 5 pieces against `jr5s` 12 of 12; ORDS 135 of
  135; with B = 0 and no cuts the plain count is m! times the ORDS count; 288 cases where "objects exist" is the
  same with and without ORDS (note gpu2 4.2). `gj3` against `jr6` and `gj2` (note tune 3).
- Joint rules against brute force. ref16 3.5: the referee's `bf` lists every object on 5 and 6 symbols; in every
  configuration of the run book (plain, ORD, ORDS, PREV on each sequence piece, ORD + PREV, ORDS + PREV, gate
  parts, start-vertex parts, windows) the program finds an object iff one exists: 3,753 runs, 0 failures.
  ref16b 3: 98,075 runs on 5, 6 and 7 symbols for the windows, RLO, both halves of VS and several rings with
  ORDS and PREV, 0 discrepancies; a split made wrong by one on purpose is caught in 448 of 5,792 runs. The tuned
  settings of the run book: 114 cases with objects on 5 and 6 symbols, all found (note tune 8).
- Tables. RX by three programs and 60 witnesses; the caps files by the referees' scripts chkcaps.py (ref16) and
  chktab.py (ref16b); the ring table of the card host with RVMIN against the rule written out by the referee,
  0 differences in 2.84e8 entries (the referee's hostchk.c).
- Accounting. The identities of Lemma CUT16 and the shifts recomputed by the referee; the knapsack by two
  programs (by pieces and by items) with equal comparable counts.

Not covered by any test: Lemma CUT16 on enumerated configurations (the identities were checked by hand and
recomputed by the referee, but not run on my enumeration of the configurations of 5 symbols; Lean proves the cut
at level 1, section 7.3); a run of four rings with objects; VS with several rings (not used); the card kernel
`gj3.cu` beyond its equal counts; joint objects on 7 symbols with two or more rings.

## 7. What has not been done

### 7.1 The kernel statements K0, K1, K2

All three ended without violation: K2 (512 parts), K0 (4,096 parts, 2026-10-17) and K1 (2,048 parts, 89,682 card
seconds, 2026-10-18 18:37), each with one statement line; their kept counts are in Table C. With them K3 and K4
hold and Theorem K16 holds. K7 and K10 have stored part files (`audit/records/`; no violation, the counts of
Table C); the part files of K0, K1, K2 are packed in an archive of mine.

### 7.2 Second programs that are missing

At defect 15 every statement had two programs that share no code. At defect 16, K7, K8, K9, K10, T7, T8 and T9'
have independent second counts equal to Table C, and K0 to K6 and T1 to T6' rest on one card program each. For
T2 48..55 a second program exists, but it shares the rule code with the card host. By "independent" I mean a
program that shares no code with the card programs: the second programs of defect 15, which were written from
the texts only (`k2_s12` and `j2_np5`, section 6.1), the referee's `ref7`, and the Lean engines
(`K16.seqSearch`, `J16.jSearch`, evaluated as compiled code, section 0.4).

The second count of T7 by `j2_np5` ran on 2 threads in 8 resumable parts (`audit/t7second/run_t7.sh`) from
2026-10-20 17:32 to 2026-10-21 20:04. Two workers stopped once without a result and their parts were run again
(`audit/t7second/run.log`). Its parts add up to 1,432,335,917,907 kept and 7,283,065,963,552 tried, found 0, the
counts of Table C; they took 171,865 s of CPU time (about 48 thread-hours).

The Lean equation of K7 ran as four `native_decide` theorems on 3 threads (`lean/nk_queue.sh`, log
`lean/nk_queue.log`) and ended on 2026-10-21 at 16:46; section 0.4 says what is still missing to make them the
field `k7`. The Lean equation of K6 started on 2026-10-24 at 03:26, after the evaluations of 5,900 that had
priority on the machine (`lean/start_k6_20261024.sh`: the 16 files one after the other on 4 threads). Before the
start I estimated about 217 thread-hours. The first file took 13,552 s; at that rate the 16 files take about 60
hours, so K6 should end around 2026-10-26. Finished modules are skipped when the queue is started again.

| statement | second count now | what would give one |
|---|---|---|
| K0, K1, K2 | none (`gkjs` only) | a second card program or the Lean engine; 1.6e15 kept in all is out of reach of the CPU |
| K3, K4 | none | the same (5.3e14 and 1.6e14 kept) |
| K5 | none | `k2_s12` on the CPU: 2.4e13 kept, about 470 thread-hours at the 0.071 us per kept of the K7 run |
| K6 | none; the Lean equation is being evaluated (see above) | the end of that evaluation (an answer, not a count), or `k2_s12`: 2.6e12 kept, about 51 thread-hours |
| K7 | `k2_s12`: 320,243,136,927 kept, no violation, 64 parts, 6.3 thread-hours (`audit/k7second/summary.txt`); the Lean equation: four theorems by `native_decide`, answer "nothing found" | done |
| K8 | `k2_s12` 22,732,567,392 (`audit/second/k2_K8.txt`); the Lean engine: theorem `k8_ev` (`native_decide`), counting copy 22,732,567,392; `kfast2` (card lineage) | done |
| K9 | `k2_s12` 384,081,983 (`audit/second/k2_K9.txt`); refjs `ref7`; the Lean engine: theorem `k9_ev`, count 384,081,983 (and 359,998,813 with Rule JS, as `kjs`); `kfast2` | done |
| K10 | `k2_s12` 172,577 (`audit/second/k2_K10.txt`); the Lean engine: theorem `k10_ev`, count 172,577 | done |
| T1 | none | `j2` of defect 15 (no reversal cut; size not known) or the Lean engine |
| T2 windows 8..31, 56..89 | none | the same |
| T2 32..39, 40..47, both halves | none | upper halves: `j2r` with a = 17, 20; lower halves: `j2` with the lowered files, order S7 R |
| T2 48..55, both halves | `jr6` on the CPU, which shares `jr_core.h` with the card host | `j2r` with a = 23 (about 5e11 tried), `j2` for the lower half |
| T3' | none | out of reach of the CPU (2.1e14 tried): a second card program or the Lean engine |
| T4' | none | `j2` with its window arguments (7.9e12 tried) |
| T5 | none (`jr3` shares `jr_core.h` with the card host) | `j2` (2.7e14 tried) or the Lean engine |
| T6' | none (the counted run is the plain one, T6rp; the ORDS run T6r is not counted) | `j2` (5.9e11 tried) |
| T7 | `j2_np5` 1,432,335,917,907 kept, 7,283,065,963,552 tried, found 0, 8 parts (`audit/t7second/`); the `gj2` repeat shares `jr_core.h` with `gj`, so it is not independent | done |
| T8 | `j2_np5` 7,126,584,865 kept, 36,384,111,126 tried (`audit/second/j2_T8.txt`); the Lean engine: theorem `t8_ev`, count 7,126,584,865 / 36,384,111,126; `gj2` repeat (not independent) | done |
| T9' | `j2_np5` 11,105,597 kept, 59,706,146 tried (`audit/second/j2_T9r.txt`); the Lean engine: theorem `t9_ev`, count 11,105,597 / 59,706,146 | done |
| ORDS on 7 symbols | no counted statement rests on ORDS | one positive case (V lowered), plain against ORDS, CPU against card (ref16 6), needed only before an ORDS run is counted |
| knapsack | two programs | done |
| RX | three programs | done |

### 7.3 The Lean form: level 1 done, six search equations evaluated

Level 1 is done (PLAN_5901; states STATE_5901A, STATE_5901B, STATE_5901C; the assembly `covers_5901_of_search` in
`LowerBounds/F5901Search.lean`; axioms propext, Classical.choice, Quot.sound; no `sorry`, no `native_decide`).
The level-1 sources are not in this folder; they come with the other Lean proofs in `proofs/lean/`, and the
README of this folder lists the modules with their SHA-256. Level 1 consists of these parts:

- part A16, the accounting: ACC16 and EPS16 at cost 136 (`acc_value` 40, `acc_weight` 96, `eps_le_two`); Lemma
  CUT16 as the cut at every dear seam (`A16.cutG`, with `kernel_pieces16` for (lin), `cyc_decomp`, `cyc_glue`
  and `cyc_ext` for (cyc), `hanging_ext16` for (lin')), whose identities Lean uses as inequalities; hull tables
  and 40 closed checks (`A16.core`) in place of the enumeration KN16; and the fact that every ring piece has at
  least 8 holes;
- part B16, the kernel alone: Rule JS (JS1 to JS3 and Theorem JS), the engine `K16.seqSearch` with the JS flag
  and its completeness, and the instance of Lemma CL that the kernel statements need (`K16.cl16_of`, rows 9 and
  10 of D16 below LO, from Theorem K of defect 15);
- part C16, the joint statements: PREV, ORD, the ring classes, the windows, VS (hi) and (lo), the engine
  `J16.jSearch` and its completeness, and RX from its ring search.

STATE_5901A 4, STATE_5901B 5 and STATE_5901C 3 list the steps where the Lean proof is organised differently from
this text; none of them changes a statement of Table C.

Level 2 is the evaluation of the search equations: `K16.Evals` (eleven fields) and `J16.Evals` (eighteen runs and
the ring search of RX). These equations are statements about the Lean engines, and section 0.4 says how they
relate to the card runs. Six of them are proved as theorems by `native_decide` in `lean/Audit5901/`, outside the
build of the level-1 sources: the fields k10, k9, k8, t9 and t8 (`NEv.lean`) and the four ranges of parts of k7
(`NK7_0.lean` to `NK7_3.lean`; section 0.4 says what is missing to make them the field). K6 is being evaluated
(section 7.2). The rest is about 2.4e15 kept prefixes (kernel) and 9.2e14 (joint), about 420 and 490 days on 28
threads at the measured rates of the Lean engines (PLAN_5901 4). At those rates T4', T6', T7 and the six VS
halves of T2 would each take under a day on 28 threads. K0 to K5, T1, the windows 8..31 and 56..89 of T2, T3'
and T5 are out of reach without new rules or a faster engine. At defect 15 the searches were 2.9e13 start
vertices (joint) and 1.5e13 kept prefixes ([W] 0.1); at defect 16 they are more than a hundred times as large.

### 7.4 Other things

- No end-to-end check on 6 symbols, for the reason of [W] 7.4: the method is a sufficient condition and does not
  apply there.
- Lemma CUT16 on real configurations. Its identities were checked by hand and recomputed by the referee, but
  they were not run on the enumerated configurations of 5 symbols, as the conversions of defect 15 were. Lean
  proves the cut at level 1 (part A16, section 7.3), so the argument is checked; the enumeration test would only
  compare the text with examples.
- I kept a list of the disagreements between the sources and of the steps that were only asserted somewhere,
  with the reading taken here. The list is a working note; its points are summarised in `REFEREE_NOTES.md`
  (section C), whose sections A and B are my last referee pass over this text.
