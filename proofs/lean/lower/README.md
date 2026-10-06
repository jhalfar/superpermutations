# Three lower bounds in Lean: Theorems A, B and C

Write hpv(k) = k! + (k-1)! + (k-2)! + k - 3. A word over k symbols that contains every permutation has at
least

    hpv(k) + ceil( 2 ((k-2)! - (k-2)) / (k (k-3)) )         letters, for k >= 5        (Theorem A)
    hpv(k) + ceil( 2 ((k-2)! - (k-2)) / (k^2 - 4k + 1) )    letters, for k >= 7        (Theorem B)
    hpv(k) + ceil( (2 (k-2)! - 2 (k-2) - b) / (k^2 - 4k + 1 - c (k-1)) )   letters     (Theorem C)

Theorem C holds for k >= 5 and for every pair of rational numbers c and b that passes two tests: three
inequalities between c, b and k, and one statement about pieces of paths, the window bound, which a finite
search proves. With c = 0 and b = 0 its formula is that of Theorem B. For k = 8 to 14 this directory has
searches, checked by the Lean kernel, for 27 pairs (c, b). The best of them give

| k | Theorem A | Theorem B | Theorem C | Liu's Lean value | shortest word proven in `../words` |
|---|---|---|---|---|---|
| 5 | 153 | | | 153 | |
| 6 | 870 | | | 869 | |
| 7 | 5,893 | 5,895 | | 5,892 | 5,905 |
| 8 | 46,121 | 46,129 | 46,133 | 46,118 | 46,181 |
| 9 | 408,433 | 408,465 | 408,469 | 408,418 | 408,731 |
| 10 | 4,033,159 | 4,033,329 | 4,033,378 | 4,033,080 | 4,034,855 |
| 11 | 43,916,736 | 43,917,793 | 43,917,903 | 43,916,235 | 43,930,578 |
| 12 | 522,614,409 | 522,622,030 | 522,622,378 | 522,610,764 | 522,737,175 (`../words12`) |
| 13 | 6,746,553,315 | 6,746,615,766 | 6,746,626,957 | 6,746,523,219 | |
| 14 | 93,890,534,411 | 93,891,107,960 | 93,891,141,008 | 93,890,256,441 | |

Liu's values are those of `PreimageChain.superperm_numerical_bounds_closed`.

The build has two levels. The default level checks 22 of the 27 searches and gives, for Theorem C, 46,132,
408,469, 4,033,378, 43,917,901, 522,622,378, 6,746,626,601 and 93,891,140,217 for k = 8 to 14.
`./build.sh full` checks the five large searches as well, which raise k = 8, 11, 13 and 14 to the values of
the table. The costs of both are under "Building".

All three theorems are proven here in Lean, on top of Xiaolong Liu's preimage-chain library
(github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds), which is built on the Hunter-Raudvere
library (github.com/urdvr/superpermutations-hunter). Both libraries are used unchanged.

Every proof is checked by the Lean kernel. There is no `native_decide` and no `sorry`. Each theorem below
depends on the axioms `propext`, `Classical.choice` and `Quot.sound` only.

## Whose the parts are

* Theorem A. Zach Hunter wrote this formula on 21 October 2019 in the group thread "New Lower Bound"
  (https://groups.google.com/g/superpermutators/c/M-1yQC0Aj44), as a bound he expected to prove. His
  expression, (k! - k(k-1)(k-2)) (k^3 - 2k^2 - 2k - 2) / (k(k-1)(k-2) - 2k) + k^3 - 2k^2 + k - 3, is the same
  number for every k. The note "Defect Budgets, Run Separators, and a Stronger Lower Bound for
  Superpermutations" by GPT 5.6 Sol and Marin Kisic (7 August 2026, github.com/mkisic/superpermutations) has a
  proof on paper, which Kisic posted as unverified. Uku Raudvere answered the next day that he had an
  unpublished independent proof based on an idea of Hunter's. The Lean proof is new. It needs no new lemma
  about paths, only lemmas of Liu's library.
* Theorem B. The formula is Cole Fritsch's. He posted it on 20 January 2020 in the same thread with an
  argument that he himself called far from rigorous and that Zach Hunter disputed the same day. The Lean proof
  is new. Besides Liu's library it uses the deficit-one lemma of the note of GPT 5.6 Sol and Kisic, which is
  proven here in Lean, a capacity bound for chains with slope k - 3, and one new lemma about junctions of cost
  zero. It is stated for k >= 7: for k = 6 the arithmetic of the capacity lemma is false from the five facts it
  uses (n = 3, g = (3,3,3,3), d = (2,3,2)).
* Theorem C, the window search and its proof are new.
* Jay Pantone announced on 29 September 2026 a Lean proof of the bound of Theorem B with n - 1 in place of
  n - 2 in the numerator, which gives the same integers for n <= 14, and a table that goes further: 46,130,
  408,468, 4,033,374, 43,917,903, 522,622,378 and 6,746,626,519 for n = 8 to 13. He announced his table
  first. His proof is not public, and the proofs here were made without it. He announced no value for
  n = 14.
* William Echols proved 46,130 for n = 8 in Lean by another method
  (github.com/williamechols/superperm8-ge-46130). His proof and the proofs here share nothing but Mathlib.

## The statements

The statements are copied from the Lean files with the symbols spelled in ASCII (`forall`, `exists`, `<=`,
`/\`, `Nat`). `Ssuper` is `Hunter.Ssuper`, the least length of a superpermutation in the Hunter-Raudvere
library. `Covers` is the definition of Jay Pantone's `Challenge.lean`: every list of k different letters occurs
in the word as a contiguous part.

```lean
-- LowerBounds/TheoremA.lean, TheoremBCore.lean                 (namespace SuperpermLowerBounds)
def hpv (k : Nat) : Nat := k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3
def kisicBound (k : Nat) : Nat :=
  hpv k + (2 * ((k - 2).factorial - (k - 2)) + k * (k - 3) - 1) / (k * (k - 3))
def boundB (k : Nat) : Nat :=
  hpv k + (2 * ((k - 2).factorial - (k - 2)) + (k * k - 4 * k + 1) - 1) / (k * k - 4 * k + 1)

-- LowerBounds/TheoremA.lean, TheoremB.lean
theorem superperm_kisic_bound (hk : 5 <= k) : kisicBound k <= Ssuper k
theorem superperm_boundB {k : Nat} (hk : 7 <= k) : boundB k <= Ssuper k

-- LowerBounds/TheoremAWords.lean, TheoremBWords.lean
theorem covers_length_ge_kisicBound {k : Nat} (hk : 5 <= k) :
    forall w : List (Fin k), Covers w -> kisicBound k <= w.length
theorem covers_length_ge_boundB {k : Nat} (hk : 7 <= k) :
    forall w : List (Fin k), Covers w -> boundB k <= w.length
```

The division is that of natural numbers, and (a + d - 1) / d is the ceiling of a / d.
`superperm_kisic_numerical_bounds` and `superperm_boundB_numerical_bounds` state the values of the table for
`Ssuper`, and `covers_kisic_numerical_bounds` and `covers_boundB_numerical_bounds` state them in the form
`forall w : List (Fin 9), Covers w -> 408465 <= w.length`. `AuditA.lean` and `AuditB.lean` write the general
statements and the values out with no definition of this project.

### Theorem C

The numbers c and b are written over one denominator: c = cn / q and b = bn / q.

```lean
-- LowerBounds/TheoremCCore.lean                                (namespace SuperpermLowerBounds)
def piC (k cn q : Nat) : Nat := q * (k * k - 4 * k + 1) - cn * (k - 1)
def boundC (k cn bn q : Nat) : Nat :=
  hpv k + (2 * q * (k - 2).factorial - (2 * q * (k - 2) + bn) + piC k cn q - 1) / piC k cn q
structure ConditionsC (k cn bn q : Nat) : Prop where
  q_pos : 0 < q
  cond_i : bn + cn * k <= q * k * (k - 5)
  cond_ii : bn + 4 * cn + 2 * q * k <= 4 * q * (k - 3) + (q * (k - 5) - cn) * (k - 2)
  cond_iii : 2 * q * (k - 2) + bn + cn * (k - 1) <= q * (k * k - 4 * k + 1)

-- LowerBounds/ChainCapacityC.lean                              (namespace SuperpermLowerBounds.ChainC)
def WindowBound (k cn bn q : Nat) (ds : List Nat) : Prop :=
  q * (2 * ds.length + 2 * (k - 4)) + cn * ds.sum <= q * ((k - 3) * ds.sum) + bn

-- LowerBounds/ComponentCapacityC.lean: the hypothesis, about the chains of Liu's library
def HStatement (k cn bn q : Nat) : Prop :=
  forall (p : HPath k), p.StronglyExitless -> forall chain : ExactWeightThreePieceChain p,
    ChainC.IsWindow (chain.pieces.map ComponentIntervalPiece.deficit) ->
    ChainC.WindowBound k cn bn q (chain.pieces.map ComponentIntervalPiece.deficit)

-- LowerBounds/TheoremC.lean, TheoremCWords.lean: Theorem C from the hypothesis
theorem superperm_boundC (hk : 5 <= k) (hcond : ConditionsC k cn bn q) (hH : HStatement k cn bn q) :
    boundC k cn bn q <= Ssuper k
theorem covers_length_ge_boundC {k cn bn q : Nat} (hk : 5 <= k) (hcond : ConditionsC k cn bn q)
    (hH : HStatement k cn bn q) : forall w : List (Fin k), Covers w -> boundC k cn bn q <= w.length

-- LowerBounds/SModelDef.lean, SBridge.lean: the hypothesis from a statement about a model
def ModelStatement (k cn bn q : Nat) : Prop :=
  forall L : List (List (Vtx k)), IsModelChain k L ->
    ChainC.IsWindow (modelDeficits k L) -> ChainC.WindowBound k cn bn q (modelDeficits k L)
theorem hStatement_of_model {k cn bn q : Nat} (hk : 5 <= k) :
    ModelStatement k cn bn q -> HStatement k cn bn q

-- LowerBounds/SModel.lean: the statement about the model from a search on numbers
theorem modelStatement_of_search {k cn bn q A q2 C1 C2 fuel : Nat} (hk : 5 <= k) (hk15 : k <= 15)
    (hc : cn <= q * (k - 5)) (hA : A = q * (k - 3) - cn) (hq2 : q2 = 2 * q)
    (hC1 : C1 = 2 * q * (k - 4)) (hC2 : C2 = 2 * q * (k - 3))
    (hrun : S.runSearch k = false) (hs : S.search k A q2 C1 C2 bn fuel = false) :
    ModelStatement k cn bn q

-- LowerBounds/SFinal.lean (generated): the bounds, with no hypothesis left
theorem covers_lower_bound_8  : forall w : List (Fin 8),  Covers w -> 46133 <= w.length
theorem covers_lower_bound_9  : forall w : List (Fin 9),  Covers w -> 408469 <= w.length
theorem covers_lower_bound_10 : forall w : List (Fin 10), Covers w -> 4033378 <= w.length
theorem covers_lower_bound_11 : forall w : List (Fin 11), Covers w -> 43917903 <= w.length
theorem covers_lower_bound_12 : forall w : List (Fin 12), Covers w -> 522622378 <= w.length
theorem covers_lower_bound_13 : forall w : List (Fin 13), Covers w -> 6746626957 <= w.length
theorem covers_lower_bound_14 : forall w : List (Fin 14), Covers w -> 93891141008 <= w.length
theorem ssuper_lower_bound_8  : 46133 <= Ssuper 8
-- and ssuper_lower_bound_9 to ssuper_lower_bound_14 with the same numbers

-- LowerBounds/SFinalSmall.lean (generated): the same from the 22 small certificates (the default level)
theorem covers_lower_bound_8_small  : forall w : List (Fin 8),  Covers w -> 46132 <= w.length
theorem covers_lower_bound_11_small : forall w : List (Fin 11), Covers w -> 43917901 <= w.length
theorem covers_lower_bound_13_small : forall w : List (Fin 13), Covers w -> 6746626601 <= w.length
theorem covers_lower_bound_14_small : forall w : List (Fin 14), Covers w -> 93891140217 <= w.length
-- and covers_lower_bound_9_small, _10_small, _12_small with the numbers of SFinal.lean,
-- and ssuper_lower_bound_8_small to ssuper_lower_bound_14_small
```

`SFinal.lean` has the two statements for each of the 26 different bounds of the 27 certificates, under the
names `covers_length_ge_N` and `ssuper_ge_N` with the number N written out, for example `ssuper_ge_46133`;
`SFinalSmall.lean` has them for the 22 bounds of the 22 small certificates. `AuditCFinal.lean` and
`AuditCSmall.lean` write the seven best bounds of each file out by hand with no definition of this project, and
`AuditC.lean` does the same for Theorem C with its hypothesis.

### With the literal words

`Superperm/TwoSidedC.lean` puts the values of Theorem C and the literal words of `../words` into one statement,
for n = 8, 9, 10 and 11. `Superperm/TwoSidedB.lean` and `TwoSidedA.lean` do the same with the values of
Theorems B and A for n = 9, 10 and 11. The statements of `../words/Superperm/TwoSided*.lean`, which use Liu's
values, stay as they are. For n = 12 the three statements are in `../words12/Superperm/`:
522,622,378 <= L(12) <= 522,737,175 with the value of Theorem C.

```lean
-- Superperm/TwoSidedC.lean                                     (namespace SuperpermBridge)
theorem ssuper_eight_boundC  : 46133 <= Hunter.Ssuper 8 /\ Hunter.Ssuper 8 <= 46181
theorem ssuper_nine_boundC   : 408469 <= Hunter.Ssuper 9 /\ Hunter.Ssuper 9 <= 408731
theorem ssuper_ten_boundC    : 4033378 <= Hunter.Ssuper 10 /\ Hunter.Ssuper 10 <= 4034855
theorem ssuper_eleven_boundC : 43917903 <= Hunter.Ssuper 11 /\ Hunter.Ssuper 11 <= 43930578
theorem words_eleven_boundC : (exists w : List (Fin 11), Covers w /\ w.length = 43930578) /\
    forall w : List (Fin 11), Covers w -> 43917903 <= w.length
-- and words_eight_boundC, words_nine_boundC, words_ten_boundC in the same form

-- Superperm/TwoSidedB.lean
theorem ssuper_nine_boundB   : 408465 <= Hunter.Ssuper 9 /\ Hunter.Ssuper 9 <= 408731
theorem ssuper_ten_boundB    : 4033329 <= Hunter.Ssuper 10 /\ Hunter.Ssuper 10 <= 4034855
theorem ssuper_eleven_boundB : 43917793 <= Hunter.Ssuper 11 /\ Hunter.Ssuper 11 <= 43930578
theorem words_eleven_boundB : (exists w : List (Fin 11), Covers w /\ w.length = 43930578) /\
    forall w : List (Fin 11), Covers w -> 43917793 <= w.length
-- and words_nine_boundB, words_ten_boundB in the same form

-- Superperm/TwoSidedA.lean
theorem ssuper_nine_kisic   : 408433 <= Hunter.Ssuper 9 /\ Hunter.Ssuper 9 <= 408731
theorem ssuper_ten_kisic    : 4033159 <= Hunter.Ssuper 10 /\ Hunter.Ssuper 10 <= 4034855
theorem ssuper_eleven_kisic : 43916736 <= Hunter.Ssuper 11 /\ Hunter.Ssuper 11 <= 43930578
-- and words_nine_kisic, words_ten_kisic, words_eleven_kisic
```

## How the proof of Theorem A goes

All of it is in `LowerBounds/TheoremA.lean` (536 lines). `P` is a Hamiltonian path that is reduced in the
sense of Liu's library (`Sigma2Reduced`), and `C` runs over the components of its Hunter image. A component
has r pieces, a deficit, a seam residual x, a minimum entry weight mu, and two bits a and b that say whether
its first and its last piece are full. The lemmas named below are those of the two libraries unless marked
as mine.

1. `sum_actual_component_pValue`, `sum_actual_component_t` and `actualComponentGeometry_weightEquations` write
   the baseline of the bound as a sum over the components.
2. `actualBaseline_add_actualPathPaymentCore_le` adds the root gap, the terminal indicator and the chain
   costs.
3. `actual_component_capacity` bounds the pieces of every component: 2r <= (k-2)(deficit + 2x + a + b).
4. `aBit_le` (mine): a full first piece of a component other than the root is paid by mu - 2 of that
   component.
5. `bBit_le` (mine): a full last piece is paid by the cost of the chain that leaves the component or by
   mu - 2 of the component the chain enters. `target_injective` (mine) shows that no component is entered
   twice, and `unpaid_le_one` (mine) that only one component is left unpaid.
6. `reduced_pathwise` (mine) adds this up: the sum of a + b is at most 2 + 2 (sum of mu - 2 over the
   components other than the root) + chain cost. The rest is linear arithmetic.
7. `sigma2_reduced_normal_form` and `Hunter.bridge_Lstar_eq_Ssuper` carry the bound from reduced paths to
   `Ssuper`.

The proof does not use the layer optimisation of Liu's library (`Numerics.gamma`, the `Pathwise*Core` portal
modules).

## How the proof of Theorem B goes

Steps 1, 2 and 7 are those of Theorem A. Step 3 is replaced by a capacity bound with slope k - 3 in place of
k - 2, and the accounting of steps 4 to 6 is done again with the end terms of that bound, where the junction
lemma is used. Six files, 2,258 lines:

* `DeficitOne.lean` (371 lines): the deficit-one lemma of that note. `deficitOne_path` is the lemma in block
  coordinates, `actualPiece_after_full_unit_deficit_ge_two` the same for the pieces of Liu's library, and
  `partition_unit_after_full_next_large` the form the capacity bound uses: in a chain, a partial piece of
  deficit 1 that follows full pieces is followed by a partial piece of deficit at least 2.
* `LemmaZ.lean` (387 lines): the lemma about junctions of cost zero, `lemma_Z`. Take a chain of cost 0 whose
  route does not end at the last vertex of the path and which enters a component of minimum entry weight 2.
  Then either that component is the one the chain leaves and has a single piece, or the last piece of the
  component it leaves and the first piece of the component it enters both have deficit at least 2.
* `ChainCapacityB.lean` (384 lines): `ChainB.chain_capacity_slope3`, the capacity bound as a statement about
  two sequences of natural numbers (gap lengths g and deficits d) under five hypotheses. It imports six
  modules of Mathlib and nothing of the libraries.
* `ComponentCapacityB.lean` (475 lines): `chain_capacity_B` and `component_capacity_B_cuts` apply it to the
  chains and components of Liu's library.
* `TheoremBCore.lean` (531 lines): the definition `boundB` and the assembly, with the deficit-one lemma and
  the junction lemma as hypotheses (`G5Statement`, `ZStatement`): `junction_le`, `sum_prices_le`,
  `reduced_pathwise_B_of`, `superperm_boundB_of`.
* `TheoremB.lean` (110 lines): the two hypotheses are discharged; `theoremB_reduced`, `theoremB_pathwise`,
  `superperm_boundB` and the eight values.

`LowerBounds/TheoremAWords.lean` (49 lines) and `TheoremBWords.lean` (45 lines) turn the two bounds into
statements about covering words with `SuperpermBridge.hunter_le_ssuper_iff` of
`../words/Superperm/Bridge.lean`.

## How the bound of Theorem C arises

The words of Liu's library first. A path through all permutations is cut into blocks: a block is a
permutation followed by its k - 1 rotations. The step from a block to the next costs at least 2, and
consecutive blocks joined by steps of cost 2 form a piece. A piece has at most k - 1 blocks; one with k - 1
blocks is full, a shorter one is partial, and its deficit is the number of blocks it lacks. A chain is a
sequence of pieces in which each step from a piece to the next costs exactly 3.

Theorems A and B bound the number of pieces of a chain by its total deficit with a slope that holds for
every chain: k - 2 pieces for two units of deficit in Theorem A, k - 3 in Theorem B. Theorem C lowers the
slope of Theorem B by a number c and lets a search say which c holds.

1. A window is a chain that starts and ends with a partial piece and in which every maximal run of partial
   pieces has a piece of deficit at least 2 (`ChainC.IsWindow`, a property of the list of deficits). The
   window bound with the constants c and b says that a window with r pieces and total deficit d satisfies
   2r + 2(k-4) + c d <= (k-3) d + b (`ChainC.WindowBound`). The hypothesis `HStatement k cn bn q` says that
   every window of every chain of Liu's library satisfies it.
2. The deduction (`ChainCapacityC`, `WindowSlackC`, `ComponentCapacityC`, `LemmaZC`, `TheoremCCore`,
   `TheoremC`, `TheoremCWords`; 2,266 lines). From the hypothesis and the three conditions `ConditionsC` the
   accounting of Theorem B is done again with the better slope. The result is `superperm_boundC` and
   `covers_length_ge_boundC`: the bound for every k >= 5 and every (c, b), with the hypothesis as its one
   assumption. A larger c makes the denominator of the formula smaller and so the bound larger; the search
   decides which c can be had.
3. The model (`SModelDef`, 85 lines). A model chain is a list of pieces, each a list of permutations, with
   five properties that mention only words: no piece is empty, a piece has at most k - 1 blocks, consecutive
   blocks of a piece overlap in k - 2 symbols, the last block of a piece and the first block of the next
   overlap in k - 3 symbols, and all blocks lie in different rotation classes. `ModelStatement k cn bn q` is
   the window bound for all model chains.
4. The bridge (`SBridgePath`, `SBridgeChain`, `SBridgeRelabel`, `SBridge`, `SBridgeTheoremC`, `SBridgeModel`;
   1,155 lines). Every chain of Liu's library is a model chain with the same list of deficits, so
   `ModelStatement` gives `HStatement` (`hStatement_of_model`). The model may contain chains that no path
   has. That costs nothing in correctness: a bound for more chains is a bound for fewer.
5. The search (`SSearch`, 303 lines, no Mathlib). `S.search k A q2 C1 C2 bn fuel` is a function on natural
   numbers that looks for a window of the model that violates the bound, among the violating windows with the
   fewest pieces. A permutation is one number (its symbols as hexadecimal digits), the set of used rotation
   classes is a search tree of such numbers, and the two sides of the inequality are two running sums. If it
   returns `false`, there is no such window.
6. Soundness (`SWord`, `SSound`, `SRun`, `SModel`; 1,598 lines). `modelStatement_of_search`: if the search
   returns `false`, and so does the small search `S.runSearch k` (one block cannot be followed by k - 2 full
   pieces), then `ModelStatement k cn bn q` holds, for 5 <= k <= 15. The proof takes a violating window with
   the fewest pieces, relabels the symbols so that it begins with the word 1 2 ... k, and shows that the
   search would have followed it piece by piece.
7. The certificates. That a given search returns `false` is proven by evaluation in the Lean kernel:
   `decide +kernel`, not `native_decide`, so no compiled code is trusted. A search of up to 827,022 states is
   too much for one evaluation, so a generator (`tools/s_plan.py`, `tools/s_plan2.py`) cuts it into lemmas of
   at most 1,500 states and writes the Lean files; `SCut`, `SLit` and `SDec` (392 lines, no Mathlib) hold the
   lemmas that put the parts together. The generator decides only where to cut. A wrong cut makes a lemma
   fail; it cannot make a false statement pass, because every lemma is evaluated by the kernel and the
   assembly is checked like any other proof.
8. `SFinal.lean` and `SFinalSmall.lean` (generated) apply `covers_length_ge_boundC` and `superperm_boundC`
   through the bridge to each certificate and evaluate `ConditionsC` and `boundC` by `decide`.

The certificates are listed in `certificates.txt` (the 22 small ones) and `certificates-large.txt` (five
more). The best ones for each k, with the Lean process time of their search in my build:

| k | bound | c | b | states of the search | generated files | Lean time | level |
|---|---|---|---|---|---|---|---|
| 8 | 46,132 | 3/10 | 64/10 | 2,915 | 3 | 44 s | default |
| 8 | 46,133 | 41/100 | 1188/100 | 827,022 | 192 | 2.9 h | full |
| 9 | 408,469 | 21/250 | 630/250 | 886 | 3 | 28 s | default |
| 10 | 4,033,378 | 6/25 | 92/25 | 10,774 | 9 | 5 min | default |
| 11 | 43,917,901 | 9/100 | 392/100 | 2,509 | 6 | 98 s | default |
| 11 | 43,917,903 | 91/1000 | 4016/1000 | 14,992 | 29 | 11 min | full |
| 12 | 522,622,378 | 51/1250 | 2956/1250 | 2,361 | 7 | 130 s | default |
| 13 | 6,746,626,601 | 31/200 | 632/200 | 3,897 | 7 | 3 min | default |
| 13 | 6,746,626,957 | 4/25 | 88/25 | 26,721 | 47 | 25 min | full |
| 14 | 93,891,140,217 | 41/800 | 2952/800 | 1,407 | 4 | 68 s | default |
| 14 | 93,891,141,008 | 21/400 | 1550/400 | 15,284 | 57 | 26 min | full |

The fractions are written as in the names of the certificates (`8 41 1188 100` is c = 41/100, b = 1188/100).
The other certificates give smaller bounds from smaller searches; 46,130 and 46,131 for k = 8 need 99 and
244 states. The fifth large certificate, `9 1 38 10`, is a second search for 408,469 with 50,100 states. It
takes 34 minutes and adds no bound. The cost of a search in the kernel is 7.5 ms for a state at k = 8, 12 to
15 ms at k = 9 and 10, and 20 to 25 ms at k = 11 and 13, and 1 to 4 MB of memory for a state inside one
lemma, which is why the lemmas are small.

Beside the Lean proof the searches were run by programs outside Lean, and a second program, written from the
written proof without the first, gave the same minima and the same counts of states. Neither program is in
this directory, and the Lean proof does not use them.

## The files

* `LowerBounds/`: the nine files of Theorems A and B and the 22 hand-written files of Theorem C named above.
* `certificates.txt`, `certificates-large.txt`: the 22 small and the five large certificates, with the
  options of their generators.
* `tools/`: the generators. `s_plan.py` and `s_plan2.py` write the search of one certificate as Lean files
  (the second writes the state of every part out, which deep searches need); `s_ksim.py` is the Python copy
  of `SSearch.lean` that they use to decide where to cut; `s_certs.py` and `s_final.py` write the files
  that state the results.
* `generated.sha256`: the hashes of the 435 generated Lean files (57 MB; 2.6 MB without the five large
  certificates). They are not in the repository; `build.sh` generates them into the build directory and
  compares them with this list.
* `Superperm/TwoSidedA.lean`, `TwoSidedB.lean`, `TwoSidedC.lean`: lower and upper bound in one statement.
* `AuditA.lean`, `AuditB.lean`, `AuditC.lean`, `AuditCSmall.lean`, `AuditCFinal.lean`: the statements written
  out in full.
* `build.sh`: generates the certificates and builds whatever is in these places.

## Building

The files of `LowerBounds/` import 150 of the 151 modules of the two libraries that `../words/build.sh`
compiles, and the two-sided statements import the literal words. So run `../words/build.sh` first. `build.sh`
here works in the same build directory and compiles only what is missing.

```sh
../words/build.sh
JOBS=4 ./build.sh          # the default level: Theorems A and B, Theorem C with the 22 small certificates
JOBS=4 ./build.sh full     # the five large certificates as well
```

`build.sh` generates the files of all 27 certificates (Python 3, about a minute), lets Lean evaluate the
searches of the level, `JOBS` processes at a time, and then builds every file it finds in `LowerBounds/`, the
generated files that state the results, every `Audit*.lean`, and, if the certificates of the words are in the
build directory, every file in `Superperm/`. At the default level it leaves out what rests on the large
certificates: `SFinal.lean`, `AuditCFinal.lean` and `Superperm/TwoSidedC.lean`. A file added to one of these
places is built without a change of the script. At the end it prints the axioms of every statement and fails
if one of them is not `propext`, `Classical.choice` or `Quot.sound`. A run after `full` at either level
compiles nothing again. The settings are listed at the top of the script and in `../tools/common.sh`; `../README.md`
says how to fetch what the build needs.

Measured on my machine (Ryzen 9 5950X, 32 GB, Windows 11 with Git Bash; one thread per Lean process, other
work running beside it), after `../words/build.sh` had compiled the two libraries (68 minutes) and the
literal words:

| what | modules | Lean time | largest working set |
|---|---|---|---|
| Theorems A and B: nine files, two audits, two two-sided files | 13 | 7.6 min | 3.6 GB |
| Theorem C: the 22 hand-written files | 22 | 12 min | 3.6 GB |
| the searches of the 22 small certificates | 85 | 23 min | 2.5 GB |
| their statement files and axiom files, `AuditC`, `AuditCSmall` | 7 | 3 min | 3.3 GB |
| the default level in all | 127 | 46 min | |
| the searches of the five large certificates | 340 | 4.5 h | 2.8 GB |
| `SCertW`, `SCertificates`, `SFinal`, their axiom files, `AuditCFinal`, `TwoSidedC` | 7 | 3 min | 3.3 GB |
| the full level in all | 474 | 5.3 h | |

Lean time is the sum over the Lean processes. With four processes the searches of all 27 certificates took 81
minutes by the clock; everything else ran one process at a time and took 30 minutes. A part of a search takes
up to four minutes. Five of the
hand-written files of Theorem C need no Mathlib and compile in seconds; the other 17 took 16 to 63 s each,
except `SModel` with 268 s, which was the first module to load Mathlib after the searches. The modules that
load all of Mathlib, which are most of those outside the searches, need 3.6 GB of working set at most and
commit 8 to 9 GB. The build directory grows by 0.5 GB at the full level, of which 57 MB are the generated
Lean files.

## What is trusted

The Lean kernel, the three axioms, and the definitions the statements rest on: `Hunter.Ssuper` of the
Hunter-Raudvere library, and for the statements about words `Covers` of `Challenge.lean`.
`../words/Superperm/Bridge.lean` proves that the two say the same. The lemmas of Liu's library and of the
Hunter-Raudvere library that the proofs use are compiled here from their sources, like everything else.

For Theorem C the kernel does more arithmetic than in the other parts: the searches are evaluated with the
kernel's built-in arithmetic on natural numbers, as in every `decide +kernel`. The generators, the Python
copy of the search and the list of hashes are not trusted: Lean checks the files they write.

## What is not here

* Pantone's proofs. They are not public.
* Theorem B for k = 5 and 6, and certificates of Theorem C for k = 5, 6, 7 and k = 15. Theorem A covers
  k = 5 and 6; the soundness theorem of the search holds for 5 <= k <= 15.
* Later certificates. Certificates for 522,622,398 (k = 12) and 6,746,627,046 (k = 13) have been built since
  this version was put together and are not in it. Higher values are known by computation only, with no Lean
  certificate: 408,470 (k = 9), 43,917,905 (k = 11), 522,622,405 (k = 12), 6,746,627,223 (k = 13) and
  93,891,141,126 (k = 14).
