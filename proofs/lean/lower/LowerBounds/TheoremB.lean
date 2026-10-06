import LowerBounds.TheoremBCore
import LowerBounds.DeficitOne
import LowerBounds.LemmaZ

/-!
# Theorem B: the lower bound with denominator k² - 4k + 1

For every `k ≥ 7`

  Ssuper k ≥ k! + (k-1)! + (k-2)! + k - 3 + ⌈2((k-2)! - (k-2)) / (k² - 4k + 1)⌉.

`TheoremBCore` proves this from two geometric statements taken as hypotheses.  Here they are
discharged by `partition_unit_after_full_next_large` (the deficit-one lemma, `DeficitOne.lean`)
and `lemma_Z` (`LemmaZ.lean`).

Final statements:

* `theoremB_reduced`, `theoremB_pathwise`: the inequality
  `(k² - 4k + 1)·hpv k + 2((k-2)! - (k-2)) ≤ (k² - 4k + 1)·(wt(P) + k)` for `σ²`-reduced and
  for all Hamiltonian paths;
* `superperm_boundB`: `boundB k ≤ Ssuper k`;
* `superperm_boundB_numerical_bounds`: the values for `k = 7, …, 14`.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators Classical

variable {k : ℕ}

/-- (G5) holds: it is the deficit-one lemma. -/
theorem g5Statement (hk : 5 ≤ k) : G5Statement k :=
  fun _ hp _ _ _ partition => partition_unit_after_full_next_large hk hp partition

/-- Lemma Z holds. -/
theorem zStatement (hk : 5 ≤ k) : ZStatement k :=
  fun _ hP _ hred s hsEnd hzero hmu => lemma_Z hk hP hred s hsEnd hzero hmu

/-- Capacity of an exact weight-three chain with slope `k - 3`, without hypotheses. -/
theorem chain_capacity_slope3 (hk : 7 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) :
    2 * chain.pieces.length ≤ (k - 3) * pieceListTotalDeficit chain.pieces +
      (chainFirstPrice chain + chainLastPrice chain) :=
  chain_capacity_B hk (g5Statement (by omega)) hp chain

/-- Capacity of a strongly exitless path with slope `k - 3`, without hypotheses: `x⁺` is the
number of seams of weight at least 4. -/
theorem component_capacity_slope3 (hk : 7 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    2 * componentPieceCount p ≤ (k - 3) * componentPieceDeficit p +
      2 * ((k - 2) * (componentPositiveSeams p).card) +
        tailPrice p (by omega) hp + headPrice p (by omega) hp :=
  component_capacity_B_cuts hk (g5Statement (by omega)) hp

/-- **Theorem B for `σ²`-reduced Hamiltonian paths.** -/
theorem theoremB_reduced {k : ℕ} (hk : 7 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P) :
    (k * k - 4 * k + 1) * hpv k + 2 * ((k - 2).factorial - (k - 2)) ≤
      (k * k - 4 * k + 1) * (P.wtP + k) :=
  theoremB_reduced_of hk (g5Statement (by omega)) (zStatement (by omega)) hP hred

/-- **Theorem B for every Hamiltonian path.** -/
theorem theoremB_pathwise {k : ℕ} (hk : 7 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    (k * k - 4 * k + 1) * hpv k + 2 * ((k - 2).factorial - (k - 2)) ≤
      (k * k - 4 * k + 1) * (P.wtP + k) := by
  have h := pathwise_B_of hk (g5Statement (by omega)) (zStatement (by omega)) hP
  have hT : k - 2 ≤ (k - 2).factorial := Nat.self_le_factorial _
  omega

/-- Theorem B for every Hamiltonian path, with the ceiling. -/
theorem boundB_le_pathwise {k : ℕ} (hk : 7 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    boundB k ≤ P.wtP + k :=
  boundB_le_pathwise_of hk (g5Statement (by omega)) (zStatement (by omega)) hP

/-- **Theorem B.** For `k ≥ 7`, every superpermutation on `k` symbols has at least
`k! + (k-1)! + (k-2)! + k - 3 + ⌈2((k-2)! - (k-2)) / (k² - 4k + 1)⌉` letters. -/
theorem superperm_boundB {k : ℕ} (hk : 7 ≤ k) : boundB k ≤ Ssuper k :=
  superperm_boundB_of hk (g5Statement (by omega)) (zStatement (by omega))

/-- The values of Theorem B for `k = 7, …, 14`. -/
theorem superperm_boundB_numerical_bounds :
    5895 ≤ Ssuper 7 ∧
    46129 ≤ Ssuper 8 ∧
    408465 ≤ Ssuper 9 ∧
    4033329 ≤ Ssuper 10 ∧
    43917793 ≤ Ssuper 11 ∧
    522622030 ≤ Ssuper 12 ∧
    6746615766 ≤ Ssuper 13 ∧
    93891107960 ≤ Ssuper 14 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by decide : boundB 7 = 5895) ▸ superperm_boundB (by norm_num)
  · exact (by decide : boundB 8 = 46129) ▸ superperm_boundB (by norm_num)
  · exact (by decide : boundB 9 = 408465) ▸ superperm_boundB (by norm_num)
  · exact (by decide : boundB 10 = 4033329) ▸ superperm_boundB (by norm_num)
  · exact (by decide : boundB 11 = 43917793) ▸ superperm_boundB (by norm_num)
  · exact (by decide : boundB 12 = 522622030) ▸ superperm_boundB (by norm_num)
  · exact (by decide : boundB 13 = 6746615766) ▸ superperm_boundB (by norm_num)
  · exact (by decide : boundB 14 = 93891107960) ▸ superperm_boundB (by norm_num)

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.g5Statement
#print axioms SuperpermLowerBounds.zStatement
#print axioms SuperpermLowerBounds.chain_capacity_slope3
#print axioms SuperpermLowerBounds.component_capacity_slope3
#print axioms SuperpermLowerBounds.theoremB_reduced
#print axioms SuperpermLowerBounds.theoremB_pathwise
#print axioms SuperpermLowerBounds.boundB_le_pathwise
#print axioms SuperpermLowerBounds.superperm_boundB
#print axioms SuperpermLowerBounds.superperm_boundB_numerical_bounds
