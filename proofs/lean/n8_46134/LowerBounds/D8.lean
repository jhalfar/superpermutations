import LowerBounds.DTheorem

/-!
# 46,134 for 8 symbols from three statements about chains

the written proof of Theorem D, section 5.2.  The three hypotheses, for exact weight-three chains
of strongly exitless paths on 8 symbols (`r` pieces, total deficit `δ`):

* (H1) `ChainLine 8 4 9 56`: `4 r ≤ 9 δ + 56`;
* (H2) `ChainLine 8 17 38 264`: `17 r ≤ 38 δ + 264`;
* (H3) `Zone8`: `4 r - 9 δ ≥ 54` and `17 r - 38 δ ≥ 258` imply `4 r - 9 δ = 56`.

`covers_boundD_8`: under these, every word over `Fin 8` that contains all permutations has at
least 46,134 letters.

The proof.  Let `P` be a `σ²`-reduced Hamiltonian path with `wt(P) + 8 ≤ 46133`.  The budget
(`coverage_bound`) and the two line inequalities (`lineD_reduced_holes`, with `γ = 5` and `γ = 6`)
leave exactly one possibility: 766 rows, 322 holes, two paid links, no free junction, hence three
chains.  For the chains of `P` together, `Tri` says: both lines hold in the sum, and either all
chains are on the first line, or the sum is at least 3 below the first line, or at least 7 below
the second (this is (H3), chain by chain: a chain that is not on the first line is at least 3
below it or at least 7 below the second line).  With the numbers above the sum is 2 below the
first line and 6 below the second: a contradiction.  The arithmetic is `d8_arith`.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators Classical

/-- What the three hypotheses say about a family of chains with `r` pieces, total deficit `δ` and
`n` chains: both lines hold, and either the family is on the first line, or at least 3 below
it, or at least 7 below the second line. -/
def Tri (r δ n : ℕ) : Prop :=
  4 * r ≤ 9 * δ + 56 * n ∧ 17 * r ≤ 38 * δ + 264 * n ∧
    (4 * r = 9 * δ + 56 * n ∨ 4 * r + 3 ≤ 9 * δ + 56 * n ∨ 17 * r + 7 ≤ 38 * δ + 264 * n)

theorem Tri.zero : Tri 0 0 0 := by
  unfold Tri
  omega

theorem Tri.add {r δ n r' δ' n' : ℕ} (h : Tri r δ n) (h' : Tri r' δ' n') :
    Tri (r + r') (δ + δ') (n + n') := by
  unfold Tri at *
  omega

/-- The arithmetic of the last cell: the budget, the two line inequalities and `Tri` cannot hold
together for a path of weight at most `46133 - 8`.  (`w` the weight, `R` the rows, `Δ` the holes,
`X` the seams of weight at least 4, `J` the paid and `F` the free junctions, `cc` the
components.)  The steps: `R + X + J ≤ 768`; then `F = 0`, `R = 766`, `X + J = 2`, `Δ = 322`,
three chains; and `Tri 766 322 3` is false. -/
theorem d8_arith (w R Δ X J F cc : ℕ) (hw : w + 8 ≤ 46133)
    (hcov : 7 * 46085 + Δ + 7 * (X + J) ≤ 7 * (w + 8)) (hhol : Δ + 7 * 720 = 7 * R)
    (hl1 : 4 * R + 5 * F ≤ 9 * Δ + 56 * (1 + X + J))
    (hl2 : 17 * R + 6 * F ≤ 38 * Δ + 264 * (1 + X + J)) (hcard : cc = F + J + 1)
    (htri : Tri R Δ (X + cc)) : False := by
  unfold Tri at htri
  have hC : R + (X + J) ≤ 768 := by omega
  have hA : 2296 + 5 * F ≤ 3 * R := by omega
  have hB : 15 * R + 6 * F ≤ 11496 := by omega
  have hF : F = 0 := by omega
  have hR : R = 766 := by omega
  have hp : X + J = 2 := by omega
  subst hF
  subst hR
  have hΔ : Δ = 322 := by omega
  subst hΔ
  have hn : X + cc = 3 := by omega
  rw [hn] at htri
  omega

section Chains

variable (h1 : ChainLine 8 4 9 56) (h2 : ChainLine 8 17 38 264) (h3 : Zone8)

include h1 h2 h3

/-- One chain. -/
theorem tri_chain {p : HPath 8} (hp : p.StronglyExitless) (Q : ExactWeightThreePieceChain p) :
    Tri Q.pieces.length (pieceListTotalDeficit Q.pieces) 1 := by
  have e1 := h1 p hp Q
  have e2 := h2 p hp Q
  have e3 := h3 p hp Q
  unfold pieceListTotalDeficit Tri
  by_cases hA : 9 * (Q.pieces.map ComponentIntervalPiece.deficit).sum + 54 ≤ 4 * Q.pieces.length
  · by_cases hB : 38 * (Q.pieces.map ComponentIntervalPiece.deficit).sum + 258 ≤
        17 * Q.pieces.length
    · have := e3 hA hB
      omega
    · omega
  · omega

/-- The chains of one strongly exitless path. -/
theorem tri_component {p : HPath 8} (hp : p.StronglyExitless) :
    Tri (componentPieceCount p) (componentPieceDeficit p)
      ((componentPositiveSeams p).card + 1) := by
  obtain ⟨chains, hflatten, hlength⟩ :=
    exists_componentExactWeightThreeChainPartition p (by norm_num) hp
  have hr := exactWeightThreeChainPartition_pieceCount_sum p (by norm_num) hp chains hflatten
  have hΔ := exactWeightThreeChainPartition_totalDeficit_sum (by norm_num : 4 ≤ 8) hp chains
    hflatten
  have hall : ∀ L : List (ExactWeightThreePieceChain p),
      Tri (L.map fun Q => Q.pieces.length).sum
        (L.map fun Q => pieceListTotalDeficit Q.pieces).sum L.length := by
    intro L
    induction L with
    | nil => exact Tri.zero
    | cons Q L ih =>
      have h := (tri_chain h1 h2 h3 hp Q).add ih
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.add_comm L.length 1]
      exact h
  have h := hall chains
  rw [hr, hΔ, hlength] at h
  exact h

/-- The chains of all components of a Hamiltonian path. -/
theorem tri_path {P : HPath 8} (hP : P.IsHamiltonian) :
    Tri (rowsP hP) (holesP hP) (heavyP hP + Fintype.card (ActualComponent P)) := by
  have hall : ∀ s : Finset (ActualComponent P),
      Tri (∑ C ∈ s, componentPieceCount (actualComponentPath hP C))
        (∑ C ∈ s, componentPieceDeficit (actualComponentPath hP C))
        (∑ C ∈ s, (componentPositiveSeams (actualComponentPath hP C)).card + s.card) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using Tri.zero
    | insert C s hC ih =>
      have h := (tri_component h1 h2 h3
        (actualComponentPath_stronglyExitless hP (by norm_num) C)).add ih
      rw [Finset.sum_insert hC, Finset.sum_insert hC, Finset.sum_insert hC,
        Finset.card_insert_of_notMem hC]
      have e : (componentPositiveSeams (actualComponentPath hP C)).card +
            ∑ C ∈ s, (componentPositiveSeams (actualComponentPath hP C)).card + (s.card + 1) =
          (componentPositiveSeams (actualComponentPath hP C)).card + 1 +
            (∑ C ∈ s, (componentPositiveSeams (actualComponentPath hP C)).card + s.card) := by
        omega
      rw [e]
      exact h
  have h := hall Finset.univ
  rw [Finset.card_univ] at h
  exact h

/-- The bound for a `σ²`-reduced Hamiltonian path on 8 symbols. -/
theorem theoremD8_reduced {P : HPath 8} (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) :
    46134 ≤ P.wtP + 8 := by
  have hcov : (8 - 1) * hpv 8 + holesP hP + (8 - 1) * (heavyP hP + (paidJunctions hP).card) ≤
      (8 - 1) * (P.wtP + 8) := coverage_bound (by norm_num) hP
  have hhol := holes_eq (by norm_num : 5 ≤ 8) hP
  have hl1 := lineD_reduced_holes (by norm_num : 5 ≤ 8) (by norm_num : 4 ≤ 9) h1 (by norm_num)
    hP hred
  have hl2 := lineD_reduced_holes (by norm_num : 5 ≤ 8) (by norm_num : 17 ≤ 38) h2
    (by norm_num) hP hred
  have hcard := card_components_eq (by norm_num : 5 ≤ 8) hP
  have htri := tri_path h1 h2 h3 hP
  have hg1 : gammaD 8 4 9 56 = 5 := by decide
  have hg2 : gammaD 8 17 38 264 = 6 := by decide
  have hhpv : hpv 8 = 46085 := by decide
  have hfac : (8 - 2).factorial = 720 := by decide
  rw [hg1] at hl1
  rw [hg2] at hl2
  rw [hhpv] at hcov
  rw [hfac] at hhol
  by_contra hlt
  exact d8_arith P.wtP (rowsP hP) (holesP hP) (heavyP hP) (paidJunctions hP).card
    (freeJunctions hP).card (Fintype.card (ActualComponent P)) (by omega) (by omega) (by omega)
    hl1 hl2 hcard htri

/-- **The bound for every Hamiltonian path on 8 symbols**, from (H1), (H2), (H3). -/
theorem theoremD8_pathwise {P : HPath 8} (hP : P.IsHamiltonian) : 46134 ≤ P.wtP + 8 := by
  obtain ⟨Q, hQ, hred, hwt⟩ := sigma2_reduced_normal_form (by norm_num : 3 ≤ 8) hP
  have h := theoremD8_reduced h1 h2 h3 hQ hred
  omega

/-- (H1), (H2), (H3) give `Ssuper 8 ≥ 46134`. -/
theorem superperm_boundD_8 : 46134 ≤ Ssuper 8 :=
  ssuper_ge_of_pathwise (by norm_num) (fun _ hP => theoremD8_pathwise h1 h2 h3 hP)

/-- **(H1), (H2), (H3) give 46,134**: every word over `Fin 8` that contains all permutations has
at least 46134 letters. -/
theorem covers_boundD_8 :
    ∀ w : List (Fin 8), SuperpermutationBounds.Covers w → 46134 ≤ w.length :=
  (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp (superperm_boundD_8 h1 h2 h3)

end Chains

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.tri_path
#print axioms SuperpermLowerBounds.theoremD8_pathwise
#print axioms SuperpermLowerBounds.covers_boundD_8
