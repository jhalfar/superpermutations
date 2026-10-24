import LowerBounds.DJunction
import Superperm.Bridge

/-!
# Theorem D

the written proof of Theorem D, section 3.  Let `k ≥ 5` and let `lines` be a list of closed chain
lines `(a, b, c)` with `a ≤ b` (`ChainLine k a b c`, `c + 2 a ≤ b k`).  If for every number
`p < m` of paid links one of the lines has

  `b (k - 1) (m - 1 - p) + c (1 + p) < a ((k-2)! + (m - 1 - p))`      (`lineExcludes k m p a b c`),

then every Hamiltonian path `P` on `k` symbols has `wt(P) + k ≥ hpv k + m`
(`theoremD_pathwise`), so every superpermutation on `k` symbols has at least `hpv k + m` letters
(`superperm_boundD`, `covers_length_ge_boundD`).

The proof: for a `σ²`-reduced path with `wt + k < hpv k + m`, the budget (`coverage_bound`) gives
`N + p ≤ m - 1`, where `N = rows - (k-2)!` and `p` is the number of seams of weight at least 4
plus the number of paid junctions; the line chosen for this `p` contradicts the line inequality
(`lineD_reduced`), because `b (k - 1) ≥ a`.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators Classical

variable {k : ℕ}

/-- The test of Theorem D for one number `p` of paid links: the line `(a, b, c)` excludes a path
of defect `m - 1` with `p` paid links. -/
def lineExcludes (k m p a b c : ℕ) : Prop :=
  b * (k - 1) * (m - 1 - p) + c * (1 + p) < a * ((k - 2).factorial + (m - 1 - p))

instance (k m p a b c : ℕ) : Decidable (lineExcludes k m p a b c) := by
  unfold lineExcludes
  infer_instance

set_option maxHeartbeats 800000 in
/-- Theorem D for a `σ²`-reduced Hamiltonian path. -/
theorem theoremD_reduced (hk : 5 ≤ k) (lines : List (ℕ × ℕ × ℕ))
    (hlines : ∀ l ∈ lines, l.1 ≤ l.2.1 ∧ l.2.2 + 2 * l.1 ≤ l.2.1 * k ∧ ChainLine k l.1 l.2.1 l.2.2)
    (m : ℕ) (hm : ∀ p, p < m → ∃ l ∈ lines, lineExcludes k m p l.1 l.2.1 l.2.2)
    {P : HPath k} (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) :
    hpv k + m ≤ P.wtP + k := by
  by_contra hlt
  have hlt' : P.wtP + k + 1 ≤ hpv k + m := by omega
  have hcov : (k - 1) * hpv k + holesP hP +
      (k - 1) * (heavyP hP + (paidJunctions hP).card) ≤ (k - 1) * (P.wtP + k) :=
    coverage_bound hk hP
  have hhol := holes_eq hk hP
  obtain ⟨K1, hK1⟩ : ∃ K1, K1 = k - 1 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = (k - 2).factorial := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = rowsP hP := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = heavyP hP + (paidJunctions hP).card := ⟨_, rfl⟩
  rw [← hK1, ← hp] at hcov
  rw [← hK1, ← hT, ← hR] at hhol
  have hK1pos : 0 < K1 := by omega
  have hmul : K1 * (R + p + 1) ≤ K1 * (T + m) := by
    have h1 := Nat.mul_le_mul_left K1 hlt'
    simp only [Nat.mul_add, Nat.mul_one] at h1 hcov ⊢
    omega
  have hle : R + p + 1 ≤ T + m := Nat.le_of_mul_le_mul_left hmul hK1pos
  have hTR : T ≤ R := by
    have h1 : K1 * T ≤ K1 * R := by omega
    exact Nat.le_of_mul_le_mul_left h1 hK1pos
  have hpm : p < m := by omega
  obtain ⟨l, hl, hex⟩ := hm p hpm
  obtain ⟨hab, hclosed, hline⟩ := hlines l hl
  have hD := lineD_reduced hk hab hline hclosed hP hred
  obtain ⟨N, hN⟩ := Nat.exists_eq_add_of_le hTR
  obtain ⟨N', hN'⟩ : ∃ N', m = p + 1 + N' := Nat.exists_eq_add_of_le (by omega)
  have hNN : N ≤ N' := by omega
  have e1 : m - 1 - p = N' := by omega
  have e2 : 1 + heavyP hP + (paidJunctions hP).card = 1 + p := by omega
  unfold lineExcludes at hex
  rw [← hK1, ← hT, e1] at hex
  rw [← hK1, ← hT, ← hR, e2, hN] at hD
  generalize l.1 = a at hab hex hD
  generalize l.2.1 = b at hab hex hD
  generalize l.2.2 = c at hex hD
  generalize gammaD k a b c * (freeJunctions hP).card = G at hD
  zify at hab hex hD hNN hK1pos
  have hb0 : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
  have hK1' : (1 : ℤ) ≤ (K1 : ℤ) := by linarith
  have hbK : (b : ℤ) * 1 ≤ (b : ℤ) * (K1 : ℤ) := mul_le_mul_of_nonneg_left hK1' hb0
  have hkey : ((b : ℤ) * (K1 : ℤ) - (a : ℤ)) * (N : ℤ) ≤ ((b : ℤ) * (K1 : ℤ) - (a : ℤ)) * (N' : ℤ) :=
    mul_le_mul_of_nonneg_left hNN (by linarith)
  have hG0 : (0 : ℤ) ≤ (G : ℤ) := Int.natCast_nonneg G
  nlinarith [hkey, hD, hex, hG0]

/-- **Theorem D** for every Hamiltonian path. -/
theorem theoremD_pathwise (hk : 5 ≤ k) (lines : List (ℕ × ℕ × ℕ))
    (hlines : ∀ l ∈ lines, l.1 ≤ l.2.1 ∧ l.2.2 + 2 * l.1 ≤ l.2.1 * k ∧ ChainLine k l.1 l.2.1 l.2.2)
    (m : ℕ) (hm : ∀ p, p < m → ∃ l ∈ lines, lineExcludes k m p l.1 l.2.1 l.2.2)
    {P : HPath k} (hP : P.IsHamiltonian) : hpv k + m ≤ P.wtP + k := by
  obtain ⟨Q, hQ, hred, hwt⟩ := sigma2_reduced_normal_form (by omega : 3 ≤ k) hP
  have h := theoremD_reduced hk lines hlines m hm hQ hred
  omega

/-- **Theorem D** for superpermutations. -/
theorem superperm_boundD (hk : 5 ≤ k) (lines : List (ℕ × ℕ × ℕ))
    (hlines : ∀ l ∈ lines, l.1 ≤ l.2.1 ∧ l.2.2 + 2 * l.1 ≤ l.2.1 * k ∧ ChainLine k l.1 l.2.1 l.2.2)
    (m : ℕ) (hm : ∀ p, p < m → ∃ l ∈ lines, lineExcludes k m p l.1 l.2.1 l.2.2) :
    hpv k + m ≤ Ssuper k :=
  ssuper_ge_of_pathwise (by omega) (fun _ hP => theoremD_pathwise hk lines hlines m hm hP)

/-- **Theorem D** for covering words over `Fin k`. -/
theorem covers_length_ge_boundD (hk : 5 ≤ k) (lines : List (ℕ × ℕ × ℕ))
    (hlines : ∀ l ∈ lines, l.1 ≤ l.2.1 ∧ l.2.2 + 2 * l.1 ≤ l.2.1 * k ∧ ChainLine k l.1 l.2.1 l.2.2)
    (m : ℕ) (hm : ∀ p, p < m → ∃ l ∈ lines, lineExcludes k m p l.1 l.2.1 l.2.2) :
    ∀ w : List (Fin k), SuperpermutationBounds.Covers w → hpv k + m ≤ w.length :=
  (SuperpermBridge.hunter_le_ssuper_iff (by omega)).mp (superperm_boundD hk lines hlines m hm)

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.theoremD_pathwise
#print axioms SuperpermLowerBounds.superperm_boundD
#print axioms SuperpermLowerBounds.covers_length_ge_boundD
