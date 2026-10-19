import SuperpermutationUpperBound43586371.MainD
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# The bound in the shape of `SuperpermutationBounds.Finite`, and two values

`Cost21751799` is `SuperpermutationBounds.Cost` of `Challenge.lean` with `21751799/43243200` in place
of `43/80` and `297743/43243200` in place of `17/240`; `Finite21751799` and `FiniteInteger21751799` are
`Finite` and `FiniteInteger` with this cost, starting at `m = 20` (22 symbols).

The two `HasWord` statements are `finite_bound22` at the best parameter `a` for 22 and 23
symbols (`ledgerC.py`).
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationBounds

/-- `SuperpermutationBounds.Cost` with the constants 21751799/43243200 and 297743/43243200. -/
def Cost21751799 (m : ℕ) (a : ℤ) : ℚ :=
  F3 (m + 2) + (21751799 / 43243200 : ℚ) * (Nat.factorial (m - 1) : ℚ) +
    ((a : ℚ) - 2) * ((297743 / 43243200 : ℚ) * (Nat.factorial (m - 1) : ℚ) /
      ((m : ℚ) - 1)) +
    ((m : ℚ) - (a : ℚ)) * min
      ((297743 / 43243200 : ℚ) * (Nat.factorial (m - 1) : ℚ) / ((m : ℚ) - 1))
      ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (a + 1).toNat : ℚ))

def Finite21751799 : Prop :=
  ∀ m a : ℕ, 20 ≤ m → 2 ≤ a → a ≤ m →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost21751799 m (a : ℤ)

def FiniteInteger21751799 : Prop :=
  ∀ m : ℕ, ∀ a : ℤ, 20 ≤ m → 2 ≤ a → a ≤ (m : ℤ) →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost21751799 m a

theorem finite_21751799 : Finite21751799 := by
  intro m a hm ha ham
  obtain ⟨w, hw, hl⟩ := finite_bound22 m hm a ha ham
  refine ⟨w, hw, ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hfac1 : m + 2 - 1 = m + 1 := by omega
  have hfac2 : m + 2 - 2 = m := by omega
  have hfacA : ((a : ℤ) + 1).toNat = a + 1 := by omega
  simpa only [Cost21751799, SuperpermutationBounds.F3, hfac1, hfac2, hfacA,
    Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub ham, Nat.cast_sub hm1,
    Nat.cast_ofNat, Nat.cast_one, Int.cast_natCast, mul_div_assoc, mul_assoc] using hl

theorem finiteInteger_21751799 : FiniteInteger21751799 := by
  intro m a hm ha ham
  have h0 : 0 ≤ a := by omega
  have he : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h0
  have h := finite_21751799 m a.toNat hm (by omega) (by omega)
  rwa [he] at h

/-- 22 symbols: `m = 20`, `a = 10`. -/
theorem hasWord_twentytwo_D : HasWord 22 1177586126221615488000 := by
  obtain ⟨w, hw, hl⟩ := finite_bound22 20 (by norm_num) 10 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

/-- 23 symbols: `m = 21`, `a = 10`. -/
theorem hasWord_twentythree_D : HasWord 23 27028339195215218595840 := by
  obtain ⟨w, hw, hl⟩ := finite_bound22 21 (by norm_num) 10 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

end SuperpermutationUpperBound43586371

#print axioms SuperpermutationUpperBound43586371.finite_21751799
#print axioms SuperpermutationUpperBound43586371.finiteInteger_21751799
#print axioms SuperpermutationUpperBound43586371.hasWord_twentytwo_D
#print axioms SuperpermutationUpperBound43586371.hasWord_twentythree_D
