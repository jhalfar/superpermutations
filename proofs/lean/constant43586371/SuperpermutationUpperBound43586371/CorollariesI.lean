import SuperpermutationUpperBound43586371.MainI
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# The bound in the shape of `SuperpermutationBounds.Finite`, and two values

`Cost3853` is `SuperpermutationBounds.Cost` of `Challenge.lean` with `3853/8736` in place
of `43/80` and `6113/96096` in place of `17/240`; `Finite3853` and `FiniteInteger3853` are
`Finite` and `FiniteInteger` with this cost, starting at `m = 17` (19 symbols).

The two `HasWord` statements are `finite_bound19_3853` at the best parameter `a` for 19 and 20
symbols (`ledgerC.py`).
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationBounds

/-- `SuperpermutationBounds.Cost` with the constants 3853/8736 and 6113/96096. -/
def Cost3853 (m : ℕ) (a : ℤ) : ℚ :=
  F3 (m + 2) + (3853 / 8736 : ℚ) * (Nat.factorial (m - 1) : ℚ) +
    ((a : ℚ) - 2) * ((6113 / 96096 : ℚ) * (Nat.factorial (m - 1) : ℚ) /
      ((m : ℚ) - 1)) +
    ((m : ℚ) - (a : ℚ)) * min
      ((6113 / 96096 : ℚ) * (Nat.factorial (m - 1) : ℚ) / ((m : ℚ) - 1))
      ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (a + 1).toNat : ℚ))

def Finite3853 : Prop :=
  ∀ m a : ℕ, 17 ≤ m → 2 ≤ a → a ≤ m →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost3853 m (a : ℤ)

def FiniteInteger3853 : Prop :=
  ∀ m : ℕ, ∀ a : ℤ, 17 ≤ m → 2 ≤ a → a ≤ (m : ℤ) →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost3853 m a

theorem finite_3853 : Finite3853 := by
  intro m a hm ha ham
  obtain ⟨w, hw, hl⟩ := finite_bound19_3853 m hm a ha ham
  refine ⟨w, hw, ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hfac1 : m + 2 - 1 = m + 1 := by omega
  have hfac2 : m + 2 - 2 = m := by omega
  have hfacA : ((a : ℤ) + 1).toNat = a + 1 := by omega
  simpa only [Cost3853, SuperpermutationBounds.F3, hfac1, hfac2, hfacA,
    Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub ham, Nat.cast_sub hm1,
    Nat.cast_ofNat, Nat.cast_one, Int.cast_natCast, mul_div_assoc, mul_assoc] using hl

theorem finiteInteger_3853 : FiniteInteger3853 := by
  intro m a hm ha ham
  have h0 : 0 ≤ a := by omega
  have he : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h0
  have h := finite_3853 m a.toNat hm (by omega) (by omega)
  rwa [he] at h

/-- 19 symbols: `m = 17`, `a = 9`. -/
theorem hasWord_nineteen_I : HasWord 19 128412985922988480 := by
  obtain ⟨w, hw, hl⟩ := finite_bound19_3853 17 (by norm_num) 9 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

/-- 20 symbols: `m = 18`, `a = 9`. -/
theorem hasWord_twenty_I : HasWord 20 2561115976208213760 := by
  obtain ⟨w, hw, hl⟩ := finite_bound19_3853 18 (by norm_num) 9 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

end SuperpermutationUpperBound43586371

#print axioms SuperpermutationUpperBound43586371.finite_3853
#print axioms SuperpermutationUpperBound43586371.finiteInteger_3853
#print axioms SuperpermutationUpperBound43586371.hasWord_nineteen_I
#print axioms SuperpermutationUpperBound43586371.hasWord_twenty_I
