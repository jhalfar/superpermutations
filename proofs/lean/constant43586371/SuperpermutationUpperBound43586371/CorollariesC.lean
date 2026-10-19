import SuperpermutationUpperBound43586371.MainC
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# The bound in the shape of `SuperpermutationBounds.Finite`, and two values

`Cost43586371` is `SuperpermutationBounds.Cost` of `Challenge.lean` with `43586371/86486400` in place
of `43/80` and `654131/86486400` in place of `17/240`; `Finite43586371` and `FiniteInteger43586371` are
`Finite` and `FiniteInteger` with this cost, starting at `m = 17` (19 symbols).

The two `HasWord` statements are `finite_bound19` at the best parameter `a` for 19 and 20
symbols (`ledgerC.py`).
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationBounds

/-- `SuperpermutationBounds.Cost` with the constants 43586371/86486400 and 654131/86486400. -/
def Cost43586371 (m : ℕ) (a : ℤ) : ℚ :=
  F3 (m + 2) + (43586371 / 86486400 : ℚ) * (Nat.factorial (m - 1) : ℚ) +
    ((a : ℚ) - 2) * ((654131 / 86486400 : ℚ) * (Nat.factorial (m - 1) : ℚ) /
      ((m : ℚ) - 1)) +
    ((m : ℚ) - (a : ℚ)) * min
      ((654131 / 86486400 : ℚ) * (Nat.factorial (m - 1) : ℚ) / ((m : ℚ) - 1))
      ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (a + 1).toNat : ℚ))

def Finite43586371 : Prop :=
  ∀ m a : ℕ, 17 ≤ m → 2 ≤ a → a ≤ m →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost43586371 m (a : ℤ)

def FiniteInteger43586371 : Prop :=
  ∀ m : ℕ, ∀ a : ℤ, 17 ≤ m → 2 ≤ a → a ≤ (m : ℤ) →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost43586371 m a

theorem finite_43586371 : Finite43586371 := by
  intro m a hm ha ham
  obtain ⟨w, hw, hl⟩ := finite_bound19 m hm a ha ham
  refine ⟨w, hw, ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hfac1 : m + 2 - 1 = m + 1 := by omega
  have hfac2 : m + 2 - 2 = m := by omega
  have hfacA : ((a : ℤ) + 1).toNat = a + 1 := by omega
  simpa only [Cost43586371, SuperpermutationBounds.F3, hfac1, hfac2, hfacA,
    Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub ham, Nat.cast_sub hm1,
    Nat.cast_ofNat, Nat.cast_one, Int.cast_natCast, mul_div_assoc, mul_assoc] using hl

theorem finiteInteger_43586371 : FiniteInteger43586371 := by
  intro m a hm ha ham
  have h0 : 0 ≤ a := by omega
  have he : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h0
  have h := finite_43586371 m a.toNat hm (by omega) (by omega)
  rwa [he] at h

/-- 19 symbols: `m = 17`, `a = 10`. -/
theorem hasWord_nineteen_C : HasWord 19 128413786203964800 := by
  obtain ⟨w, hw, hl⟩ := finite_bound19 17 (by norm_num) 10 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

/-- 20 symbols: `m = 18`, `a = 10`. -/
theorem hasWord_twenty_C : HasWord 20 2561130027702731520 := by
  obtain ⟨w, hw, hl⟩ := finite_bound19 18 (by norm_num) 10 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

end SuperpermutationUpperBound43586371

#print axioms SuperpermutationUpperBound43586371.finite_43586371
#print axioms SuperpermutationUpperBound43586371.finiteInteger_43586371
#print axioms SuperpermutationUpperBound43586371.hasWord_nineteen_C
#print axioms SuperpermutationUpperBound43586371.hasWord_twenty_C
