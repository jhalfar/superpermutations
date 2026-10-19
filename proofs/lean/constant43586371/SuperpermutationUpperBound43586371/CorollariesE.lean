import SuperpermutationUpperBound43586371.MainE
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# The bound in the shape of `SuperpermutationBounds.Finite`, and two values

`Cost3961457` is `SuperpermutationBounds.Cost` of `Challenge.lean` with `3961457/7862400` in place
of `43/80` and `121207/17297280` in place of `17/240`; `Finite3961457` and `FiniteInteger3961457` are
`Finite` and `FiniteInteger` with this cost, starting at `m = 17` (19 symbols).

The two `HasWord` statements are `finite_bound19_3961457` at the best parameter `a` for 19 and 20
symbols (`ledgerC.py`).
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationBounds

/-- `SuperpermutationBounds.Cost` with the constants 3961457/7862400 and 121207/17297280. -/
def Cost3961457 (m : ℕ) (a : ℤ) : ℚ :=
  F3 (m + 2) + (3961457 / 7862400 : ℚ) * (Nat.factorial (m - 1) : ℚ) +
    ((a : ℚ) - 2) * ((121207 / 17297280 : ℚ) * (Nat.factorial (m - 1) : ℚ) /
      ((m : ℚ) - 1)) +
    ((m : ℚ) - (a : ℚ)) * min
      ((121207 / 17297280 : ℚ) * (Nat.factorial (m - 1) : ℚ) / ((m : ℚ) - 1))
      ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (a + 1).toNat : ℚ))

def Finite3961457 : Prop :=
  ∀ m a : ℕ, 17 ≤ m → 2 ≤ a → a ≤ m →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost3961457 m (a : ℤ)

def FiniteInteger3961457 : Prop :=
  ∀ m : ℕ, ∀ a : ℤ, 17 ≤ m → 2 ≤ a → a ≤ (m : ℤ) →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost3961457 m a

theorem finite_3961457 : Finite3961457 := by
  intro m a hm ha ham
  obtain ⟨w, hw, hl⟩ := finite_bound19_3961457 m hm a ha ham
  refine ⟨w, hw, ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hfac1 : m + 2 - 1 = m + 1 := by omega
  have hfac2 : m + 2 - 2 = m := by omega
  have hfacA : ((a : ℤ) + 1).toNat = a + 1 := by omega
  simpa only [Cost3961457, SuperpermutationBounds.F3, hfac1, hfac2, hfacA,
    Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub ham, Nat.cast_sub hm1,
    Nat.cast_ofNat, Nat.cast_one, Int.cast_natCast, mul_div_assoc, mul_assoc] using hl

theorem finiteInteger_3961457 : FiniteInteger3961457 := by
  intro m a hm ha ham
  have h0 : 0 ≤ a := by omega
  have he : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h0
  have h := finite_3961457 m a.toNat hm (by omega) (by omega)
  rwa [he] at h

/-- 19 symbols: `m = 17`, `a = 10`. -/
theorem hasWord_nineteen_E : HasWord 19 128413777883852160 := by
  obtain ⟨w, hw, hl⟩ := finite_bound19_3961457 17 (by norm_num) 10 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

/-- 20 symbols: `m = 18`, `a = 10`. -/
theorem hasWord_twenty_E : HasWord 20 2561129892078508800 := by
  obtain ⟨w, hw, hl⟩ := finite_bound19_3961457 18 (by norm_num) 10 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

end SuperpermutationUpperBound43586371

#print axioms SuperpermutationUpperBound43586371.finite_3961457
#print axioms SuperpermutationUpperBound43586371.finiteInteger_3961457
#print axioms SuperpermutationUpperBound43586371.hasWord_nineteen_E
#print axioms SuperpermutationUpperBound43586371.hasWord_twenty_E
