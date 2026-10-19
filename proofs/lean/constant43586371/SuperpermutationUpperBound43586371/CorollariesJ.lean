import SuperpermutationUpperBound43586371.MainJ
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# The bound in the shape of `SuperpermutationBounds.Finite`, and two values

`Cost11117297` is `SuperpermutationBounds.Cost` of `Challenge.lean` with `11117297/27675648` in place
of `43/80` and `1769507/19768320` in place of `17/240`; `Finite11117297` and `FiniteInteger11117297` are
`Finite` and `FiniteInteger` with this cost, starting at `m = 20` (22 symbols).

The two `HasWord` statements are `finite_bound22_11117297` at the best parameter `a` for 22 and 23
symbols (`ledgerC.py`).
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationBounds

/-- `SuperpermutationBounds.Cost` with the constants 11117297/27675648 and 1769507/19768320. -/
def Cost11117297 (m : ℕ) (a : ℤ) : ℚ :=
  F3 (m + 2) + (11117297 / 27675648 : ℚ) * (Nat.factorial (m - 1) : ℚ) +
    ((a : ℚ) - 2) * ((1769507 / 19768320 : ℚ) * (Nat.factorial (m - 1) : ℚ) /
      ((m : ℚ) - 1)) +
    ((m : ℚ) - (a : ℚ)) * min
      ((1769507 / 19768320 : ℚ) * (Nat.factorial (m - 1) : ℚ) / ((m : ℚ) - 1))
      ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (a + 1).toNat : ℚ))

def Finite11117297 : Prop :=
  ∀ m a : ℕ, 20 ≤ m → 2 ≤ a → a ≤ m →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost11117297 m (a : ℤ)

def FiniteInteger11117297 : Prop :=
  ∀ m : ℕ, ∀ a : ℤ, 20 ≤ m → 2 ≤ a → a ≤ (m : ℤ) →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost11117297 m a

theorem finite_11117297 : Finite11117297 := by
  intro m a hm ha ham
  obtain ⟨w, hw, hl⟩ := finite_bound22_11117297 m hm a ha ham
  refine ⟨w, hw, ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hfac1 : m + 2 - 1 = m + 1 := by omega
  have hfac2 : m + 2 - 2 = m := by omega
  have hfacA : ((a : ℤ) + 1).toNat = a + 1 := by omega
  simpa only [Cost11117297, SuperpermutationBounds.F3, hfac1, hfac2, hfacA,
    Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub ham, Nat.cast_sub hm1,
    Nat.cast_ofNat, Nat.cast_one, Int.cast_natCast, mul_div_assoc, mul_assoc] using hl

theorem finiteInteger_11117297 : FiniteInteger11117297 := by
  intro m a hm ha ham
  have h0 : 0 ≤ a := by omega
  have he : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h0
  have h := finite_11117297 m a.toNat hm (by omega) (by omega)
  rwa [he] at h

/-- 22 symbols: `m = 20`, `a = 9`. -/
theorem hasWord_twentytwo_J : HasWord 22 1177577603255664374400 := by
  obtain ⟨w, hw, hl⟩ := finite_bound22_11117297 20 (by norm_num) 9 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

/-- 23 symbols: `m = 21`, `a = 9`. -/
theorem hasWord_twentythree_J : HasWord 23 27028165642650064065600 := by
  obtain ⟨w, hw, hl⟩ := finite_bound22_11117297 21 (by norm_num) 9 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

end SuperpermutationUpperBound43586371

#print axioms SuperpermutationUpperBound43586371.finite_11117297
#print axioms SuperpermutationUpperBound43586371.finiteInteger_11117297
#print axioms SuperpermutationUpperBound43586371.hasWord_twentytwo_J
#print axioms SuperpermutationUpperBound43586371.hasWord_twentythree_J
