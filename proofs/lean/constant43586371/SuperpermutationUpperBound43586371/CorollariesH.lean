import SuperpermutationUpperBound43586371.MainH
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# The bound in the shape of `SuperpermutationBounds.Finite`, and two values

`Cost629507` is `SuperpermutationBounds.Cost` of `Challenge.lean` with `629507/1441440` in place
of `43/80` and `32759/288288` in place of `17/240`; `Finite629507` and `FiniteInteger629507` are
`Finite` and `FiniteInteger` with this cost, starting at `m = 20` (22 symbols).

The two `HasWord` statements are `finite_bound22_629507` at the best parameter `a` for 22 and 23
symbols (`ledgerC.py`).
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationBounds

/-- `SuperpermutationBounds.Cost` with the constants 629507/1441440 and 32759/288288. -/
def Cost629507 (m : ℕ) (a : ℤ) : ℚ :=
  F3 (m + 2) + (629507 / 1441440 : ℚ) * (Nat.factorial (m - 1) : ℚ) +
    ((a : ℚ) - 2) * ((32759 / 288288 : ℚ) * (Nat.factorial (m - 1) : ℚ) /
      ((m : ℚ) - 1)) +
    ((m : ℚ) - (a : ℚ)) * min
      ((32759 / 288288 : ℚ) * (Nat.factorial (m - 1) : ℚ) / ((m : ℚ) - 1))
      ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (a + 1).toNat : ℚ))

def Finite629507 : Prop :=
  ∀ m a : ℕ, 20 ≤ m → 2 ≤ a → a ≤ m →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost629507 m (a : ℤ)

def FiniteInteger629507 : Prop :=
  ∀ m : ℕ, ∀ a : ℤ, 20 ≤ m → 2 ≤ a → a ≤ (m : ℤ) →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost629507 m a

theorem finite_629507 : Finite629507 := by
  intro m a hm ha ham
  obtain ⟨w, hw, hl⟩ := finite_bound22_629507 m hm a ha ham
  refine ⟨w, hw, ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hfac1 : m + 2 - 1 = m + 1 := by omega
  have hfac2 : m + 2 - 2 = m := by omega
  have hfacA : ((a : ℤ) + 1).toNat = a + 1 := by omega
  simpa only [Cost629507, SuperpermutationBounds.F3, hfac1, hfac2, hfacA,
    Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub ham, Nat.cast_sub hm1,
    Nat.cast_ofNat, Nat.cast_one, Int.cast_natCast, mul_div_assoc, mul_assoc] using hl

theorem finiteInteger_629507 : FiniteInteger629507 := by
  intro m a hm ha ham
  have h0 : 0 ≤ a := by omega
  have he : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h0
  have h := finite_629507 m a.toNat hm (by omega) (by omega)
  rwa [he] at h

/-- 22 symbols: `m = 20`, `a = 9`. -/
theorem hasWord_twentytwo_H : HasWord 22 1177582944431453414400 := by
  obtain ⟨w, hw, hl⟩ := finite_bound22_629507 20 (by norm_num) 9 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

/-- 23 symbols: `m = 21`, `a = 9`. -/
theorem hasWord_twentythree_H : HasWord 23 27028271385160615987200 := by
  obtain ⟨w, hw, hl⟩ := finite_bound22_629507 21 (by norm_num) 9 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

end SuperpermutationUpperBound43586371

#print axioms SuperpermutationUpperBound43586371.finite_629507
#print axioms SuperpermutationUpperBound43586371.finiteInteger_629507
#print axioms SuperpermutationUpperBound43586371.hasWord_twentytwo_H
#print axioms SuperpermutationUpperBound43586371.hasWord_twentythree_H
