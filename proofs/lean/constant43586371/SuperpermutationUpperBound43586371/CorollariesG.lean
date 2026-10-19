import SuperpermutationUpperBound43586371.MainG
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# The bound in the shape of `SuperpermutationBounds.Finite`, and two values

`Cost21736511` is `SuperpermutationBounds.Cost` of `Challenge.lean` with `21736511/43243200` in place
of `43/80` and `56491/8648640` in place of `17/240`; `Finite21736511` and `FiniteInteger21736511` are
`Finite` and `FiniteInteger` with this cost, starting at `m = 20` (22 symbols).

The two `HasWord` statements are `finite_bound22_21736511` at the best parameter `a` for 22 and 23
symbols (`ledgerC.py`).
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationBounds

/-- `SuperpermutationBounds.Cost` with the constants 21736511/43243200 and 56491/8648640. -/
def Cost21736511 (m : ℕ) (a : ℤ) : ℚ :=
  F3 (m + 2) + (21736511 / 43243200 : ℚ) * (Nat.factorial (m - 1) : ℚ) +
    ((a : ℚ) - 2) * ((56491 / 8648640 : ℚ) * (Nat.factorial (m - 1) : ℚ) /
      ((m : ℚ) - 1)) +
    ((m : ℚ) - (a : ℚ)) * min
      ((56491 / 8648640 : ℚ) * (Nat.factorial (m - 1) : ℚ) / ((m : ℚ) - 1))
      ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (a + 1).toNat : ℚ))

def Finite21736511 : Prop :=
  ∀ m a : ℕ, 20 ≤ m → 2 ≤ a → a ≤ m →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost21736511 m (a : ℤ)

def FiniteInteger21736511 : Prop :=
  ∀ m : ℕ, ∀ a : ℤ, 20 ≤ m → 2 ≤ a → a ≤ (m : ℤ) →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost21736511 m a

theorem finite_21736511 : Finite21736511 := by
  intro m a hm ha ham
  obtain ⟨w, hw, hl⟩ := finite_bound22_21736511 m hm a ha ham
  refine ⟨w, hw, ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hfac1 : m + 2 - 1 = m + 1 := by omega
  have hfac2 : m + 2 - 2 = m := by omega
  have hfacA : ((a : ℤ) + 1).toNat = a + 1 := by omega
  simpa only [Cost21736511, SuperpermutationBounds.F3, hfac1, hfac2, hfacA,
    Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub ham, Nat.cast_sub hm1,
    Nat.cast_ofNat, Nat.cast_one, Int.cast_natCast, mul_div_assoc, mul_assoc] using hl

theorem finiteInteger_21736511 : FiniteInteger21736511 := by
  intro m a hm ha ham
  have h0 : 0 ≤ a := by omega
  have he : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h0
  have h := finite_21736511 m a.toNat hm (by omega) (by omega)
  rwa [he] at h

/-- 22 symbols: `m = 20`, `a = 10`. -/
theorem hasWord_twentytwo_G : HasWord 22 1177586065108048296960 := by
  obtain ⟨w, hw, hl⟩ := finite_bound22_21736511 20 (by norm_num) 10 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

/-- 23 symbols: `m = 21`, `a = 10`. -/
theorem hasWord_twentythree_G : HasWord 23 27028337991051598387200 := by
  obtain ⟨w, hw, hl⟩ := finite_bound22_21736511 21 (by norm_num) 10 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

end SuperpermutationUpperBound43586371

#print axioms SuperpermutationUpperBound43586371.finite_21736511
#print axioms SuperpermutationUpperBound43586371.finiteInteger_21736511
#print axioms SuperpermutationUpperBound43586371.hasWord_twentytwo_G
#print axioms SuperpermutationUpperBound43586371.hasWord_twentythree_G
