import SuperpermutationUpperBound305989.MainB
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# The bound in the shape of `SuperpermutationBounds.Finite`, and two values

`Cost305989` is `SuperpermutationBounds.Cost` of `Challenge.lean` with `305989/604800` in place
of `43/80` and `23333/2217600` in place of `17/240`; `Finite305989` and `FiniteInteger305989` are
`Finite` and `FiniteInteger` with this cost, starting at `m = 14` (16 symbols).

The two `HasWord` statements are `finite_bound16` at the best parameter `a` for 16 and 17
symbols.
-/

namespace SuperpermutationUpperBound305989

open SuperpermutationBounds

/-- `SuperpermutationBounds.Cost` with the constants 305989/604800 and 23333/2217600. -/
def Cost305989 (m : ℕ) (a : ℤ) : ℚ :=
  F3 (m + 2) + (305989 / 604800 : ℚ) * (Nat.factorial (m - 1) : ℚ) +
    ((a : ℚ) - 2) * ((23333 / 2217600 : ℚ) * (Nat.factorial (m - 1) : ℚ) /
      ((m : ℚ) - 1)) +
    ((m : ℚ) - (a : ℚ)) * min
      ((23333 / 2217600 : ℚ) * (Nat.factorial (m - 1) : ℚ) / ((m : ℚ) - 1))
      ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (a + 1).toNat : ℚ))

def Finite305989 : Prop :=
  ∀ m a : ℕ, 14 ≤ m → 2 ≤ a → a ≤ m →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost305989 m (a : ℤ)

def FiniteInteger305989 : Prop :=
  ∀ m : ℕ, ∀ a : ℤ, 14 ≤ m → 2 ≤ a → a ≤ (m : ℤ) →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost305989 m a

theorem finite_305989 : Finite305989 := by
  intro m a hm ha ham
  obtain ⟨w, hw, hl⟩ := finite_bound16 m hm a ha ham
  refine ⟨w, hw, ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hfac1 : m + 2 - 1 = m + 1 := by omega
  have hfac2 : m + 2 - 2 = m := by omega
  have hfacA : ((a : ℤ) + 1).toNat = a + 1 := by omega
  simpa only [Cost305989, SuperpermutationBounds.F3, hfac1, hfac2, hfacA,
    Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub ham, Nat.cast_sub hm1,
    Nat.cast_ofNat, Nat.cast_one, Int.cast_natCast, mul_div_assoc, mul_assoc] using hl

theorem finiteInteger_305989 : FiniteInteger305989 := by
  intro m a hm ha ham
  have h0 : 0 ≤ a := by omega
  have he : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h0
  have h := finite_305989 m a.toNat hm (by omega) (by omega)
  rwa [he] at h

/-- 16 symbols: `m = 14`, `a = 9`. -/
theorem hasWord_sixteen_B : HasWord 16 22320830091240 := by
  obtain ⟨w, hw, hl⟩ := finite_bound16 14 (by norm_num) 9 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

/-- 17 symbols: `m = 15`, `a = 9`. -/
theorem hasWord_seventeen_B : HasWord 17 377962492058424 := by
  obtain ⟨w, hw, hl⟩ := finite_bound16 15 (by norm_num) 9 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

/-- 18 symbols: `m = 16`, `a = 9`. -/
theorem hasWord_eighteen_B : HasWord 18 6779652627881952 := by
  obtain ⟨w, hw, hl⟩ := finite_bound16 16 (by norm_num) 9 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

end SuperpermutationUpperBound305989

#print axioms SuperpermutationUpperBound305989.finite_305989
#print axioms SuperpermutationUpperBound305989.finiteInteger_305989
#print axioms SuperpermutationUpperBound305989.hasWord_sixteen_B
#print axioms SuperpermutationUpperBound305989.hasWord_seventeen_B
#print axioms SuperpermutationUpperBound305989.hasWord_eighteen_B
