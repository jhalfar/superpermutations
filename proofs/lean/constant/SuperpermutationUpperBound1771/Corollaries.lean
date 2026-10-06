import SuperpermutationUpperBound1771.Main
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# The bound in the shape of `SuperpermutationBounds.Finite`, and three values

`Cost1771` is `SuperpermutationBounds.Cost` of `Challenge.lean` with `1771/3456` in place of
`43/80` and `25/1152` in place of `17/240`; `Finite1771` and `FiniteInteger1771` are `Finite`
and `FiniteInteger` with this cost, starting at `m = 11` (13 symbols).

The three `HasWord` statements are `finite_bound` at the best parameter `a` for 14, 15 and 16
symbols.  The value for 13 symbols is `word_thirteen`.
-/

namespace SuperpermutationUpperBound1771

open SuperpermutationBounds

/-- `SuperpermutationBounds.Cost` with the constants of the selection with blocks. -/
def Cost1771 (m : ℕ) (a : ℤ) : ℚ :=
  F3 (m + 2) + (1771 / 3456 : ℚ) * (Nat.factorial (m - 1) : ℚ) +
    ((a : ℚ) - 2) * ((25 / 1152 : ℚ) * (Nat.factorial (m - 1) : ℚ) /
      ((m : ℚ) - 1)) +
    ((m : ℚ) - (a : ℚ)) * min
      ((25 / 1152 : ℚ) * (Nat.factorial (m - 1) : ℚ) / ((m : ℚ) - 1))
      ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (a + 1).toNat : ℚ))

def Finite1771 : Prop :=
  ∀ m a : ℕ, 11 ≤ m → 2 ≤ a → a ≤ m →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost1771 m (a : ℤ)

def FiniteInteger1771 : Prop :=
  ∀ m : ℕ, ∀ a : ℤ, 11 ≤ m → 2 ≤ a → a ≤ (m : ℤ) →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost1771 m a

theorem finite_1771 : Finite1771 := by
  intro m a hm ha ham
  obtain ⟨w, hw, hl⟩ := finite_bound m hm a ha ham
  refine ⟨w, hw, ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hfac1 : m + 2 - 1 = m + 1 := by omega
  have hfac2 : m + 2 - 2 = m := by omega
  have hfacA : ((a : ℤ) + 1).toNat = a + 1 := by omega
  simpa only [Cost1771, SuperpermutationBounds.F3, hfac1, hfac2, hfacA,
    Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub ham, Nat.cast_sub hm1,
    Nat.cast_ofNat, Nat.cast_one, Int.cast_natCast, mul_div_assoc, mul_assoc] using hl

theorem finiteInteger_1771 : FiniteInteger1771 := by
  intro m a hm ha ham
  have h0 : 0 ≤ a := by omega
  have he : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h0
  have h := finite_1771 m a.toNat hm (by omega) (by omega)
  rwa [he] at h

/-- 14 symbols: `m = 12`, `a = 8`. -/
theorem hasWord_fourteen : HasWord 14 93905309790 := by
  obtain ⟨w, hw, hl⟩ := finite_bound 12 (by norm_num) 8 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

/-- 15 symbols: `m = 13`, `a = 9`. -/
theorem hasWord_fifteen : HasWord 15 1401331300446 := by
  obtain ⟨w, hw, hl⟩ := finite_bound 13 (by norm_num) 9 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

/-- 16 symbols: `m = 14`, `a = 9`. -/
theorem hasWord_sixteen : HasWord 16 22320908101800 := by
  obtain ⟨w, hw, hl⟩ := finite_bound 14 (by norm_num) 9 (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

end SuperpermutationUpperBound1771

#print axioms SuperpermutationUpperBound1771.finite_1771
#print axioms SuperpermutationUpperBound1771.finiteInteger_1771
#print axioms SuperpermutationUpperBound1771.hasWord_fourteen
#print axioms SuperpermutationUpperBound1771.hasWord_fifteen
#print axioms SuperpermutationUpperBound1771.hasWord_sixteen
