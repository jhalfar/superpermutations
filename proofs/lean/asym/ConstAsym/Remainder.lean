import ConstAsym.Main
import SuperpermutationUpperBound43586371.UniR.RRate

/-!
# The order of the remainder: `L(n) = n! + (n-1)! + (n-2)! + Θ((n-4)!)`

For `n ≥ 2^14`:
`(n-4)! - 2 (n-5)! ≤ L n - F3 n ≤ 9 (n-4)!`, hence `(L n - F3 n) / (n-4)!` lies in `[1 - 2/(n-4), 9] ⊆ [1/2, 9]`.

* Lower side: `ConstAsym.hunter_lower_L` (Hunter–Raudvere, `Hunter.Paper.factorial_clean`, n ≥ 6).
* Upper side: `SuperpermutationUpperBound43586371.UniR.rate_R` (leanR):
  a covering word of length at most `F3 n + (9/n) (n-3)!` for `n ≥ 2^14`, and `(9/n)(n-3)! = 9 (n-3)/n (n-4)! ≤ 9 (n-4)!`.
-/

namespace ConstAsym

open SuperpermutationBounds

/-- `(9/n) (n-3)! ≤ 9 (n-4)!` for `n ≥ 4`. -/
theorem nine_div_le {n : ℕ} (hn : 4 ≤ n) :
    9 / (n : ℚ) * ((n - 3).factorial : ℚ) ≤ 9 * ((n - 4).factorial : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega, Nat.factorial_succ]
  push_cast
  have hx : (0 : ℚ) ≤ (m.factorial : ℚ) := by positivity
  have hpos : (0 : ℚ) < (m : ℚ) + 4 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith

/-- **The order of the remainder.**  For `n ≥ 2^14`:
`(n-4)! - 2 (n-5)! ≤ L n - (n! + (n-1)! + (n-2)!) ≤ 9 (n-4)!`. -/
theorem remainder_order (n : ℕ) (hn : 2 ^ 14 ≤ n) :
    ((n - 4).factorial : ℚ) - 2 * ((n - 5).factorial : ℚ) ≤ (L n : ℚ) - F3 n ∧
    (L n : ℚ) - F3 n ≤ 9 * ((n - 4).factorial : ℚ) := by
  have h6 : 6 ≤ n := le_trans (by norm_num) hn
  refine ⟨by linarith [hunter_lower_L h6], ?_⟩
  obtain ⟨w, hw, hl⟩ := SuperpermutationUpperBound43586371.UniR.rate_R n hn
  have hL : (L n : ℚ) ≤ w.length := by exact_mod_cast L_le_length hw
  have h9 := nine_div_le (n := n) (by omega)
  linarith

/-- **Corollary.**  For `n ≥ 2^14`, `1 - 2/(n-4) ≤ (L n - F3 n) / (n-4)! ≤ 9`. -/
theorem remainder_ratio (n : ℕ) (hn : 2 ^ 14 ≤ n) :
    1 - 2 / ((n : ℚ) - 4) ≤ ((L n : ℚ) - F3 n) / ((n - 4).factorial : ℚ) ∧
    ((L n : ℚ) - F3 n) / ((n - 4).factorial : ℚ) ≤ 9 := by
  obtain ⟨h1, h2⟩ := remainder_order n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e4 : m + 5 - 4 = m + 1 := by omega
  have e5 : m + 5 - 5 = m := by omega
  rw [e4, e5, Nat.factorial_succ m] at h1
  rw [e4, Nat.factorial_succ m] at h2
  rw [e4, Nat.factorial_succ m]
  push_cast at h1 h2 ⊢
  have hx : (0 : ℚ) < (m.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos m
  have hf : (0 : ℚ) < ((m : ℚ) + 1) * (m.factorial : ℚ) := by positivity
  have hm1 : (m : ℚ) + 5 - 4 = (m : ℚ) + 1 := by ring
  rw [hm1]
  constructor
  · rw [le_div_iff₀ hf]
    have e : (1 - 2 / ((m : ℚ) + 1)) * (((m : ℚ) + 1) * (m.factorial : ℚ))
        = ((m : ℚ) + 1) * (m.factorial : ℚ) - 2 * (m.factorial : ℚ) := by
      field_simp
    linarith
  · rw [div_le_iff₀ hf]
    linarith

/-- **Corollary, simple constants.**  For `n ≥ 2^14`, `1/2 ≤ (L n - F3 n) / (n-4)! ≤ 9`:
`L(n) = n! + (n-1)! + (n-2)! + Θ((n-4)!)`. -/
theorem remainder_ratio_half (n : ℕ) (hn : 2 ^ 14 ≤ n) :
    (1 / 2 : ℚ) ≤ ((L n : ℚ) - F3 n) / ((n - 4).factorial : ℚ) ∧
    ((L n : ℚ) - F3 n) / ((n - 4).factorial : ℚ) ≤ 9 := by
  obtain ⟨h1, h2⟩ := remainder_ratio n hn
  refine ⟨le_trans ?_ h1, h2⟩
  have hn' : (2 ^ 14 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hpos : (0 : ℚ) < (n : ℚ) - 4 := by linarith
  have : 2 / ((n : ℚ) - 4) ≤ 1 / 2 := by
    rw [div_le_iff₀ hpos]
    linarith
  linarith

end ConstAsym

#print axioms ConstAsym.remainder_order
#print axioms ConstAsym.remainder_ratio
#print axioms ConstAsym.remainder_ratio_half
#print axioms ConstAsym.shortest_superpermutation_coefficient
