import ConstAsym.Main
import SuperpermutationUpperBound43586371.UniR.RRate8
import LowerBounds.TheoremBWords

/-!
# The remainder between `2 (n-4)!` and `8 (n-4)!`

For `n ≥ 2^14`:  `2 (n-4)! - 2 (n-5)! ≤ L n - F3 n ≤ (41/5) (n-4)!`, and in the limit: for every `ε > 0`,
eventually `2 - ε ≤ (L n - F3 n) / (n-4)! ≤ 8 + ε`.

* Lower side: Theorem B of `lean` (`SuperpermLowerBounds.covers_length_ge_boundB`, k ≥ 7, built on Liu's
  library), with `boundB n - F3 n ≥ 2 (n-4)! - 2 (n-5)!` (`boundB_sub_F3`, from
  `2 (n-2)! = (n² - 4n + 1)(2 (n-4)! - 2 (n-5)!) + 2 (5n - 19)(n-5)!`).
* Upper side: `SuperpermutationUpperBound43586371.UniR.rate_R8` and `rate_R8_eventually` (leanR).

`ConstAsym.remainder_order` (with `(n-4)! - 2 (n-5)!` and `9 (n-4)!`) is unchanged.
-/

namespace ConstAsym

open SuperpermutationBounds

/-- Theorem B's bound exceeds `F3 n` by at least `2 (n-4)! - 2 (n-5)!`, for `n ≥ 7`. -/
theorem boundB_sub_F3 {n : ℕ} (hn : 7 ≤ n) :
    2 * ((n - 4).factorial : ℚ) - 2 * ((n - 5).factorial : ℚ) ≤
      (SuperpermLowerBounds.boundB n : ℚ) - F3 n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have hd : (m + 5) * (m + 5) - 4 * (m + 5) + 1 = m * m + 6 * m + 6 := by
    have : (m + 5) * (m + 5) = m * m + 10 * m + 25 := by ring
    omega
  have h2 : m + 5 - 2 = m + 3 := by omega
  have hself : m + 3 ≤ (m + 3).factorial := Nat.self_le_factorial _
  set x := 2 * ((m + 3).factorial - (m + 3)) with hx
  set d := m * m + 6 * m + 6 with hdd
  have hd0 : 0 < d := by omega
  obtain ⟨q, hqd⟩ : ∃ q, q = (2 * ((m + 3).factorial - (m + 3)) + d - 1) / d := ⟨_, rfl⟩
  -- the ceiling: x ≤ q * d
  have hq : x ≤ q * d := by
    have h1 := Nat.div_add_mod (x + d - 1) d
    have h2' := Nat.mod_lt (x + d - 1) hd0
    have hq' : (x + d - 1) / d = q := by rw [hqd, hx]
    rw [hq'] at h1
    rw [Nat.mul_comm q d]
    generalize (x + d - 1) % d = r at h1 h2'
    generalize d * q = P at h1 ⊢
    omega
  -- boundB in these terms
  have hB : SuperpermLowerBounds.boundB (m + 5) + 3 =
      (m + 5).factorial + (m + 4).factorial + (m + 3).factorial + (m + 5) + q := by
    unfold SuperpermLowerBounds.boundB SuperpermLowerBounds.hpv
    rw [hd, h2, ← hqd, show m + 5 - 1 = m + 4 by omega]
    omega
  have hBQ : (SuperpermLowerBounds.boundB (m + 5) : ℚ) =
      (m + 5).factorial + (m + 4).factorial + (m + 3).factorial + ((m : ℚ) + 2) + q := by
    have := congrArg (fun t : ℕ => (t : ℚ)) hB
    push_cast at this
    linarith
  have hF : F3 (m + 5) = (m + 5).factorial + (m + 4).factorial + (m + 3).factorial := by
    unfold F3
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega]
  rw [hBQ, hF, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega]
  -- the arithmetic
  have f3 : ((m + 3).factorial : ℚ) = (m + 3) * (m + 2) * (m + 1) * (m.factorial : ℚ) := by
    simp [Nat.factorial_succ]; push_cast; ring
  have f1 : ((m + 1).factorial : ℚ) = (m + 1) * (m.factorial : ℚ) := by
    simp [Nat.factorial_succ]
  have hxQ : (x : ℚ) = 2 * ((m + 3).factorial : ℚ) - 2 * ((m : ℚ) + 3) := by
    rw [hx, Nat.cast_mul, Nat.cast_sub hself]; push_cast; ring
  have hdQ : (d : ℚ) = (m : ℚ) * m + 6 * m + 6 := by rw [hdd]; push_cast; ring
  have hqQ : (x : ℚ) ≤ (q : ℚ) * d := by exact_mod_cast hq
  rw [hxQ, f3, hdQ] at hqQ
  rw [f1]
  have hM : (0 : ℚ) ≤ (m.factorial : ℚ) := by positivity
  have hm0 : (0 : ℚ) ≤ m := by positivity
  have hdpos : (0 : ℚ) < (m : ℚ) * m + 6 * m + 6 := by positivity
  -- (q + m + 2) d ≥ 2 m m! d
  have key : (2 * (m : ℚ) * (m.factorial : ℚ)) * ((m : ℚ) * m + 6 * m + 6) ≤
      ((q : ℚ) + (m + 2)) * ((m : ℚ) * m + 6 * m + 6) := by
    have e : ((q : ℚ) + (m + 2)) * ((m : ℚ) * m + 6 * m + 6) =
        (q : ℚ) * ((m : ℚ) * m + 6 * m + 6) + (m + 2) * ((m : ℚ) * m + 6 * m + 6) := by ring
    rw [e]
    have : (0 : ℚ) ≤ (10 * m + 12) * (m.factorial : ℚ) := by positivity
    nlinarith
  have := le_of_mul_le_mul_right key hdpos
  linarith

/-- **Lower side 2.**  For `n ≥ 7`: `2 (n-4)! - 2 (n-5)! ≤ L n - F3 n` (Theorem B). -/
theorem lower2_L {n : ℕ} (hn : 7 ≤ n) :
    2 * ((n - 4).factorial : ℚ) - 2 * ((n - 5).factorial : ℚ) ≤ (L n : ℚ) - F3 n := by
  obtain ⟨w, hw, hlen⟩ := L_spec n
  have h := SuperpermLowerBounds.covers_length_ge_boundB hn w hw
  have hB : (SuperpermLowerBounds.boundB n : ℚ) ≤ (L n : ℚ) := by
    rw [← hlen]; exact_mod_cast h
  linarith [boundB_sub_F3 hn]

/-- **The remainder between 2 and 8.**  For `n ≥ 2^14`:
`2 (n-4)! - 2 (n-5)! ≤ L n - (n! + (n-1)! + (n-2)!) ≤ (41/5) (n-4)!`. -/
theorem remainder_order8 (n : ℕ) (hn : 2 ^ 14 ≤ n) :
    2 * ((n - 4).factorial : ℚ) - 2 * ((n - 5).factorial : ℚ) ≤ (L n : ℚ) - F3 n ∧
    (L n : ℚ) - F3 n ≤ 41 / 5 * ((n - 4).factorial : ℚ) := by
  refine ⟨lower2_L (le_trans (by norm_num) hn), ?_⟩
  obtain ⟨w, hw, hl⟩ := SuperpermutationUpperBound43586371.UniR.rate_R8 n hn
  have hL : (L n : ℚ) ≤ w.length := by exact_mod_cast L_le_length hw
  linarith

/-- The lower side as a ratio: `2 - 2/(n-4) ≤ (L n - F3 n)/(n-4)!` for `n ≥ 7`. -/
theorem lower2_ratio {n : ℕ} (hn : 7 ≤ n) :
    2 - 2 / ((n : ℚ) - 4) ≤ ((L n : ℚ) - F3 n) / ((n - 4).factorial : ℚ) := by
  have h1 := lower2_L hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega, Nat.factorial_succ m] at h1
  rw [show m + 5 - 4 = m + 1 by omega, Nat.factorial_succ m]
  push_cast at h1 ⊢
  have hx : (0 : ℚ) < (m.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos m
  have hf : (0 : ℚ) < ((m : ℚ) + 1) * (m.factorial : ℚ) := by positivity
  have hm1 : (m : ℚ) + 5 - 4 = (m : ℚ) + 1 := by ring
  rw [hm1, le_div_iff₀ hf]
  have e : (2 - 2 / ((m : ℚ) + 1)) * (((m : ℚ) + 1) * (m.factorial : ℚ))
      = 2 * (((m : ℚ) + 1) * (m.factorial : ℚ)) - 2 * (m.factorial : ℚ) := by
    field_simp
  linarith

/-- **Corollary.**  For `n ≥ 2^14`, `2 - 2/(n-4) ≤ (L n - F3 n) / (n-4)! ≤ 41/5`. -/
theorem remainder_ratio8 (n : ℕ) (hn : 2 ^ 14 ≤ n) :
    2 - 2 / ((n : ℚ) - 4) ≤ ((L n : ℚ) - F3 n) / ((n - 4).factorial : ℚ) ∧
    ((L n : ℚ) - F3 n) / ((n - 4).factorial : ℚ) ≤ 41 / 5 := by
  refine ⟨lower2_ratio (le_trans (by norm_num) hn), ?_⟩
  have h2 := (remainder_order8 n hn).2
  have hf : (0 : ℚ) < ((n - 4).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_iff₀ hf]
  linarith

/-- **The limit form.**  For every `ε > 0`, for all large `n`:
`2 - ε ≤ (L n - F3 n) / (n-4)! ≤ 8 + ε`  (lim inf ≥ 2, lim sup ≤ 8). -/
theorem remainder_limit8 (ε : ℚ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    2 - ε ≤ ((L n : ℚ) - F3 n) / ((n - 4).factorial : ℚ) ∧
    ((L n : ℚ) - F3 n) / ((n - 4).factorial : ℚ) ≤ 8 + ε := by
  obtain ⟨N1, hN1⟩ := SuperpermutationUpperBound43586371.UniR.rate_R8_eventually ε hε
  obtain ⟨N2, hN2⟩ := exists_nat_gt (2 / ε + 5)
  refine ⟨max (max N1 N2) 7, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn7 : 7 ≤ n := le_trans (le_max_right _ _) hn
  have hf : (0 : ℚ) < ((n - 4).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  constructor
  · have hl := lower2_ratio hn7
    have hnQ : (2 / ε + 5 : ℚ) < n := by
      have : (N2 : ℚ) ≤ n := by exact_mod_cast hn2
      linarith
    have hpos : (0 : ℚ) < (n : ℚ) - 4 := by
      have : (0 : ℚ) ≤ 2 / ε := by positivity
      linarith
    have : 2 / ((n : ℚ) - 4) ≤ ε := by
      rw [div_le_iff₀ hpos]
      have h2 : 2 / ε * ε = 2 := by field_simp
      have : 2 / ε < (n : ℚ) - 4 := by linarith
      nlinarith
    linarith
  · obtain ⟨w, hw, hlw⟩ := hN1 n hn1
    have hL : (L n : ℚ) ≤ w.length := by exact_mod_cast L_le_length hw
    rw [div_le_iff₀ hf]
    linarith

end ConstAsym

#print axioms ConstAsym.boundB_sub_F3
#print axioms ConstAsym.lower2_L
#print axioms ConstAsym.remainder_order8
#print axioms ConstAsym.lower2_ratio
#print axioms ConstAsym.remainder_ratio8
#print axioms ConstAsym.remainder_limit8
