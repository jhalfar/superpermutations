import SuperpermutationUpperBound43586371.UniR.RRate

/-!
# The rate with the sharp constant 8 at `(n-4)!`

`RRate.lean` bounds charge + cycles per level by `(17/2) N / a`.  In fact `charge / rows = 8/(a+12)`, and the
slack `8·12·2|G|a` absorbs the cycles as soon as `a + 2 ≤ 24 |G|` (true for `a ≥ 9`): per level `a ≥ 49`,
`(charge + cycles) · a ≤ 8 · rows`.  The invariant becomes `x + (8/m0) p ≤ 8/m0`, so
`κ + γ ≤ 8/m0 + 2 (3/4)^K + 8K/m0²`, and with `K = 5 log₂ n`, `m0 = n - 3 - 3K`:
`(κ + γ) n ≤ 8 + 164 (log₂ n + 1)/n`.  Hence a covering word of length at most
`F3 n + (41/5)(n-4)!` for every `n ≥ 2^14`, and `F3 n + (8 + ε)(n-4)!` for all large `n`.
Nothing in `RRate.lean` is changed; this file only adds theorems.
-/

namespace SuperpermutationUpperBound43586371.UniR

open SuperpermutationUpperBound
open SuperpermutationUpperBound43586371.Uniform

/-- Charge and cycles of one level are at most `8 · rows / a`. -/
theorem cost_le8 (a : Nat) (ha : 49 ≤ a) :
    (chargeR a + (a + 2) * ncycR a) * a ≤ 8 * rowsR a := by
  rw [rowsR_eq, chargeR_eq]
  have hG := Gl_len_ge a (by omega)
  have h6 : a ≤ 6 * (Gl a).length + 6 := by omega
  have hn := ncycR_le a
  generalize (Gl a).length = G at h6
  generalize ncycR a = c at hn
  have h24 : a + 2 ≤ 24 * G := by omega
  have h1 : (a + 2) * c ≤ (a + 2) * 8 := Nat.mul_le_mul_left _ hn
  have h3 : (a + 2) * c ≤ 192 * G := by nlinarith
  have h4 : (a + 2) * c * a ≤ 192 * G * a := Nat.mul_le_mul_right _ h3
  nlinarith

theorem invariants8 (m0 : Nat) (hm : 49 ≤ m0) : ∀ K,
    Xr m0 K + 8 / (m0 : ℚ) * Pr m0 K ≤ 8 / (m0 : ℚ) ∧ Pr m0 K ≤ (3 / 4) ^ K ∧
      Xcr m0 K ≤ 8 * K / ((m0 : ℚ) * m0) := by
  have hm0 : (0 : ℚ) < m0 := by exact_mod_cast (show 0 < m0 by omega)
  intro K
  induction K with
  | zero =>
    have hP : Pr m0 0 = 1 := by
      unfold Pr; simp only [cntR, Nat.mul_zero, Nat.add_zero]
      have : ((m0 - 1).factorial : ℚ) ≠ 0 := by positivity
      field_simp
    have hX : Xr m0 0 = 0 := by unfold Xr; simp [cntR]
    have hXc : Xcr m0 0 = 0 := by unfold Xcr; simp [cntR]
    rw [hP, hX, hXc]; norm_num
  | succ K ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    set a := m0 + 3 * K with ha
    have hrows := rowsR_le a (by omega)
    obtain ⟨sX, sXc, sP⟩ := step_rec m0 K a (by omega) ha hrows
    have haQ : (m0 : ℚ) ≤ a := by exact_mod_cast (show m0 ≤ a by omega)
    have hL : (0 : ℚ) < (a : ℚ) * ((a + 1) * (a + 2)) := by positivity
    set L : ℚ := (a : ℚ) * ((a + 1) * (a + 2)) with hLdef
    have hq := rows_quarter a (by omega)
    have hc := cost_le8 a (by omega)
    have hqQ : L ≤ 4 * (rowsR a : ℚ) := by rw [hLdef]; exact_mod_cast hq
    have hcQ : ((chargeR a : ℚ) + (a + 2) * ncycR a) * a ≤ 8 * (rowsR a : ℚ) := by exact_mod_cast hc
    have hrQ : (rowsR a : ℚ) ≤ L := by rw [hLdef]; exact_mod_cast hrows
    have hP0 := Pr_nonneg m0 K
    have hn8 : (ncycR a : ℚ) ≤ 8 := by exact_mod_cast ncycR_le a
    refine ⟨?_, ?_, ?_⟩
    · rw [sX, sP]
      have hC0 : (0 : ℚ) ≤ (chargeR a : ℚ) + (a + 2) * ncycR a := by positivity
      have hcost : ((chargeR a : ℚ) + (a + 2) * ncycR a) ≤ 8 / (m0 : ℚ) * rowsR a := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
        have := mul_le_mul_of_nonneg_left haQ hC0
        linarith
      have : Pr m0 K * ((chargeR a : ℚ) + (a + 2) * ncycR a) / L + 8 / (m0 : ℚ) * (Pr m0 K * (L - rowsR a) / L)
          ≤ 8 / (m0 : ℚ) * Pr m0 K := by
        rw [mul_div_assoc', ← add_div, div_le_iff₀ hL]
        have h1 := mul_le_mul_of_nonneg_left hcost hP0
        have e : 8 / (m0 : ℚ) * (Pr m0 K * (L - rowsR a)) + Pr m0 K * (8 / (m0 : ℚ) * rowsR a)
            = 8 / (m0 : ℚ) * Pr m0 K * L := by ring
        nlinarith
      linarith
    · rw [sP, pow_succ]
      rw [div_le_iff₀ hL]
      have : Pr m0 K * (L - rowsR a) ≤ Pr m0 K * (3 / 4 * L) := by
        apply mul_le_mul_of_nonneg_left _ hP0; linarith
      have h34 : Pr m0 K * (3 / 4 * L) ≤ (3 / 4) ^ K * (3 / 4) * L := by
        have := mul_le_mul_of_nonneg_right i2 (show (0 : ℚ) ≤ 3 / 4 * L by positivity)
        linarith
      linarith
    · exact (invariants m0 hm (K + 1)).2.2

theorem coef_bound8 (m0 K : Nat) (hm : 49 ≤ m0) :
    kappaR m0 K + gammaR m0 K ≤ 8 / (m0 : ℚ) + 2 * (3 / 4) ^ K + 8 * K / ((m0 : ℚ) * m0) := by
  obtain ⟨i1, i2, i3⟩ := invariants8 m0 hm K
  rw [kappaR_eq, gammaR_eq]
  have hP0 := Pr_nonneg m0 K
  have hm0 : (0 : ℚ) < m0 := by exact_mod_cast (show 0 < m0 by omega)
  have : 0 ≤ 8 / (m0 : ℚ) * Pr m0 K := by positivity
  linarith

/-- With `L = ⌊log₂ n⌋`, `K = 5L`, `m0 = n - 3 - 3K` (the parameters of `rate_R`):
`(κ + γ) · n ≤ 8 + 164 (L + 1) / n` for every `n ≥ 2^14`. -/
theorem coef_n_bound8 (n : Nat) (hn : 2 ^ 14 ≤ n) :
    (kappaR (n - 3 - 3 * (5 * Nat.log 2 n)) (5 * Nat.log 2 n) +
        gammaR (n - 3 - 3 * (5 * Nat.log 2 n)) (5 * Nat.log 2 n)) * n ≤
      8 + 164 * ((Nat.log 2 n : ℚ) + 1) / n := by
  set L := Nat.log 2 n with hLd
  have hn0 : n ≠ 0 := by omega
  have hL14 : 14 ≤ L := Nat.le_log_of_pow_le (by norm_num) hn
  have hpow : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn0
  have hlt : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hg := grow64 L hL14
  set K := 5 * L with hK
  set m0 := n - 3 - 3 * K with hm0d
  have hm0 : 64 * m0 ≥ 63 * n := by omega
  have hm49 : 49 ≤ m0 := by omega
  have hsum : m0 + (15 * L + 3) = n := by omega
  have hcb := coef_bound8 m0 K hm49
  have hnQ : (2 ^ 14 : ℚ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℚ) < n := by linarith
  have hm0Q : 63 * (n : ℚ) ≤ 64 * m0 := by exact_mod_cast hm0
  have hm0pos : (0 : ℚ) < m0 := by
    have : (49 : ℚ) ≤ m0 := by exact_mod_cast hm49
    linarith
  have hsumQ : (m0 : ℚ) + (15 * L + 3) = n := by exact_mod_cast hsum
  have hpowQ : (n : ℚ) < 2 * 2 ^ L := by
    have : (n : ℚ) < (2 : ℚ) ^ (L + 1) := by exact_mod_cast hlt
    rw [pow_succ] at this; linarith
  have h34 : (3 / 4 : ℚ) ^ K ≤ 4 / ((n : ℚ) * n) := by
    rw [hK, pow_mul]
    have h1 : ((3 / 4 : ℚ) ^ 5) ^ L ≤ (1 / 4) ^ L := pow_le_pow_left₀ (by norm_num) (by norm_num) L
    have h2 : ((1 : ℚ) / 4) ^ L = 1 / ((2 : ℚ) ^ L * 2 ^ L) := by
      rw [div_pow, one_pow, ← mul_pow]; norm_num
    rw [h2] at h1
    refine h1.trans ?_
    have hp : (0 : ℚ) < 2 ^ L := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hKQ : (K : ℚ) = 5 * L := by rw [hK]; push_cast; ring
  have hL0 : (0 : ℚ) ≤ L := by positivity
  -- the three parts, each times n
  have t1 : 8 / (m0 : ℚ) * n ≤ 8 + (8 * 64 * (15 * L + 3) / 63) / n := by
    have e : 8 / (m0 : ℚ) * n = 8 + 8 * (15 * L + 3) / m0 := by
      rw [← hsumQ]; field_simp
    rw [e]
    have : 8 * (15 * (L : ℚ) + 3) / m0 ≤ (8 * 64 * (15 * L + 3) / 63) / n := by
      rw [div_div, div_le_div_iff₀ hm0pos (by positivity)]
      have h0 : (0 : ℚ) ≤ 8 * (15 * L + 3) := by positivity
      nlinarith
    linarith
  have t2 : 2 * (3 / 4 : ℚ) ^ K * n ≤ 8 / n := by
    have := mul_le_mul_of_nonneg_right h34 hnpos.le
    have e : 4 / ((n : ℚ) * n) * n = 4 / n := by field_simp
    rw [e] at this
    have e2 : 8 / (n : ℚ) = 2 * (4 / n) := by ring
    nlinarith
  have t3 : 8 * (K : ℚ) / ((m0 : ℚ) * m0) * n ≤ (40 * 4096 * L / 3969) / n := by
    rw [hKQ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hnpos]
    have hsq : (63 * (n : ℚ)) * (63 * n) ≤ (64 * m0) * (64 * m0) := by nlinarith
    have : (8 * (5 * (L : ℚ)) * n) * n * 3969 ≤ 40 * 4096 * L * ((m0 : ℚ) * m0) := by
      have h0 : (0 : ℚ) ≤ 40 * L := by positivity
      nlinarith
    linarith
  have hsplit : (kappaR m0 K + gammaR m0 K) * n ≤
      8 / (m0 : ℚ) * n + 2 * (3 / 4 : ℚ) ^ K * n + 8 * (K : ℚ) / ((m0 : ℚ) * m0) * n := by
    have := mul_le_mul_of_nonneg_right hcb hnpos.le
    linarith
  have hfin : 8 + (8 * 64 * (15 * (L : ℚ) + 3) / 63) / n + 8 / n + (40 * 4096 * L / 3969) / n ≤
      8 + 164 * ((L : ℚ) + 1) / n := by
    have : (8 * 64 * (15 * (L : ℚ) + 3) / 63) / n + 8 / n + (40 * 4096 * L / 3969) / n ≤
        164 * ((L : ℚ) + 1) / n := by
      rw [← add_div, ← add_div]
      apply div_le_div_of_nonneg_right _ hnpos.le
      nlinarith
    linarith
  linarith

/-- `(L + 1) · 2^j ≤ (j + 1) · 2^L` for `L ≥ j`: `(L+1)/2^L` decreases. -/
theorem log_ratio_mono (j : Nat) : ∀ L, j ≤ L → (L + 1) * 2 ^ j ≤ (j + 1) * 2 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => exact le_rfl
  | succ L hL ih =>
    rw [pow_succ]
    have : (L + 1 + 1) * 2 ^ j ≤ 2 * ((L + 1) * 2 ^ j) := by
      have : L + 1 + 1 ≤ 2 * (L + 1) := by omega
      calc (L + 1 + 1) * 2 ^ j ≤ 2 * (L + 1) * 2 ^ j := Nat.mul_le_mul_right _ this
        _ = 2 * ((L + 1) * 2 ^ j) := by ring
    calc (L + 1 + 1) * 2 ^ j ≤ 2 * ((L + 1) * 2 ^ j) := this
      _ ≤ 2 * ((j + 1) * 2 ^ L) := Nat.mul_le_mul_left _ ih
      _ = (j + 1) * (2 ^ L * 2) := by ring

/-- For `n ≥ 2^j`: `(⌊log₂ n⌋ + 1)/n ≤ (j+1)/2^j`. -/
theorem log_over_n (j n : Nat) (hn : 2 ^ j ≤ n) :
    ((Nat.log 2 n : ℚ) + 1) / n ≤ ((j : ℚ) + 1) / 2 ^ j := by
  have hn0 : n ≠ 0 := by have := Nat.one_le_two_pow (n := j); omega
  set L := Nat.log 2 n
  have hjL : j ≤ L := Nat.le_log_of_pow_le (by norm_num) hn
  have hpow : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn0
  have hm := log_ratio_mono j L hjL
  have hmQ : ((L : ℚ) + 1) * 2 ^ j ≤ ((j : ℚ) + 1) * 2 ^ L := by exact_mod_cast hm
  have hpQ : (2 : ℚ) ^ L ≤ n := by exact_mod_cast hpow
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
  rw [div_le_div_iff₀ hnpos (by positivity)]
  have h0 : (0 : ℚ) ≤ (j : ℚ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpQ h0]

/-- `(n-3)! = (n-3) · (n-4)!` in `ℚ`, for `n ≥ 4`. -/
theorem fact_n3 (n : Nat) (hn : 4 ≤ n) :
    ((n - 3).factorial : ℚ) = ((n : ℚ) - 3) * ((n - 4).factorial : ℚ) := by
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 4 := ⟨n - 4, by omega⟩
  rw [show b + 4 - 3 = b + 1 by omega, show b + 4 - 4 = b by omega, Nat.factorial_succ]
  push_cast; ring

/-- The word of `finite_boundR` with the parameters of `rate_R`, bounded by `(κ + γ) n (n-4)!`. -/
theorem word_bound8 (n : Nat) (hn : 2 ^ 14 ≤ n) :
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      (w.length : ℚ) ≤ SuperpermutationBounds.F3 n +
        (8 + 164 * ((Nat.log 2 n : ℚ) + 1) / n) * ((n - 4).factorial : ℚ) := by
  set L := Nat.log 2 n with hLd
  have hL14 : 14 ≤ L := Nat.le_log_of_pow_le (by norm_num) hn
  have hpow : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hg := grow64 L hL14
  set K := 5 * L with hK
  set m0 := n - 3 - 3 * K with hm0d
  have hm49 : 49 ≤ m0 := by omega
  obtain ⟨w, hw, hl⟩ := finite_boundR m0 K n 2 (by omega) (by omega) le_rfl (by omega)
  refine ⟨w, hw, ?_⟩
  have hγ : 0 ≤ gammaR m0 K := by unfold gammaR; positivity
  have hκ : 0 ≤ kappaR m0 K := by unfold kappaR; positivity
  have hu := ubound_two (kappaR m0 K) (gammaR m0 K) (n - 2) (by omega) hγ
  rw [show n - 2 + 2 = n by omega, show n - 2 - 1 = n - 3 by omega] at hu
  have hcn := coef_n_bound8 n hn
  have hF4 : (0 : ℚ) ≤ ((n - 4).factorial : ℚ) := by positivity
  have h3 := fact_n3 n (by omega)
  have hnQ : (3 : ℚ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have hle : (kappaR m0 K + gammaR m0 K) * ((n : ℚ) - 3) ≤ (kappaR m0 K + gammaR m0 K) * n := by
    apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
  have key : (kappaR m0 K + gammaR m0 K) * ((n - 3).factorial : ℚ) ≤
      (8 + 164 * ((L : ℚ) + 1) / n) * ((n - 4).factorial : ℚ) := by
    rw [h3, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hle.trans hcn) hF4
  calc (w.length : ℚ) ≤ ubound (kappaR m0 K) (gammaR m0 K) (n - 2) 2 := hl
    _ ≤ (F3 n : ℚ) + (kappaR m0 K + gammaR m0 K) * (Nat.factorial (n - 3) : ℚ) := hu
    _ ≤ (F3 n : ℚ) + (8 + 164 * ((L : ℚ) + 1) / n) * ((n - 4).factorial : ℚ) := by linarith
    _ = SuperpermutationBounds.F3 n + (8 + 164 * ((L : ℚ) + 1) / n) * ((n - 4).factorial : ℚ) := by
        simp only [SuperpermutationBounds.F3, F3, Nat.cast_add]

/-- **The rate with constant 8.** For every `n ≥ 2^14` there is a covering word of length at most
`n! + (n-1)! + (n-2)! + (41/5)·(n-4)!`. -/
theorem rate_R8 (n : Nat) (hn : 2 ^ 14 ≤ n) :
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      (w.length : ℚ) ≤ SuperpermutationBounds.F3 n + 41 / 5 * ((n - 4).factorial : ℚ) := by
  obtain ⟨w, hw, hl⟩ := word_bound8 n hn
  refine ⟨w, hw, hl.trans ?_⟩
  have hr := log_over_n 14 n hn
  have hF4 : (0 : ℚ) ≤ ((n - 4).factorial : ℚ) := by positivity
  have : 8 + 164 * ((Nat.log 2 n : ℚ) + 1) / n ≤ 41 / 5 := by
    have e : 164 * ((Nat.log 2 n : ℚ) + 1) / n = 164 * (((Nat.log 2 n : ℚ) + 1) / n) := by ring
    rw [e]
    have : 164 * (((Nat.log 2 n : ℚ) + 1) / n) ≤ 164 * (((14 : ℕ) : ℚ) + 1) / 2 ^ 14 := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hr (by norm_num)
    norm_num at this ⊢
    linarith
  have := mul_le_mul_of_nonneg_right this hF4
  linarith

/-- `2^j ≥ (j+1)^2` for `j ≥ 6`. -/
theorem pow_ge_sq (j : Nat) (hj : 6 ≤ j) : (j + 1) * (j + 1) ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih => rw [pow_succ]; nlinarith

/-- **The constant 8 in the limit.** For every `ε > 0`, for all large `n` there is a covering word of length at
most `n! + (n-1)! + (n-2)! + (8 + ε)·(n-4)!`. -/
theorem rate_R8_eventually (ε : ℚ) (hε : 0 < ε) : ∃ N : Nat, ∀ n : Nat, N ≤ n →
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      (w.length : ℚ) ≤ SuperpermutationBounds.F3 n + (8 + ε) * ((n - 4).factorial : ℚ) := by
  obtain ⟨j0, hj0⟩ := exists_nat_gt (164 / ε)
  set j := max j0 14 with hj
  refine ⟨2 ^ j, fun n hn => ?_⟩
  have hj14 : 14 ≤ j := le_max_right _ _
  have hn14 : 2 ^ 14 ≤ n := le_trans (Nat.pow_le_pow_right (by norm_num) hj14) hn
  obtain ⟨w, hw, hl⟩ := word_bound8 n hn14
  refine ⟨w, hw, hl.trans ?_⟩
  have hr := log_over_n j n hn
  have hsq := pow_ge_sq j (by omega)
  have hsqQ : ((j : ℚ) + 1) * ((j : ℚ) + 1) ≤ 2 ^ j := by exact_mod_cast hsq
  have hjpos : (0 : ℚ) < (j : ℚ) + 1 := by positivity
  have hr2 : ((j : ℚ) + 1) / 2 ^ j ≤ 1 / ((j : ℚ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) hjpos]; nlinarith
  have hjj : (164 / ε : ℚ) < (j : ℚ) + 1 := by
    have : (j0 : ℚ) ≤ j := by exact_mod_cast le_max_left j0 14
    linarith
  have hfin : 164 * (1 / ((j : ℚ) + 1)) ≤ ε := by
    rw [div_lt_iff₀ hε] at hjj
    rw [mul_one_div, div_le_iff₀ hjpos]; linarith
  have hF4 : (0 : ℚ) ≤ ((n - 4).factorial : ℚ) := by positivity
  have : 8 + 164 * ((Nat.log 2 n : ℚ) + 1) / n ≤ 8 + ε := by
    have e : 164 * ((Nat.log 2 n : ℚ) + 1) / n = 164 * (((Nat.log 2 n : ℚ) + 1) / n) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left (hr.trans hr2) (show (0 : ℚ) ≤ 164 by norm_num)
    linarith
  have := mul_le_mul_of_nonneg_right this hF4
  linarith

end SuperpermutationUpperBound43586371.UniR
