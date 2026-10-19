import SuperpermutationUpperBound43586371.UniR.RMain

/-!
# The rate: coefficient at most `9/n` for every `n ≥ 2^14`

Per level `a ≥ 49` of R'(a) (`|Gl a| ≥ 8`): rows `N = 2|G| a (a+12) ≥ L/4` and charge + cycles
`≤ (17/2) N / a`.  With `x = Q/A! + c/(A-1)!`, `xc = c/(A-1)!`, `p = P/(A-1)!` after `K` levels from `m0 ≥ 49`:
`x + (17/(2 m0)) p ≤ 17/(2 m0)`, `p ≤ (3/4)^K`, `xc ≤ 8K/m0²`.  Hence the excess of `finite_boundR` with `a = 2`
is at most `17/(2 m0) + 2 (3/4)^K + 8K/m0²`, and with `K = 5 log₂ n`, `m0 = n - 3 - 3K` this is `≤ 9/n`.
-/

namespace SuperpermutationUpperBound43586371.UniR

open SuperpermutationUpperBound
open SuperpermutationUpperBound43586371.Uniform

/-! ### Sizes of the block -/

theorem Gl_len_ge (a : Nat) (ha : 7 ≤ a) : (a - 7) / 6 + 1 ≤ (Gl a).length := by
  have hsub : ((List.range ((a - 7) / 6 + 1)).map (fun i => 3 * i + 1)).Subperm (Gl a) := by
    refine List.Nodup.subperm (List.Nodup.map (fun x y h => by omega) List.nodup_range) ?_
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
    have := List.mem_range.mp hi
    rw [mem_Gl]; omega
  simpa using hsub.length_le

theorem Sl_Pm (a : Nat) : (Sl a).length * Pm a = a := by
  unfold Sl Pm; split_ifs <;> simp <;> omega

theorem Dl_len (a : Nat) : (Dl a).length = 2 * (Gl a).length * (Sl a).length := by
  unfold Dl
  rw [length_flatMap_const _ _ (2 * (Sl a).length) (fun g _ => by simp; omega)]
  ring

theorem rowsR_eq (a : Nat) : rowsR a = 2 * (Gl a).length * a * (a + 12) := by
  unfold rowsR; rw [Dl_len]
  calc 2 * (Gl a).length * (Sl a).length * (Pm a * (a + 12))
      = 2 * (Gl a).length * ((Sl a).length * Pm a) * (a + 12) := by ring
    _ = 2 * (Gl a).length * a * (a + 12) := by rw [Sl_Pm]

theorem chargeR_eq (a : Nat) : chargeR a = 16 * (Gl a).length * a := by
  unfold chargeR; rw [Dl_len]
  calc 2 * (Gl a).length * (Sl a).length * (8 * Pm a)
      = 16 * (Gl a).length * ((Sl a).length * Pm a) := by ring
    _ = 16 * (Gl a).length * a := by rw [Sl_Pm]

theorem ncycR_le (a : Nat) : ncycR a ≤ 8 := by unfold ncycR; split_ifs <;> omega

theorem rows_quarter (a : Nat) (ha : 49 ≤ a) : a * ((a + 1) * (a + 2)) ≤ 4 * rowsR a := by
  rw [rowsR_eq]
  have hG := Gl_len_ge a (by omega)
  have h6 : a ≤ 6 * (Gl a).length + 6 := by omega
  generalize (Gl a).length = G at h6
  zify at h6 ha ⊢
  have h1 : (0 : ℤ) ≤ (6 * G + 6 - a) * (a + 12) := mul_nonneg (by linarith) (by linarith)
  have h2 : ((a : ℤ) + 1) * (a + 2) ≤ 8 * G * (a + 12) := by nlinarith
  nlinarith

theorem cost_le (a : Nat) (ha : 49 ≤ a) :
    2 * (chargeR a + (a + 2) * ncycR a) * a ≤ 17 * rowsR a := by
  rw [rowsR_eq, chargeR_eq]
  have hG := Gl_len_ge a (by omega)
  have h8 : 8 ≤ (Gl a).length := by omega
  have hn := ncycR_le a
  generalize (Gl a).length = G at h8
  generalize ncycR a = c at hn
  zify at h8 hn ha ⊢
  have h1 : ((a : ℤ) + 2) * c ≤ (a + 2) * 8 := mul_le_mul_of_nonneg_left hn (by linarith)
  have h2 : ((a : ℤ) + 2) * 8 ≤ (a + 2) * G := mul_le_mul_of_nonneg_left h8 (by linarith)
  have h3 : 2 * (16 * G * a + (a + 2) * c) ≤ 17 * (2 * G * (a + 12)) := by nlinarith
  nlinarith

/-- A concrete frame on `a` old letters, to use `rows_le`. -/
def frameStd (a : Nat) : Frame := ⟨(List.range a).map (· + 11), a + 11, a + 12, a + 13, a + 14⟩

theorem frameStd_ok (a : Nat) : (frameStd a).OK := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [frameStd, Frame.alph', Frame.alph]
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
      List.nodup_cons.mpr ⟨?_, List.Nodup.map (fun x y h => by omega) List.nodup_range⟩⟩⟩⟩ <;>
      simp <;> omega
  · simp [frameStd, Frame.alph', Frame.alph]
  · simp [frameStd, Frame.alph', Frame.alph]

theorem rowsR_le (a : Nat) (ha : 7 ≤ a) : rowsR a ≤ a * ((a + 1) * (a + 2)) := by
  have h := rows_le (frameStd a) (frameStd_ok a) (by simp [frameStd]; omega)
  simpa [frameStd] using h

/-! ### The normalised recursion -/

/-- `Q/A! + c/(A-1)!`. -/
def Xr (m0 K : Nat) : ℚ := ((cntR m0 K).2.1 : ℚ) / (m0 + 3 * K).factorial +
  ((cntR m0 K).2.2.1 : ℚ) / (m0 + 3 * K - 1).factorial

/-- `c/(A-1)!`. -/
def Xcr (m0 K : Nat) : ℚ := ((cntR m0 K).2.2.1 : ℚ) / (m0 + 3 * K - 1).factorial

/-- `P/(A-1)!`. -/
def Pr (m0 K : Nat) : ℚ := ((cntR m0 K).2.2.2 : ℚ) / (m0 + 3 * K - 1).factorial

theorem kappaR_eq (m0 K : Nat) : kappaR m0 K = Xr m0 K + Pr m0 K := by
  unfold kappaR Xr Pr; push_cast; ring

theorem gammaR_eq (m0 K : Nat) : gammaR m0 K = Xcr m0 K + Pr m0 K := by
  unfold gammaR Xcr Pr; push_cast; ring

theorem fact_q (a : Nat) (ha : 1 ≤ a) :
    ((a + 3).factorial : ℚ) = (a + 3) * (a + 2) * (a + 1) * a * (a - 1).factorial ∧
      ((a + 3 - 1).factorial : ℚ) = (a + 2) * (a + 1) * a * (a - 1).factorial ∧
      (a.factorial : ℚ) = a * (a - 1).factorial := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  simp only [Nat.add_sub_cancel, show b + 1 + 3 - 1 = b + 3 by omega]
  refine ⟨?_, ?_, ?_⟩ <;> simp [Nat.factorial_succ] <;> push_cast <;> ring

theorem step_rec (m0 K a : Nat) (hm : 1 ≤ m0) (had : a = m0 + 3 * K)
    (hrows : rowsR a ≤ a * ((a + 1) * (a + 2))) :
    Xr m0 (K + 1) = Xr m0 K + Pr m0 K * ((chargeR a : ℚ) + (a + 2) * ncycR a) / ((a : ℚ) * ((a + 1) * (a + 2))) ∧
      Xcr m0 (K + 1) = Xcr m0 K + Pr m0 K * ((a + 2) * ncycR a) / ((a : ℚ) * ((a + 1) * (a + 2))) ∧
      Pr m0 (K + 1) = Pr m0 K * ((a : ℚ) * ((a + 1) * (a + 2)) - rowsR a) / ((a : ℚ) * ((a + 1) * (a + 2))) := by
  have ha : 1 ≤ a := by omega
  obtain ⟨f3, f2, f1⟩ := fact_q a ha
  have hA : m0 + 3 * (K + 1) = a + 3 := by omega
  have hF : ((a - 1).factorial : ℚ) ≠ 0 := by positivity
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hsub : ((a * ((a + 1) * (a + 2)) - rowsR a : Nat) : ℚ) = (a : ℚ) * ((a + 1) * (a + 2)) - rowsR a := by
    rw [Nat.cast_sub hrows]; push_cast; ring
  unfold Xr Xcr Pr
  rw [hA, f3, f2]
  simp only [cntR]
  rw [← had, f1]
  refine ⟨?_, ?_, ?_⟩
  · push_cast
    field_simp
    ring
  · push_cast
    field_simp
  · rw [Nat.cast_mul, hsub]
    field_simp

/-! ### The invariants -/

theorem Pr_nonneg (m0 K : Nat) : 0 ≤ Pr m0 K := by unfold Pr; positivity
theorem Xcr_nonneg (m0 K : Nat) : 0 ≤ Xcr m0 K := by unfold Xcr; positivity

theorem invariants (m0 : Nat) (hm : 49 ≤ m0) : ∀ K,
    Xr m0 K + 17 / (2 * m0) * Pr m0 K ≤ 17 / (2 * m0) ∧ Pr m0 K ≤ (3 / 4) ^ K ∧
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
    have hc := cost_le a (by omega)
    have hqQ : L ≤ 4 * (rowsR a : ℚ) := by rw [hLdef]; exact_mod_cast hq
    have hcQ : 2 * ((chargeR a : ℚ) + (a + 2) * ncycR a) * a ≤ 17 * (rowsR a : ℚ) := by exact_mod_cast hc
    have hrQ : (rowsR a : ℚ) ≤ L := by rw [hLdef]; exact_mod_cast hrows
    have hP0 := Pr_nonneg m0 K
    have hn8 : (ncycR a : ℚ) ≤ 8 := by exact_mod_cast ncycR_le a
    refine ⟨?_, ?_, ?_⟩
    · rw [sX, sP]
      have hcost : ((chargeR a : ℚ) + (a + 2) * ncycR a) ≤ 17 / (2 * m0) * rowsR a := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      have : Pr m0 K * ((chargeR a : ℚ) + (a + 2) * ncycR a) / L + 17 / (2 * m0) * (Pr m0 K * (L - rowsR a) / L)
          ≤ 17 / (2 * m0) * Pr m0 K := by
        rw [mul_div_assoc', ← add_div, div_le_iff₀ hL]
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
    · rw [sXc]
      have hP1 : Pr m0 K ≤ 1 := i2.trans (pow_le_one₀ (by norm_num) (by norm_num))
      have hstep : Pr m0 K * ((a + 2) * ncycR a) / L ≤ 8 / ((m0 : ℚ) * m0) := by
        rw [div_le_div_iff₀ hL (by positivity)]
        have h1 : Pr m0 K * ((a + 2) * ncycR a) ≤ 8 * (a + 2) := by
          have : ((a : ℚ) + 2) * ncycR a ≤ (a + 2) * 8 := by
            apply mul_le_mul_of_nonneg_left hn8; positivity
          nlinarith
        have hmm : (m0 : ℚ) * m0 ≤ a * (a + 1) := by nlinarith
        have h2 : (m0 : ℚ) * m0 * (a + 2) ≤ L := by
          have e : (a : ℚ) * ((a + 1) * (a + 2)) = a * (a + 1) * (a + 2) := by ring
          rw [hLdef, e]; exact mul_le_mul_of_nonneg_right hmm (by positivity)
        nlinarith
      have : (8 * (K + 1 : Nat) : ℚ) / ((m0 : ℚ) * m0) = 8 * K / ((m0 : ℚ) * m0) + 8 / ((m0 : ℚ) * m0) := by
        push_cast; ring
      rw [this]
      linarith

/-! ### The rate theorem -/

theorem coef_bound (m0 K : Nat) (hm : 49 ≤ m0) :
    kappaR m0 K + gammaR m0 K ≤ 17 / (2 * m0) + 2 * (3 / 4) ^ K + 8 * K / ((m0 : ℚ) * m0) := by
  obtain ⟨i1, i2, i3⟩ := invariants m0 hm K
  rw [kappaR_eq, gammaR_eq]
  have hP0 := Pr_nonneg m0 K
  have hm0 : (0 : ℚ) < m0 := by exact_mod_cast (show 0 < m0 by omega)
  have : 0 ≤ 17 / (2 * (m0 : ℚ)) * Pr m0 K := by positivity
  linarith

theorem ubound_two (κ γ : ℚ) (m : Nat) (hm : 3 ≤ m) (hγ : 0 ≤ γ) :
    ubound κ γ m 2 ≤ (F3 (m + 2) : ℚ) + (κ + γ) * (Nat.factorial (m - 1) : ℚ) := by
  unfold ubound
  have hF : (0 : ℚ) ≤ (Nat.factorial (m - 1) : ℚ) := by positivity
  have hm1 : (0 : ℚ) < ((m - 1 : Nat) : ℚ) := by exact_mod_cast (show 0 < m - 1 by omega)
  have hmin : ((m - 2 : Nat) : ℚ) * min (γ * (Nat.factorial (m - 1) : ℚ) / ((m - 1 : Nat) : ℚ))
      ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (2 + 1) : ℚ)) ≤ γ * (Nat.factorial (m - 1) : ℚ) := by
    apply (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans
    rw [mul_div_assoc', div_le_iff₀ hm1]
    have h2 : ((m - 2 : Nat) : ℚ) ≤ ((m - 1 : Nat) : ℚ) := by exact_mod_cast (show m - 2 ≤ m - 1 by omega)
    have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ γ * (Nat.factorial (m - 1) : ℚ) by positivity)
    linarith
  simp only [Nat.sub_self, Nat.cast_zero, zero_mul, zero_div, add_zero]
  linarith

theorem grow64 : ∀ L, 14 ≤ L → 64 * (15 * L + 3) ≤ 2 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have : 960 ≤ 2 ^ L := by
      calc 960 ≤ 2 ^ 14 := by norm_num
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
    rw [pow_succ]; omega

/-- **The rate.** For every `n ≥ 2^14` there is a covering word of length at most
`n! + (n-1)! + (n-2)! + (9/n) (n-3)!`. -/
theorem rate_R (n : Nat) (hn : 2 ^ 14 ≤ n) :
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      (w.length : ℚ) ≤ SuperpermutationBounds.F3 n + 9 / (n : ℚ) * (Nat.factorial (n - 3) : ℚ) := by
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
  obtain ⟨w, hw, hl⟩ := finite_boundR m0 K n 2 (by omega) (by omega) le_rfl (by omega)
  refine ⟨w, hw, ?_⟩
  have hγ : 0 ≤ gammaR m0 K := by unfold gammaR; positivity
  have hu := ubound_two (kappaR m0 K) (gammaR m0 K) (n - 2) (by omega) hγ
  have hcb := coef_bound m0 K hm49
  rw [show n - 2 + 2 = n by omega, show n - 2 - 1 = n - 3 by omega] at hu
  -- the numbers
  have hnQ : (2 ^ 14 : ℚ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℚ) < n := by linarith
  have hm0Q : 63 * (n : ℚ) ≤ 64 * m0 := by exact_mod_cast hm0
  have hm49Q : (49 : ℚ) ≤ m0 := by exact_mod_cast hm49
  have hm0pos : (0 : ℚ) < m0 := by linarith
  have hLQ : 960 * (L : ℚ) ≤ n := by exact_mod_cast (show 960 * L ≤ n by omega)
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
  have t1 : 17 / (2 * (m0 : ℚ)) ≤ 544 / (63 * n) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have t2 : 8 * (K : ℚ) / ((m0 : ℚ) * m0) ≤ (1 / 20) / n := by
    have hKQ : (K : ℚ) = 5 * L := by rw [hK]; push_cast; ring
    rw [hKQ, div_le_div_iff₀ (by positivity) hnpos]
    have hsq : (63 * (n : ℚ)) * (63 * n) ≤ (64 * m0) * (64 * m0) := by nlinarith
    nlinarith
  have t3 : 2 * (3 / 4 : ℚ) ^ K ≤ (1 / 1000) / n := by
    have : 2 * (4 / ((n : ℚ) * n)) ≤ (1 / 1000) / n := by
      rw [show 2 * (4 / ((n : ℚ) * n)) = 8 / ((n : ℚ) * n) by ring, div_le_div_iff₀ (by positivity) hnpos]; nlinarith
    linarith
  have htot : kappaR m0 K + gammaR m0 K ≤ 9 / n := by
    have e : 544 / (63 * (n : ℚ)) + (1 / 1000) / n + (1 / 20) / n ≤ 9 / n := by
      rw [show 544 / (63 * (n : ℚ)) = (544 / 63) / n by field_simp]
      rw [← add_div, ← add_div]
      apply div_le_div_of_nonneg_right _ hnpos.le
      norm_num
    linarith
  have hF : (0 : ℚ) ≤ (Nat.factorial (n - 3) : ℚ) := by positivity
  calc (w.length : ℚ) ≤ ubound (kappaR m0 K) (gammaR m0 K) (n - 2) 2 := hl
    _ ≤ (F3 n : ℚ) + (kappaR m0 K + gammaR m0 K) * (Nat.factorial (n - 3) : ℚ) := hu
    _ ≤ (F3 n : ℚ) + 9 / n * (Nat.factorial (n - 3) : ℚ) := by
        linarith [mul_le_mul_of_nonneg_right htot hF]
    _ = SuperpermutationBounds.F3 n + 9 / (n : ℚ) * (Nat.factorial (n - 3) : ℚ) := by
        simp only [SuperpermutationBounds.F3, F3, Nat.cast_add]

end SuperpermutationUpperBound43586371.UniR
