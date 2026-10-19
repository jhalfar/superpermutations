import SuperpermutationUpperBound43586371.Uniform.Bounds
import Challenge

/-!
# The coefficient of `(n-3)!` tends to `0`

For every rational `ε > 0` there is `N` such that for every `K ≥ N` some word on `K` symbols contains every
permutation as a factor and has length at most `K! + (K-1)! + (K-2)! + ε (K-3)!`
(`coefficient_tends_to_zero`, in the vocabulary of `Challenge.lean`).

The construction (`PROOF.md`): no seed on `m0 + 1` letters with `m0` odd, `m0 > 40/δ`
(`δ = min ε 1`); then `K'` pairs of levels, the one-walk block `walkData` at odd `a` and the empty block at
`a + 3`, with `K' > (m0+1) (4/δ)^6`; the closed level at `a = m0 + 6K'` has coefficient at most `δ/2`
(`closed_level`: `m0 (Q + a c) ≤ 10 a!` and `(aP)^6 (a+1) ≤ (m0+1) (a!)^6`), and `eventual_of_finite` adds the
lower-order terms.
-/

namespace SuperpermutationUpperBound43586371.Uniform

open SuperpermutationUpperBound

private theorem covers_of_construction {K : ℕ} {w : List (Fin K)}
    (h : IsSuperpermutation w) : SuperpermutationBounds.Covers w := by
  intro p hlength hnodup
  obtain ⟨u, v, heq⟩ := h p ⟨hlength, hnodup⟩
  exact ⟨u, v, heq.symm⟩

/-- The closed level of `closed_level` has coefficient at most `δ/2` when `m0 > 40/δ` and
`K' > (m0+1)(4/δ)^6`. -/
theorem small_coefficient (δ : ℚ) (hδ : 0 < δ) (m0 K' a Q c P : Nat) (ha : a = m0 + 6 * K')
    (hm0 : (40 : ℚ) / δ < m0) (hK : ((m0 : ℚ) + 1) * (4 / δ) ^ 6 < K')
    (h2 : m0 * (Q + a * c) ≤ 10 * a.factorial)
    (h3 : (a * P) ^ 6 * (a + 1) ≤ (m0 + 1) * (a.factorial) ^ 6) (h1 : 1 ≤ a) :
    (Q : ℚ) / a.factorial + ((c + P : Nat) : ℚ) / (a - 1).factorial ≤ δ / 2 := by
  have hF : (0 : ℚ) < a.factorial := by exact_mod_cast Nat.factorial_pos a
  have hfp : ((a - 1).factorial : ℚ) = (a.factorial : ℚ) / a := by
    have := fact_pred a h1
    have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    field_simp
    rw [mul_comm]; exact_mod_cast this.symm
  have hm0pos : (0 : ℚ) < m0 := lt_trans (by positivity) hm0
  -- the charge and cycles part
  have hpart1 : ((Q : ℚ) + a * c) / a.factorial ≤ δ / 4 := by
    have h2q : (m0 : ℚ) * ((Q : ℚ) + a * c) ≤ 10 * a.factorial := by exact_mod_cast h2
    rw [div_le_iff₀ hF]
    have h10 : (10 : ℚ) / m0 < δ / 4 := by
      rw [div_lt_iff₀ hm0pos]
      have := (div_lt_iff₀ hδ).mp hm0
      nlinarith
    have hq : ((Q : ℚ) + a * c) ≤ 10 / m0 * a.factorial := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hm0pos]; linarith
    nlinarith
  -- the pending part
  set p : ℚ := (a : ℚ) * P / a.factorial with hp
  have hp0 : 0 ≤ p := by positivity
  have hp6 : p ^ 6 * ((a : ℚ) + 1) ≤ (m0 : ℚ) + 1 := by
    have h3q : ((a : ℚ) * P) ^ 6 * ((a : ℚ) + 1) ≤ ((m0 : ℚ) + 1) * (a.factorial : ℚ) ^ 6 := by
      exact_mod_cast h3
    rw [hp, div_pow]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  have hpart2 : p ≤ δ / 4 := by
    by_contra hcon
    push Not at hcon
    have hlt : (δ / 4) ^ 6 < p ^ 6 := pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
    have haK : (K' : ℚ) ≤ (a : ℚ) + 1 := by
      have : K' ≤ a + 1 := by omega
      exact_mod_cast this
    have hK' : ((m0 : ℚ) + 1) < (δ / 4) ^ 6 * K' := by
      have e : ((m0 : ℚ) + 1) * (4 / δ) ^ 6 * (δ / 4) ^ 6 = (m0 : ℚ) + 1 := by
        field_simp
      have hpos : (0 : ℚ) < (δ / 4) ^ 6 := by positivity
      nlinarith
    have : (δ / 4) ^ 6 * K' ≤ p ^ 6 * ((a : ℚ) + 1) := by
      apply mul_le_mul (le_of_lt hlt) haK (by positivity) (by positivity)
    linarith
  have hsplit : (Q : ℚ) / a.factorial + ((c + P : Nat) : ℚ) / (a - 1).factorial =
      ((Q : ℚ) + a * c) / a.factorial + p := by
    rw [hfp, hp]
    have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    push_cast
    field_simp
    ring
  rw [hsplit]
  linarith

/-- **The coefficient of `(n-3)!` tends to `0`.**  For every rational `ε > 0`, from some `N` on, there is a
covering word of length at most `n! + (n-1)! + (n-2)! + ε (n-3)!`. -/
theorem coefficient_tends_to_zero :
    ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ K : ℕ, N ≤ K → ∃ w : List (Fin K), SuperpermutationBounds.Covers w ∧
      (w.length : ℚ) ≤ SuperpermutationBounds.F3 K + ε * (Nat.factorial (K - 3) : ℚ) := by
  intro ε hε
  set δ := min ε 1 with hδdef
  have hδ : 0 < δ := lt_min hε one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  obtain ⟨t, ht⟩ := exists_nat_gt ((40 : ℚ) / δ)
  set m0 := 2 * (t + 6) + 1 with hm0def
  have hm0 : (40 : ℚ) / δ < m0 := by
    have : (t : ℚ) ≤ m0 := by exact_mod_cast (show t ≤ m0 by omega)
    linarith
  obtain ⟨K', hK'⟩ := exists_nat_gt (((m0 : ℚ) + 1) * (4 / δ) ^ 6)
  obtain ⟨A, comps, circles, Q, c, P, C, hfull, h2, h3⟩ :=
    closed_level m0 (by omega) (by omega) K'
  set a := m0 + 6 * K' with hadef
  have hκ := small_coefficient δ hδ m0 K' a Q c P rfl hm0 hK' h2 h3 (by omega)
  set κ : ℚ := (Q : ℚ) / a.factorial + ((c + P : Nat) : ℚ) / (a - 1).factorial
  set γ : ℚ := ((c + P : Nat) : ℚ) / (a - 1).factorial
  have hγ0 : 0 ≤ γ := by positivity
  have hγκ : γ ≤ κ := by
    have : (0 : ℚ) ≤ (Q : ℚ) / a.factorial := by positivity
    linarith
  have hγ1 : γ ≤ 1 := by linarith
  have hfin := fun m (hm : a + 1 ≤ m) a' (ha : 2 ≤ a') (ham : a' ≤ m) =>
    finite_of_closed C hfull m a' hm ha ham
  obtain ⟨N, hN⟩ := eventual_of_finite κ γ hγ0 hγ1 (a + 1) hfin (δ / 2) (by positivity)
  refine ⟨N, fun K hK => ?_⟩
  obtain ⟨w, hw, hl⟩ := hN K hK
  refine ⟨w, covers_of_construction hw, ?_⟩
  have hle : (F3 K : ℚ) + (κ + δ / 2) * (Fourth K : ℚ) ≤ (F3 K : ℚ) + ε * (Fourth K : ℚ) := by
    apply add_le_add (le_refl _)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have h := hl.trans hle
  simpa only [SuperpermutationBounds.F3, F3, Fourth, Nat.cast_add] using h

end SuperpermutationUpperBound43586371.Uniform
