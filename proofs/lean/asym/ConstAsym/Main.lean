import ConstAsym.Bridge
import SuperpermutationUpperBound43586371.Uniform.Main
import Hunter.Paper

/-!
# The shortest superpermutation: `(L(n) - n! - (n-1)! - (n-2)!) / (n-3)! → 0`

`L n` is the least length of a word over `Fin n` that contains every permutation as a factor, in the vocabulary
of Pantone's `Challenge.lean` (`SuperpermutationBounds.Covers`).

* Lower side: Hunter–Raudvere, `Hunter.Paper.factorial_clean` (commit d452221):
  `Ssuper n ≥ n! + (n-1)! + (n-2)! + (n-4)! - 2 (n-5)!` for `n ≥ 6`, moved to covering words by `ConstAsym.Bridge`.
* Upper side: `SuperpermutationUpperBound43586371.Uniform.coefficient_tends_to_zero` (const_uniform).
-/

namespace ConstAsym

open SuperpermutationBounds Filter Topology

/-- The least length of a word over `Fin n` that contains every permutation of `Fin n` as a factor. -/
noncomputable def L (n : ℕ) : ℕ :=
  sInf {m | ∃ w : List (Fin n), Covers w ∧ w.length = m}

theorem exists_covers (n : ℕ) : ∃ w : List (Fin n), Covers w := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    refine ⟨[], ?_⟩
    intro p hp _
    exact ⟨[], [], by simp [List.eq_nil_of_length_eq_zero hp]⟩
  · obtain ⟨w, hw, _⟩ := exists_covers_length_eq h
    exact ⟨w, hw⟩

/-- `L n` is attained. -/
theorem L_spec (n : ℕ) : ∃ w : List (Fin n), Covers w ∧ w.length = L n := by
  obtain ⟨w, hw⟩ := exists_covers n
  exact Nat.sInf_mem (s := {m | ∃ w : List (Fin n), Covers w ∧ w.length = m}) ⟨w.length, w, hw, rfl⟩

/-- No covering word is shorter than `L n`. -/
theorem L_le_length {n : ℕ} {w : List (Fin n)} (hw : Covers w) : L n ≤ w.length :=
  Nat.sInf_le ⟨w, hw, rfl⟩

/-- `L` is the Hunter–Raudvere `Ssuper` for `n ≥ 1`. -/
theorem L_eq_ssuper {n : ℕ} (hn : 0 < n) : L n = Hunter.Ssuper n :=
  (ssuper_eq_sInf hn).symm

theorem two_mul_factorial_le {n : ℕ} (hn : 6 ≤ n) : 2 * (n - 5).factorial ≤ (n - 4).factorial := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 4 = (m + 1) + 1 by omega, show m + 6 - 5 = m + 1 by omega, Nat.factorial_succ]
  exact Nat.mul_le_mul_right _ (by omega)

/-- Hunter–Raudvere's lower bound for every covering word, in `ℕ` (`n ≥ 6`). -/
theorem hunter_lower_nat {n : ℕ} (hn : 6 ≤ n) {w : List (Fin n)} (hw : Covers w) :
    n.factorial + (n - 1).factorial + (n - 2).factorial + (n - 4).factorial
      ≤ w.length + 2 * (n - 5).factorial := by
  have h := Hunter.Paper.factorial_clean hn
  have h3 : ((Hunter.Ssuper n : ℕ) : ℝ) ≤ (w.length : ℝ) := by exact_mod_cast ssuper_le_length hw
  have h4 : ((n.factorial + (n - 1).factorial + (n - 2).factorial + (n - 4).factorial : ℕ) : ℝ)
      ≤ ((w.length + 2 * (n - 5).factorial : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h4

/-- Hunter–Raudvere's lower bound for `L` (`n ≥ 6`). -/
theorem hunter_lower_L {n : ℕ} (hn : 6 ≤ n) :
    F3 n + ((n - 4).factorial : ℚ) - 2 * ((n - 5).factorial : ℚ) ≤ (L n : ℚ) := by
  obtain ⟨w, hw, hl⟩ := L_spec n
  have h := hunter_lower_nat hn hw
  rw [hl] at h
  have h' : ((n.factorial + (n - 1).factorial + (n - 2).factorial + (n - 4).factorial : ℕ) : ℚ)
      ≤ ((L n + 2 * (n - 5).factorial : ℕ) : ℚ) := by exact_mod_cast h
  push_cast at h'
  unfold F3
  linarith

/-- `n! + (n-1)! + (n-2)! ≤ L n` for `n ≥ 6`. -/
theorem F3_le_L {n : ℕ} (hn : 6 ≤ n) : F3 n ≤ (L n : ℚ) := by
  have h := hunter_lower_L hn
  have h2 : (2 * (n - 5).factorial : ℚ) ≤ ((n - 4).factorial : ℚ) := by
    exact_mod_cast two_mul_factorial_le hn
  linarith

/-- **Two-sided form.**  For every rational `ε > 0` there is `N` with
`n! + (n-1)! + (n-2)! ≤ L n ≤ n! + (n-1)! + (n-2)! + ε (n-3)!` for all `n ≥ N`. -/
theorem two_sided :
    ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      F3 n ≤ (L n : ℚ) ∧ (L n : ℚ) ≤ F3 n + ε * ((n - 3).factorial : ℚ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := SuperpermutationUpperBound43586371.Uniform.coefficient_tends_to_zero ε hε
  refine ⟨max N 6, fun n hn => ⟨F3_le_L (le_of_max_le_right hn), ?_⟩⟩
  obtain ⟨v, hv, hvl⟩ := hN n (le_of_max_le_left hn)
  have : (L n : ℚ) ≤ v.length := by exact_mod_cast L_le_length hv
  linarith

/-- **The coefficient of `(n-3)!` tends to `0`** (over `ℝ`):
`(L(n) - n! - (n-1)! - (n-2)!) / (n-3)! → 0`. -/
theorem coefficient_limit :
    Tendsto (fun n : ℕ => ((L n : ℝ) - (F3 n : ℝ)) / ((n - 3).factorial : ℝ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hq : (0 : ℚ) < q := by exact_mod_cast hq0
  obtain ⟨N, hN⟩ := two_sided q hq
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  have h1' : ((F3 n : ℚ) : ℝ) ≤ ((L n : ℚ) : ℝ) := Rat.cast_le.mpr h1
  have h2' : ((L n : ℚ) : ℝ) ≤ ((F3 n + q * ((n - 3).factorial : ℚ) : ℚ) : ℝ) := Rat.cast_le.mpr h2
  push_cast at h1' h2'
  have hf : (0 : ℝ) < ((n - 3).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (by linarith) hf.le), div_lt_iff₀ hf]
  have := mul_lt_mul_of_pos_right hqε hf
  linarith

/-- The same limit over `ℚ`. -/
theorem coefficient_limit_rat :
    Tendsto (fun n : ℕ => ((L n : ℚ) - F3 n) / ((n - 3).factorial : ℚ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp coefficient_limit ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [Real.dist_eq] at h
  rw [Rat.dist_eq]
  push_cast
  simpa only [sub_zero] using h

/-- **Main theorem.**  With `L n` the least length of a word over `Fin n` containing every permutation
(Pantone's `Covers`): `L n = Hunter.Ssuper n` for `n ≥ 1`, `n! + (n-1)! + (n-2)! ≤ L n` for `n ≥ 6`, and
`(L n - n! - (n-1)! - (n-2)!) / (n-3)! → 0`. -/
theorem shortest_superpermutation_coefficient :
    (∀ n, 0 < n → L n = Hunter.Ssuper n) ∧
    (∀ n, 6 ≤ n → F3 n ≤ (L n : ℚ)) ∧
    Tendsto (fun n : ℕ => ((L n : ℝ) - (F3 n : ℝ)) / ((n - 3).factorial : ℝ)) atTop (𝓝 0) :=
  ⟨fun _ hn => L_eq_ssuper hn, fun _ hn => F3_le_L hn, coefficient_limit⟩

end ConstAsym

#print axioms ConstAsym.L_eq_ssuper
#print axioms ConstAsym.hunter_lower_L
#print axioms ConstAsym.two_sided
#print axioms ConstAsym.coefficient_limit
#print axioms ConstAsym.coefficient_limit_rat
#print axioms ConstAsym.shortest_superpermutation_coefficient
