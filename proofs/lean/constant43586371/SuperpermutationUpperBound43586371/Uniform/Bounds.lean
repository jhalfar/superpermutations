import SuperpermutationUpperBound43586371.Uniform.Iterate
import SuperpermutationUpperBound.Bounds.AsymptoticEpsilon

/-!
# From a closed level to an eventual bound, for any coefficient (`PROOF.md`, section 9)

constant43586371's `GenericBounds*` files with the constants replaced by variables: a closed level on `h + 1` letters with
`h!` rows, total charge `Q` and `c` cycles gives, for every `m ≥ h + 1` and `2 ≤ a ≤ m`, a word on `m + 2`
symbols of length at most `ubound κ γ m a` with `κ = Q/h! + c/(h-1)!`, `γ = c/(h-1)!` (`finite_of_closed`);
for `0 ≤ γ ≤ 1` this gives `F3 K + (κ + ε) (K-3)!` for all large `K` (`eventual_of_closed`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace SuperpermutationUpperBound43586371.Uniform

open SuperpermutationUpperBound

/-- The finite expression with coefficient `κ` and cycle ratio `γ`. -/
def ubound (κ γ : ℚ) (m a : Nat) : ℚ :=
  (F3 (m + 2) : ℚ) + κ * (Nat.factorial (m - 1) : ℚ)
    + ((a - 2 : Nat) : ℚ) * γ * (Nat.factorial (m - 1) : ℚ) / ((m - 1 : Nat) : ℚ)
    + ((m - a : Nat) : ℚ) *
        min (γ * (Nat.factorial (m - 1) : ℚ) / ((m - 1 : Nat) : ℚ))
          ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (a + 1) : ℚ))

theorem desc_rat (m a : Nat) (ha : a ≤ m) :
    (((m + 1).descFactorial (m - a) : Nat) : ℚ) = ((m + 1).factorial : ℚ) / ((a + 1).factorial : ℚ) := by
  have hf : ((a + 1).factorial : ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hf).mpr
  have h := Nat.factorial_mul_descFactorial (show m - a ≤ m + 1 by omega)
  rw [show m + 1 - (m - a) = a + 1 by omega] at h
  have hq : (((a + 1).factorial * (m + 1).descFactorial (m - a) : Nat) : ℚ) = ((m + 1).factorial : ℚ) := by
    exact_mod_cast h
  rw [← hq]; push_cast; ring

/-- A closed level gives the finite bound at every larger size. -/
theorem finite_of_closed {A : List Nat} {h : Nat} {comps : List (List (Row Nat))}
    {circles : List (List Nat)} {Q c : Nat} (C : Closed A h comps circles h.factorial Q c)
    (hfull : (10 :: (A ++ [9])).Perm (List.range (h + 3))) (m a : Nat) (hm : h + 1 ≤ m)
    (ha : 2 ≤ a) (ham : a ≤ m) :
    ∃ w : Word (m + 2), IsSuperpermutation w ∧
      (w.length : ℚ) ≤ ubound ((Q : ℚ) / h.factorial + (c : ℚ) / (h - 1).factorial)
        ((c : ℚ) / (h - 1).factorial) m a := by
  have h2 := C.two
  obtain ⟨Q', c', Ck, hq, hc⟩ := C.all hfull Q h.factorial c (h - 1).factorial (by ring) (by ring) (m - 1 - h)
  have hk : m - 1 - h + h = m - 1 := by omega
  rw [hk] at Ck hq hc
  have hfull' : (10 :: (alphG A (h + 3) (m - 1 - h) ++ [9])).Perm (List.range (m + 2)) := by
    have := alphG_full hfull (m - 1 - h)
    rwa [show m - 1 - h + (h + 3) = m + 2 by omega] at this
  obtain ⟨w, hw, hl⟩ := Ck.word (K := m + 2) (by omega) hfull' a ha (by omega)
  refine ⟨w, hw, ?_⟩
  have hl' : (w.length : ℚ) ≤ ((F3 (m + 2) + Q' + (m - 1) * c' + (a - 2) * c' +
      (m - 1 + 1 - a) * min c' ((m + 2 - 1).descFactorial (m - 1 + 1 - a)) : Nat) : ℚ) := by
    exact_mod_cast hl
  refine hl'.trans (le_of_eq ?_)
  rw [show m + 2 - 1 = m + 1 by omega, show m - 1 + 1 - a = m - a by omega]
  push_cast
  rw [desc_rat m a ham]
  have hfh : ((h.factorial : Nat) : ℚ) ≠ 0 := by positivity
  have hfh1 : (((h - 1).factorial : Nat) : ℚ) ≠ 0 := by positivity
  have hm1 : ((m - 1 : Nat) : ℚ) ≠ 0 := by
    have : (1 : ℚ) ≤ ((m - 1 : Nat) : ℚ) := by exact_mod_cast (show 1 ≤ m - 1 by omega)
    linarith
  have hQ' : (Q' : ℚ) = (Q : ℚ) / h.factorial * (m - 1).factorial := by
    have hq' : ((h.factorial : Nat) : ℚ) * Q' = Q * (m - 1).factorial := by exact_mod_cast hq
    field_simp; linarith
  have hmf : ((m - 1).factorial : ℚ) = ((m - 1 : Nat) : ℚ) * ((m - 1 - 1).factorial : ℚ) := by
    exact_mod_cast fact_pred (m - 1) (by omega)
  have hc' : (c' : ℚ) = (c : ℚ) / (h - 1).factorial * (m - 1).factorial / ((m - 1 : Nat) : ℚ) := by
    have hc'' : (((h - 1).factorial : Nat) : ℚ) * c' = c * (m - 1 - 1).factorial := by exact_mod_cast hc
    rw [hmf]; field_simp; linarith
  have hcast : ((m - 1 : Nat) : ℚ) = (m : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  unfold ubound
  rw [hQ', hc']
  rw [show ((m - 1 : Nat) : ℚ) = (m : ℚ) - 1 from hcast] at hm1 ⊢
  field_simp
  ring

/-- The linear-overlap error is at most 2/r (for `0 ≤ γ ≤ 1`). -/
theorem linear_error_le (γ : ℚ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (m a r : Nat) (hm : 2 ≤ m) (hr : 1 ≤ r)
    (har : a * r ≤ m) : ((a - 2 : Nat) : ℚ) * γ / ((m - 1 : Nat) : ℚ) ≤ 2 / (r : ℚ) := by
  have hmQ : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hrQ : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by omega)
  have harQ : (a : ℚ) * r ≤ m := by exact_mod_cast har
  have hd : ((m - 1 : Nat) : ℚ) = (m : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hn : ((a - 2 : Nat) : ℚ) * γ ≤ a := by
    have hsub : ((a - 2 : Nat) : ℚ) ≤ a := by exact_mod_cast Nat.sub_le a 2
    have hmul := mul_le_mul_of_nonneg_left hγ1 (show (0 : ℚ) ≤ ((a - 2 : Nat) : ℚ) by positivity)
    have hm' : ((a - 2 : Nat) : ℚ) * γ ≤ ((a - 2 : Nat) : ℚ) := by simpa only [mul_one] using hmul
    exact hm'.trans hsub
  rw [hd]
  apply (div_le_div_iff₀ (by linarith : (0 : ℚ) < (m : ℚ) - 1) hrQ).mpr
  have hnR := mul_le_mul_of_nonneg_right hn (le_of_lt hrQ)
  linarith

theorem bound_floor_majorant (κ γ : ℚ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (m r : Nat) (hr : 1 ≤ r)
    (hm : 8 * r ≤ m) :
    ubound κ γ m (m / r) ≤ (F3 (m + 2) : ℚ) + (κ + 2 / (r : ℚ) + 512 * (r : ℚ) ^ 4 / m) *
      (Fourth (m + 2) : ℚ) := by
  have hb := SuperpermutationUpperBound.Bounds.floor_parameter_bounds m r hr hm
  have hm2 : 2 ≤ m := by omega
  have hlinear := linear_error_le γ hγ0 hγ1 m (m / r) r hm2 hr hb.2.2.1
  have hfactorial := SuperpermutationUpperBound.Bounds.factorial_error_le m (m / r) r
    (by omega) (by omega) hb.2.2.2
  have hfac : (Nat.factorial (m + 1) : ℚ) = ((m : ℚ) + 1) * m * (Nat.factorial (m - 1) : ℚ) := by
    rw [Nat.factorial_succ, ← Nat.mul_factorial_pred (n := m) (by omega)]
    push_cast
    ring
  have htail :
      ((m - m / r : Nat) : ℚ) *
          min (γ * (Nat.factorial (m - 1) : ℚ) / ((m - 1 : Nat) : ℚ))
            ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / r + 1) : ℚ)) ≤
        (m : ℚ) * ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / r + 1) : ℚ)) := by
    apply (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.sub_le m (m / r)
  have hFourth : (m + 2) - 3 = m - 1 := by omega
  unfold ubound
  rw [Fourth, hFourth]
  calc
    _ ≤ (F3 (m + 2) : ℚ) + κ * (Nat.factorial (m - 1) : ℚ) +
          ((m / r - 2 : Nat) : ℚ) * γ * (Nat.factorial (m - 1) : ℚ) / ((m - 1 : Nat) : ℚ) +
          (m : ℚ) * ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / r + 1) : ℚ)) :=
      add_le_add (le_refl _) htail
    _ = (F3 (m + 2) : ℚ) +
          (κ + ((m / r - 2 : Nat) : ℚ) * γ / ((m - 1 : Nat) : ℚ) +
            (m : ℚ) * m * (m + 1) / (Nat.factorial (m / r + 1) : ℚ)) *
          (Nat.factorial (m - 1) : ℚ) := by
      rw [hfac]
      ring
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact add_le_add (add_le_add (le_refl _) hlinear) hfactorial

/-- The finite bound at every `m ≥ m1` gives the eventual coefficient `κ + ε`. -/
theorem eventual_of_finite (κ γ : ℚ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (m1 : Nat)
    (hfin : ∀ m, m1 ≤ m → ∀ a, 2 ≤ a → a ≤ m →
      ∃ w : Word (m + 2), IsSuperpermutation w ∧ (w.length : ℚ) ≤ ubound κ γ m a) :
    ∀ ε : ℚ, 0 < ε → ∃ N : Nat, ∀ K : Nat, N ≤ K → ∃ w : Word K, IsSuperpermutation w ∧
      (w.length : ℚ) ≤ (F3 K : ℚ) + (κ + ε) * (Fourth K : ℚ) := by
  intro ε hε
  obtain ⟨r, hr⟩ := exists_nat_gt ((4 : ℚ) / ε)
  have hrpos : (0 : ℚ) < r := lt_trans (by positivity) hr
  have hrNat : 1 ≤ r := by exact_mod_cast hrpos
  have hsmall : (2 : ℚ) / r ≤ ε / 2 := by
    apply (div_le_iff₀ hrpos).mpr
    have hh := (div_lt_iff₀ hε).mp hr
    nlinarith
  obtain ⟨M, hM⟩ := exists_nat_gt ((1024 : ℚ) * (r : ℚ) ^ 4 / ε)
  refine ⟨m1 + 22 + 8 * r + M, ?_⟩
  intro K hK
  have hmr : 8 * r ≤ K - 2 := by omega
  have hmM : M ≤ K - 2 := by omega
  have hmpos : (0 : ℚ) < ((K - 2 : Nat) : ℚ) := by exact_mod_cast (show 0 < K - 2 by omega)
  have hlarge : 512 * (r : ℚ) ^ 4 / ((K - 2 : Nat) : ℚ) ≤ ε / 2 := by
    apply (div_le_iff₀ hmpos).mpr
    have hbound : (1024 : ℚ) * (r : ℚ) ^ 4 / ε < ((K - 2 : Nat) : ℚ) :=
      hM.trans_le (by exact_mod_cast hmM)
    have hh := (div_lt_iff₀ hε).mp hbound
    nlinarith
  have hb := SuperpermutationUpperBound.Bounds.floor_parameter_bounds (K - 2) r hrNat hmr
  obtain ⟨w, hw, hlen⟩ := hfin (K - 2) (by omega) ((K - 2) / r) (by omega) hb.2.1
  have hlength : (w.length : ℚ) ≤ (F3 ((K - 2) + 2) : ℚ) + (κ + ε) * (Fourth ((K - 2) + 2) : ℚ) := by
    apply hlen.trans
    apply (bound_floor_majorant κ γ hγ0 hγ1 (K - 2) r hrNat hmr).trans
    apply add_le_add (le_refl _)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have hKeq : K - 2 + 2 = K := by omega
  have hout : ∃ w : Word (K - 2 + 2), IsSuperpermutation w ∧
      (w.length : ℚ) ≤ (F3 (K - 2 + 2) : ℚ) + (κ + ε) * (Fourth (K - 2 + 2) : ℚ) := ⟨w, hw, hlength⟩
  exact Eq.mp (congrArg (fun n => ∃ w : Word n, IsSuperpermutation w ∧
      (w.length : ℚ) ≤ (F3 n : ℚ) + (κ + ε) * (Fourth n : ℚ)) hKeq) hout

end SuperpermutationUpperBound43586371.Uniform
