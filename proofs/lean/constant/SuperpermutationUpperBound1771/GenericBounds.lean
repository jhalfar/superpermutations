import SuperpermutationUpperBound1771.AllSizes
import SuperpermutationUpperBound.Bounds.AsymptoticEpsilon

/-!
# The finite bound and the eventual coefficient 1771/3456

The arithmetic of `SuperpermutationUpperBound43/GenericBounds.lean` with the constants of the
selection with blocks: total charge `53/108 · (n-3)!` and `25/1152 · (n-3)!/(n-3)` connector
cycles, hence the principal coefficient `53/108 + 25/1152 = 1771/3456`.  The statements have
the shape of `finite_bound` and `asymptotic4380`, starting at 13 symbols.
-/

namespace SuperpermutationUpperBound1771.Bounds

open SuperpermutationUpperBound

set_option maxHeartbeats 2000000

/-- The finite expression for the selection with blocks and its connector cycles. -/
def bound (m a : Nat) : ℚ :=
  (F3 (m + 2) : ℚ)
    + ((1771 : ℚ) / 3456) * (Nat.factorial (m - 1) : ℚ)
    + ((a - 2 : Nat) : ℚ) * ((25 : ℚ) / 1152) * (Nat.factorial (m - 1) : ℚ)
        / ((m - 1 : Nat) : ℚ)
    + ((m - a : Nat) : ℚ) *
        min (((25 : ℚ) / 1152) * (Nat.factorial (m - 1) : ℚ) / ((m - 1 : Nat) : ℚ))
          ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (a + 1) : ℚ))

def FiniteStatement : Prop :=
  ∀ m : Nat, 11 ≤ m → ∀ a : Nat, 2 ≤ a → a ≤ m →
    ∃ w : Word (m + 2), IsSuperpermutation w ∧ (w.length : ℚ) ≤ bound m a

def AsymptoticStatement : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : Nat, 13 ≤ N ∧
    ∀ K : Nat, N ≤ K → ∃ w : Word K, IsSuperpermutation w ∧
      (w.length : ℚ) ≤ (F3 K : ℚ) + ((1771 : ℚ) / 3456 + ε) * (Fourth K : ℚ)

/-- The integer ledger of `Cert.word_ledger`. -/
def ledger (k a q c : Nat) : Nat :=
  F3 (k + 13) + q + (k + 10) * c + (a - 2) * c +
    (k + 11 - a) * min c ((k + 12).descFactorial (k + 11 - a))

theorem circle_count_scaled (k c : Nat)
    (hc : 362880 * c = 7875 * (k + 9).factorial) :
    362880 * ((k + 10) * c) = 7875 * (k + 10).factorial := by
  rw [show (k + 10).factorial = (k + 10) * (k + 9).factorial from
    Nat.factorial_succ (k + 9)]
  nlinarith

theorem circle_count_rat (k c : Nat)
    (hc : 362880 * c = 7875 * (k + 9).factorial) :
    (c : ℚ) = (25 / 1152 : ℚ) * ((k + 10).factorial : ℚ) / (k + 10 : Nat) := by
  have hk : ((k + 10 : Nat) : ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hk).mpr
  have he : (362880 : ℚ) * (((k + 10 : Nat) : ℚ) * (c : ℚ)) =
      7875 * ((k + 10).factorial : ℚ) := by
    exact_mod_cast circle_count_scaled k c hc
  linarith

theorem principal_numerator (k q c : Nat)
    (hq : 108 * q = 53 * (k + 10).factorial)
    (hc : 362880 * c = 7875 * (k + 9).factorial) :
    3456 * (q + (k + 10) * c) = 1771 * (k + 10).factorial := by
  have he := circle_count_scaled k c hc
  omega

theorem principal_rat (k q c : Nat)
    (hq : 108 * q = 53 * (k + 10).factorial)
    (hc : 362880 * c = 7875 * (k + 9).factorial) :
    ((q + (k + 10) * c : Nat) : ℚ) = (1771 / 3456 : ℚ) * ((k + 10).factorial : ℚ) := by
  have he : (3456 : ℚ) * ((q + (k + 10) * c : Nat) : ℚ) =
      1771 * ((k + 10).factorial : ℚ) := by
    exact_mod_cast principal_numerator k q c hq hc
  linarith

theorem overlap_state_count_rat (k a : Nat) (ha : a ≤ k + 11) :
    (((k + 12).descFactorial (k + 11 - a) : Nat) : ℚ) =
      ((k + 12).factorial : ℚ) / ((a + 1).factorial : ℚ) := by
  have hf : ((a + 1).factorial : ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hf).mpr
  have h := Nat.factorial_mul_descFactorial (show k + 11 - a ≤ k + 12 by omega)
  rw [show k + 12 - (k + 11 - a) = a + 1 by omega] at h
  have hq : (((a + 1).factorial * (k + 12).descFactorial (k + 11 - a) : Nat) : ℚ) =
      ((k + 12).factorial : ℚ) := by exact_mod_cast h
  rw [← hq]
  push_cast
  ring

theorem ledger_eq_bound (k a q c : Nat) (ha : a ≤ k + 11)
    (hq : 108 * q = 53 * (k + 10).factorial)
    (hc : 362880 * c = 7875 * (k + 9).factorial) :
    (ledger k a q c : ℚ) = bound (k + 11) a := by
  have hp := principal_rat k q c hq hc
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hp
  unfold ledger bound
  rw [show k + 11 + 2 = k + 13 by omega, show k + 11 - 1 = k + 10 by omega,
    show k + 11 + 1 = k + 12 by omega]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_min, Nat.cast_ofNat]
  rw [show (F3 (k + 13) : ℚ) + (q : ℚ) + ((k : ℚ) + 10) * (c : ℚ) =
      (F3 (k + 13) : ℚ) + (1771 / 3456 : ℚ) * ((k + 10).factorial : ℚ) by linarith]
  rw [circle_count_rat k c hc, overlap_state_count_rat k a ha]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  ring

theorem bound_of_nat_ledger (k a q c len : Nat) (ha : a ≤ k + 11)
    (hq : 108 * q = 53 * (k + 10).factorial)
    (hc : 362880 * c = 7875 * (k + 9).factorial)
    (hl : len ≤ ledger k a q c) : (len : ℚ) ≤ bound (k + 11) a := by
  rw [← ledger_eq_bound k a q c ha hq hc]
  exact_mod_cast hl

/-- The finite statement from the certificate. -/
theorem finite_of_cert (C : Cert) : FiniteStatement := by
  intro m hm a ha ham
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hak : a ≤ k + 11 := by omega
  obtain ⟨q, c, w, hs, hq, hc, hl⟩ := C.word_ledger k a ha hak
  have he : ∃ w : Word (k + 13), IsSuperpermutation w ∧
      (w.length : ℚ) ≤ bound (k + 11) a :=
    ⟨w, hs, bound_of_nat_ledger k a q c w.length hak hq hc hl⟩
  rw [Nat.add_comm 11 k]
  exact he

/-- The linear-overlap error is at most 2/r. -/
theorem linear_error_le (m a r : Nat) (hm : 2 ≤ m) (hr : 1 ≤ r)
    (har : a * r ≤ m) :
    ((a - 2 : Nat) : ℚ) * ((25 : ℚ) / 1152) / ((m - 1 : Nat) : ℚ) ≤
      2 / (r : ℚ) := by
  have hmQ : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hrQ : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by omega)
  have harQ : (a : ℚ) * r ≤ m := by exact_mod_cast har
  have hd : ((m - 1 : Nat) : ℚ) = (m : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hn : ((a - 2 : Nat) : ℚ) * ((25 : ℚ) / 1152) ≤ a := by
    have hsub : ((a - 2 : Nat) : ℚ) ≤ a := by exact_mod_cast Nat.sub_le a 2
    have hmul := mul_le_mul_of_nonneg_left
      (by norm_num : (25 : ℚ) / 1152 ≤ 1) (show (0 : ℚ) ≤ ((a - 2 : Nat) : ℚ) by positivity)
    have hm' : ((a - 2 : Nat) : ℚ) * ((25 : ℚ) / 1152) ≤ ((a - 2 : Nat) : ℚ) := by
      simpa only [mul_one] using hmul
    exact hm'.trans hsub
  rw [hd]
  apply (div_le_div_iff₀ (by linarith : (0 : ℚ) < (m : ℚ) - 1) hrQ).mpr
  have hnR := mul_le_mul_of_nonneg_right hn (le_of_lt hrQ)
  linarith

/-- With a = floor(m/r), both errors have an explicit elementary majorant. -/
theorem bound_floor_majorant (m r : Nat) (hr : 1 ≤ r) (hm : 8 * r ≤ m) :
    bound m (m / r) ≤
      (F3 (m + 2) : ℚ) +
        ((1771 : ℚ) / 3456 + 2 / (r : ℚ) + 512 * (r : ℚ) ^ 4 / m) *
          (Fourth (m + 2) : ℚ) := by
  have hb := SuperpermutationUpperBound.Bounds.floor_parameter_bounds m r hr hm
  have hm2 : 2 ≤ m := by omega
  have hlinear := linear_error_le m (m / r) r hm2 hr hb.2.2.1
  have hfactorial := SuperpermutationUpperBound.Bounds.factorial_error_le m (m / r) r
    (by omega) (by omega) hb.2.2.2
  have hfac : (Nat.factorial (m + 1) : ℚ) =
      ((m : ℚ) + 1) * m * (Nat.factorial (m - 1) : ℚ) := by
    rw [Nat.factorial_succ, ← Nat.mul_factorial_pred (n := m) (by omega)]
    push_cast
    ring
  have htail :
      ((m - m / r : Nat) : ℚ) *
          min (((25 : ℚ) / 1152) * (Nat.factorial (m - 1) : ℚ) / ((m - 1 : Nat) : ℚ))
            ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / r + 1) : ℚ)) ≤
        (m : ℚ) * ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / r + 1) : ℚ)) := by
    apply (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.sub_le m (m / r)
  have hFourth : (m + 2) - 3 = m - 1 := by omega
  unfold bound
  rw [Fourth, hFourth]
  calc
    _ ≤ (F3 (m + 2) : ℚ) + ((1771 : ℚ) / 3456) * (Nat.factorial (m - 1) : ℚ) +
          ((m / r - 2 : Nat) : ℚ) * ((25 : ℚ) / 1152) * (Nat.factorial (m - 1) : ℚ)
            / ((m - 1 : Nat) : ℚ) +
          (m : ℚ) * ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / r + 1) : ℚ)) :=
      add_le_add (le_refl _) htail
    _ = (F3 (m + 2) : ℚ) +
          ((1771 : ℚ) / 3456 +
            ((m / r - 2 : Nat) : ℚ) * ((25 : ℚ) / 1152) / ((m - 1 : Nat) : ℚ) +
            (m : ℚ) * m * (m + 1) / (Nat.factorial (m / r + 1) : ℚ)) *
          (Nat.factorial (m - 1) : ℚ) := by
      rw [hfac]
      ring
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact add_le_add (add_le_add (le_refl _) hlinear) hfactorial

/-- The finite statement implies the eventual coefficient 1771/3456 + ε. -/
theorem asymptotic_of_finite (hfinite : FiniteStatement) : AsymptoticStatement := by
  intro ε hε
  obtain ⟨r, hr⟩ := exists_nat_gt ((4 : ℚ) / ε)
  have hrpos : (0 : ℚ) < r := lt_trans (by positivity) hr
  have hrNat : 1 ≤ r := by exact_mod_cast hrpos
  have hsmall : (2 : ℚ) / r ≤ ε / 2 := by
    apply (div_le_iff₀ hrpos).mpr
    have hh := (div_lt_iff₀ hε).mp hr
    nlinarith
  obtain ⟨M, hM⟩ := exists_nat_gt ((1024 : ℚ) * (r : ℚ) ^ 4 / ε)
  refine ⟨13 + 8 * r + M, by omega, ?_⟩
  intro K hK
  have hm11 : 11 ≤ K - 2 := by omega
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
  obtain ⟨w, hw, hlen⟩ := hfinite (K - 2) hm11 ((K - 2) / r) (by omega) hb.2.1
  have hlength : (w.length : ℚ) ≤
      (F3 ((K - 2) + 2) : ℚ) +
        ((1771 : ℚ) / 3456 + ε) * (Fourth ((K - 2) + 2) : ℚ) := by
    apply hlen.trans
    apply (bound_floor_majorant (K - 2) r hrNat hmr).trans
    apply add_le_add (le_refl _)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have hKeq : K - 2 + 2 = K := by omega
  have hout : ∃ w : Word (K - 2 + 2), IsSuperpermutation w ∧
      (w.length : ℚ) ≤ (F3 (K - 2 + 2) : ℚ) +
        ((1771 : ℚ) / 3456 + ε) * (Fourth (K - 2 + 2) : ℚ) := ⟨w, hw, hlength⟩
  exact Eq.mp (congrArg (fun n => ∃ w : Word n, IsSuperpermutation w ∧
      (w.length : ℚ) ≤ (F3 n : ℚ) +
        ((1771 : ℚ) / 3456 + ε) * (Fourth n : ℚ)) hKeq) hout

theorem asymptotic_of_cert (C : Cert) : AsymptoticStatement :=
  asymptotic_of_finite (finite_of_cert C)

end SuperpermutationUpperBound1771.Bounds
