import SuperpermutationUpperBound305989.Fifteen

/-!
# All sizes from 16 symbols on

The level on 15 symbols of `Fifteen.lean` satisfies the divisibility condition, so from there on
transport works as in `AllSizes.lean`: level `k` has `k + 15` symbols, alphabet `alphB k` (new
letters 16, 17, …), `k + 13` ports, `(k + 13)!` rows with total charge `11771/23760 · (k + 13)!`,
and `23333/2217600 · (k + 12)!` connector cycles.  `word_ledgerB` is the natural-number form of the
finite bound on `k + 16` symbols.
-/

namespace SuperpermutationUpperBound305989

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

/-- The ordinary letters on `k + 15` symbols. -/
def alphB : Nat → List Nat
  | 0 => alphabet 3
  | k + 1 => (k + 16) :: alphB k

theorem alphB_length (k : Nat) : (alphB k).length = k + 13 + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [alphB, ih]

theorem alphB_lt (k : Nat) : ∀ a ∈ alphB k, a < k + 16 := by
  induction k with
  | zero => decide
  | succ k ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have := ih a ha
      omega

theorem alphB_fresh (k : Nat) : k + 16 ∉ alphB k :=
  fun h => Nat.lt_irrefl _ (alphB_lt k _ h)

theorem alphB_nodup (k : Nat) : (alphB k).Nodup := by
  induction k with
  | zero => decide
  | succ k ih => exact List.nodup_cons.mpr ⟨alphB_fresh k, ih⟩

theorem alphB_nine (k : Nat) : 9 ∉ alphB k := by
  induction k with
  | zero => decide
  | succ k ih =>
    intro h
    rcases List.mem_cons.mp h with h | h
    · omega
    · exact ih h

theorem alphB_ten (k : Nat) : 10 ∉ alphB k := by
  induction k with
  | zero => decide
  | succ k ih =>
    intro h
    rcases List.mem_cons.mp h with h | h
    · omega
    · exact ih h

theorem alphB_ne (k : Nat) : alphB k ≠ [] := by
  intro h
  have := alphB_length k
  rw [h] at this
  simp at this

theorem alphB_full (k : Nat) : (10 :: (alphB k ++ [9])).Perm (List.range (k + 16)) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : (10 :: ((k + 16) :: alphB k ++ [9])).Perm
        ((k + 16) :: (10 :: (alphB k ++ [9]))) := List.Perm.swap _ _ _
    have h2 : ((k + 16) :: (10 :: (alphB k ++ [9]))).Perm
        ((k + 16) :: List.range (k + 16)) := ih.cons _
    have h3 : ((k + 16) :: List.range (k + 16)).Perm (List.range (k + 16) ++ [k + 16]) :=
      List.perm_append_comm (l₁ := [k + 16])
    have h4 : List.range (k + 1 + 16) = List.range (k + 16) ++ [k + 16] := by
      rw [show k + 1 + 16 = (k + 16) + 1 by omega, List.range_succ]
    rw [h4]
    exact h1.trans (h2.trans h3)

namespace Cert

variable (C : Cert) (K : BlockCert)

/-- The closed trails on `k + 15` symbols. -/
def compsB (C : Cert) (K : BlockCert) : Nat → List (List (Row Nat))
  | 0 => C.comps15 K
  | k + 1 => transportComps (compsB C K k) (k + 16) (k + 13)

/-- The connector cycles on `k + 16` symbols. -/
def cycB (C : Cert) (K : BlockCert) : Nat → List (List Nat)
  | 0 => C.circles15 K
  | k + 1 => extendCircles (cycB C K k) (k + 16)

theorem levelB (k : Nat) : Level (alphB k) (k + 13) (C.compsB K k) := by
  induction k with
  | zero => exact C.level15 K
  | succ k ih =>
    exact ih.transport (k + 16) (alphB_length k) (by omega) (alphB_fresh k) (by omega)

theorem completeB (k : Nat) : BlockComplete (alphB k) (C.compsB K k).flatten := by
  induction k with
  | zero => exact C.complete15 K
  | succ k ih =>
    have hp := transportComps_flatten_perm (C.compsB K k) (k + 16) (k + 13) (by omega)
      ((C.levelB K k).len (alphB_length k))
    have hc := ih.transport (C.levelB K k).basedOn_flatten (alphB_nodup k) (alphB_ne k)
      (alphB_fresh k)
    intro x hx
    obtain ⟨r, hr, hrx⟩ := hc x hx
    exact ⟨r, hp.mem_iff.mpr hr, hrx⟩

theorem countsB (k : Nat) : (C.compsB K k).flatten.length = (k + 13).factorial ∧
    23760 * ((C.compsB K k).flatten.map Row.charge).sum = 11771 * (k + 13).factorial := by
  induction k with
  | zero =>
    have h := C.counts15 K
    constructor
    · rw [show C.compsB K 0 = C.comps15 K from rfl, h.1]
      decide
    · rw [show C.compsB K 0 = C.comps15 K from rfl, h.2]
      decide
  | succ k ih =>
    have h := (C.levelB K k).transport_counts (k + 16) (alphB_length k) (by omega)
      (alphB_fresh k) (by omega)
    have hf : (k + 1 + 13).factorial = (k + 13 + 1) * (k + 13).factorial := by
      rw [show k + 1 + 13 = (k + 13) + 1 by omega, Nat.factorial_succ]
    constructor
    · rw [show C.compsB K (k + 1) = transportComps (C.compsB K k) (k + 16) (k + 13) from rfl,
        h.1, ih.1, hf]
    · rw [show C.compsB K (k + 1) = transportComps (C.compsB K k) (k + 16) (k + 13) from rfl,
        h.2, hf, ← Nat.mul_assoc, Nat.mul_comm 23760, Nat.mul_assoc, ih.2, ← Nat.mul_assoc,
        Nat.mul_comm (k + 13 + 1) 11771, Nat.mul_assoc]

theorem cycB_support (k : Nat) : ∀ c ∈ C.cycB K k, ∀ a ∈ c, a < k + 16 ∧ a ≠ 9 := by
  induction k with
  | zero => exact C.circles15_support K
  | succ k ih => exact extend_support ih (by omega)

theorem cycB_valid (k : Nat) : CircleFamilyValid (k + 13) (C.cycB K k) := by
  induction k with
  | zero => exact C.circles15_valid K
  | succ k ih => exact extend_valid ih (C.cycB_support K k)

theorem cycB_length (k : Nat) :
    2217600 * (C.cycB K k).length = 23333 * (k + 12).factorial := by
  induction k with
  | zero =>
    rw [show C.cycB K 0 = C.circles15 K from rfl, C.circles15_length K]
    decide
  | succ k ih =>
    rw [show C.cycB K (k + 1) = extendCircles (C.cycB K k) (k + 16) from rfl,
      extend_length (C.cycB_valid K k),
      show k + 1 + 12 = (k + 12) + 1 by omega, Nat.factorial_succ, ← Nat.mul_assoc,
      Nat.mul_comm 2217600, Nat.mul_assoc, ih, ← Nat.mul_assoc, Nat.mul_comm (k + 13) 23333,
      Nat.mul_assoc]

theorem safeB (k : Nat) : ∀ rs ∈ C.compsB K k, SafeComp rs 10 (k + 13) (C.cycB K k) := by
  induction k with
  | zero => exact C.safe15 K
  | succ k ih =>
    exact (C.levelB K k).safe_transport (alphB_length k) (by omega) (alphB_ten k)
      (C.cycB_valid K k) ih (k + 16)

/-- The finite bound on `k + 16` symbols in natural numbers: `q` is the total charge and `c`
the number of connector cycles. -/
theorem word_ledgerB (C : Cert) (K : BlockCert) (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 14) :
    ∃ q c : Nat, ∃ w : Word (k + 16), IsSuperpermutation w ∧
      23760 * q = 11771 * (k + 13).factorial ∧ 2217600 * c = 23333 * (k + 12).factorial ∧
      w.length ≤ F3 (k + 16) + q + (k + 13) * c + (a - 2) * c +
        (k + 14 - a) * min c ((k + 15).descFactorial (k + 14 - a)) := by
  obtain ⟨t, J, w, hw, ht, hJ, hl⟩ := word_of_level (K := k + 16) (ell := k + 14 - a)
    (h := k + 13) (by omega) (by omega) (C.levelB K k) (alphB_length k) (by omega)
    (alphB_nodup k) (alphB_nine k) (alphB_ten k) (alphB_full k) (C.completeB K k)
    (C.cycB_valid K k) (C.safeB K k) ((Finset.range (k + 16)).erase 9)
    (fun c hc a ha => Finset.mem_erase.mpr
      ⟨(C.cycB_support K k c hc a ha).2, Finset.mem_range.mpr (C.cycB_support K k c hc a ha).1⟩)
    (fun c hc a ha => (C.cycB_support K k c hc a ha).1)
  have hcard : ((Finset.range (k + 16)).erase 9).card = k + 15 := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
    omega
  rw [hcard] at hJ
  refine ⟨((C.compsB K k).flatten.map Row.charge).sum, (C.cycB K k).length, w, hw,
    (C.countsB K k).2, C.cycB_length K k, ?_⟩
  rw [(C.countsB K k).1] at hl
  have hfac : (k + 16 + 1) * ((k + 13 + 1) * (k + 13 + 1 + 1) * (k + 13).factorial) +
      (k + 13 + 1) * (k + 13).factorial = F3 (k + 16) := by
    unfold F3
    rw [show k + 16 - 1 = k + 15 by omega, show k + 16 - 2 = k + 14 by omega,
      show k + 16 = (k + 15) + 1 by omega, Nat.factorial_succ (k + 15),
      show k + 15 = (k + 14) + 1 by omega, Nat.factorial_succ (k + 14),
      show k + 14 = (k + 13) + 1 by omega, Nat.factorial_succ (k + 13)]
    ring
  have hl' : w.length = (F3 (k + 16) + ((C.compsB K k).flatten.map Row.charge).sum +
      (k + 13) * (C.cycB K k).length) + (k + 14 - 2) * t - (k + 14 - a) * (t - J) := by
    rw [hl, ← hfac, show k + 13 - 1 = k + 14 - 2 by omega]
    ring_nf
  exact overlap_bound (m := k + 14) ha ham ht hJ hl'

end Cert

end SuperpermutationUpperBound305989
