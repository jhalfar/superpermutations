import SuperpermutationUpperBound1771.Thirteen
import SuperpermutationUpperBound.Bounds.Definitions

/-!
# All sizes from 13 symbols on

The selection on 12 symbols of `Hybrid.lean` satisfies the divisibility condition, so from
there on transport works as in `SuperpermutationUpperBound43/Family.lean`: level `k` has
`k + 12` symbols, alphabet `alphabet k` (new letters 13, 14, …), `k + 10` ports, `(k + 10)!`
rows with total charge `53/108 · (k + 10)!`, and `7875 · (k + 9)! / 9!` connector cycles.
`word_ledger` is the natural-number form of the finite bound on `k + 13` symbols.
-/

namespace SuperpermutationUpperBound1771

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

/-- The ordinary letters on `k + 12` symbols. -/
def alphabet : Nat → List Nat
  | 0 => alph11
  | k + 1 => (k + 13) :: alphabet k

theorem alphabet_length (k : Nat) : (alphabet k).length = k + 10 + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [alphabet, ih]

theorem alphabet_lt (k : Nat) : ∀ a ∈ alphabet k, a < k + 13 := by
  induction k with
  | zero => decide
  | succ k ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have := ih a ha
      omega

theorem alphabet_fresh (k : Nat) : k + 13 ∉ alphabet k :=
  fun h => Nat.lt_irrefl _ (alphabet_lt k _ h)

theorem alphabet_nodup (k : Nat) : (alphabet k).Nodup := by
  induction k with
  | zero => decide
  | succ k ih => exact List.nodup_cons.mpr ⟨alphabet_fresh k, ih⟩

theorem alphabet_nine (k : Nat) : 9 ∉ alphabet k := by
  induction k with
  | zero => decide
  | succ k ih =>
    intro h
    rcases List.mem_cons.mp h with h | h
    · omega
    · exact ih h

theorem alphabet_ten (k : Nat) : 10 ∉ alphabet k := by
  induction k with
  | zero => decide
  | succ k ih =>
    intro h
    rcases List.mem_cons.mp h with h | h
    · omega
    · exact ih h

theorem alphabet_ne (k : Nat) : alphabet k ≠ [] := by
  intro h
  have := alphabet_length k
  rw [h] at this
  simp at this

theorem alphabet_full (k : Nat) :
    (10 :: (alphabet k ++ [9])).Perm (List.range (k + 13)) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : (10 :: ((k + 13) :: alphabet k ++ [9])).Perm
        ((k + 13) :: (10 :: (alphabet k ++ [9]))) := List.Perm.swap _ _ _
    have h2 : ((k + 13) :: (10 :: (alphabet k ++ [9]))).Perm
        ((k + 13) :: List.range (k + 13)) := ih.cons _
    have h3 : ((k + 13) :: List.range (k + 13)).Perm (List.range (k + 13) ++ [k + 13]) :=
      List.perm_append_comm (l₁ := [k + 13])
    have h4 : List.range (k + 1 + 13) = List.range (k + 13) ++ [k + 13] := by
      rw [show k + 1 + 13 = (k + 13) + 1 by omega, List.range_succ]
    rw [h4]
    exact h1.trans (h2.trans h3)

namespace Cert

variable (C : Cert)

/-- The closed trails of the selection on `k + 12` symbols. -/
def comps (C : Cert) : Nat → List (List (Row Nat))
  | 0 => C.comps12
  | k + 1 => transportComps (comps C k) (k + 13) (k + 10)

/-- The connector cycles on `k + 13` symbols. -/
def cyc (C : Cert) : Nat → List (List Nat)
  | 0 => C.circles12
  | k + 1 => extendCircles (cyc C k) (k + 13)

theorem level (k : Nat) : Level (alphabet k) (k + 10) (C.comps k) := by
  induction k with
  | zero => exact C.level12
  | succ k ih =>
    exact ih.transport (k + 13) (alphabet_length k) (by omega) (alphabet_fresh k) (by omega)

theorem complete (k : Nat) : BlockComplete (alphabet k) (C.comps k).flatten := by
  induction k with
  | zero => exact C.complete12
  | succ k ih =>
    have hp := transportComps_flatten_perm (C.comps k) (k + 13) (k + 10) (by omega)
      ((C.level k).len (alphabet_length k))
    have hc := ih.transport (C.level k).basedOn_flatten (alphabet_nodup k) (alphabet_ne k)
      (alphabet_fresh k)
    intro x hx
    obtain ⟨r, hr, hrx⟩ := hc x hx
    exact ⟨r, hp.mem_iff.mpr hr, hrx⟩

theorem counts (k : Nat) : (C.comps k).flatten.length = (k + 10).factorial ∧
    108 * ((C.comps k).flatten.map Row.charge).sum = 53 * (k + 10).factorial := by
  induction k with
  | zero =>
    have h := C.comps12_counts
    constructor
    · rw [show C.comps 0 = C.comps12 from rfl, h.1]
      decide
    · rw [show C.comps 0 = C.comps12 from rfl, h.2]
      decide
  | succ k ih =>
    have h := (C.level k).transport_counts (k + 13) (alphabet_length k) (by omega)
      (alphabet_fresh k) (by omega)
    have hf : (k + 1 + 10).factorial = (k + 10 + 1) * (k + 10).factorial := by
      rw [show k + 1 + 10 = (k + 10) + 1 by omega, Nat.factorial_succ]
    constructor
    · rw [show C.comps (k + 1) = transportComps (C.comps k) (k + 13) (k + 10) from rfl, h.1,
        ih.1, hf]
    · rw [show C.comps (k + 1) = transportComps (C.comps k) (k + 13) (k + 10) from rfl, h.2,
        hf, ← Nat.mul_assoc, Nat.mul_comm 108, Nat.mul_assoc, ih.2, ← Nat.mul_assoc,
        Nat.mul_comm (k + 10 + 1) 53, Nat.mul_assoc]

theorem cyc_support (k : Nat) : ∀ c ∈ C.cyc k, ∀ a ∈ c, a < k + 13 ∧ a ≠ 9 := by
  induction k with
  | zero =>
    intro c hc a ha
    exact (by decide : ∀ b ∈ letters12, b < 0 + 13 ∧ b ≠ 9) a (C.circles12_support c hc a ha)
  | succ k ih =>
    intro c hc a ha
    have hc' : c ∈ extendCircles (C.cyc k) (k + 13) := hc
    simp only [extendCircles, circleExtensions, fullBases, List.mem_flatMap, List.mem_map,
      List.mem_range] at hc'
    obtain ⟨c0, hc0, j, _, rfl⟩ := hc'
    rcases List.mem_cons.mp ((insertLetter_perm c0 (k + 13) j).mem_iff.mp ha) with rfl | ha0
    · omega
    · have := ih c0 hc0 a ha0
      omega

theorem cyc_fresh (k : Nat) : ∀ c ∈ C.cyc k, k + 13 ∉ c :=
  fun c hc hm => Nat.lt_irrefl _ (C.cyc_support k c hc _ hm).1

theorem cyc_valid (k : Nat) : CircleFamilyValid (k + 10) (C.cyc k) := by
  induction k with
  | zero => exact C.circles12_valid
  | succ k ih => exact ih.extend (k + 13) (C.cyc_fresh k)

theorem cyc_length (k : Nat) : 362880 * (C.cyc k).length = 7875 * (k + 9).factorial := by
  induction k with
  | zero =>
    rw [show C.cyc 0 = C.circles12 from rfl, C.circles12_length]
    decide
  | succ k ih =>
    rw [show C.cyc (k + 1) = extendCircles (C.cyc k) (k + 13) from rfl,
      extendCircles_length (k + 10) (C.cyc k) (k + 13) (fun c hc => (C.cyc_valid k c hc).1),
      show k + 1 + 9 = (k + 9) + 1 by omega, Nat.factorial_succ, ← Nat.mul_assoc,
      Nat.mul_comm 362880, Nat.mul_assoc, ih, ← Nat.mul_assoc, Nat.mul_comm (k + 10) 7875,
      Nat.mul_assoc]

theorem safe (k : Nat) : ∀ rs ∈ C.comps k, SafeComp rs 10 (k + 10) (C.cyc k) := by
  induction k with
  | zero => exact C.safe12
  | succ k ih =>
    intro W hW
    obtain ⟨rs, hrs, p, hp, rfl⟩ := mem_transportComps.mp hW
    exact (ih rs hrs).transport (k + 13) (by omega) (C.cyc_valid k)
      ((C.level k).len (alphabet_length k) rs hrs) ((C.level k).kind rs hrs)
      ((C.level k).fresh (alphabet_ten k) rs hrs) p hp

/-- The finite bound on `k + 13` symbols in natural numbers: `q` is the total charge and
`c` the number of connector cycles. -/
theorem word_ledger (C : Cert) (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 11) :
    ∃ q c : Nat, ∃ w : Word (k + 13), IsSuperpermutation w ∧
      108 * q = 53 * (k + 10).factorial ∧ 362880 * c = 7875 * (k + 9).factorial ∧
      w.length ≤ F3 (k + 13) + q + (k + 10) * c + (a - 2) * c +
        (k + 11 - a) * min c ((k + 12).descFactorial (k + 11 - a)) := by
  obtain ⟨t, J, w, hw, ht, hJ, hl⟩ := word_of_level (K := k + 13) (ell := k + 11 - a)
    (h := k + 10) (by omega) (by omega) (C.level k) (alphabet_length k) (by omega)
    (alphabet_nodup k) (alphabet_nine k) (alphabet_ten k) (alphabet_full k) (C.complete k)
    (C.cyc_valid k) (C.safe k) ((Finset.range (k + 13)).erase 9)
    (fun c hc a ha => Finset.mem_erase.mpr
      ⟨(C.cyc_support k c hc a ha).2, Finset.mem_range.mpr (C.cyc_support k c hc a ha).1⟩)
    (fun c hc a ha => (C.cyc_support k c hc a ha).1)
  have hcard : ((Finset.range (k + 13)).erase 9).card = k + 12 := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
    omega
  rw [hcard] at hJ
  refine ⟨((C.comps k).flatten.map Row.charge).sum, (C.cyc k).length, w, hw, (C.counts k).2,
    C.cyc_length k, ?_⟩
  rw [(C.counts k).1] at hl
  have hfac : (k + 13 + 1) * ((k + 10 + 1) * (k + 10 + 1 + 1) * (k + 10).factorial) +
      (k + 10 + 1) * (k + 10).factorial = F3 (k + 13) := by
    unfold F3
    rw [show k + 13 - 1 = k + 12 by omega, show k + 13 - 2 = k + 11 by omega,
      show k + 13 = (k + 12) + 1 by omega, Nat.factorial_succ (k + 12),
      show k + 12 = (k + 11) + 1 by omega, Nat.factorial_succ (k + 11),
      show k + 11 = (k + 10) + 1 by omega, Nat.factorial_succ (k + 10)]
    ring
  have hl' : w.length = (F3 (k + 13) + ((C.comps k).flatten.map Row.charge).sum +
      (k + 10) * (C.cyc k).length) + (k + 11 - 2) * t - (k + 11 - a) * (t - J) := by
    rw [hl, ← hfac, show k + 10 - 1 = k + 11 - 2 by omega]
    ring_nf
  exact overlap_bound (m := k + 11) ha ham ht hJ hl'

end Cert

end SuperpermutationUpperBound1771
