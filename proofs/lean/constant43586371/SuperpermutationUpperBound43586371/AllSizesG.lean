import SuperpermutationUpperBound43586371.Stage
import SuperpermutationUpperBound.Bounds.Definitions

/-!
# From a closed level to every size

A `Closed` level (`Stage.lean`) on the letters `A` with `h` ports, whose completion uses the
symbols `0 .. h + 2` (`(10 :: (A ++ [9])).Perm (List.range (h + 3))`), transports to every size:
level `k` has the letters `alphG A (h + 3) k` (new letters `h + 3, h + 4, …`), `k + h` ports,
`(k + h)!` rows, and the charge and cycle counts keep their ratios to `(k + h)!` and
`(k + h - 1)!` (`Closed.all`).  `Closed.word` is `word_of_level` with the ledger written as in the
finite bound.  This is `AllSizesB.lean` of step (B) for an arbitrary starting level.
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

/-- The letters `k` levels above `A`: new letters `N, N + 1, …`. -/
def alphG (A : List Nat) (N : Nat) : Nat → List Nat
  | 0 => A
  | k + 1 => (k + N) :: alphG A N k

theorem alphG_full {A : List Nat} {N : Nat} (h0 : (10 :: (A ++ [9])).Perm (List.range N)) :
    ∀ k, (10 :: (alphG A N k ++ [9])).Perm (List.range (k + N)) := by
  intro k
  induction k with
  | zero => simpa [alphG] using h0
  | succ k ih =>
    have h1 : (10 :: ((k + N) :: alphG A N k ++ [9])).Perm
        ((k + N) :: (10 :: (alphG A N k ++ [9]))) := List.Perm.swap _ _ _
    have h2 : ((k + N) :: (10 :: (alphG A N k ++ [9]))).Perm
        ((k + N) :: List.range (k + N)) := ih.cons _
    have h3 : ((k + N) :: List.range (k + N)).Perm (List.range (k + N) ++ [k + N]) :=
      List.perm_append_comm (l₁ := [k + N])
    have h4 : List.range (k + 1 + N) = List.range (k + N) ++ [k + N] := by
      rw [show k + 1 + N = (k + N) + 1 by omega, List.range_succ]
    rw [h4]
    exact h1.trans (h2.trans h3)

theorem full_lt {A : List Nat} {N : Nat} (h : (10 :: (A ++ [9])).Perm (List.range N)) :
    ∀ a ∈ A, a < N := fun a ha =>
  List.mem_range.mp (h.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_append_left _ ha)))

theorem full_ten {A : List Nat} {N : Nat} (h : (10 :: (A ++ [9])).Perm (List.range N)) :
    10 < N := List.mem_range.mp (h.mem_iff.mp List.mem_cons_self)

namespace Closed

variable {A : List Nat} {h : Nat} {comps : List (List (Row Nat))} {circles : List (List Nat)}
  {R Q c : Nat}

theorem congr {R' Q' c' : Nat} (C : Closed A h comps circles R Q c) (hR : R = R') (hQ : Q = Q')
    (hc : c = c') : Closed A h comps circles R' Q' c' := by
  subst hR hQ hc
  exact C

theorem transport (C : Closed A h comps circles R Q c) (z : Nat) (hz : z ∉ A) (hz9 : z ≠ 9)
    (hz10 : z ≠ 10) :
    Closed (z :: A) (h + 1) (transportComps comps z h) (extendCircles circles z) ((h + 1) * R)
      ((h + 1) * Q) (h * c) := by
  have hn : 3 ≤ h + 1 := by have := C.two; omega
  have hne : A ≠ [] := by intro he; have := C.hA; rw [he] at this; simp at this
  have hc := C.level.transport_counts z C.hA hn hz hz9
  refine ⟨by simp [C.hA], by have := C.two; omega, List.nodup_cons.mpr ⟨hz, C.nodup⟩, ?_, ?_,
    C.level.transport z C.hA hn hz hz9, ?_, extend_valid C.valid C.support (not_mem_ten hz10 hz),
    extend_mem10 C.support, C.level.safe_transport C.hA hn C.ten C.valid C.safe z, ?_, ?_, ?_⟩
  · intro hm
    rcases List.mem_cons.mp hm with h | h
    · exact hz9 h.symm
    · exact C.nine h
  · intro hm
    rcases List.mem_cons.mp hm with h | h
    · exact hz10 h.symm
    · exact C.ten h
  · have hp := transportComps_flatten_perm comps z h hn (C.level.len C.hA)
    have hb := C.complete.transport C.level.basedOn_flatten C.nodup hne hz
    intro x hx
    obtain ⟨r, hr, hrx⟩ := hb x hx
    exact ⟨r, hp.mem_iff.mpr hr, hrx⟩
  · rw [hc.1, C.rows]
  · rw [hc.2, C.charge]
  · rw [extend_length C.valid, C.ncirc]

/-- The closed trails `k` levels up. -/
def compsUp (comps : List (List (Row Nat))) (h N : Nat) : Nat → List (List (Row Nat))
  | 0 => comps
  | k + 1 => transportComps (Closed.compsUp comps h N k) (k + N) (k + h)

/-- The connector cycles `k` levels up. -/
def cycUp (circles : List (List Nat)) (N : Nat) : Nat → List (List Nat)
  | 0 => circles
  | k + 1 => extendCircles (cycUp circles N k) (k + N)

/-- Every level from a closed one, with the counts as ratios to factorials. -/
theorem all (C : Closed A h comps circles h.factorial Q c)
    (hfull : (10 :: (A ++ [9])).Perm (List.range (h + 3))) (qn qd cn cd : Nat)
    (hq : qd * Q = qn * h.factorial) (hc : cd * c = cn * (h - 1).factorial) (k : Nat) :
    ∃ Q' c', Closed (alphG A (h + 3) k) (k + h) (Closed.compsUp comps h (h + 3) k)
      (Closed.cycUp circles (h + 3) k) (k + h).factorial Q' c' ∧
      qd * Q' = qn * (k + h).factorial ∧ cd * c' = cn * (k + h - 1).factorial := by
  induction k with
  | zero =>
    refine ⟨Q, c, ?_, ?_, ?_⟩
    · rw [Nat.zero_add]; exact C
    · rw [Nat.zero_add]; exact hq
    · rw [Nat.zero_add]; exact hc
  | succ k ih =>
    obtain ⟨Q', c', Ck, hq', hc'⟩ := ih
    have hf := alphG_full hfull k
    have hlt : ∀ a ∈ alphG A (h + 3) k, a < k + (h + 3) := full_lt hf
    have h10 := full_ten hfull
    have hz : k + (h + 3) ∉ alphG A (h + 3) k := fun hm => Nat.lt_irrefl _ (hlt _ hm)
    have Ct := Ck.transport (k + (h + 3)) hz (by omega) (by omega)
    have hfac : (k + 1 + h).factorial = (k + h + 1) * (k + h).factorial := by
      rw [show k + 1 + h = (k + h) + 1 by omega, Nat.factorial_succ]
    have hfac' : (k + 1 + h - 1).factorial = (k + h) * (k + h - 1).factorial := by
      have h2 := C.two
      rw [show k + 1 + h - 1 = k + h by omega]
      exact (Nat.mul_factorial_pred (by omega)).symm
    refine ⟨(k + h + 1) * Q', (k + h) * c', ?_, ?_, ?_⟩
    · rw [hfac, show k + 1 + h = k + h + 1 by omega]
      exact Ct
    · rw [hfac]
      calc qd * ((k + h + 1) * Q') = (k + h + 1) * (qd * Q') := by ring
        _ = (k + h + 1) * (qn * (k + h).factorial) := by rw [hq']
        _ = qn * ((k + h + 1) * (k + h).factorial) := by ring
    · rw [hfac']
      calc cd * ((k + h) * c') = (k + h) * (cd * c') := by ring
        _ = (k + h) * (cn * (k + h - 1).factorial) := by rw [hc']
        _ = cn * ((k + h) * (k + h - 1).factorial) := by ring

/-- The word of a closed level with `h!` rows, with the ledger of the finite bound. -/
theorem word (C : Closed A h comps circles h.factorial Q c) {K : Nat} (hK : K = h + 3)
    (hfull : (10 :: (A ++ [9])).Perm (List.range K)) (a : Nat) (ha : 2 ≤ a) (ham : a ≤ h + 1) :
    ∃ w : Word K, IsSuperpermutation w ∧
      w.length ≤ F3 K + Q + h * c + (a - 2) * c +
        (h + 1 - a) * min c ((K - 1).descFactorial (h + 1 - a)) := by
  subst hK
  have hn : 3 ≤ h + 1 := by have := C.two; omega
  have hsup : ∀ cc ∈ circles, ∀ b ∈ cc, b < h + 3 ∧ b ≠ 9 := by
    intro cc hc b hb
    have hm := C.support cc hc b hb
    refine ⟨List.mem_range.mp (hfull.mem_iff.mp ?_), ?_⟩
    · rcases List.mem_cons.mp hm with hm | hm
      · rw [hm]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)
    · rintro rfl
      rcases List.mem_cons.mp hm with hm | hm
      · exact absurd hm (by decide)
      · exact C.nine hm
  have h9 : 9 < h + 3 := List.mem_range.mp (hfull.mem_iff.mp
    (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)))
  obtain ⟨t, J, w, hw, ht, hJ, hl⟩ := word_of_level (K := h + 3) (ell := h + 1 - a)
    (h := h) rfl (by omega) C.level C.hA hn C.nodup C.nine C.ten hfull C.complete
    C.valid C.safe ((Finset.range (h + 3)).erase 9)
    (fun cc hc b hb => Finset.mem_erase.mpr
      ⟨(hsup cc hc b hb).2, Finset.mem_range.mpr (hsup cc hc b hb).1⟩)
    (fun cc hc b hb => (hsup cc hc b hb).1)
  have hcard : ((Finset.range (h + 3)).erase 9).card = h + 3 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr h9), Finset.card_range]
  rw [hcard] at hJ
  refine ⟨w, hw, ?_⟩
  rw [C.rows, C.charge, C.ncirc] at hl
  have hfac : (h + 3 + 1) * ((h + 1) * (h + 1 + 1) * h.factorial) +
      (h + 1) * h.factorial = F3 (h + 3) := by
    unfold F3
    rw [show h + 3 - 1 = h + 2 by omega, show h + 3 - 2 = h + 1 by omega,
      show h + 3 = (h + 2) + 1 by omega, Nat.factorial_succ (h + 2),
      show h + 2 = (h + 1) + 1 by omega, Nat.factorial_succ (h + 1), Nat.factorial_succ h]
    ring
  have hl' : w.length = (F3 (h + 3) + Q + h * c) + (h + 1 - 2) * t - (h + 1 - a) * (t - J) := by
    rw [hl, ← hfac, show h - 1 = h + 1 - 2 by omega]
    ring_nf
  rw [C.ncirc] at ht
  exact overlap_bound (m := h + 1) ha ham ht hJ hl'

end Closed

end SuperpermutationUpperBound43586371
