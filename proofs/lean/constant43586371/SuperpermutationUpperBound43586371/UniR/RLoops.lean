import SuperpermutationUpperBound43586371.UniR.RDistinct
import SuperpermutationUpperBound43586371.UniR.RArith

/-!
# The rows of the block R'(m) are distinct; the loops without a row (`PROOF_R.md`, sections 4-5)

The walks of `R'(m)`: `g ∈ Gl m` (`g ≡ 1 mod 3`, `2g + 5 ≤ m`), role order `σ ∈ {0, 1}` (`(A, B) = (t1, t2)` or
`(t2, t1)`, always `C = t3`), shift `s ∈ Sl m` (`{0}` for odd `m`, `{0, 1}` for even `m`), `Pm m` periods.
`block_canon_nodup`: the C-normal forms of all rows of all walks are distinct; `block_canon_mem`: each lies in
`above3T t1 t2 t3 d0`; `block_dloops_length`: exactly `L - |rows|` loops of `above3T` have no row.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SuperpermutationUpperBound43586371.UniR

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound43586371.Uniform

/-! ### Every arrangement of `d0` with two tokens is in `above3T` -/

theorem of_cyc_rot {X Y : List Nat} (h : CyclicEq X Y) : ∃ k, k < X.length ∧ X = rot Y k := by
  obtain ⟨j, hj⟩ := h
  have hpos : 0 < X.length := by have := j.isLt; omega
  have hl : Y.length = X.length := by rw [← hj]; simp
  refine ⟨(X.length - j.val % X.length) % X.length, Nat.mod_lt _ hpos, ?_⟩
  have e := rot_inverse X j.val
  rw [show rot X j.val = Y from hj] at e
  conv_lhs => rw [← e]
  have h := rot_mod Y (X.length - j.val % X.length)
  rw [hl] at h
  exact h.symm

theorem filt_cyc {x y : List Nat} (h : CyclicEq x y) (p : Nat → Bool) (hne : x.filter p ≠ []) :
    CyclicEq (x.filter p) (y.filter p) := h.filter p hne

theorem filter_append_ne {Y : List Nat} {t : Nat} (ht : t ∉ Y) :
    (Y ++ [t]).filter (fun y => y != t) = Y := by
  rw [List.filter_append]
  simp only [List.filter_cons, List.filter_nil, bne_self_eq_false, Bool.false_eq_true, if_false, List.append_nil]
  exact List.filter_eq_self.mpr (fun a ha => by simp; rintro rfl; exact ht ha)

theorem above3T_of {t1 t2 t3 : Nat} {d0 X : List Nat} (hX : X.Nodup) (h1 : t1 ∈ X) (h2 : t2 ∈ X)
    (h12 : t1 ≠ t2)
    (hf : CyclicEq ((X.filter (fun y => y != t2)).filter (fun y => y != t1)) d0) :
    X ++ [t3] ∈ above3T t1 t2 t3 d0 := by
  obtain ⟨Y2, hY2, hc2⟩ := canon_spec h2
  rw [hY2] at hc2
  obtain ⟨k, hk, hXk⟩ := of_cyc_rot hc2
  have hnd2 : (Y2 ++ [t2]).Nodup := hc2.nodup_iff.mp hX
  have ht2 : t2 ∉ Y2 := fun hm => (List.nodup_append.mp hnd2).2.2 t2 hm t2 (by simp) rfl
  have h1Y : t1 ∈ Y2 := by
    have := hc2.perm.mem_iff.mp h1
    rcases List.mem_append.mp this with h | h
    · exact h
    · simp at h; exact absurd h h12
  obtain ⟨Y1, hY1, hc1⟩ := canon_spec h1Y
  rw [hY1] at hc1
  obtain ⟨k2, hk2, hYk⟩ := of_cyc_rot hc1
  have hnd1 : (Y1 ++ [t1]).Nodup := hc1.nodup_iff.mp (List.nodup_append.mp hnd2).1
  have ht1 : t1 ∉ Y1 := fun hm => (List.nodup_append.mp hnd1).2.2 t1 hm t1 (by simp) rfl
  have e1 : CyclicEq (X.filter (fun y => y != t2)) Y2 := by
    have := filt_cyc hc2 (fun y => y != t2) (by
      intro he
      have : t1 ∈ X.filter (fun y => y != t2) := List.mem_filter.mpr ⟨h1, by simpa using h12⟩
      rw [he] at this; simp at this)
    rwa [filter_append_ne ht2] at this
  have e2 : CyclicEq ((X.filter (fun y => y != t2)).filter (fun y => y != t1)) (Y2.filter (fun y => y != t1)) :=
    filt_cyc e1 _ hf.nonempty_left
  have e3 : CyclicEq (Y2.filter (fun y => y != t1)) Y1 := by
    have := filt_cyc hc1 (fun y => y != t1) e2.nonempty_right
    rwa [filter_append_ne ht1] at this
  have e4 : CyclicEq d0 Y1 := (hf.symm.trans e2).trans e3
  obtain ⟨i, hi⟩ := e4
  have hl1 : Y1.length = d0.length := by rw [← show rot d0 i.val = Y1 from hi]; simp
  have hl2 : Y2.length = d0.length + 1 := by
    have := hc1.length_eq; simp at this; omega
  have hl3 : X.length = d0.length + 2 := by
    have := hc2.length_eq; simp at this; omega
  refine mem_above3T.mpr ⟨i.val, i.isLt, k2, by omega, k, by omega, ?_⟩
  unfold ent
  rw [show rot d0 i.val = Y1 from hi, ← hYk, ← hXk]

/-! ### The walks of the block -/

/-- The parameters `g`: `g ≡ 1 (mod 3)`, `2g + 5 ≤ m`. -/
def Gl (m : Nat) : List Nat := (List.range m).filter (fun g => g % 3 == 1 && decide (2 * g + 5 ≤ m))

/-- The shifts: `{0}` for odd `m`, `{0, 1}` for even `m`. -/
def Sl (m : Nat) : List Nat := if m % 2 = 1 then [0] else [0, 1]

/-- The number of periods of a walk. -/
def Pm (m : Nat) : Nat := if m % 2 = 1 then m else m / 2

def rA (σ t1 t2 : Nat) : Nat := if σ = 0 then t1 else t2
def rB (σ t1 t2 : Nat) : Nat := if σ = 0 then t2 else t1

/-- The walk descriptors `(g, σ, s)`. -/
def Dl (m : Nat) : List (Nat × Nat × Nat) :=
  (Gl m).flatMap fun g => [0, 1].flatMap fun σ => (Sl m).map fun s => (g, σ, s)

/-- Period `k` of the walk `d`. -/
def pD (d0 : List Nat) (t1 t2 t3 : Nat) (d : Nat × Nat × Nat) (k : Nat) : Pg :=
  pgOf (rot d0 (d.2.2 + 2 * k + 2)) d.1 (rA d.2.1 t1 t2) (rB d.2.1 t1 t2) t3

/-- The walk `d`. -/
def walkD (d0 : List Nat) (t1 t2 t3 : Nat) (d : Nat × Nat × Nat) : List (Row Nat) :=
  walkR d0 d.1 (rA d.2.1 t1 t2) (rB d.2.1 t1 t2) t3 d.2.2 (Pm d0.length)

/-- All rows of the block. -/
def blockRows (d0 : List Nat) (t1 t2 t3 : Nat) : List (Row Nat) :=
  (Dl d0.length).flatMap (walkD d0 t1 t2 t3)

theorem mem_Gl {m g : Nat} : g ∈ Gl m ↔ g < m ∧ g % 3 = 1 ∧ 2 * g + 5 ≤ m := by
  simp [Gl]

theorem mem_Dl {m : Nat} {d : Nat × Nat × Nat} (h : d ∈ Dl m) :
    d.1 % 3 = 1 ∧ 2 * d.1 + 5 ≤ m ∧ d.2.1 < 2 ∧
      ((m % 2 = 1 ∧ d.2.2 = 0) ∨ (m % 2 = 0 ∧ d.2.2 < 2)) := by
  simp only [Dl, List.mem_flatMap, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at h
  obtain ⟨g, hg, σ, hσ, s, hs, rfl⟩ := h
  rw [mem_Gl] at hg
  refine ⟨hg.2.1, hg.2.2, by rcases hσ with h | h <;> simp [h], ?_⟩
  unfold Sl at hs
  by_cases hm : m % 2 = 1
  · rw [if_pos hm] at hs; simp at hs; left; exact ⟨hm, hs⟩
  · rw [if_neg hm] at hs; simp at hs; right; refine ⟨by omega, by rcases hs with h | h <;> simp [h]⟩

theorem Dl_nodup (m : Nat) : (Dl m).Nodup := by
  unfold Dl
  refine List.nodup_flatMap.mpr ⟨fun g _ => List.nodup_flatMap.mpr ⟨fun σ _ => ?_, ?_⟩, ?_⟩
  · refine List.Nodup.map (fun a b h => by simp at h; exact h) ?_
    unfold Sl; split_ifs <;> simp
  · refine List.Pairwise.imp_of_mem ?_ (by simp : [0, 1].Nodup)
    intro σ σ' _ _ hne x hx hx'
    simp at hx hx'
    obtain ⟨s, _, rfl⟩ := hx
    obtain ⟨s', _, h⟩ := hx'
    exact hne (by simp at h; exact h.1.symm)
  · have key : ∀ g x, x ∈ ([0, 1].flatMap fun σ => (Sl m).map fun s => ((g, σ, s) : Nat × Nat × Nat)) →
        x.1 = g := by
      intro g x hx
      simp only [List.mem_flatMap, List.mem_map] at hx
      obtain ⟨σ, _, s, _, rfl⟩ := hx; rfl
    refine List.Pairwise.imp_of_mem ?_ ((List.nodup_range).filter _)
    intro g g' _ _ hne x hx hx'
    exact hne ((key g x hx).symm.trans (key g' x hx'))

theorem Pm_spec (m : Nat) : (m % 2 = 1 ∧ Pm m = m) ∨ (m % 2 = 0 ∧ 2 * Pm m = m) := by
  unfold Pm; split_ifs with h
  · left; exact ⟨h, rfl⟩
  · right; exact ⟨by omega, by omega⟩

/-- The setting: old letters `d0` (`7 ≤ m`), tokens `t1 t2 t3`, all distinct and different from `9`. -/
structure Setting (d0 : List Nat) (t1 t2 t3 : Nat) : Prop where
  nd : (t3 :: t2 :: t1 :: d0).Nodup
  m7 : 7 ≤ d0.length

namespace Setting

variable {d0 : List Nat} {t1 t2 t3 : Nat}

theorem d0_nodup (S : Setting d0 t1 t2 t3) : d0.Nodup :=
  (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp S.nd).2).2).2

theorem t12 (S : Setting d0 t1 t2 t3) : t1 ≠ t2 := fun h => (List.nodup_cons.mp (List.nodup_cons.mp S.nd).2).1 (by simp [h])

theorem t1_d0 (S : Setting d0 t1 t2 t3) : t1 ∉ d0 := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp S.nd).2).2).1

theorem t2_d0 (S : Setting d0 t1 t2 t3) : t2 ∉ d0 := fun h => (List.nodup_cons.mp (List.nodup_cons.mp S.nd).2).1 (by simp [h])

/-- The period data of a walk satisfies the nodup hypothesis of `Pg`. -/
theorem pD_nd (S : Setting d0 t1 t2 t3) (d : Nat × Nat × Nat) (hσ : d.2.1 < 2) (k : Nat) :
    ((pD d0 t1 t2 t3 d k).C :: (pD d0 t1 t2 t3 d k).B :: (pD d0 t1 t2 t3 d k).A ::
      (pD d0 t1 t2 t3 d k).list).Nodup := by
  show (t3 :: rB d.2.1 t1 t2 :: rA d.2.1 t1 t2 :: (pgOf _ _ _ _ _).list).Nodup
  rw [pgOf_list]
  have hp : (t3 :: t2 :: t1 :: rot d0 (d.2.2 + 2 * k + 2)).Nodup :=
    ((((rot_perm d0 _).cons t1).cons t2).cons t3).nodup_iff.mpr S.nd
  unfold rA rB
  split_ifs
  · exact hp
  · exact hp.perm ((List.Perm.swap _ _ _).cons _)

end Setting

theorem pD_lens (d0 : List Nat) (t1 t2 t3 : Nat) (d : Nat × Nat × Nat) (k : Nat) (hg : d.1 + 4 ≤ d0.length) :
    (pD d0 t1 t2 t3 d k).mid1.length = d0.length - 2 - d.1 ∧ (pD d0 t1 t2 t3 d k).q.length = d.1 + 2 :=
  pgOf_lens' d0 _ _ _ _ _ hg

theorem walkD_eq (d0 : List Nat) (t1 t2 t3 : Nat) (d : Nat × Nat × Nat) (hg : d.1 + 4 ≤ d0.length) :
    walkD d0 t1 t2 t3 d = (List.range (Pm d0.length)).flatMap fun k =>
      (List.range (d0.length + 12)).map (pD d0 t1 t2 t3 d k).rowAt := by
  unfold walkD walkR
  congr 1; funext k
  rw [Pg.period_eq_range]
  obtain ⟨h1, h2⟩ := pD_lens d0 t1 t2 t3 d k hg
  unfold pD at h1 h2
  rw [h1, h2]
  congr 2
  omega

end SuperpermutationUpperBound43586371.UniR
