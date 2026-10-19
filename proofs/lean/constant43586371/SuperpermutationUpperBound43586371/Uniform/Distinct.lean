import SuperpermutationUpperBound43586371.Uniform.Canon

/-!
# C-normal forms of the rows of one period (`PROOF.md`, section 5)

Every row of a period is a rotation of `X ++ [C]` with `X = rot (arr f) j` for one of the four arrangements
`arr 0 = a1`, `arr 1 = u`, `arr 2 = a2`, `arr 3 = v` (`canon_rowAt`).  The invariants `key1` (the rotation of
`X` without `B` that ends with `A`) and `key2` (the rotation of `X` without `A` that ends with `B`) are computed
for the four arrangements (`key1_arr`, `key2_arr`), and each arrangement is written as an element of
`above3T` (`arr_yform`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SuperpermutationUpperBound43586371.Uniform

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

/-- The invariant of `X` read with `B` deleted: the rotation that ends with `A`. -/
def key1 (A B : Nat) (X : List Nat) : List Nat := canon A (X.filter (fun x => x != B))

/-- The invariant of `X` read with `A` deleted: the rotation that ends with `B`. -/
def key2 (A B : Nat) (X : List Nat) : List Nat := canon B (X.filter (fun x => x != A))

theorem key1_rot {A B : Nat} {X : List Nat} (hX : X.Nodup) (hA : A ∈ X) (hAB : A ≠ B) (j : Nat) :
    key1 A B (rot X j) = key1 A B X := by
  unfold key1
  rw [filter_rot]
  exact canon_rot (hX.filter _) (List.mem_filter.mpr ⟨hA, by simpa using hAB⟩) _

theorem key2_rot {A B : Nat} {X : List Nat} (hX : X.Nodup) (hB : B ∈ X) (hAB : A ≠ B) (j : Nat) :
    key2 A B (rot X j) = key2 A B X := by
  unfold key2
  rw [filter_rot]
  exact canon_rot (hX.filter _) (List.mem_filter.mpr ⟨hB, by simpa using hAB.symm⟩) _

theorem glue (a b : Nat) (f g : Nat → Row Nat) :
    (List.range a).map f ++ (List.range b).map g =
      (List.range (a + b)).map (fun i => if i < a then f i else g (i - a)) := by
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  · exact List.map_congr_left (fun i hi => by simp [List.mem_range.mp hi])
  · exact List.map_congr_left (fun i _ => by simp)

namespace Pd

variable (p : Pd)

def a1 : List Nat := [p.e1] ++ p.mid ++ [p.A, p.el, p.e0, p.B]
def a2 : List Nat := [p.e0, p.e1, p.B] ++ p.mid ++ [p.el, p.A]

/-- The four arrangements of a period: `a1`, `u`, `a2`, `v`. -/
def arr : Nat → List Nat
  | 0 => p.a1
  | 1 => p.arrU
  | 2 => p.a2
  | _ => p.arrV

theorem facts (hp : (p.C :: p.B :: p.A :: p.list).Nodup) :
    p.A ≠ p.B ∧ p.A ≠ p.C ∧ p.B ≠ p.C ∧ p.A ∉ p.list ∧ p.B ∉ p.list ∧ p.C ∉ p.list ∧
      p.list.Nodup := by
  simp only [List.nodup_cons, List.mem_cons, not_or] at hp
  exact ⟨fun h => hp.2.1.1 h.symm, fun h => hp.1.2.1 h.symm, fun h => hp.1.1 h.symm, hp.2.2.1,
    hp.2.1.2, hp.1.2.2, hp.2.2.2⟩

theorem not_mem_list {p : Pd} {x : Nat} (h : x ∉ p.list) :
    x ≠ p.e0 ∧ x ≠ p.e1 ∧ x ∉ p.mid ∧ x ≠ p.el := by
  simp [list] at h; tauto

theorem perm_a1 : (p.a1 ++ [p.C]).Perm (p.C :: p.B :: p.A :: p.list) := by
  rw [← Multiset.coe_eq_coe]
  simp only [a1, list, ← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

theorem perm_a2 : (p.a2 ++ [p.C]).Perm (p.C :: p.B :: p.A :: p.list) := by
  rw [← Multiset.coe_eq_coe]
  simp only [a2, list, ← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

theorem arr_perm (f : Nat) : (p.arr f ++ [p.C]).Perm (p.C :: p.B :: p.A :: p.list) := by
  match f with
  | 0 => exact p.perm_a1
  | 1 => exact p.perm_U
  | 2 => exact p.perm_a2
  | _ + 3 => exact p.perm_V

theorem arr_nodupC (hp : (p.C :: p.B :: p.A :: p.list).Nodup) (f : Nat) : (p.arr f ++ [p.C]).Nodup :=
  (p.arr_perm f).nodup_iff.mpr hp

theorem arr_nodup (hp : (p.C :: p.B :: p.A :: p.list).Nodup) (f : Nat) : (p.arr f).Nodup :=
  (List.nodup_append.mp (p.arr_nodupC hp f)).1

theorem C_not_mem_arr (hp : (p.C :: p.B :: p.A :: p.list).Nodup) (f : Nat) : p.C ∉ p.arr f := by
  intro hm
  exact (List.nodup_append.mp (p.arr_nodupC hp f)).2.2 p.C hm p.C (by simp) rfl

theorem arr_length (f : Nat) : (p.arr f).length = p.mid.length + 5 := by
  match f with
  | 0 => simp [arr, a1]
  | 1 => simp [arr, arrU]
  | 2 => simp [arr, a2]
  | _ + 3 => simp [arr, arrV]

theorem A_mem_arr (f : Nat) : p.A ∈ p.arr f := by
  match f with
  | 0 => simp [arr, a1]
  | 1 => simp [arr, arrU]
  | 2 => simp [arr, a2]
  | _ + 3 => simp [arr, arrV]

theorem B_mem_arr (f : Nat) : p.B ∈ p.arr f := by
  match f with
  | 0 => simp [arr, a1]
  | 1 => simp [arr, arrU]
  | 2 => simp [arr, a2]
  | _ + 3 => simp [arr, arrV]

/-! ### Rotations of the old letters -/

theorem rot_list_one : rot p.list 1 = [p.e1] ++ p.mid ++ [p.el, p.e0] := by
  simp only [list, List.cons_append, List.nil_append]
  rw [rot_cons_one_generic] <;> simp

theorem rot_list_two : rot p.list 2 = p.mid ++ [p.el, p.e0, p.e1] := by
  have h := rot_append_length [p.e0, p.e1] (p.mid ++ [p.el])
  simp only [list]
  simpa using h

theorem rot_list_m1 : rot p.list (p.mid.length + 2) = [p.el, p.e0, p.e1] ++ p.mid := by
  have h := rot_append_length ([p.e0, p.e1] ++ p.mid) [p.el]
  simp only [list]
  rw [show p.mid.length + 2 = ([p.e0, p.e1] ++ p.mid).length by simp <;> omega]
  simpa using h

/-! ### The invariants of the four arrangements -/

/-- `key1` of arrangement `f` is `rot list (cA f) ++ [A]`. -/
def cA (f : Nat) : Nat := if f ≤ 1 then p.mid.length + 2 else f - 2

/-- `key2` of arrangement `f` is `rot list (cB f) ++ [B]`. -/
def cB (f : Nat) : Nat := if f = 0 then 1 else 2

theorem mid_filter {x : Nat} (h : x ∉ p.mid) : p.mid.filter (fun y => y != x) = p.mid :=
  List.filter_eq_self.mpr (fun a ha => by simp; rintro rfl; exact h ha)

theorem key1_arr (hp : (p.C :: p.B :: p.A :: p.list).Nodup) (f : Nat) (hf : f < 4) :
    key1 p.A p.B (p.arr f) = rot p.list (p.cA f) ++ [p.A] := by
  obtain ⟨hAB, hAC, hBC, hA, hB, hC, hl⟩ := p.facts hp
  obtain ⟨h0, h1, hm, hle⟩ := not_mem_list hB
  have hnd := (p.arr_nodup hp f).filter (fun x => x != p.B)
  unfold key1
  match f, hf with
  | 0, _ =>
    have e : (p.arr 0).filter (fun x => x != p.B) = ([p.e1] ++ p.mid) ++ [p.A] ++ [p.el, p.e0] := by
      simp [arr, a1, List.filter_append, p.mid_filter hm, Ne.symm h0, Ne.symm h1, Ne.symm hle, hAB]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (cyc_mid _ _ _), cA, if_pos (by omega), rot_list_m1] <;> simp
  | 1, _ =>
    have e : (p.arr 1).filter (fun x => x != p.B) = p.mid ++ [p.A] ++ [p.el, p.e0, p.e1] := by
      simp [arr, arrU, List.filter_append, p.mid_filter hm, Ne.symm h0, Ne.symm h1, Ne.symm hle, hAB]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (cyc_mid _ _ _), cA, if_pos (by omega), rot_list_m1] <;> simp
  | 2, _ =>
    have e : (p.arr 2).filter (fun x => x != p.B) = p.list ++ [p.A] := by
      simp [arr, a2, list, List.filter_append, p.mid_filter hm, Ne.symm h0, Ne.symm h1, Ne.symm hle, hAB]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (CyclicEq.refl (by simp)), cA, if_neg (by omega)] <;> simp
  | 3, _ =>
    have e : (p.arr 3).filter (fun x => x != p.B) = rot p.list 1 ++ [p.A] := by
      rw [rot_list_one]
      simp [arr, arrV, List.filter_append, p.mid_filter hm, Ne.symm h0, Ne.symm h1, Ne.symm hle, hAB]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (CyclicEq.refl (by simp)), cA, if_neg (by omega)]

theorem key2_arr (hp : (p.C :: p.B :: p.A :: p.list).Nodup) (f : Nat) (hf : f < 4) :
    key2 p.A p.B (p.arr f) = rot p.list (cB f) ++ [p.B] := by
  obtain ⟨hAB, hAC, hBC, hA, hB, hC, hl⟩ := p.facts hp
  obtain ⟨h0, h1, hm, hle⟩ := not_mem_list hA
  have hnd := (p.arr_nodup hp f).filter (fun x => x != p.A)
  unfold key2
  match f, hf with
  | 0, _ =>
    have e : (p.arr 0).filter (fun x => x != p.A) = rot p.list 1 ++ [p.B] := by
      rw [rot_list_one]
      simp [arr, a1, List.filter_append, p.mid_filter hm, Ne.symm h0, Ne.symm h1, Ne.symm hle, hAB.symm]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (CyclicEq.refl (by simp)), cB, if_pos rfl]
  | 1, _ =>
    have e : (p.arr 1).filter (fun x => x != p.A) = rot p.list 2 ++ [p.B] := by
      rw [rot_list_two]
      simp [arr, arrU, List.filter_append, p.mid_filter hm, Ne.symm h0, Ne.symm h1, Ne.symm hle, hAB.symm]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (CyclicEq.refl (by simp)), cB, if_neg (by omega)]
  | 2, _ =>
    have e : (p.arr 2).filter (fun x => x != p.A) = [p.e0, p.e1] ++ [p.B] ++ (p.mid ++ [p.el]) := by
      simp [arr, a2, List.filter_append, p.mid_filter hm, Ne.symm h0, Ne.symm h1, Ne.symm hle, hAB.symm]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (cyc_mid _ _ _), cB, if_neg (by omega), rot_list_two] <;> simp
  | 3, _ =>
    have e : (p.arr 3).filter (fun x => x != p.A) = [p.e1] ++ [p.B] ++ (p.mid ++ [p.el, p.e0]) := by
      simp [arr, arrV, List.filter_append, p.mid_filter hm, Ne.symm h0, Ne.symm h1, Ne.symm hle, hAB.symm]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (cyc_mid _ _ _), cB, if_neg (by omega), rot_list_two] <;> simp

/-! ### The arrangements as elements of `above3T` -/

def iota (f : Nat) : Nat := if f = 0 then 2 else if f = 1 then 3 else if f = 2 then 2 else 1

def kappa (f : Nat) : Nat := if f ≤ 1 then 0 else if f = 2 then p.mid.length + 2 else p.mid.length + 3

theorem arr_yform (f : Nat) (hf : f < 4) :
    p.arr f = rot (rot (rot p.list (p.cA f) ++ [p.A]) (iota f) ++ [p.B]) (p.kappa f) := by
  match f, hf with
  | 0, _ =>
    simp only [cA, iota, kappa, if_pos (show (0 : Nat) ≤ 1 by omega), if_pos rfl, rot_zero, rot_list_m1]
    rw [rot_eq_drop_append_take_of_le _ _ (by simp)]
    simp [arr, a1]
  | 1, _ =>
    simp only [cA, iota, kappa, if_pos (show (1 : Nat) ≤ 1 by omega), rot_zero, rot_list_m1]
    simp only [show (1 : Nat) ≠ 0 by omega, if_false, if_true]
    rw [rot_eq_drop_append_take_of_le _ _ (by simp)]
    simp [arr, arrU]
  | 2, _ =>
    simp only [cA, iota, kappa, if_neg (show ¬ (2 : Nat) ≤ 1 by omega),
      show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega, if_false, if_true, Nat.sub_self,
      rot_zero]
    rw [rot_eq_drop_append_take_of_le (p.list ++ [p.A]) 2 (by simp [list]),
      rot_eq_drop_append_take_of_le _ _ (by simp [list] <;> omega)]
    simp [arr, a2, list, List.take_append, List.drop_append]
  | 3, _ =>
    simp only [cA, iota, kappa, if_neg (show ¬ (3 : Nat) ≤ 1 by omega),
      show (3 : Nat) ≠ 0 by omega, show (3 : Nat) ≠ 1 by omega, show (3 : Nat) ≠ 2 by omega,
      if_false, show (3 : Nat) - 2 = 1 by rfl, rot_list_one]
    rw [rot_eq_drop_append_take_of_le (([p.e1] ++ p.mid ++ [p.el, p.e0]) ++ [p.A]) 1 (by simp),
      rot_eq_drop_append_take_of_le _ _ (by simp <;> omega)]
    simp [arr, arrV, List.take_append, List.drop_append]

/-! ### The rows of a period by index -/

/-- Row `i` of the period (`i < m + 12`, `m = |mid| + 3`). -/
def rowAt (i : Nat) : Row Nat :=
  if i < 2 + 1 + (p.mid.length + 3 + 1) + (2 + 1) then
    (if i < 2 + 1 + (p.mid.length + 3 + 1) then
      (if i < 2 + 1 then sweepRow p.arrW p.B 2 i
       else sweepRow p.arrU p.C (p.mid.length + 3) (i - (2 + 1)))
     else sweepRow p.arrY p.A 2 (i - (2 + 1 + (p.mid.length + 3 + 1))))
  else sweepRow p.arrV p.C 4 (i - (2 + 1 + (p.mid.length + 3 + 1) + (2 + 1)))

theorem period_eq_range : p.period = (List.range (p.mid.length + 15)).map p.rowAt := by
  unfold period sweep
  rw [glue, glue, glue]
  rw [show 2 + 1 + (p.mid.length + 3 + 1) + (2 + 1) + (4 + 1) = p.mid.length + 15 by omega]
  rfl

/-- The arrangement and the rotation of the C-normal form of row `i` (`m = |mid| + 3`). -/
def famOf (m i : Nat) : Nat :=
  if i < m + 7 then (if i < m + 4 then (if i < 2 then 0 else 1) else (if i < m + 6 then 2 else 3)) else 3

def jjOf (m i : Nat) : Nat :=
  if i < m + 7 then
    (if i < m + 4 then
      (if i = 0 then 0 else if i = 1 then m + 1 else if i = 2 then m else if i = 3 then m + 1 else i - 4)
     else (if i = m + 4 then 0 else if i = m + 5 then m + 1 else m))
  else (if i = m + 7 then m + 1 else i - (m + 8))

theorem famOf_lt (m i : Nat) : famOf m i < 4 := by unfold famOf; split_ifs <;> omega

theorem jjOf_lt (m i : Nat) (hi : i < m + 12) (hm : 5 ≤ m) : jjOf m i < m + 2 := by
  unfold jjOf; repeat' split
  all_goals omega

theorem jjOf_02 (m i : Nat) (h : famOf m i = 0 ∨ famOf m i = 2) : jjOf m i = 0 ∨ jjOf m i = m + 1 := by
  rcases h with h | h
  · have hi : i < 2 := by
      unfold famOf at h; repeat' split at h
      all_goals omega
    interval_cases i <;> simp [jjOf]
  · have hi : i = m + 4 ∨ i = m + 5 := by
      unfold famOf at h; repeat' split at h
      all_goals omega
    rcases hi with rfl | rfl <;> simp [jjOf]

theorem famOf_jjOf_inj (m i i' : Nat) (hm : 5 ≤ m) (hi : i < m + 12) (hi' : i' < m + 12)
    (hf : famOf m i = famOf m i') (hj : jjOf m i = jjOf m i') : i = i' := by
  unfold famOf at hf; unfold jjOf at hj; split_ifs at hf hj <;> omega

theorem canon_sweepC (s : List Nat) (C J t : Nat) (hnd : (s ++ [C]).Nodup) (ht : t ≤ J) :
    canon C (sweepRow s C J t).base = rot s (if t = 0 then s.length - 1 else t - 1) ++ [C] := by
  have hb : (sweepRow s C J t).base = rot s (if t = 0 then s.length - 1 else t - 1) ++ [C] := by
    unfold sweepRow
    by_cases h1 : t = 0
    · simp [h1, fullRow]
    · by_cases h2 : t < J
      · simp [h1, h2, fullRow]
      · have : t = J := by omega
        subst this
        simp [h1, shortRow]
  rw [hb]
  refine canon_eq ?_ (CyclicEq.refl (by simp))
  exact ((rot_perm s _).append_right [C]).nodup_iff.mpr hnd

theorem canon_of_cyc (hp : (p.C :: p.B :: p.A :: p.list).Nodup) {x : List Nat} (P Q : List Nat)
    (hx : x.Perm (p.C :: p.B :: p.A :: p.list)) (h : x = P ++ [p.C] ++ Q) :
    canon p.C x = Q ++ P ++ [p.C] := by
  have hc : CyclicEq x ((Q ++ P) ++ [p.C]) := by rw [h]; exact cyc_mid P Q p.C
  exact canon_eq (hx.nodup_iff.mpr hp) hc

theorem jj_U (m i : Nat) (h3 : 3 ≤ i) (h4 : i < m + 4) : jjOf m i = if i = 3 then m + 1 else i - 4 := by
  unfold jjOf; repeat' split
  all_goals omega

theorem jj_V (m i : Nat) (h7 : m + 7 ≤ i) : jjOf m i = if i = m + 7 then m + 1 else i - (m + 8) := by
  unfold jjOf; repeat' split
  all_goals omega

theorem canon_W (hp : (p.C :: p.B :: p.A :: p.list).Nodup) (i : Nat) (hi : i < 3) :
    canon p.C (sweepRow p.arrW p.B 2 i).base =
      rot (p.arr (if i < 2 then 0 else 1))
        (if i = 0 then 0 else if i = 1 then p.mid.length + 4 else p.mid.length + 3) ++ [p.C] := by
  have hW : p.arrW = ([p.e1] ++ p.mid ++ [p.A, p.el, p.e0]) ++ [p.C] := by simp [arrW]
  have hperm : ∀ j, (rot p.arrW j ++ [p.B]).Perm (p.C :: p.B :: p.A :: p.list) :=
    fun j => ((rot_perm _ j).append_right _).trans p.perm_W
  interval_cases i
  · have hb : rot p.arrW (p.arrW.length - 1) ++ [p.B] =
        [] ++ [p.C] ++ (([p.e1] ++ p.mid ++ [p.A, p.el, p.e0]) ++ [p.B]) := by
      rw [hW, show (([p.e1] ++ p.mid ++ [p.A, p.el, p.e0]) ++ [p.C]).length - 1 =
        ([p.e1] ++ p.mid ++ [p.A, p.el, p.e0]).length by simp, rot_append_length]
      simp
    rw [show (sweepRow p.arrW p.B 2 0).base = rot p.arrW (p.arrW.length - 1) ++ [p.B] by
      simp [sweepRow, fullRow]]
    rw [p.canon_of_cyc hp _ _ (hperm _) hb]
    simp [arr, a1]
  · have hb : rot p.arrW 0 ++ [p.B] = ([p.e1] ++ p.mid ++ [p.A, p.el, p.e0]) ++ [p.C] ++ [p.B] := by
      rw [rot_zero, hW]
    rw [show (sweepRow p.arrW p.B 2 1).base = rot p.arrW 0 ++ [p.B] by simp [sweepRow, fullRow]]
    rw [p.canon_of_cyc hp _ _ (hperm _) hb]
    have hr : rot p.a1 (p.mid.length + 4) = [p.B] ++ ([p.e1] ++ p.mid ++ [p.A, p.el, p.e0]) := by
      have h := rot_append_length ([p.e1] ++ p.mid ++ [p.A, p.el, p.e0]) [p.B]
      simp only [a1]
      rw [show p.mid.length + 4 = ([p.e1] ++ p.mid ++ [p.A, p.el, p.e0]).length by simp <;> omega]
      simpa using h
    simp only [show (1 : Nat) < 2 by omega, if_true, show (1 : Nat) ≠ 0 by omega, if_false, arr]
    rw [hr]
  · have hb : rot p.arrW 1 ++ [p.B] = (p.mid ++ [p.A, p.el, p.e0]) ++ [p.C] ++ [p.e1, p.B] := by
      simp only [arrW, List.cons_append, List.nil_append]
      rw [rot_cons_one_generic]; simp
    rw [show (sweepRow p.arrW p.B 2 2).base = rot p.arrW 1 ++ [p.B] by simp [sweepRow, shortRow]]
    rw [p.canon_of_cyc hp _ _ (hperm _) hb]
    have hr : rot p.arrU (p.mid.length + 3) = [p.e1, p.B] ++ (p.mid ++ [p.A, p.el, p.e0]) := by
      have h := rot_append_length (p.mid ++ [p.A, p.el, p.e0]) [p.e1, p.B]
      simp only [arrU]
      rw [show p.mid.length + 3 = (p.mid ++ [p.A, p.el, p.e0]).length by simp]
      simpa using h
    simp only [show ¬ (2 : Nat) < 2 by omega, if_false, show (2 : Nat) ≠ 0 by omega,
      show (2 : Nat) ≠ 1 by omega, arr]
    rw [hr]

theorem canon_Y (hp : (p.C :: p.B :: p.A :: p.list).Nodup) (t : Nat) (ht : t < 3) :
    canon p.C (sweepRow p.arrY p.A 2 t).base =
      rot (p.arr (if t < 2 then 2 else 3))
        (if t = 0 then 0 else if t = 1 then p.mid.length + 4 else p.mid.length + 3) ++ [p.C] := by
  have hY : p.arrY = ([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]) ++ [p.C] := by simp [arrY]
  have hperm : ∀ j, (rot p.arrY j ++ [p.A]).Perm (p.C :: p.B :: p.A :: p.list) :=
    fun j => ((rot_perm _ j).append_right _).trans p.perm_Y
  interval_cases t
  · have hb : rot p.arrY (p.arrY.length - 1) ++ [p.A] =
        [] ++ [p.C] ++ (([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]) ++ [p.A]) := by
      rw [hY, show (([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]) ++ [p.C]).length - 1 =
        ([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]).length by simp, rot_append_length]
      simp
    rw [show (sweepRow p.arrY p.A 2 0).base = rot p.arrY (p.arrY.length - 1) ++ [p.A] by
      simp [sweepRow, fullRow]]
    rw [p.canon_of_cyc hp _ _ (hperm _) hb]
    simp [arr, a2]
  · have hb : rot p.arrY 0 ++ [p.A] = ([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]) ++ [p.C] ++ [p.A] := by
      rw [rot_zero, hY]
    rw [show (sweepRow p.arrY p.A 2 1).base = rot p.arrY 0 ++ [p.A] by simp [sweepRow, fullRow]]
    rw [p.canon_of_cyc hp _ _ (hperm _) hb]
    have hr : rot p.a2 (p.mid.length + 4) = [p.A] ++ ([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]) := by
      have h := rot_append_length ([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]) [p.A]
      simp only [a2]
      rw [show p.mid.length + 4 = ([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]).length by simp <;> omega]
      simpa using h
    simp only [show (1 : Nat) < 2 by omega, if_true, show (1 : Nat) ≠ 0 by omega, if_false, arr]
    rw [hr]
  · have hb : rot p.arrY 1 ++ [p.A] = ([p.e1, p.B] ++ p.mid ++ [p.el]) ++ [p.C] ++ [p.e0, p.A] := by
      simp only [arrY, List.cons_append, List.nil_append]
      rw [rot_cons_one_generic]; simp
    rw [show (sweepRow p.arrY p.A 2 2).base = rot p.arrY 1 ++ [p.A] by simp [sweepRow, shortRow]]
    rw [p.canon_of_cyc hp _ _ (hperm _) hb]
    have hr : rot p.arrV (p.mid.length + 3) = [p.e0, p.A] ++ ([p.e1, p.B] ++ p.mid ++ [p.el]) := by
      have h := rot_append_length ([p.e1, p.B] ++ p.mid ++ [p.el]) [p.e0, p.A]
      simp only [arrV]
      rw [show p.mid.length + 3 = ([p.e1, p.B] ++ p.mid ++ [p.el]).length by simp <;> omega]
      simpa using h
    simp only [show ¬ (2 : Nat) < 2 by omega, if_false, show (2 : Nat) ≠ 0 by omega,
      show (2 : Nat) ≠ 1 by omega, arr]
    rw [hr]

theorem canon_rowAt (hp : (p.C :: p.B :: p.A :: p.list).Nodup) (i : Nat) (hi : i < p.mid.length + 15) :
    canon p.C (p.rowAt i).base =
      rot (p.arr (famOf (p.mid.length + 3) i)) (jjOf (p.mid.length + 3) i) ++ [p.C] := by
  have hndU : (p.arrU ++ [p.C]).Nodup := p.arr_nodupC hp 1
  have hndV : (p.arrV ++ [p.C]).Nodup := p.arr_nodupC hp 3
  rcases Nat.lt_or_ge i 3 with h3 | h3
  · have hr : p.rowAt i = sweepRow p.arrW p.B 2 i := by
      simp only [rowAt]; rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    rw [hr, p.canon_W hp i h3]
    interval_cases i <;> simp [famOf, jjOf]
  rcases Nat.lt_or_ge i (p.mid.length + 7) with h7 | h7
  · have hr : p.rowAt i = sweepRow p.arrU p.C (p.mid.length + 3) (i - 3) := by
      simp only [rowAt]; rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)]
    rw [hr, canon_sweepC _ _ _ _ hndU (by omega)]
    have hf : famOf (p.mid.length + 3) i = 1 := by
      unfold famOf; rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)]
    rw [hf, jj_U _ _ h3 (by omega)]
    by_cases h0 : i = 3
    · subst h0; simp [arr, len_arrU]
    · rw [if_neg (show i - 3 ≠ 0 by omega), if_neg h0, show i - 3 - 1 = i - 4 by omega]; rfl
  rcases Nat.lt_or_ge i (p.mid.length + 10) with h10 | h10
  · have hr : p.rowAt i = sweepRow p.arrY p.A 2 (i - (p.mid.length + 7)) := by
      simp only [rowAt]; rw [if_pos (by omega), if_neg (by omega)]
      congr 1; omega
    rw [hr, p.canon_Y hp _ (by omega)]
    have ht : i - (p.mid.length + 7) = 0 ∨ i - (p.mid.length + 7) = 1 ∨ i - (p.mid.length + 7) = 2 := by
      omega
    rcases ht with ht | ht | ht
    · rw [ht, show i = p.mid.length + 3 + 4 by omega]; simp [famOf, jjOf]
    · rw [ht, show i = p.mid.length + 3 + 5 by omega]; simp [famOf, jjOf]
    · rw [ht, show i = p.mid.length + 3 + 6 by omega]; simp [famOf, jjOf]
  · have hr : p.rowAt i = sweepRow p.arrV p.C 4 (i - (p.mid.length + 10)) := by
      simp only [rowAt]; rw [if_neg (by omega)]
      congr 1; omega
    rw [hr, canon_sweepC _ _ _ _ hndV (by omega)]
    have hf : famOf (p.mid.length + 3) i = 3 := by
      unfold famOf; rw [if_neg (by omega)]
    rw [hf, jj_V _ _ (by omega)]
    by_cases h0 : i = p.mid.length + 10
    · rw [if_pos (show i - (p.mid.length + 10) = 0 by omega), if_pos (by omega)]; simp [arr, len_arrV]
    · rw [if_neg (show i - (p.mid.length + 10) ≠ 0 by omega), if_neg (by omega),
        show i - (p.mid.length + 10) - 1 = i - (p.mid.length + 3 + 8) by omega]; rfl

end Pd

end SuperpermutationUpperBound43586371.Uniform
