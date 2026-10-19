import SuperpermutationUpperBound43586371.UniR.RWalk
import SuperpermutationUpperBound43586371.Uniform.Distinct

/-!
# C-normal forms and keys of the rows of one period, for every `g` (`PROOF_R.md`, sections 2-3)

Every row is a rotation of `X ++ [C]` with `X = rot (arr f) j`, `arr 0 = a1`, `arr 1 = u`, `arr 2 = a2`,
`arr 3 = v` (`canon_rowAt`).  The keys of the arrangements in terms of the old letters `O = mid1 ++ q`:
`key1 (arr f) = rot O (cA f) ++ [A]` and `key2 (arr f) = rot O (cB f) ++ [B]` (`key1_arr`, `key2_arr`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SuperpermutationUpperBound43586371.UniR

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound43586371.Uniform

namespace Pg

variable (p : Pg)

def a1 : List Nat := [p.ql] ++ p.mid1 ++ [p.A] ++ p.q.dropLast ++ [p.B]
def a2 : List Nat := p.q.drop 1 ++ [p.B] ++ p.mid1 ++ [p.q0, p.A]

/-- The four arrangements: `a1`, `u`, `a2`, `v`. -/
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

theorem perm_a1 (h3 : 3 ≤ p.q.length) : (p.a1 ++ [p.C]).Perm (p.C :: p.B :: p.A :: p.list) := by
  obtain ⟨x0, x1, qm, xl, hq, hq0, hq1, hql⟩ := p.q_split h3
  refine perm_of_eq ([xl] ++ p.mid1 ++ [p.A, x0, x1] ++ qm ++ [p.B, p.C])
    ([p.C, p.B, p.A] ++ p.mid1 ++ [x0, x1] ++ qm ++ [xl]) (by simp [a1, hq, hql]) (by simp [list, hq]) ?_
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

theorem perm_a2 (h3 : 3 ≤ p.q.length) : (p.a2 ++ [p.C]).Perm (p.C :: p.B :: p.A :: p.list) := by
  obtain ⟨x0, x1, qm, xl, hq, hq0, hq1, hql⟩ := p.q_split h3
  refine perm_of_eq ([x1] ++ qm ++ [xl, p.B] ++ p.mid1 ++ [x0, p.A, p.C])
    ([p.C, p.B, p.A] ++ p.mid1 ++ [x0, x1] ++ qm ++ [xl]) (by simp [a2, hq, hq0]) (by simp [list, hq]) ?_
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

theorem arr_perm (h3 : 3 ≤ p.q.length) (f : Nat) :
    (p.arr f ++ [p.C]).Perm (p.C :: p.B :: p.A :: p.list) := by
  match f with
  | 0 => exact p.perm_a1 h3
  | 1 => exact p.perm_U
  | 2 => exact p.perm_a2 h3
  | _ + 3 => exact p.perm_V h3

theorem arr_nodupC (h3 : 3 ≤ p.q.length) (hp : (p.C :: p.B :: p.A :: p.list).Nodup) (f : Nat) :
    (p.arr f ++ [p.C]).Nodup :=
  (p.arr_perm h3 f).nodup_iff.mpr hp

theorem arr_nodup (h3 : 3 ≤ p.q.length) (hp : (p.C :: p.B :: p.A :: p.list).Nodup) (f : Nat) :
    (p.arr f).Nodup :=
  (List.nodup_append.mp (p.arr_nodupC h3 hp f)).1

theorem arr_length (h3 : 3 ≤ p.q.length) (f : Nat) : (p.arr f).length = p.mid1.length + p.q.length + 2 := by
  have h := (p.arr_perm h3 f).length_eq
  simp [list] at h; omega

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

/-! ### Keys -/

def cA (f : Nat) : Nat := if f ≤ 1 then p.mid1.length else p.mid1.length + f - 1
def cB (f : Nat) : Nat := if f = 0 then p.mid1.length + p.q.length - 1 else 0

theorem filt_self {x : Nat} {l : List Nat} (h : x ∉ l) : l.filter (fun y => y != x) = l :=
  List.filter_eq_self.mpr (fun a ha => by simp; rintro rfl; exact h ha)

theorem key1_arr (h3 : 3 ≤ p.q.length) (hp : (p.C :: p.B :: p.A :: p.list).Nodup) (f : Nat) (hf : f < 4) :
    key1 p.A p.B (p.arr f) = rot p.list (p.cA f) ++ [p.A] := by
  obtain ⟨hAB, hAC, hBC, hA, hB, hC, hl⟩ := p.facts hp
  obtain ⟨x0, x1, qm, xl, hq, hq0, hq1, hql⟩ := p.q_split h3
  have hBl : p.B ∉ p.mid1 ∧ p.B ≠ x0 ∧ p.B ≠ x1 ∧ p.B ∉ qm ∧ p.B ≠ xl := by
    simp only [list, hq, List.mem_append, List.mem_cons, not_or] at hB; tauto
  obtain ⟨hm, h0, h1, hqm, hxl⟩ := hBl
  have hnd := (p.arr_nodup h3 hp f).filter (fun x => x != p.B)
  have hrot : rot p.list p.mid1.length = (x0 :: x1 :: (qm ++ [xl])) ++ p.mid1 := by
    simp only [list, hq]; exact rot_append_length _ _
  unfold key1
  match f, hf with
  | 0, _ =>
    have e : (p.arr 0).filter (fun x => x != p.B) = ([xl] ++ p.mid1) ++ [p.A] ++ (x0 :: x1 :: qm) := by
      simp [arr, a1, hq, hql, List.filter_append, filt_self hm, filt_self hqm, Ne.symm h0, Ne.symm h1,
        Ne.symm hxl, hAB]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (cyc_mid _ _ _), cA, if_pos (by omega), hrot]; simp
  | 1, _ =>
    have e : (p.arr 1).filter (fun x => x != p.B) = p.mid1 ++ [p.A] ++ (x0 :: x1 :: (qm ++ [xl])) := by
      simp [arr, arrU, hq, List.filter_append, filt_self hm, filt_self hqm, Ne.symm h0, Ne.symm h1,
        Ne.symm hxl, hAB]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (cyc_mid _ _ _), cA, if_pos (by omega), hrot]
  | 2, _ =>
    have e : (p.arr 2).filter (fun x => x != p.B) = rot p.list (p.mid1.length + 1) ++ [p.A] := by
      rw [← rot_add, hrot, List.cons_append, rot_cons_one_generic]
      simp [arr, a2, hq, hq0, List.filter_append, filt_self hm, filt_self hqm, Ne.symm h0, Ne.symm h1,
        Ne.symm hxl, hAB]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (CyclicEq.refl (by simp)), cA, if_neg (by omega)]; rfl
  | 3, _ =>
    have e : (p.arr 3).filter (fun x => x != p.B) = rot p.list (p.mid1.length + 2) ++ [p.A] := by
      rw [← rot_add, hrot]
      rw [show (x0 :: x1 :: (qm ++ [xl])) ++ p.mid1 = [x0, x1] ++ (qm ++ [xl] ++ p.mid1) by simp]
      rw [show (2 : Nat) = [x0, x1].length by rfl, rot_append_length]
      simp [arr, arrV, hq, hq0, hq1, List.filter_append, filt_self hm, filt_self hqm, Ne.symm h0,
        Ne.symm h1, Ne.symm hxl, hAB]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (CyclicEq.refl (by simp)), cA, if_neg (by omega)]; rfl

theorem key2_arr (h3 : 3 ≤ p.q.length) (hp : (p.C :: p.B :: p.A :: p.list).Nodup) (f : Nat) (hf : f < 4) :
    key2 p.A p.B (p.arr f) = rot p.list (p.cB f) ++ [p.B] := by
  obtain ⟨hAB, hAC, hBC, hA, hB, hC, hl⟩ := p.facts hp
  obtain ⟨x0, x1, qm, xl, hq, hq0, hq1, hql⟩ := p.q_split h3
  have hAl : p.A ∉ p.mid1 ∧ p.A ≠ x0 ∧ p.A ≠ x1 ∧ p.A ∉ qm ∧ p.A ≠ xl := by
    simp only [list, hq, List.mem_append, List.mem_cons, not_or] at hA; tauto
  obtain ⟨hm, h0, h1, hqm, hxl⟩ := hAl
  have hnd := (p.arr_nodup h3 hp f).filter (fun x => x != p.A)
  unfold key2
  match f, hf with
  | 0, _ =>
    have e : (p.arr 0).filter (fun x => x != p.A) = rot p.list (p.mid1.length + p.q.length - 1) ++ [p.B] := by
      have hr : rot p.list (p.mid1.length + p.q.length - 1) = [xl] ++ (p.mid1 ++ x0 :: x1 :: qm) := by
        have h := rot_append_length (p.mid1 ++ x0 :: x1 :: qm) [xl]
        rw [show p.mid1.length + p.q.length - 1 = (p.mid1 ++ x0 :: x1 :: qm).length by rw [hq]; simp <;> omega]
        simp only [list, hq]
        simpa using h
      rw [hr]
      simp [arr, a1, hq, hql, List.filter_append, filt_self hm, filt_self hqm, Ne.symm h0, Ne.symm h1,
        Ne.symm hxl, hAB.symm]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (CyclicEq.refl (by simp)), cB, if_pos rfl]
  | 1, _ =>
    have e : (p.arr 1).filter (fun x => x != p.A) = rot p.list 0 ++ [p.B] := by
      simp [arr, arrU, list, hq, List.filter_append, filt_self hm, filt_self hqm, Ne.symm h0, Ne.symm h1,
        Ne.symm hxl, hAB.symm]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (CyclicEq.refl (by simp)), cB, if_neg (by omega)]
  | 2, _ =>
    have e : (p.arr 2).filter (fun x => x != p.A) = (x1 :: (qm ++ [xl])) ++ [p.B] ++ (p.mid1 ++ [x0]) := by
      simp [arr, a2, hq, hq0, List.filter_append, filt_self hm, filt_self hqm, Ne.symm h0, Ne.symm h1,
        Ne.symm hxl, hAB.symm]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (cyc_mid _ _ _), cB, if_neg (by omega)]
    simp [list, hq]
  | 3, _ =>
    have e : (p.arr 3).filter (fun x => x != p.A) = (qm ++ [xl]) ++ [p.B] ++ (p.mid1 ++ [x0, x1]) := by
      simp [arr, arrV, hq, hq0, hq1, List.filter_append, filt_self hm, filt_self hqm, Ne.symm h0,
        Ne.symm h1, Ne.symm hxl, hAB.symm]
    rw [e] at hnd ⊢
    rw [canon_eq hnd (cyc_mid _ _ _), cB, if_neg (by omega)]
    simp [list, hq]

/-! ### The rows of a period by index -/

def rowAt (i : Nat) : Row Nat :=
  if i < 2 + 1 + (p.mid1.length + 3 + 1) + (2 + 1) then
    (if i < 2 + 1 + (p.mid1.length + 3 + 1) then
      (if i < 2 + 1 then sweepRow p.arrW p.B 2 i
       else sweepRow p.arrU p.C (p.mid1.length + 3) (i - (2 + 1)))
     else sweepRow p.arrY p.A 2 (i - (2 + 1 + (p.mid1.length + 3 + 1))))
  else sweepRow p.arrV p.C (p.q.length + 1) (i - (2 + 1 + (p.mid1.length + 3 + 1) + (2 + 1)))

theorem period_eq_range : p.period = (List.range (p.mid1.length + p.q.length + 12)).map p.rowAt := by
  unfold period sweep
  rw [glue, glue, glue]
  rw [show 2 + 1 + (p.mid1.length + 3 + 1) + (2 + 1) + (p.q.length + 1 + 1) =
    p.mid1.length + p.q.length + 12 by omega]
  rfl

/-- The arrangement of row `i` (`M1 = |mid1|`). -/
def famOf (M1 i : Nat) : Nat := if i < 2 then 0 else if i < M1 + 7 then 1 else if i < M1 + 9 then 2 else 3

/-- The rotation of row `i` (`m = |mid1| + |q|`). -/
def jjOf (M1 m i : Nat) : Nat :=
  if i = 0 then 0 else if i = 1 then m + 1 else if i = 2 then m else if i = 3 then m + 1
  else if i < M1 + 7 then i - 4 else if i = M1 + 7 then 0 else if i = M1 + 8 then m + 1
  else if i = M1 + 9 then m else if i = M1 + 10 then m + 1 else i - (M1 + 11)

theorem famOf_lt (M1 i : Nat) : famOf M1 i < 4 := by unfold famOf; split_ifs <;> omega

theorem jjOf_lt (M1 m i : Nat) (hm : M1 + 3 ≤ m) (hi : i < m + 12) : jjOf M1 m i < m + 2 := by
  unfold jjOf; split_ifs <;> omega

theorem jjOf_02 (M1 m i : Nat) (h : famOf M1 i = 0 ∨ famOf M1 i = 2) :
    jjOf M1 m i = 0 ∨ jjOf M1 m i = m + 1 := by
  rcases h with h | h
  · have hi : i < 2 := by
      unfold famOf at h; repeat' split at h
      all_goals omega
    interval_cases i <;> simp [jjOf]
  · have hi : i = M1 + 7 ∨ i = M1 + 8 := by
      unfold famOf at h; repeat' split at h
      all_goals omega
    rcases hi with rfl | rfl <;> simp [jjOf]

/-- The index of a row from its arrangement and rotation. -/
def decIdx (M1 m f j : Nat) : Nat :=
  if f = 0 then (if j = 0 then 0 else 1)
  else if f = 1 then (if j = m then 2 else if j = m + 1 then 3 else j + 4)
  else if f = 2 then (if j = 0 then M1 + 7 else M1 + 8)
  else (if j = m then M1 + 9 else if j = m + 1 then M1 + 10 else j + M1 + 11)

theorem decIdx_spec (M1 m i : Nat) (h2 : 2 ≤ M1) (hm : M1 + 3 ≤ m) (hi : i < m + 12) :
    decIdx M1 m (famOf M1 i) (jjOf M1 m i) = i := by
  rcases Nat.lt_or_ge i 4 with h | h
  · interval_cases i <;> simp [decIdx, famOf, jjOf] <;> omega
  rcases Nat.lt_or_ge i (M1 + 7) with h' | h'
  · have hf : famOf M1 i = 1 := by unfold famOf; rw [if_neg (by omega), if_pos h']
    have hj : jjOf M1 m i = i - 4 := by
      unfold jjOf; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h']
    rw [hf, hj]; unfold decIdx
    rw [if_neg (by omega), if_pos rfl, if_neg (by omega), if_neg (by omega)]; omega
  rcases Nat.lt_or_ge i (M1 + 11) with h'' | h''
  · have hcase : i = M1 + 7 ∨ i = M1 + 8 ∨ i = M1 + 9 ∨ i = M1 + 10 := by omega
    rcases hcase with rfl | rfl | rfl | rfl
    · simp [decIdx, famOf, jjOf]
    · simp [decIdx, famOf, jjOf]
    · simp [decIdx, famOf, jjOf]
    · simp [decIdx, famOf, jjOf]
  · have hf : famOf M1 i = 3 := by unfold famOf; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hj : jjOf M1 m i = i - (M1 + 11) := by
      unfold jjOf
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [hf, hj]; unfold decIdx
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; omega

theorem famOf_jjOf_inj (M1 m i i' : Nat) (h2 : 2 ≤ M1) (hm : M1 + 3 ≤ m) (hi : i < m + 12)
    (hi' : i' < m + 12) (hf : famOf M1 i = famOf M1 i') (hj : jjOf M1 m i = jjOf M1 m i') : i = i' := by
  rw [← decIdx_spec M1 m i h2 hm hi, ← decIdx_spec M1 m i' h2 hm hi', hf, hj]

theorem canon_of_cyc (hp : (p.C :: p.B :: p.A :: p.list).Nodup) {x : List Nat} (P Q : List Nat)
    (hx : x.Perm (p.C :: p.B :: p.A :: p.list)) (h : x = P ++ [p.C] ++ Q) :
    canon p.C x = Q ++ P ++ [p.C] := by
  have hc : CyclicEq x ((Q ++ P) ++ [p.C]) := by rw [h]; exact cyc_mid P Q p.C
  exact canon_eq (hx.nodup_iff.mpr hp) hc

theorem canon_W (h3 : 3 ≤ p.q.length) (hp : (p.C :: p.B :: p.A :: p.list).Nodup) (i : Nat) (hi : i < 3) :
    canon p.C (sweepRow p.arrW p.B 2 i).base =
      rot (p.arr (if i < 2 then 0 else 1))
        (if i = 0 then 0 else if i = 1 then p.mid1.length + p.q.length + 1
          else p.mid1.length + p.q.length) ++ [p.C] := by
  set P := [p.ql] ++ p.mid1 ++ [p.A] ++ p.q.dropLast with hP
  have hPl : P.length = p.mid1.length + p.q.length + 1 := by
    have := p.len_arrW h3; simp [arrW, hP] at this ⊢; omega
  have hW : p.arrW = P ++ [p.C] := by simp [arrW, hP]
  have hperm : ∀ j, (rot p.arrW j ++ [p.B]).Perm (p.C :: p.B :: p.A :: p.list) :=
    fun j => ((rot_perm _ j).append_right _).trans (p.perm_W h3)
  interval_cases i
  · have hb : rot p.arrW (p.arrW.length - 1) ++ [p.B] = [] ++ [p.C] ++ (P ++ [p.B]) := by
      rw [hW, show (P ++ [p.C]).length - 1 = P.length by simp, rot_append_length]; simp
    rw [show (sweepRow p.arrW p.B 2 0).base = rot p.arrW (p.arrW.length - 1) ++ [p.B] by
      simp [sweepRow, fullRow]]
    rw [p.canon_of_cyc hp _ _ (hperm _) hb]
    simp [arr, a1, hP]
  · have hb : rot p.arrW 0 ++ [p.B] = P ++ [p.C] ++ [p.B] := by rw [rot_zero, hW]
    rw [show (sweepRow p.arrW p.B 2 1).base = rot p.arrW 0 ++ [p.B] by simp [sweepRow, fullRow]]
    rw [p.canon_of_cyc hp _ _ (hperm _) hb]
    have hr : rot p.a1 (p.mid1.length + p.q.length + 1) = [p.B] ++ P := by
      rw [show p.a1 = P ++ [p.B] by simp [a1, hP], ← hPl, rot_append_length]
    simp only [show (1 : Nat) < 2 by omega, if_true, show (1 : Nat) ≠ 0 by omega, if_false, arr]
    rw [hr]
  · obtain ⟨x0, x1, qm, xl, hq, hq0, hq1, hql⟩ := p.q_split h3
    have hb : rot p.arrW 1 ++ [p.B] = (p.mid1 ++ [p.A] ++ (x0 :: x1 :: qm)) ++ [p.C] ++ [xl, p.B] := by
      simp only [arrW, hql, hq, dropLast_cons2_concat, List.singleton_append, List.cons_append,
        List.append_assoc]
      rw [rot_cons_one_generic]; simp
    rw [show (sweepRow p.arrW p.B 2 2).base = rot p.arrW 1 ++ [p.B] by simp [sweepRow, shortRow]]
    rw [p.canon_of_cyc hp _ _ (hperm _) hb]
    have hr : rot p.arrU (p.mid1.length + p.q.length) = [xl, p.B] ++ (p.mid1 ++ [p.A] ++ (x0 :: x1 :: qm)) := by
      rw [show p.arrU = (p.mid1 ++ [p.A] ++ (x0 :: x1 :: qm)) ++ [xl, p.B] by simp [arrU, hq],
        show p.mid1.length + p.q.length = (p.mid1 ++ [p.A] ++ (x0 :: x1 :: qm)).length by rw [hq]; simp <;> omega,
        rot_append_length]
    simp only [show ¬ (2 : Nat) < 2 by omega, if_false, show (2 : Nat) ≠ 0 by omega,
      show (2 : Nat) ≠ 1 by omega, arr]
    rw [hr]

theorem canon_Y (h3 : 3 ≤ p.q.length) (hp : (p.C :: p.B :: p.A :: p.list).Nodup) (t : Nat) (ht : t < 3) :
    canon p.C (sweepRow p.arrY p.A 2 t).base =
      rot (p.arr (if t < 2 then 2 else 3))
        (if t = 0 then 0 else if t = 1 then p.mid1.length + p.q.length + 1
          else p.mid1.length + p.q.length) ++ [p.C] := by
  obtain ⟨x0, x1, qm, xl, hq, hq0, hq1, hql⟩ := p.q_split h3
  set R := (x1 :: (qm ++ [xl])) ++ [p.B] ++ p.mid1 ++ [x0] with hR
  have hRl : R.length = p.mid1.length + p.q.length + 1 := by rw [hR, hq]; simp; omega
  have hY : p.arrY = R ++ [p.C] := by simp [arrY, hR, hq, hq0]
  have hperm : ∀ j, (rot p.arrY j ++ [p.A]).Perm (p.C :: p.B :: p.A :: p.list) :=
    fun j => ((rot_perm _ j).append_right _).trans (p.perm_Y h3)
  interval_cases t
  · have hb : rot p.arrY (p.arrY.length - 1) ++ [p.A] = [] ++ [p.C] ++ (R ++ [p.A]) := by
      rw [hY, show (R ++ [p.C]).length - 1 = R.length by simp, rot_append_length]; simp
    rw [show (sweepRow p.arrY p.A 2 0).base = rot p.arrY (p.arrY.length - 1) ++ [p.A] by
      simp [sweepRow, fullRow]]
    rw [p.canon_of_cyc hp _ _ (hperm _) hb]
    simp [arr, a2, hR, hq, hq0]
  · have hb : rot p.arrY 0 ++ [p.A] = R ++ [p.C] ++ [p.A] := by rw [rot_zero, hY]
    rw [show (sweepRow p.arrY p.A 2 1).base = rot p.arrY 0 ++ [p.A] by simp [sweepRow, fullRow]]
    rw [p.canon_of_cyc hp _ _ (hperm _) hb]
    have hr : rot p.a2 (p.mid1.length + p.q.length + 1) = [p.A] ++ R := by
      rw [show p.a2 = R ++ [p.A] by simp [a2, hR, hq, hq0], ← hRl, rot_append_length]
    simp only [show (1 : Nat) < 2 by omega, if_true, show (1 : Nat) ≠ 0 by omega, if_false, arr]
    rw [hr]
  · have hb : rot p.arrY 1 ++ [p.A] = (qm ++ [xl, p.B] ++ p.mid1 ++ [x0]) ++ [p.C] ++ [x1, p.A] := by
      simp only [arrY, hq0, hq, List.drop_succ_cons, List.drop_zero, List.cons_append]
      rw [rot_cons_one_generic]; simp
    rw [show (sweepRow p.arrY p.A 2 2).base = rot p.arrY 1 ++ [p.A] by simp [sweepRow, shortRow]]
    rw [p.canon_of_cyc hp _ _ (hperm _) hb]
    have hr : rot p.arrV (p.mid1.length + p.q.length) = [x1, p.A] ++ (qm ++ [xl, p.B] ++ p.mid1 ++ [x0]) := by
      rw [show p.arrV = (qm ++ [xl, p.B] ++ p.mid1 ++ [x0]) ++ [x1, p.A] by simp [arrV, hq, hq0, hq1],
        show p.mid1.length + p.q.length = (qm ++ [xl, p.B] ++ p.mid1 ++ [x0]).length by rw [hq]; simp <;> omega,
        rot_append_length]
    simp only [show ¬ (2 : Nat) < 2 by omega, if_false, show (2 : Nat) ≠ 0 by omega,
      show (2 : Nat) ≠ 1 by omega, arr]
    rw [hr]

theorem canon_rowAt (h2 : 2 ≤ p.mid1.length) (h3 : 3 ≤ p.q.length) (hp : (p.C :: p.B :: p.A :: p.list).Nodup)
    (i : Nat) (hi : i < p.mid1.length + p.q.length + 12) :
    canon p.C (p.rowAt i).base =
      rot (p.arr (famOf p.mid1.length i)) (jjOf p.mid1.length (p.mid1.length + p.q.length) i) ++ [p.C] := by
  have hndU : (p.arrU ++ [p.C]).Nodup := p.arr_nodupC h3 hp 1
  have hndV : (p.arrV ++ [p.C]).Nodup := p.arr_nodupC h3 hp 3
  rcases Nat.lt_or_ge i 3 with h3' | h3'
  · have hr : p.rowAt i = sweepRow p.arrW p.B 2 i := by
      simp only [rowAt]; rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    rw [hr, p.canon_W h3 hp i h3']
    interval_cases i <;> simp [famOf, jjOf]
  rcases Nat.lt_or_ge i (p.mid1.length + 7) with h7 | h7
  · have hr : p.rowAt i = sweepRow p.arrU p.C (p.mid1.length + 3) (i - 3) := by
      simp only [rowAt]; rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)]
    rw [hr, Pd.canon_sweepC _ _ _ _ hndU (by omega)]
    have hf : famOf p.mid1.length i = 1 := by
      unfold famOf; rw [if_neg (by omega), if_pos h7]
    rw [hf]
    by_cases h0 : i = 3
    · subst h0; simp [arr, jjOf, len_arrU] <;> omega
    · have hj : jjOf p.mid1.length (p.mid1.length + p.q.length) i = i - 4 := by
        unfold jjOf
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg h0, if_pos h7]
      rw [hj, if_neg (show i - 3 ≠ 0 by omega), show i - 3 - 1 = i - 4 by omega]; rfl
  rcases Nat.lt_or_ge i (p.mid1.length + 10) with h10 | h10
  · have hr : p.rowAt i = sweepRow p.arrY p.A 2 (i - (p.mid1.length + 7)) := by
      simp only [rowAt]; rw [if_pos (by omega), if_neg (by omega)]
      congr 1; omega
    rw [hr, p.canon_Y h3 hp _ (by omega)]
    have ht : i - (p.mid1.length + 7) = 0 ∨ i - (p.mid1.length + 7) = 1 ∨ i - (p.mid1.length + 7) = 2 := by
      omega
    rcases ht with ht | ht | ht
    · rw [ht, show i = p.mid1.length + 7 by omega]; simp [famOf, jjOf]
    · rw [ht, show i = p.mid1.length + 8 by omega]; simp [famOf, jjOf]
    · rw [ht, show i = p.mid1.length + 9 by omega]; simp [famOf, jjOf]
  · have hr : p.rowAt i = sweepRow p.arrV p.C (p.q.length + 1) (i - (p.mid1.length + 10)) := by
      simp only [rowAt]; rw [if_neg (by omega)]
      congr 1; omega
    rw [hr, Pd.canon_sweepC _ _ _ _ hndV (by omega)]
    have hf : famOf p.mid1.length i = 3 := by
      unfold famOf; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [hf]
    by_cases h0 : i = p.mid1.length + 10
    · subst h0; simp [arr, jjOf, p.len_arrV h3]
    · have hj : jjOf p.mid1.length (p.mid1.length + p.q.length) i = i - (p.mid1.length + 11) := by
        unfold jjOf
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg h0]
      rw [hj, if_neg (show i - (p.mid1.length + 10) ≠ 0 by omega),
        show i - (p.mid1.length + 10) - 1 = i - (p.mid1.length + 11) by omega]; rfl

end Pg

end SuperpermutationUpperBound43586371.UniR
