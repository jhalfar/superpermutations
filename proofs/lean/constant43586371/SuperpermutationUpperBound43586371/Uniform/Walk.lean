import SuperpermutationUpperBound43586371.NoSeed
import SuperpermutationUpperBound43586371.AllSizesG

/-!
# The caterpillar walk W(m) for every odd m (`PROOF.md`, sections 2-4)

Old letters `d0` (length `m`), tokens `A B C`.  Period `k` uses the old letters `e = rot d0 (2k)`, written
`[e0, e1] ++ mid ++ [el]` (a `Pd`), and four sweeps.  A sweep `(s, T, J)` lists the rows with bases
`rot s j ++ [T]` for `j = m+1, 0, 1, ..., J-1`, all full except the last.  This file defines the walk and proves
that it is a closed trail over the alphabet `C :: B :: A :: d0`, with `m (m+12)` rows of total charge `8m`.
-/

namespace SuperpermutationUpperBound43586371.Uniform

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

/-! ### Rows and their ends -/

/-- The full row with base `x ++ [T]`. -/
def fullRow (x : List Nat) (T : Nat) : Row Nat := ⟨x ++ [T], 9, x.length + 1⟩

/-- The short row with base `x ++ [T]`. -/
def shortRow (x : List Nat) (T : Nat) : Row Nat := ⟨x ++ [T], 9, x.length - 1⟩

theorem take_len_add (l1 l2 : List Nat) (k : Nat) : (l1 ++ l2).take (l1.length + k) = l1 ++ l2.take k := by
  simp [List.take_append]

theorem drop_len_add (l1 l2 : List Nat) (k : Nat) : (l1 ++ l2).drop (l1.length + k) = l2.drop k := by
  simp [List.drop_append]
@[simp] theorem take_self_add (l : List Nat) (k : Nat) : l.take (l.length + k) = l :=
  List.take_of_length_le (by omega)

@[simp] theorem drop_self_add (l : List Nat) (k : Nat) : l.drop (l.length + k) = [] :=
  List.drop_of_length_le (by omega)


theorem head_mk (x : List Nat) (T v n : Nat) (hx : x.length = n + 2) :
    (Row.mk (x ++ [T]) 9 v).head = x.take (n + 1) := by
  simp only [Row.head, List.length_append, List.length_singleton, hx]
  rw [show n + 2 + 1 - 2 = n + 1 by omega, List.take_append_of_le_length (by omega)]

theorem rot_one_eq (y : List Nat) (hy : 1 ≤ y.length) : rot y 1 = y.drop 1 ++ y.take 1 :=
  rot_eq_drop_append_take_of_le y 1 hy

theorem fullRow_tail (x : List Nat) (T n : Nat) (hx : x.length = n + 2) :
    (fullRow x T).tail = x.drop 1 := by
  simp only [Row.tail, fullRow, List.length_append, List.length_singleton, hx]
  have h1 : (x ++ [T]).rotateLeft (n + 2 + 1 + 1) = rot (x ++ [T]) 1 := by
    change rot (x ++ [T]) (n + 2 + 1 + 1) = _
    rw [← rot_mod (x ++ [T]) (n + 2 + 1 + 1)]
    simp only [List.length_append, List.length_singleton, hx]
    rw [show n + 2 + 1 + 1 = 1 + (n + 2 + 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  rw [h1, rot_one_eq _ (by simp)]
  rw [show n + 2 + 1 - 2 = n + 1 by omega]
  rw [List.drop_append_of_le_length (by omega)]
  rw [List.append_assoc, List.take_append_of_le_length (by simp [hx])]
  rw [List.take_of_length_le (by simp [hx])]

theorem shortRow_tail (x : List Nat) (T n : Nat) (hx : x.length = n + 2) :
    (shortRow x T).tail = T :: x.take n := by
  simp only [Row.tail, shortRow, List.length_append, List.length_singleton, hx]
  rw [show n + 2 - 1 + 1 = x.length by omega]
  change (rot (x ++ [T]) x.length).take _ = _
  rw [rot_append_length, show n + 2 + 1 - 2 = n + 1 by omega]
  simp

/-- A full row is followed compatibly by the next rotation of its arrangement. -/
theorem compat_step (y : List Nat) (T v n : Nat) (hy : y.length = n + 2) :
    (fullRow y T).Compatible ⟨rot y 1 ++ [T], 9, v⟩ := by
  change (fullRow y T).tail = (Row.mk (rot y 1 ++ [T]) 9 v).head
  rw [fullRow_tail y T n hy, head_mk (rot y 1) T v n (by simp [hy]), rot_one_eq y (by omega),
    List.take_append_of_le_length (by simp [hy]), List.take_of_length_le (by simp [hy])]

/-- A short row is followed compatibly by the first row of the next sweep. -/
theorem compat_trans (x s : List Nat) (T T' n : Nat) (hx : x.length = n + 2)
    (hs : s.length = n + 1) (h : x.take n = s.take n) :
    (shortRow x T).Compatible (fullRow (rot (s ++ [T]) (n + 1)) T') := by
  change (shortRow x T).tail = (fullRow (rot (s ++ [T]) (n + 1)) T').head
  have hr : rot (s ++ [T]) (n + 1) = T :: s := by
    rw [← hs, rot_append_length]; rfl
  rw [shortRow_tail x T n hx, fullRow, hr, head_mk (T :: s) T' _ n (by simp [hs]), h]
  rfl

/-! ### Paths -/

theorem runs_single {r last : Row Nat} (h : r.Compatible last) : PathRunsTo [r] last :=
  ⟨h, trivial⟩

theorem runs_append {left right : List (Row Nat)} {first last : Row Nat}
    (hr0 : right.head? = some first) (hl : PathRunsTo left first) (hr : PathRunsTo right last) :
    PathRunsTo (left ++ right) last := by
  cases right with
  | nil => simp at hr0
  | cons a rest =>
    simp only [List.head?_cons, Option.some.injEq] at hr0
    subst hr0
    exact pathRunsTo_append hl hr

theorem runs_range (f : Nat → Row Nat) :
    ∀ n, 1 ≤ n → (∀ j < n, (f j).Compatible (f (j + 1))) → PathRunsTo ((List.range n).map f) (f n) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _ hc
    by_cases h0 : n = 0
    · subst h0
      exact runs_single (hc 0 (by omega))
    · rw [List.range_succ, List.map_append, List.map_singleton]
      exact runs_append rfl (ih (by omega) (fun j hj => hc j (by omega)))
        (runs_single (hc n (by omega)))

/-- A list of periods, each running into the first row of the next, the last into the first: a closed
trail. -/
theorem closed_of_periods (g : Nat → Row Nat) (t : Nat → List (Row Nat)) (M : Nat) (hM : 1 ≤ M)
    (hrun : ∀ k, PathRunsTo (g k :: t k) (g (k + 1))) (hper : g M = g 0) :
    ClosedTrail ((List.range M).flatMap fun k => g k :: t k) := by
  have key : ∀ M, 1 ≤ M → PathRunsTo ((List.range M).flatMap fun k => g k :: t k) (g M) := by
    intro M
    induction M with
    | zero => intro h; omega
    | succ M ih =>
      intro _
      by_cases h0 : M = 0
      · subst h0
        simpa using hrun 0
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
        exact runs_append rfl (ih (by omega)) (hrun M)
  have hk := key M hM
  rw [hper] at hk
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [List.range_succ_eq_map, List.flatMap_cons, List.cons_append] at hk ⊢
  exact closedTrail_of_pathRunsTo hk

/-! ### Sweeps -/

/-- Row `i` of the sweep `(s, T, J)`: `j = m+1` first, then `j = 0, ..., J-2` full, `j = J-1` short. -/
def sweepRow (s : List Nat) (T J i : Nat) : Row Nat :=
  if i = 0 then fullRow (rot s (s.length - 1)) T
  else if i < J then fullRow (rot s (i - 1)) T else shortRow (rot s (J - 1)) T

def sweep (s : List Nat) (T J : Nat) : List (Row Nat) := (List.range (J + 1)).map (sweepRow s T J)

theorem sweep_head (s : List Nat) (T J : Nat) :
    (sweep s T J).head? = some (fullRow (rot s (s.length - 1)) T) := by
  simp [sweep, List.range_succ_eq_map, sweepRow]

theorem sweepRow_base (s : List Nat) (T J i : Nat) (hi : 1 ≤ i) (hiJ : i ≤ J) :
    ∃ v, sweepRow s T J i = ⟨rot s (i - 1) ++ [T], 9, v⟩ := by
  unfold sweepRow
  by_cases h : i < J
  · exact ⟨(rot s (i - 1)).length + 1, by simp [show i ≠ 0 by omega, h, fullRow]⟩
  · have : i = J := by omega
    subst this
    exact ⟨(rot s (i - 1)).length - 1, by simp [show i ≠ 0 by omega, shortRow]⟩

/-- A sweep runs into any row that follows its short row compatibly. -/
theorem sweep_runs (s : List Nat) (T J n : Nat) (hs : s.length = n + 2) (hJ : 1 ≤ J)
    (next : Row Nat) (hnext : (shortRow (rot s (J - 1)) T).Compatible next) :
    PathRunsTo (sweep s T J) next := by
  unfold sweep
  rw [List.range_succ, List.map_append, List.map_singleton]
  have hlast : sweepRow s T J J = shortRow (rot s (J - 1)) T := by
    simp [sweepRow, show J ≠ 0 by omega]
  refine runs_append rfl (runs_range _ J hJ ?_) (runs_single (hlast ▸ hnext))
  intro j hj
  obtain ⟨v, hv⟩ := sweepRow_base s T J (j + 1) (by omega) (by omega)
  rw [hv]
  by_cases h0 : j = 0
  · subst h0
    have h1 : sweepRow s T J 0 = fullRow (rot s (n + 1)) T := by simp [sweepRow, hs]
    rw [h1]
    have h2 : rot (rot s (n + 1)) 1 = rot s (0 + 1 - 1) := by
      rw [rot_add, show n + 1 + 1 = s.length by omega, rot_length_self]; simp
    rw [← h2]
    exact compat_step _ T v n (by simp [hs])
  · have h1 : sweepRow s T J j = fullRow (rot s (j - 1)) T := by
      simp [sweepRow, h0, show j < J by omega]
    rw [h1]
    have h2 : rot (rot s (j - 1)) 1 = rot s (j + 1 - 1) := by
      rw [rot_add]; congr 1; omega
    rw [← h2]
    exact compat_step _ T v n (by simp [hs])

theorem sweep_length (s : List Nat) (T J : Nat) : (sweep s T J).length = J + 1 := by
  simp [sweep]

theorem sweep_charge (s : List Nat) (T J : Nat) (hs : 2 ≤ s.length) (hJ1 : 1 ≤ J) :
    ((sweep s T J).map Row.charge).sum = 2 := by
  unfold sweep
  rw [List.range_succ, List.map_append, List.map_append, List.sum_append]
  have h0 : ∀ i ∈ List.range J, (sweepRow s T J i).charge = 0 := by
    intro i hi
    have hi := List.mem_range.mp hi
    unfold sweepRow
    by_cases h : i = 0
    · simp [h, fullRow, Row.charge]
    · simp [h, hi, fullRow, Row.charge]
  have hz : ((List.range J).map (sweepRow s T J)).map Row.charge = (List.range J).map (fun _ => 0) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i hi => h0 i hi)
  rw [hz]
  simp [sweepRow, show J ≠ 0 by omega, shortRow, Row.charge]; omega

theorem sweep_basedOn (s : List Nat) (T J : Nat) (alph : List Nat) (hp : (s ++ [T]).Perm alph)
    (hnd : alph.Nodup) (h9 : 9 ∉ alph) (hs : 2 ≤ s.length) : BasedOn alph 9 (sweep s T J) := by
  intro r hr
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  have keyF : ∀ x, (x ++ [T]).Perm alph →
      (fullRow x T).Valid ∧ (fullRow x T).base.Perm alph ∧ (fullRow x T).satellite = 9 ∧
        ((fullRow x T).visible = (fullRow x T).base.length ∨
          (fullRow x T).visible = (fullRow x T).base.length - 2) := by
    intro x hxp
    have hn : (x ++ [T]).Nodup := hxp.nodup_iff.mpr hnd
    have h9' : 9 ∉ x ++ [T] := fun hm => h9 (hxp.mem_iff.mp hm)
    exact ⟨⟨hn, h9', by simp [fullRow], by simp [fullRow]⟩, hxp, rfl, Or.inl (by simp [fullRow])⟩
  have keyS : ∀ x, x.length = s.length → (x ++ [T]).Perm alph →
      (shortRow x T).Valid ∧ (shortRow x T).base.Perm alph ∧ (shortRow x T).satellite = 9 ∧
        ((shortRow x T).visible = (shortRow x T).base.length ∨
          (shortRow x T).visible = (shortRow x T).base.length - 2) := by
    intro x hx hxp
    have hn : (x ++ [T]).Nodup := hxp.nodup_iff.mpr hnd
    have h9' : 9 ∉ x ++ [T] := fun hm => h9 (hxp.mem_iff.mp hm)
    exact ⟨⟨hn, h9', by simp [shortRow]; omega, by simp [shortRow]; omega⟩, hxp, rfl,
      Or.inr (by simp [shortRow])⟩
  have hrot : ∀ j, (rot s j ++ [T]).Perm alph := fun j => ((rot_perm s j).append_right [T]).trans hp
  unfold sweepRow
  split_ifs
  · exact keyF _ (hrot _)
  · exact keyF _ (hrot _)
  · exact keyS _ (by simp) (hrot _)

/-! ### Periods -/

/-- The data of one period: old letters `[e0, e1] ++ mid ++ [el]`, tokens `A B C`. -/
structure Pd where
  e0 : Nat
  e1 : Nat
  mid : List Nat
  el : Nat
  A : Nat
  B : Nat
  C : Nat

namespace Pd

variable (p : Pd)

def list : List Nat := [p.e0, p.e1] ++ p.mid ++ [p.el]

def arrW : List Nat := [p.e1] ++ p.mid ++ [p.A, p.el, p.e0, p.C]
def arrU : List Nat := p.mid ++ [p.A, p.el, p.e0, p.e1, p.B]
def arrY : List Nat := [p.e0, p.e1, p.B] ++ p.mid ++ [p.el, p.C]
def arrV : List Nat := [p.e1, p.B] ++ p.mid ++ [p.el, p.e0, p.A]

/-- The old letters of the next period, `rot list 2`, need `mid = a :: b :: mid2`. -/
def next : Pd :=
  match p.mid with
  | a :: b :: mid2 => ⟨a, b, mid2 ++ [p.el, p.e0], p.e1, p.A, p.B, p.C⟩
  | _ => p

def period : List (Row Nat) :=
  sweep p.arrW p.B 2 ++ sweep p.arrU p.C (p.mid.length + 3) ++ sweep p.arrY p.A 2 ++
    sweep p.arrV p.C 4

def first : Row Nat := fullRow (rot p.arrW (p.arrW.length - 1)) p.B

theorem period_head : p.period.head? = some p.first := by
  simp [period, sweep, List.range_succ_eq_map, sweepRow, first]

theorem len_arrW : p.arrW.length = p.mid.length + 5 := by simp [arrW]
theorem len_arrU : p.arrU.length = p.mid.length + 5 := by simp [arrU]
theorem len_arrY : p.arrY.length = p.mid.length + 5 := by simp [arrY]
theorem len_arrV : p.arrV.length = p.mid.length + 5 := by simp [arrV]

theorem next_mid (a b : Nat) (mid2 : List Nat) (h : p.mid = a :: b :: mid2) :
    p.next = ⟨a, b, mid2 ++ [p.el, p.e0], p.e1, p.A, p.B, p.C⟩ := by
  unfold next; rw [h]

/-- The period runs into the first row of the next period. -/
theorem period_runs (h2 : 2 ≤ p.mid.length) : PathRunsTo p.period p.next.first := by
  obtain ⟨a, b, mid2, hm⟩ : ∃ a b mid2, p.mid = a :: b :: mid2 := by
    match h : p.mid with
    | a :: b :: mid2 => exact ⟨a, b, mid2, rfl⟩
    | [] => rw [h] at h2; simp at h2
    | [a] => rw [h] at h2; simp at h2
  have hmlen : p.mid.length = mid2.length + 2 := by rw [hm]; simp
  -- sweep w -> sweep u
  have r1 : PathRunsTo (sweep p.arrW p.B 2) (fullRow (rot p.arrU (p.arrU.length - 1)) p.C) := by
    refine sweep_runs _ _ 2 (p.mid.length + 3) (by rw [len_arrW]) (by omega) _ ?_
    have hu : p.arrU = (p.mid ++ [p.A, p.el, p.e0, p.e1]) ++ [p.B] := by simp [arrU]
    rw [hu, show ((p.mid ++ [p.A, p.el, p.e0, p.e1]) ++ [p.B]).length - 1 = p.mid.length + 3 + 1 by
      simp]
    refine compat_trans _ _ _ _ _ (by simp [len_arrW]) (by simp) ?_
    have hr : rot p.arrW (2 - 1) = p.mid ++ [p.A, p.el, p.e0, p.C, p.e1] := by
      simp only [arrW, show (2 : Nat) - 1 = 1 by rfl, List.singleton_append, List.cons_append]
      rw [rot_cons_one_generic]; simp
    rw [hr]
    simp [List.take_append]
  -- sweep u -> sweep y
  have r2 : PathRunsTo (sweep p.arrU p.C (p.mid.length + 3))
      (fullRow (rot p.arrY (p.arrY.length - 1)) p.A) := by
    refine sweep_runs _ _ _ (p.mid.length + 3) (by rw [len_arrU]) (by omega) _ ?_
    have hy : p.arrY = ([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]) ++ [p.C] := by simp [arrY]
    rw [hy, show (([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]) ++ [p.C]).length - 1 =
      p.mid.length + 3 + 1 by simp <;> omega]
    refine compat_trans _ _ _ _ _ (by simp [len_arrU]) (by simp <;> omega) ?_
    have hr : rot p.arrU (p.mid.length + 3 - 1) = [p.e0, p.e1, p.B] ++ (p.mid ++ [p.A, p.el]) := by
      rw [show p.mid.length + 3 - 1 = p.mid.length + 2 by omega,
        rot_eq_drop_append_take_of_le _ _ (by simp [arrU])]
      simp [arrU, List.take_append, List.drop_append]
    rw [hr]
    simp [List.take_append]
  -- sweep y -> sweep v
  have r3 : PathRunsTo (sweep p.arrY p.A 2) (fullRow (rot p.arrV (p.arrV.length - 1)) p.C) := by
    refine sweep_runs _ _ 2 (p.mid.length + 3) (by rw [len_arrY]) (by omega) _ ?_
    have hv : p.arrV = ([p.e1, p.B] ++ p.mid ++ [p.el, p.e0]) ++ [p.A] := by simp [arrV]
    rw [hv, show (([p.e1, p.B] ++ p.mid ++ [p.el, p.e0]) ++ [p.A]).length - 1 =
      p.mid.length + 3 + 1 by simp <;> omega]
    refine compat_trans _ _ _ _ _ (by simp [len_arrY]) (by simp <;> omega) ?_
    have hr : rot p.arrY (2 - 1) = [p.e1, p.B] ++ p.mid ++ [p.el, p.C, p.e0] := by
      simp only [arrY, show (2 : Nat) - 1 = 1 by rfl, List.cons_append]
      rw [rot_cons_one_generic]; simp
    rw [hr]
    simp [List.take_append]
  -- sweep v -> next period
  have r4 : PathRunsTo (sweep p.arrV p.C 4) p.next.first := by
    refine sweep_runs _ _ 4 (p.mid.length + 3) (by rw [len_arrV]) (by omega) _ ?_
    rw [p.next_mid a b mid2 hm]
    have hw : Pd.arrW ⟨a, b, mid2 ++ [p.el, p.e0], p.e1, p.A, p.B, p.C⟩ =
        ([b] ++ mid2 ++ [p.el, p.e0, p.A, p.e1, a]) ++ [p.C] := by simp [arrW]
    have hl : (Pd.arrW ⟨a, b, mid2 ++ [p.el, p.e0], p.e1, p.A, p.B, p.C⟩).length - 1 =
        p.mid.length + 3 + 1 := by
      rw [hw, hmlen]; simp <;> omega
    unfold first
    rw [hl, hw]
    refine compat_trans _ _ _ _ _ (by simp [len_arrV]) (by simp [hmlen] <;> omega) ?_
    have hr : rot p.arrV (4 - 1) = [b] ++ mid2 ++ [p.el, p.e0, p.A, p.e1, p.B, a] := by
      simp only [arrV, hm, show (4 : Nat) - 1 = 3 by rfl]
      rw [rot_eq_drop_append_take_of_le _ _ (by simp)]
      simp
    rw [hr, hmlen]
    simp [List.take_append]
  unfold period
  refine runs_append (sweep_head _ _ _) ?_ r4
  refine runs_append (sweep_head _ _ _) ?_ r3
  exact runs_append (sweep_head _ _ _) r1 r2

theorem period_length : p.period.length = p.mid.length + 15 := by
  simp [period, sweep_length]; omega

theorem period_charge : (p.period.map Row.charge).sum = 8 := by
  simp only [period, List.map_append, List.sum_append]
  rw [sweep_charge _ _ _ (by simp [len_arrW]) (by omega), sweep_charge _ _ _ (by simp [len_arrU]) (by omega),
    sweep_charge _ _ _ (by simp [len_arrY]) (by omega), sweep_charge _ _ _ (by simp [len_arrV]) (by omega)]

/-- Multiset form of a permutation of explicit lists. -/
theorem perm_W : (p.arrW ++ [p.B]).Perm (p.C :: p.B :: p.A :: p.list) := by
  rw [← Multiset.coe_eq_coe]
  simp only [arrW, list, ← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

theorem perm_U : (p.arrU ++ [p.C]).Perm (p.C :: p.B :: p.A :: p.list) := by
  rw [← Multiset.coe_eq_coe]
  simp only [arrU, list, ← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

theorem perm_Y : (p.arrY ++ [p.A]).Perm (p.C :: p.B :: p.A :: p.list) := by
  rw [← Multiset.coe_eq_coe]
  simp only [arrY, list, ← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

theorem perm_V : (p.arrV ++ [p.C]).Perm (p.C :: p.B :: p.A :: p.list) := by
  rw [← Multiset.coe_eq_coe]
  simp only [arrV, list, ← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

theorem period_basedOn (alph : List Nat) (hp : (p.C :: p.B :: p.A :: p.list).Perm alph)
    (hnd : alph.Nodup) (h9 : 9 ∉ alph) : BasedOn alph 9 p.period := by
  intro r hr
  simp only [period, List.mem_append] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · exact sweep_basedOn _ _ _ _ (p.perm_W.trans hp) hnd h9 (by simp [len_arrW]) r hr
  · exact sweep_basedOn _ _ _ _ (p.perm_U.trans hp) hnd h9 (by simp [len_arrU]) r hr
  · exact sweep_basedOn _ _ _ _ (p.perm_Y.trans hp) hnd h9 (by simp [len_arrY]) r hr
  · exact sweep_basedOn _ _ _ _ (p.perm_V.trans hp) hnd h9 (by simp [len_arrV]) r hr

end Pd

/-! ### The walk -/

/-- The period data read off a list of old letters. -/
def pdOf (e : List Nat) (A B C : Nat) : Pd :=
  ⟨e.getD 0 0, e.getD 1 0, (e.drop 2).take (e.length - 3), e.getD (e.length - 1) 0, A, B, C⟩

theorem pdOf_eq (e0 e1 el A B C : Nat) (mid : List Nat) :
    pdOf ([e0, e1] ++ mid ++ [el]) A B C = ⟨e0, e1, mid, el, A, B, C⟩ := by
  simp [pdOf, List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem exists_split (e : List Nat) (he : 3 ≤ e.length) :
    ∃ e0 e1 mid el, e = [e0, e1] ++ mid ++ [el] := by
  match e, he with
  | e0 :: e1 :: rest, he =>
    have hne : rest ≠ [] := by intro h; subst h; simp at he
    refine ⟨e0, e1, rest.dropLast, rest.getLast hne, ?_⟩
    simp [List.dropLast_append_getLast hne]

theorem pdOf_list (e : List Nat) (A B C : Nat) (he : 3 ≤ e.length) : (pdOf e A B C).list = e := by
  obtain ⟨e0, e1, mid, el, rfl⟩ := exists_split e he
  rw [pdOf_eq]; rfl

theorem pdOf_mid_length (e : List Nat) (A B C : Nat) (he : 3 ≤ e.length) :
    (pdOf e A B C).mid.length = e.length - 3 := by
  obtain ⟨e0, e1, mid, el, rfl⟩ := exists_split e he
  rw [pdOf_eq]; simp

theorem pdOf_tokens (e : List Nat) (A B C : Nat) :
    (pdOf e A B C).A = A ∧ (pdOf e A B C).B = B ∧ (pdOf e A B C).C = C := ⟨rfl, rfl, rfl⟩

theorem pdOf_rot2 (e : List Nat) (A B C : Nat) (he : 5 ≤ e.length) :
    pdOf (rot e 2) A B C = (pdOf e A B C).next := by
  obtain ⟨e0, e1, mid, el, rfl⟩ := exists_split e (by omega)
  match mid, he with
  | a :: b :: mid2, _ =>
    rw [pdOf_eq, Pd.next_mid _ a b mid2 rfl]
    have : rot ([e0, e1] ++ (a :: b :: mid2) ++ [el]) 2 = [a, b] ++ (mid2 ++ [el, e0]) ++ [e1] := by
      rw [rot_eq_drop_append_take_of_le _ _ (by simp)]; simp
    rw [this, pdOf_eq]

/-- The walk: `m` periods, period `k` on the old letters `rot d0 (2k)`. -/
def walk (d0 : List Nat) (A B C : Nat) : List (Row Nat) :=
  (List.range d0.length).flatMap fun k => (pdOf (rot d0 (2 * k)) A B C).period

theorem walk_closed (d0 : List Nat) (A B C : Nat) (hm : 5 ≤ d0.length) :
    ClosedTrail (walk d0 A B C) := by
  let P := fun k => pdOf (rot d0 (2 * k)) A B C
  have hsplit : ∀ k, ∃ rest, (P k).period = (P k).first :: rest := by
    intro k
    have h := (P k).period_head
    match hq : (P k).period, h with
    | r :: rest, h => simp at h; exact ⟨rest, by rw [h]⟩
  choose t ht using hsplit
  have hw : walk d0 A B C = (List.range d0.length).flatMap fun k => (P k).first :: t k := by
    unfold walk; congr 1; funext k; exact ht k
  rw [hw]
  refine closed_of_periods (fun k => (P k).first) t d0.length (by omega) ?_ ?_
  · intro k
    rw [← ht k]
    have hn : (P (k + 1)) = (P k).next := by
      show pdOf (rot d0 (2 * (k + 1))) A B C = (pdOf (rot d0 (2 * k)) A B C).next
      rw [← pdOf_rot2 _ _ _ _ (by simp; omega), rot_add]
      congr 2
    rw [hn]
    refine (P k).period_runs ?_
    show 2 ≤ (pdOf (rot d0 (2 * k)) A B C).mid.length
    rw [pdOf_mid_length _ _ _ _ (by simp; omega)]; simp; omega
  · show (P d0.length).first = (P 0).first
    show (pdOf (rot d0 (2 * d0.length)) A B C).first = (pdOf (rot d0 (2 * 0)) A B C).first
    rw [← rot_mod d0 (2 * d0.length), Nat.mul_mod_left]

theorem walk_length (d0 : List Nat) (A B C : Nat) (hm : 3 ≤ d0.length) :
    (walk d0 A B C).length = d0.length * (d0.length + 12) := by
  unfold walk
  rw [length_flatMap_const _ _ (d0.length + 12) (fun k _ => by
    rw [Pd.period_length, pdOf_mid_length _ _ _ _ (by simp; omega)]; simp; omega)]
  simp

theorem walk_charge (d0 : List Nat) (A B C : Nat) :
    ((walk d0 A B C).map Row.charge).sum = 8 * d0.length := by
  unfold walk
  rw [List.map_flatMap, sum_flatMap_const _ _ 8 (fun k _ => Pd.period_charge _)]
  simp; ring

theorem walk_basedOn (d0 : List Nat) (A B C : Nat) (hm : 3 ≤ d0.length)
    (hnd : (C :: B :: A :: d0).Nodup) (h9 : 9 ∉ C :: B :: A :: d0) :
    BasedOn (C :: B :: A :: d0) 9 (walk d0 A B C) := by
  intro r hr
  obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hr
  refine Pd.period_basedOn _ _ ?_ hnd h9 r hk
  rw [pdOf_list _ _ _ _ (by simp; omega)]
  exact (((rot_perm d0 (2 * k)).cons A).cons B).cons C

end SuperpermutationUpperBound43586371.Uniform
