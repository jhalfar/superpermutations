import SuperpermutationUpperBound43586371.Uniform.Walk

/-!
# The caterpillar walks W(m, g, roles, s) (`PROOF_R.md`, section 1)

A period is given by the old letters `O = mid1 ++ q` read from index `o + 2` (`|mid1| = m - 2 - g`,
`|q| = g + 2`) and the roles `A B C`; its four sweeps have the arrangements `arrW`, `arrU`, `arrY`, `arrV`.
The walk with shift `s` has `P` periods, period `k` on `O = rot d0 (s + 2k + 2)`.  This file proves that it is a
closed trail over `C :: B :: A :: d0` with `P (m+12)` rows of total charge `8P`, whenever `1 ≤ g`, `g + 4 ≤ m`
and `2P ≡ 0 (mod m)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SuperpermutationUpperBound43586371.UniR

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound43586371.Uniform

@[simp] theorem getLast?_cons_concat (a : Nat) (l : List Nat) (x : Nat) :
    (a :: (l ++ [x])).getLast? = some x := by
  show ((a :: l) ++ [x]).getLast? = some x
  exact List.getLast?_concat

@[simp] theorem dropLast_cons_concat (a : Nat) (l : List Nat) (x : Nat) :
    (a :: (l ++ [x])).dropLast = a :: l := by
  show ((a :: l) ++ [x]).dropLast = a :: l
  rw [List.dropLast_concat]

@[simp] theorem getLast?_cons2_concat (a b : Nat) (l : List Nat) (x : Nat) :
    (a :: b :: (l ++ [x])).getLast? = some x := by
  show ((a :: b :: l) ++ [x]).getLast? = some x
  exact List.getLast?_concat

@[simp] theorem dropLast_cons2_concat (a b : Nat) (l : List Nat) (x : Nat) :
    (a :: b :: (l ++ [x])).dropLast = a :: b :: l := by
  show ((a :: b :: l) ++ [x]).dropLast = a :: b :: l
  rw [List.dropLast_concat]

/-- A short row followed by the first row of the next sweep, with the common prefix given explicitly. -/
theorem compat_trans2 (x s P X Y : List Nat) (T T' n : Nat) (hx : x = P ++ X) (hs : s = P ++ Y)
    (hP : P.length = n) (hX : X.length = 2) (hY : Y.length = 1) :
    (shortRow x T).Compatible (fullRow (rot (s ++ [T]) (n + 1)) T') := by
  subst hx hs hP
  refine compat_trans _ _ T T' P.length (by simp [hX]) (by simp [hY]) ?_
  simp

/-- One period: `O = mid1 ++ q`, roles `A B C`. -/
structure Pg where
  mid1 : List Nat
  q : List Nat
  A : Nat
  B : Nat
  C : Nat

namespace Pg

variable (p : Pg)

def q0 : Nat := p.q.headD 0
def q1 : Nat := (p.q.drop 1).headD 0
def ql : Nat := p.q.getLastD 0

def list : List Nat := p.mid1 ++ p.q

def arrW : List Nat := [p.ql] ++ p.mid1 ++ [p.A] ++ p.q.dropLast ++ [p.C]
def arrU : List Nat := p.mid1 ++ [p.A] ++ p.q ++ [p.B]
def arrY : List Nat := p.q.drop 1 ++ [p.B] ++ p.mid1 ++ [p.q0, p.C]
def arrV : List Nat := p.q.drop 2 ++ [p.B] ++ p.mid1 ++ [p.q0, p.q1, p.A]

/-- The next period: `O' = rot O 2`. -/
def next : Pg := ⟨p.mid1.drop 2 ++ p.q.take 2, p.q.drop 2 ++ p.mid1.take 2, p.A, p.B, p.C⟩

def period : List (Row Nat) :=
  sweep p.arrW p.B 2 ++ sweep p.arrU p.C (p.mid1.length + 3) ++ sweep p.arrY p.A 2 ++
    sweep p.arrV p.C (p.q.length + 1)

def first : Row Nat := fullRow (rot p.arrW (p.arrW.length - 1)) p.B

theorem period_head : p.period.head? = some p.first := by
  simp [period, sweep, List.range_succ_eq_map, sweepRow, first]

/-- The shape `q = x0 :: x1 :: qm ++ [xl]` and its accessors. -/
theorem q_split (h3 : 3 ≤ p.q.length) :
    ∃ x0 x1 qm xl, p.q = x0 :: x1 :: (qm ++ [xl]) ∧ p.q0 = x0 ∧ p.q1 = x1 ∧ p.ql = xl := by
  match hq : p.q, h3 with
  | x0 :: x1 :: rest, h3 =>
    have hne : rest ≠ [] := by intro h; subst h; simp [hq] at h3
    have hr : rest = rest.dropLast ++ [rest.getLast hne] := (List.dropLast_append_getLast hne).symm
    refine ⟨x0, x1, rest.dropLast, rest.getLast hne, by rw [← hr], ?_, ?_, ?_⟩
    · simp [q0, hq]
    · simp [q1, hq]
    · have e : x0 :: x1 :: rest = x0 :: x1 :: (rest.dropLast ++ [rest.getLast hne]) := by
        rw [List.dropLast_append_getLast hne]
      simp only [ql, hq]; rw [e]; simp

theorem len_arrW (h3 : 3 ≤ p.q.length) : p.arrW.length = p.mid1.length + p.q.length + 2 := by
  simp [arrW]; omega
theorem len_arrU : p.arrU.length = p.mid1.length + p.q.length + 2 := by simp [arrU]; omega
theorem len_arrY (h3 : 3 ≤ p.q.length) : p.arrY.length = p.mid1.length + p.q.length + 2 := by
  simp [arrY]; omega
theorem len_arrV (h3 : 3 ≤ p.q.length) : p.arrV.length = p.mid1.length + p.q.length + 2 := by
  simp [arrV]; omega

/-- The period runs into the first row of the next period. -/
theorem period_runs (h2 : 2 ≤ p.mid1.length) (h3 : 3 ≤ p.q.length) : PathRunsTo p.period p.next.first := by
  obtain ⟨x0, x1, qm, xl, hq, hq0, hq1, hql⟩ := p.q_split h3
  obtain ⟨a, b, r, hm⟩ : ∃ a b r, p.mid1 = a :: b :: r := by
    match h : p.mid1 with
    | a :: b :: r => exact ⟨a, b, r, rfl⟩
    | [] => rw [h] at h2; simp at h2
    | [a] => rw [h] at h2; simp at h2
  have hn : p.mid1.length + p.q.length = (p.mid1 ++ [p.A, x0, x1] ++ qm).length := by
    rw [hq]; simp <;> omega
  -- w -> u
  have r1 : PathRunsTo (sweep p.arrW p.B 2) (fullRow (rot p.arrU (p.arrU.length - 1)) p.C) := by
    refine sweep_runs _ _ 2 (p.mid1.length + p.q.length) (by rw [p.len_arrW h3]) (by omega) _ ?_
    have hu : p.arrU = (p.mid1 ++ [p.A] ++ p.q) ++ [p.B] := by simp [arrU]
    rw [hu, show ((p.mid1 ++ [p.A] ++ p.q) ++ [p.B]).length - 1 = p.mid1.length + p.q.length + 1 by
      simp <;> omega]
    refine compat_trans2 _ _ (p.mid1 ++ [p.A, x0, x1] ++ qm) [p.C, xl] [xl] _ _ _ ?_ ?_ hn.symm rfl rfl
    · simp only [arrW, hql, hq, show (2 : Nat) - 1 = 1 by rfl, dropLast_cons2_concat, List.singleton_append,
        List.cons_append, List.append_assoc]
      rw [rot_cons_one_generic]; simp
    · simp [hq]
  -- u -> y
  have r2 : PathRunsTo (sweep p.arrU p.C (p.mid1.length + 3))
      (fullRow (rot p.arrY (p.arrY.length - 1)) p.A) := by
    refine sweep_runs _ _ _ (p.mid1.length + p.q.length) (by rw [p.len_arrU]) (by omega) _ ?_
    have hy : p.arrY = (p.q.drop 1 ++ [p.B] ++ p.mid1 ++ [x0]) ++ [p.C] := by simp [arrY, hq0]
    rw [hy, show ((p.q.drop 1 ++ [p.B] ++ p.mid1 ++ [x0]) ++ [p.C]).length - 1 =
      p.mid1.length + p.q.length + 1 by simp <;> omega]
    refine compat_trans2 _ _ (x1 :: qm ++ [xl, p.B] ++ p.mid1) [p.A, x0] [x0] _ _ _ ?_ ?_
      (by rw [hq]; simp <;> omega) rfl rfl
    · rw [show p.mid1.length + 3 - 1 = p.mid1.length + 2 by omega,
        rot_eq_drop_append_take_of_le _ _ (by simp [arrU] <;> omega)]
      simp [arrU, hq, List.take_append, List.drop_append]
    · simp [hq]
  -- y -> v
  have r3 : PathRunsTo (sweep p.arrY p.A 2) (fullRow (rot p.arrV (p.arrV.length - 1)) p.C) := by
    refine sweep_runs _ _ 2 (p.mid1.length + p.q.length) (by rw [p.len_arrY h3]) (by omega) _ ?_
    have hv : p.arrV = (p.q.drop 2 ++ [p.B] ++ p.mid1 ++ [x0, x1]) ++ [p.A] := by simp [arrV, hq0, hq1]
    rw [hv, show ((p.q.drop 2 ++ [p.B] ++ p.mid1 ++ [x0, x1]) ++ [p.A]).length - 1 =
      p.mid1.length + p.q.length + 1 by simp <;> omega]
    refine compat_trans2 _ _ (qm ++ [xl, p.B] ++ p.mid1 ++ [x0]) [p.C, x1] [x1] _ _ _ ?_ ?_
      (by rw [hq]; simp <;> omega) rfl rfl
    · simp only [arrY, hq0, hq, show (2 : Nat) - 1 = 1 by rfl, List.drop_succ_cons, List.drop_zero,
        List.cons_append]
      rw [rot_cons_one_generic]; simp
    · simp [hq]
  -- v -> next period
  have r4 : PathRunsTo (sweep p.arrV p.C (p.q.length + 1)) p.next.first := by
    refine sweep_runs _ _ _ (p.mid1.length + p.q.length) (by rw [p.len_arrV h3]) (by omega) _ ?_
    have hw : p.next.arrW = ([b] ++ r ++ [x0, x1, p.A] ++ qm ++ [xl, a]) ++ [p.C] := by
      simp [next, arrW, ql, hq, hm]
    have hl : p.next.arrW.length - 1 = p.mid1.length + p.q.length + 1 := by
      rw [hw, hm, hq]; simp <;> omega
    unfold first
    rw [hl, hw]
    refine compat_trans2 _ _ ([b] ++ r ++ [x0, x1, p.A] ++ qm ++ [xl]) [p.B, a] [a] _ _ _ ?_ ?_
      (by rw [hm, hq]; simp <;> omega) rfl rfl
    · rw [show p.q.length + 1 - 1 = (qm ++ [xl, p.B, a]).length by rw [hq]; simp]
      rw [show p.arrV = (qm ++ [xl, p.B, a]) ++ (b :: r ++ [x0, x1, p.A]) by simp [arrV, hq0, hq1, hm, hq],
        rot_append_length]
      simp
    · simp
  unfold period
  refine runs_append (sweep_head _ _ _) ?_ r4
  refine runs_append (sweep_head _ _ _) ?_ r3
  exact runs_append (sweep_head _ _ _) r1 r2

theorem period_length : p.period.length = p.mid1.length + p.q.length + 12 := by
  simp [period, sweep_length]; omega

theorem period_charge (h3 : 3 ≤ p.q.length) : (p.period.map Row.charge).sum = 8 := by
  simp only [period, List.map_append, List.sum_append]
  rw [sweep_charge _ _ _ (by simp [p.len_arrW h3] <;> omega) (by omega),
    sweep_charge _ _ _ (by simp [p.len_arrU] <;> omega) (by omega),
    sweep_charge _ _ _ (by simp [p.len_arrY h3] <;> omega) (by omega),
    sweep_charge _ _ _ (by simp [p.len_arrV h3] <;> omega) (by omega)]

/-- The multiset of an explicit list, for permutation proofs. -/
theorem perm_of_eq {l l' : List Nat} (L L' : List Nat) (h1 : l = L) (h2 : l' = L')
    (h : (L : Multiset Nat) = (L' : Multiset Nat)) : l.Perm l' := by
  subst h1 h2; exact Multiset.coe_eq_coe.mp h

theorem perm_W (h3 : 3 ≤ p.q.length) : (p.arrW ++ [p.B]).Perm (p.C :: p.B :: p.A :: p.list) := by
  obtain ⟨x0, x1, qm, xl, hq, hq0, hq1, hql⟩ := p.q_split h3
  refine perm_of_eq ([xl] ++ p.mid1 ++ [p.A, x0, x1] ++ qm ++ [p.C, p.B])
    ([p.C, p.B, p.A] ++ p.mid1 ++ [x0, x1] ++ qm ++ [xl]) (by simp [arrW, hq, hql]) (by simp [list, hq]) ?_
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

theorem perm_U : (p.arrU ++ [p.C]).Perm (p.C :: p.B :: p.A :: p.list) := by
  rw [← Multiset.coe_eq_coe]
  simp only [arrU, list, ← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

theorem perm_Y (h3 : 3 ≤ p.q.length) : (p.arrY ++ [p.A]).Perm (p.C :: p.B :: p.A :: p.list) := by
  obtain ⟨x0, x1, qm, xl, hq, hq0, hq1, hql⟩ := p.q_split h3
  refine perm_of_eq ([x1] ++ qm ++ [xl, p.B] ++ p.mid1 ++ [x0, p.C, p.A])
    ([p.C, p.B, p.A] ++ p.mid1 ++ [x0, x1] ++ qm ++ [xl]) (by simp [arrY, hq, hq0]) (by simp [list, hq]) ?_
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

theorem perm_V (h3 : 3 ≤ p.q.length) : (p.arrV ++ [p.C]).Perm (p.C :: p.B :: p.A :: p.list) := by
  obtain ⟨x0, x1, qm, xl, hq, hq0, hq1, hql⟩ := p.q_split h3
  refine perm_of_eq (qm ++ [xl, p.B] ++ p.mid1 ++ [x0, x1, p.A, p.C])
    ([p.C, p.B, p.A] ++ p.mid1 ++ [x0, x1] ++ qm ++ [xl]) (by simp [arrV, hq, hq0, hq1])
    (by simp [list, hq]) ?_
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

theorem period_basedOn (h3 : 3 ≤ p.q.length) (alph : List Nat)
    (hp : (p.C :: p.B :: p.A :: p.list).Perm alph) (hnd : alph.Nodup) (h9 : 9 ∉ alph) :
    BasedOn alph 9 p.period := by
  intro r hr
  simp only [period, List.mem_append] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · exact sweep_basedOn _ _ _ _ ((p.perm_W h3).trans hp) hnd h9 (by rw [p.len_arrW h3]; omega) r hr
  · exact sweep_basedOn _ _ _ _ (p.perm_U.trans hp) hnd h9 (by rw [p.len_arrU]; omega) r hr
  · exact sweep_basedOn _ _ _ _ ((p.perm_Y h3).trans hp) hnd h9 (by rw [p.len_arrY h3]; omega) r hr
  · exact sweep_basedOn _ _ _ _ ((p.perm_V h3).trans hp) hnd h9 (by rw [p.len_arrV h3]; omega) r hr

end Pg

/-! ### The walk -/

/-- The period data of the old letters `O` (read from index `o + 2`) for the parameter `g`. -/
def pgOf (O : List Nat) (g A B C : Nat) : Pg :=
  ⟨O.take (O.length - 2 - g), O.drop (O.length - 2 - g), A, B, C⟩

theorem pgOf_list (O : List Nat) (g A B C : Nat) : (pgOf O g A B C).list = O := by
  simp [pgOf, Pg.list]

theorem pgOf_lens (O : List Nat) (g A B C : Nat) (hg : g + 4 ≤ O.length) :
    (pgOf O g A B C).mid1.length = O.length - 2 - g ∧ (pgOf O g A B C).q.length = g + 2 := by
  simp [pgOf]; omega

theorem pgOf_eq (X Y : List Nat) (g A B C : Nat) (h : X.length + 2 + g = (X ++ Y).length) :
    pgOf (X ++ Y) g A B C = ⟨X, Y, A, B, C⟩ := by
  have hx : (X ++ Y).length - 2 - g = X.length := by omega
  simp only [pgOf, hx, List.take_left', List.drop_left']

theorem pgOf_rot2 (O : List Nat) (g A B C : Nat) (hg : g + 4 ≤ O.length) :
    pgOf (rot O 2) g A B C = (pgOf O g A B C).next := by
  have hO : O = (pgOf O g A B C).mid1 ++ (pgOf O g A B C).q := (pgOf_list O g A B C).symm
  obtain ⟨hl1, hl2⟩ := pgOf_lens O g A B C hg
  generalize hM : (pgOf O g A B C).mid1 = M at hO hl1
  generalize hQ : (pgOf O g A B C).q = Qq at hO hl2
  obtain ⟨a, b, r, hm⟩ : ∃ a b r, M = a :: b :: r := by
    match M, hl1 with
    | a :: b :: r, _ => exact ⟨a, b, r, rfl⟩
    | [], h => simp at h; omega
    | [a], h => simp at h; omega
  have e : rot O 2 = (r ++ Qq.take 2) ++ (Qq.drop 2 ++ [a, b]) := by
    rw [hO, hm, rot_eq_drop_append_take_of_le _ _ (by simp)]
    simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero]
    conv_lhs => rw [← List.take_append_drop 2 Qq]
    simp only [List.append_assoc]
  have hlen : (r ++ Qq.take 2).length + 2 + g = ((r ++ Qq.take 2) ++ (Qq.drop 2 ++ [a, b])).length := by
    rw [← e, rot_length, hO, hm]; simp [hm] at hl1; simp <;> omega
  rw [e, pgOf_eq _ _ _ _ _ _ hlen]
  simp only [Pg.next, hM, hQ, hm]
  simp [pgOf]

/-- The walk with parameter `g`, roles `A B C`, shift `s` and `P` periods. -/
def walkR (d0 : List Nat) (g A B C s P : Nat) : List (Row Nat) :=
  (List.range P).flatMap fun k => (pgOf (rot d0 (s + 2 * k + 2)) g A B C).period

theorem pgOf_lens' (d0 : List Nat) (g A B C i : Nat) (hg : g + 4 ≤ d0.length) :
    (pgOf (rot d0 i) g A B C).mid1.length = d0.length - 2 - g ∧
      (pgOf (rot d0 i) g A B C).q.length = g + 2 := by
  have := pgOf_lens (rot d0 i) g A B C (by simp <;> omega)
  simpa using this

theorem walkR_closed (d0 : List Nat) (g A B C s P : Nat) (hg1 : 1 ≤ g) (hg : g + 4 ≤ d0.length)
    (hP : 1 ≤ P) (h2P : (2 * P) % d0.length = 0) : ClosedTrail (walkR d0 g A B C s P) := by
  let Q := fun k => pgOf (rot d0 (s + 2 * k + 2)) g A B C
  have hsplit : ∀ k, ∃ rest, (Q k).period = (Q k).first :: rest := by
    intro k
    have h := (Q k).period_head
    match hq : (Q k).period, h with
    | r :: rest, h => simp at h; exact ⟨rest, by rw [h]⟩
  choose t ht using hsplit
  have hw : walkR d0 g A B C s P = (List.range P).flatMap fun k => (Q k).first :: t k := by
    unfold walkR; congr 1; funext k; exact ht k
  rw [hw]
  refine closed_of_periods (fun k => (Q k).first) t P hP ?_ ?_
  · intro k
    rw [← ht k]
    have hn : Q (k + 1) = (Q k).next := by
      show pgOf (rot d0 (s + 2 * (k + 1) + 2)) g A B C = (pgOf (rot d0 (s + 2 * k + 2)) g A B C).next
      rw [← pgOf_rot2 _ _ _ _ _ (by simp <;> omega), rot_add]
      congr 2
    rw [hn]
    obtain ⟨h1, h2⟩ := pgOf_lens' d0 g A B C (s + 2 * k + 2) hg
    exact (Q k).period_runs (by show 2 ≤ (pgOf _ g A B C).mid1.length; rw [h1]; omega)
      (by show 3 ≤ (pgOf _ g A B C).q.length; rw [h2]; omega)
  · show (pgOf (rot d0 (s + 2 * P + 2)) g A B C).first = (pgOf (rot d0 (s + 2 * 0 + 2)) g A B C).first
    have : rot d0 (s + 2 * P + 2) = rot d0 (s + 2 * 0 + 2) := by
      rw [← rot_mod d0 (s + 2 * P + 2), ← rot_mod d0 (s + 2 * 0 + 2)]
      congr 1
      rw [show s + 2 * P + 2 = (s + 2) + 2 * P by omega, Nat.add_mod, h2P]
      simp
    rw [this]

theorem period_len_rot (d0 : List Nat) (g A B C i : Nat) (hg : g + 4 ≤ d0.length) :
    (pgOf (rot d0 i) g A B C).period.length = d0.length + 12 := by
  rw [Pg.period_length]
  obtain ⟨h1, h2⟩ := pgOf_lens' d0 g A B C i hg
  rw [h1, h2]
  omega

theorem walkR_length (d0 : List Nat) (g A B C s P : Nat) (hg : g + 4 ≤ d0.length) :
    (walkR d0 g A B C s P).length = P * (d0.length + 12) := by
  unfold walkR
  rw [length_flatMap_const _ _ (d0.length + 12) (fun k _ => period_len_rot d0 g A B C _ hg)]
  simp

theorem walkR_charge (d0 : List Nat) (g A B C s P : Nat) (hg1 : 1 ≤ g) (hg : g + 4 ≤ d0.length) :
    ((walkR d0 g A B C s P).map Row.charge).sum = 8 * P := by
  unfold walkR
  rw [List.map_flatMap, sum_flatMap_const _ _ 8 (fun k _ => Pg.period_charge _
    (by rw [(pgOf_lens' d0 g A B C (s + 2 * k + 2) hg).2]; omega))]
  simp; ring

theorem walkR_basedOn (d0 : List Nat) (g A B C s P : Nat) (hg1 : 1 ≤ g) (hg : g + 4 ≤ d0.length)
    (hnd : (C :: B :: A :: d0).Nodup) (h9 : 9 ∉ C :: B :: A :: d0) :
    BasedOn (C :: B :: A :: d0) 9 (walkR d0 g A B C s P) := by
  intro r hr
  obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hr
  obtain ⟨h1, h2⟩ := pgOf_lens' d0 g A B C (s + 2 * k + 2) hg
  refine Pg.period_basedOn _ (by rw [h2]; omega) _ ?_ hnd h9 r hk
  show (C :: B :: A :: (pgOf (rot d0 (s + 2 * k + 2)) g A B C).list).Perm _
  rw [pgOf_list]
  exact (((rot_perm d0 _).cons A).cons B).cons C

end SuperpermutationUpperBound43586371.UniR
