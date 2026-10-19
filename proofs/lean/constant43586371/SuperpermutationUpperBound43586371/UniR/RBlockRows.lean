import SuperpermutationUpperBound43586371.UniR.RLoops

/-!
# All rows of R'(m) are distinct (`PROOF_R.md`, sections 4-5)

`row_keys`: the real keys of a row (`t1`, `t2`) in terms of `d0`; `row_inj`: equal C-normal forms force the same
walk, period and row; `block_canon_nodup`, `block_canon_mem`, `block_dloops_length`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SuperpermutationUpperBound43586371.UniR

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound43586371.Uniform

namespace Pg

variable (p : Pg)

theorem cA_eq (m g : Nat) (h1 : p.mid1.length = m - 2 - g) (f : Nat) : p.cA f = cAf m g f := by
  unfold cA cAf; rw [h1]; split_ifs <;> omega

theorem cB_eq (m : Nat) (hm : p.mid1.length + p.q.length = m) (f : Nat) : p.cB f = cBf m f := by
  unfold cB cBf; split_ifs <;> omega

theorem gat (L R : List Nat) (z n : Nat) (hn : n = L.length) : (L ++ z :: R)[n]? = some z := by
  subst hn; simp

theorem lasts (h3 : 3 ≤ p.q.length) :
    (rot p.a1 0).getLast? = some p.B ∧
      (rot p.a1 (p.mid1.length + p.q.length + 1)).getLast? = p.list[p.mid1.length + p.q.length - 2]? ∧
      (rot p.a2 0).getLast? = some p.A ∧
      (rot p.a2 (p.mid1.length + p.q.length + 1)).getLast? = p.list[p.mid1.length]? := by
  obtain ⟨x0, x1, qm, xl, hq, hq0, hq1, hql⟩ := p.q_split h3
  have glast : ∀ (l : List Nat) (x : Nat), (l ++ [x]).getLast? = some x := fun l x => by simp
  obtain ⟨D, z, hz⟩ : ∃ D z, x0 :: x1 :: qm = D ++ [z] :=
    ⟨_, _, (List.dropLast_append_getLast (by simp)).symm⟩
  have hDl : D.length = qm.length + 1 := by have := congrArg List.length hz; simp at this; omega
  have e1 : p.a1 = ([xl] ++ p.mid1 ++ [p.A] ++ (x0 :: x1 :: qm)) ++ [p.B] := by simp [a1, hq, hql]
  have e2 : p.a2 = ((x1 :: qm) ++ [xl, p.B] ++ p.mid1 ++ [x0]) ++ [p.A] := by simp [a2, hq, hq0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rot_zero, e1]; exact glast _ _
  · rw [e1, show p.mid1.length + p.q.length + 1 = ([xl] ++ p.mid1 ++ [p.A] ++ (x0 :: x1 :: qm)).length by
      rw [hq]; simp <;> omega, rot_append_length, hz]
    rw [show [p.B] ++ ([xl] ++ p.mid1 ++ [p.A] ++ (D ++ [z])) = ([p.B, xl] ++ p.mid1 ++ [p.A] ++ D) ++ [z] by
      simp, glast]
    rw [show p.list = (p.mid1 ++ D) ++ z :: [xl] by
      simp only [list, hq]; rw [show x0 :: x1 :: (qm ++ [xl]) = (x0 :: x1 :: qm) ++ [xl] by simp, hz]; simp]
    rw [gat _ _ _ _ (by rw [hq]; simp <;> omega)]
  · rw [rot_zero, e2]; exact glast _ _
  · rw [e2, show p.mid1.length + p.q.length + 1 = ((x1 :: qm) ++ [xl, p.B] ++ p.mid1 ++ [x0]).length by
      rw [hq]; simp <;> omega, rot_append_length]
    rw [show [p.A] ++ ((x1 :: qm) ++ [xl, p.B] ++ p.mid1 ++ [x0]) = ([p.A] ++ (x1 :: qm) ++ [xl, p.B] ++ p.mid1) ++ [x0] by
      simp, glast]
    rw [show p.list = p.mid1 ++ x0 :: (x1 :: (qm ++ [xl])) by simp [list, hq], gat _ _ _ _ rfl]

end Pg

/-! ### Keys of the rows of the block -/

section

variable {d0 : List Nat} {t1 t2 t3 : Nat}

theorem row_keys (S : Setting d0 t1 t2 t3) {d : Nat × Nat × Nat} (hd : d ∈ Dl d0.length) (k f : Nat)
    (hf : f < 4) (j : Nat) :
    key1 t1 t2 (rot ((pD d0 t1 t2 t3 d k).arr f) j) =
        rot d0 (d.2.2 + 2 * k + 2 + K1 d0.length d.1 d.2.1 f) ++ [t1] ∧
      key2 t1 t2 (rot ((pD d0 t1 t2 t3 d k).arr f) j) =
        rot d0 (d.2.2 + 2 * k + 2 + K2 d0.length d.1 d.2.1 f) ++ [t2] := by
  obtain ⟨hg3, hg5, hσ, -⟩ := mem_Dl hd
  set p := pD d0 t1 t2 t3 d k with hp
  have hnd := S.pD_nd d hσ k
  obtain ⟨hl1, hl2⟩ := pD_lens d0 t1 t2 t3 d k (by omega)
  have h3 : 3 ≤ p.q.length := by rw [hl2]; omega
  obtain ⟨hAB, -, -, -, -, -, -⟩ := p.facts hnd
  have hlist : p.list = rot d0 (d.2.2 + 2 * k + 2) := pgOf_list _ _ _ _ _
  have k1 := key1_rot (A := p.A) (B := p.B) (p.arr_nodup h3 hnd f) (p.A_mem_arr f) hAB j
  have k2 := key2_rot (A := p.A) (B := p.B) (p.arr_nodup h3 hnd f) (p.B_mem_arr f) hAB j
  rw [p.key1_arr h3 hnd f hf, hlist, rot_add, p.cA_eq d0.length d.1 hl1] at k1
  rw [p.key2_arr h3 hnd f hf, hlist, rot_add, p.cB_eq d0.length (by rw [hl1, hl2]; omega)] at k2
  have hAv : p.A = rA d.2.1 t1 t2 := rfl
  have hBv : p.B = rB d.2.1 t1 t2 := rfl
  rcases (show d.2.1 = 0 ∨ d.2.1 = 1 by omega) with h0 | h0
  · simp only [rA, rB, h0, if_true] at hAv hBv
    rw [hAv, hBv] at k1 k2
    simp only [K1, K2, h0, if_true]
    exact ⟨k1, k2⟩
  · simp only [rA, rB, h0, show (1 : Nat) ≠ 0 by omega, if_false] at hAv hBv
    rw [hAv, hBv] at k1 k2
    simp only [K1, K2, h0, show (1 : Nat) ≠ 0 by omega, if_false]
    exact ⟨k2, k1⟩

theorem row_canon (S : Setting d0 t1 t2 t3) {d : Nat × Nat × Nat} (hd : d ∈ Dl d0.length) (k i : Nat)
    (hi : i < d0.length + 12) :
    canon t3 ((pD d0 t1 t2 t3 d k).rowAt i).base =
      rot ((pD d0 t1 t2 t3 d k).arr (Pg.famOf (d0.length - 2 - d.1) i))
        (Pg.jjOf (d0.length - 2 - d.1) d0.length i) ++ [t3] := by
  obtain ⟨hg3, hg5, hσ, -⟩ := mem_Dl hd
  obtain ⟨hl1, hl2⟩ := pD_lens d0 t1 t2 t3 d k (by omega)
  have h := (pD d0 t1 t2 t3 d k).canon_rowAt (by rw [hl1]; omega) (by rw [hl2]; omega) (S.pD_nd d hσ k) i
    (by rw [hl1, hl2]; omega)
  rw [hl1, hl2, show d0.length - 2 - d.1 + (d.1 + 2) = d0.length by omega] at h
  exact h

theorem pD_getElem (d : Nat × Nat × Nat) (k t : Nat) (ht : t < d0.length) :
    (pD d0 t1 t2 t3 d k).list[t]? = d0[(d.2.2 + 2 * k + 2 + t) % d0.length]? := by
  rw [show (pD d0 t1 t2 t3 d k).list = rot d0 (d.2.2 + 2 * k + 2) from pgOf_list _ _ _ _ _]
  rw [List.getElem?_eq_getElem (by simp; omega), getElem_rot,
    List.getElem?_eq_getElem (Nat.mod_lt _ (by omega))]

/-- The `a1 / a2` case of Lemma 3: rows of `a1` and of `a2` never coincide. -/
theorem a1_a2_ne (S : Setting d0 t1 t2 t3) {d d' : Nat × Nat × Nat} (hd : d ∈ Dl d0.length)
    (hd' : d' ∈ Dl d0.length) (hgg : d.1 = d'.1) (hσσ : d.2.1 = d'.2.1) {k k' j j' : Nat}
    (hk : d.2.2 + 2 * k + 2 ≤ 2 * d0.length) (hk' : d'.2.2 + 2 * k' + 2 ≤ 2 * d0.length)
    (hj : j = 0 ∨ j = d0.length + 1) (hj' : j' = 0 ∨ j' = d0.length + 1)
    (hoo : d.2.2 + 2 * k = d'.2.2 + 2 * k' + 1 ∨ d.2.2 + 2 * k + d0.length = d'.2.2 + 2 * k' + 1 ∨
      d.2.2 + 2 * k = d'.2.2 + 2 * k' + 1 + d0.length ∨ d.2.2 + 2 * k + 2 * d0.length = d'.2.2 + 2 * k' + 1)
    (hX : rot ((pD d0 t1 t2 t3 d k).arr 0) j = rot ((pD d0 t1 t2 t3 d' k').arr 2) j') : False := by
  obtain ⟨hg3, hg5, hσ, hs⟩ := mem_Dl hd
  obtain ⟨hg3', hg5', hσ', hs'⟩ := mem_Dl hd'
  set m := d0.length with hm
  have hpos : 0 < m := by omega
  obtain ⟨hl1, hl2⟩ := pD_lens d0 t1 t2 t3 d k (by omega)
  obtain ⟨hl1', hl2'⟩ := pD_lens d0 t1 t2 t3 d' k' (by omega)
  obtain ⟨l1, l2, -, -⟩ := (pD d0 t1 t2 t3 d k).lasts (by rw [hl2]; omega)
  obtain ⟨-, -, l3, l4⟩ := (pD d0 t1 t2 t3 d' k').lasts (by rw [hl2']; omega)
  rw [hl1, hl2, show m - 2 - d.1 + (d.1 + 2) = m by omega] at l2
  rw [hl1', hl2', show m - 2 - d'.1 + (d'.1 + 2) = m by omega] at l4
  have hl := congrArg List.getLast? hX
  simp only [Pg.arr] at hl
  have hBv : (pD d0 t1 t2 t3 d k).B = rB d.2.1 t1 t2 := rfl
  have hAv : (pD d0 t1 t2 t3 d' k').A = rA d.2.1 t1 t2 := by rw [hσσ]; rfl
  have hmem : ∀ x i, d0[i]? = some x → x ∈ d0 := fun x i h => List.mem_of_getElem? h
  have hrB : rB d.2.1 t1 t2 ∉ d0 := by unfold rB; split_ifs; exact S.t2_d0; exact S.t1_d0
  have hrA : rA d.2.1 t1 t2 ∉ d0 := by unfold rA; split_ifs; exact S.t1_d0; exact S.t2_d0
  have hAB : rA d.2.1 t1 t2 ≠ rB d.2.1 t1 t2 := by
    unfold rA rB; split_ifs; exact S.t12; exact S.t12.symm
  rcases hj with rfl | rfl <;> rcases hj' with rfl | rfl
  · rw [l1, l3, hBv, hAv] at hl; exact hAB (Option.some.inj hl).symm
  · rw [l1, show m + 1 = m + 1 from rfl, l4, pD_getElem _ _ _ (by omega), hBv] at hl
    exact hrB (hmem _ _ hl.symm)
  · rw [l2, pD_getElem _ _ _ (by omega), l3, hAv] at hl
    exact hrA (hmem _ _ hl)
  · rw [l2, l4, pD_getElem _ _ _ (by omega), pD_getElem _ _ _ (by omega)] at hl
    rw [List.getElem?_eq_getElem (Nat.mod_lt _ hpos), List.getElem?_eq_getElem (Nat.mod_lt _ hpos)] at hl
    have hi := (List.Nodup.getElem_inj_iff S.d0_nodup).mp (Option.some.inj hl)
    have c := mod_eq_cases _ _ m hpos hi (by omega) (by omega)
    rcases c with c | c | c | c | c <;> omega

theorem row_inj (S : Setting d0 t1 t2 t3) {d d' : Nat × Nat × Nat} (hd : d ∈ Dl d0.length)
    (hd' : d' ∈ Dl d0.length) {k k' i i' : Nat} (hk : k < Pm d0.length) (hk' : k' < Pm d0.length)
    (hi : i < d0.length + 12) (hi' : i' < d0.length + 12)
    (h : canon t3 ((pD d0 t1 t2 t3 d k).rowAt i).base = canon t3 ((pD d0 t1 t2 t3 d' k').rowAt i').base) :
    d = d' ∧ k = k' ∧ i = i' := by
  obtain ⟨hg3, hg5, hσ, hs⟩ := mem_Dl hd
  obtain ⟨hg3', hg5', hσ', hs'⟩ := mem_Dl hd'
  set m := d0.length with hm
  have hpos : 0 < m := by omega
  have hP := Pm_spec m
  rw [row_canon S hd k i hi, row_canon S hd' k' i' hi'] at h
  have hX := List.append_cancel_right h
  set f := Pg.famOf (m - 2 - d.1) i
  set j := Pg.jjOf (m - 2 - d.1) m i
  set f' := Pg.famOf (m - 2 - d'.1) i'
  set j' := Pg.jjOf (m - 2 - d'.1) m i'
  have hf : f < 4 := Pg.famOf_lt _ _
  have hf' : f' < 4 := Pg.famOf_lt _ _
  obtain ⟨e1, e2⟩ := row_keys S hd k f hf j
  obtain ⟨e1', e2'⟩ := row_keys S hd' k' f' hf' j'
  have m1 := rot_app_inj S.d0_nodup hpos (e1.symm.trans ((congrArg (key1 t1 t2) hX).trans e1'))
  have m2 := rot_app_inj S.d0_nodup hpos (e2.symm.trans ((congrArg (key2 t1 t2) hX).trans e2'))
  have ho : d.2.2 + 2 * k + 2 ≤ 2 * m := by omega
  have ho' : d'.2.2 + 2 * k' + 2 ≤ 2 * m := by omega
  obtain ⟨hgg, hσσ, hcase⟩ := arithR m d.1 d'.1 d.2.1 d'.2.1 f f' (d.2.2 + 2 * k) (d'.2.2 + 2 * k')
    hg3 hg5 hg3' hg5' hσ hσ' hf hf' ho ho' (by simpa [Nat.add_assoc] using m1) (by simpa [Nat.add_assoc] using m2)
  rcases hcase with ⟨hff, hoo⟩ | ⟨hf0, hf2, hoo⟩ | ⟨hf2, hf0, hoo⟩
  · -- same family: same walk, period and row
    have hsk : d.2.2 = d'.2.2 ∧ k = k' := by omega
    have hdd : d = d' := by
      obtain ⟨a, b, c⟩ := d; obtain ⟨a', b', c'⟩ := d'
      simp only at hgg hσσ hsk ⊢; rw [hgg, hσσ, hsk.1]
    subst hdd
    obtain ⟨-, rfl⟩ := hsk
    refine ⟨rfl, rfl, ?_⟩
    obtain ⟨hl1, hl2⟩ := pD_lens d0 t1 t2 t3 d k (by omega)
    have h3 : 3 ≤ (pD d0 t1 t2 t3 d k).q.length := by rw [hl2]; omega
    rw [hff] at hX
    have hlen := (pD d0 t1 t2 t3 d k).arr_length h3 f'
    have hj : j = j' := rot_index_eq_of_nodup ((pD d0 t1 t2 t3 d k).arr_nodup h3 (S.pD_nd d hσ k) f')
      (by rw [hlen, hl1, hl2]; exact Pg.jjOf_lt _ _ _ (by omega) hi |>.trans_le (by omega))
      (by rw [hlen, hl1, hl2]; exact Pg.jjOf_lt _ _ _ (by omega) hi' |>.trans_le (by omega)) hX
    exact Pg.famOf_jjOf_inj (m - 2 - d.1) m i i' (by omega) (by omega) hi hi' hff hj
  · exfalso
    have hj := Pg.jjOf_02 (m - 2 - d.1) m i (Or.inl hf0)
    have hj' := Pg.jjOf_02 (m - 2 - d'.1) m i' (Or.inr hf2)
    rw [hf0, hf2] at hX
    exact a1_a2_ne S hd hd' hgg hσσ ho ho' hj hj' hoo hX
  · exfalso
    have hj := Pg.jjOf_02 (m - 2 - d.1) m i (Or.inr hf2)
    have hj' := Pg.jjOf_02 (m - 2 - d'.1) m i' (Or.inl hf0)
    rw [hf0, hf2] at hX
    exact a1_a2_ne S hd' hd hgg.symm hσσ.symm ho' ho hj' hj hoo hX.symm

theorem blockRows_eq (S : Setting d0 t1 t2 t3) :
    blockRows d0 t1 t2 t3 = (Dl d0.length).flatMap fun d => (List.range (Pm d0.length)).flatMap fun k =>
      (List.range (d0.length + 12)).map (pD d0 t1 t2 t3 d k).rowAt := by
  unfold blockRows
  refine List.flatMap_congr (fun d hd => ?_)
  obtain ⟨-, hg5, -, -⟩ := mem_Dl hd
  exact walkD_eq d0 t1 t2 t3 d (by omega)

theorem block_canon_nodup (S : Setting d0 t1 t2 t3) :
    ((blockRows d0 t1 t2 t3).map (fun r => canon t3 r.base)).Nodup := by
  rw [blockRows_eq S, List.map_flatMap]
  simp only [List.map_flatMap, List.map_map]
  refine List.nodup_flatMap.mpr ⟨fun d hd => List.nodup_flatMap.mpr ⟨fun k hk => ?_, ?_⟩, ?_⟩
  · refine List.Nodup.map_on (fun i hi i' hi' h => ?_) List.nodup_range
    exact (row_inj S hd hd (List.mem_range.mp hk) (List.mem_range.mp hk) (List.mem_range.mp hi)
      (List.mem_range.mp hi') h).2.2
  · refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := Pm d0.length))
    intro k k' hk hk' hne x hx hx'
    simp only [List.mem_map, List.mem_range, Function.comp] at hx hx'
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨i', hi', h⟩ := hx'
    exact hne (row_inj S hd hd (List.mem_range.mp hk) (List.mem_range.mp hk') hi hi' h.symm).2.1
  · refine List.Pairwise.imp_of_mem ?_ (Dl_nodup d0.length)
    intro d d' hd hd' hne x hx hx'
    simp only [List.mem_flatMap, List.mem_map, List.mem_range, Function.comp] at hx hx'
    obtain ⟨k, hk, i, hi, rfl⟩ := hx
    obtain ⟨k', hk', i', hi', h⟩ := hx'
    exact hne (row_inj S hd hd' hk hk' hi hi' h.symm).1

theorem block_mem (S : Setting d0 t1 t2 t3) {r : Row Nat} (hr : r ∈ blockRows d0 t1 t2 t3) :
    ∃ d ∈ Dl d0.length, ∃ k < Pm d0.length, ∃ i < d0.length + 12, r = (pD d0 t1 t2 t3 d k).rowAt i := by
  rw [blockRows_eq S] at hr
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hr
  obtain ⟨d, hd, k, hk, i, hi, rfl⟩ := hr
  exact ⟨d, hd, k, hk, i, hi, rfl⟩

theorem block_canon_mem (S : Setting d0 t1 t2 t3) {r : Row Nat} (hr : r ∈ blockRows d0 t1 t2 t3) :
    canon t3 r.base ∈ above3T t1 t2 t3 d0 := by
  obtain ⟨d, hd, k, hk, i, hi, rfl⟩ := block_mem S hr
  obtain ⟨hg3, hg5, hσ, -⟩ := mem_Dl hd
  rw [row_canon S hd k i hi]
  set p := pD d0 t1 t2 t3 d k
  set f := Pg.famOf (d0.length - 2 - d.1) i
  set j := Pg.jjOf (d0.length - 2 - d.1) d0.length i
  obtain ⟨hl1, hl2⟩ := pD_lens d0 t1 t2 t3 d k (by omega)
  have h3 : 3 ≤ p.q.length := by rw [hl2]; omega
  have hnd : (rot (p.arr f) j).Nodup := rot_nodup (p.arr_nodup h3 (S.pD_nd d hσ k) f) j
  have hAm : p.A ∈ rot (p.arr f) j := (rot_perm _ j).mem_iff.mpr (p.A_mem_arr f)
  have hBm : p.B ∈ rot (p.arr f) j := (rot_perm _ j).mem_iff.mpr (p.B_mem_arr f)
  have ht12 : t1 ∈ rot (p.arr f) j ∧ t2 ∈ rot (p.arr f) j := by
    have hAv : p.A = rA d.2.1 t1 t2 := rfl
    have hBv : p.B = rB d.2.1 t1 t2 := rfl
    unfold rA at hAv; unfold rB at hBv
    split_ifs at hAv hBv
    · rw [hAv] at hAm; rw [hBv] at hBm; exact ⟨hAm, hBm⟩
    · rw [hAv] at hAm; rw [hBv] at hBm; exact ⟨hBm, hAm⟩
  refine above3T_of hnd ht12.1 ht12.2 S.t12 ?_
  obtain ⟨e1, -⟩ := row_keys S hd k f (Pg.famOf_lt _ _) j
  have hc := canon_cyc_self (c := t1) (x := (rot (p.arr f) j).filter (fun y => y != t2))
    (List.mem_filter.mpr ⟨ht12.1, by simpa using S.t12⟩)
  change CyclicEq _ (key1 t1 t2 (rot (p.arr f) j)) at hc
  rw [e1] at hc
  have ht1 : t1 ∉ rot d0 (d.2.2 + 2 * k + 2 + K1 d0.length d.1 d.2.1 f) :=
    fun hm => S.t1_d0 ((rot_perm _ _).mem_iff.mp hm)
  have hne : d0 ≠ [] := by intro h; rw [h] at hg5; simp at hg5
  have hc2 := filt_cyc hc.symm (fun y => y != t1) (by
    rw [filter_append_ne ht1]; intro h; exact hne (by simpa using congrArg List.length h))
  rw [filter_append_ne ht1] at hc2
  exact hc2.symm.trans (CyclicEq.of_rot hne _).symm

theorem blockRows_length (S : Setting d0 t1 t2 t3) :
    (blockRows d0 t1 t2 t3).length = (Dl d0.length).length * (Pm d0.length * (d0.length + 12)) := by
  unfold blockRows
  rw [length_flatMap_const _ _ (Pm d0.length * (d0.length + 12)) (fun d hd => by
    obtain ⟨-, hg5, -, -⟩ := mem_Dl hd
    exact walkR_length _ _ _ _ _ _ _ (by omega))]

theorem blockRows_charge (S : Setting d0 t1 t2 t3) :
    ((blockRows d0 t1 t2 t3).map Row.charge).sum = (Dl d0.length).length * (8 * Pm d0.length) := by
  unfold blockRows
  rw [List.map_flatMap, sum_flatMap_const _ _ (8 * Pm d0.length) (fun d hd => by
    obtain ⟨hg3, hg5, -, -⟩ := mem_Dl hd
    exact walkR_charge _ _ _ _ _ _ _ (by omega) (by omega))]

theorem walkD_basedOn (S : Setting d0 t1 t2 t3) (h9 : 9 ∉ t3 :: t2 :: t1 :: d0) {d : Nat × Nat × Nat}
    (hd : d ∈ Dl d0.length) : BasedOn (t3 :: t2 :: t1 :: d0) 9 (walkD d0 t1 t2 t3 d) := by
  obtain ⟨hg3, hg5, hσ, -⟩ := mem_Dl hd
  have hperm : (t3 :: rB d.2.1 t1 t2 :: rA d.2.1 t1 t2 :: d0).Perm (t3 :: t2 :: t1 :: d0) := by
    unfold rA rB; split_ifs
    · exact List.Perm.refl _
    · exact (List.Perm.swap _ _ _).cons _
  have hb := walkR_basedOn d0 d.1 (rA d.2.1 t1 t2) (rB d.2.1 t1 t2) t3 d.2.2 (Pm d0.length) (by omega)
    (by omega) (hperm.nodup_iff.mpr S.nd) (fun hm => h9 (hperm.mem_iff.mp hm))
  exact basedOn_congr_alphabet hb hperm

theorem block_dloops_length (S : Setting d0 t1 t2 t3) (h9 : 9 ∉ t3 :: t2 :: t1 :: d0) :
    ((above3T t1 t2 t3 d0).filter (fun t => !Uniform.coveredB (blockRows d0 t1 t2 t3) t)).length =
      d0.length * ((d0.length + 1) * (d0.length + 2)) - (blockRows d0 t1 t2 t3).length := by
  have hb : ∀ r ∈ blockRows d0 t1 t2 t3, r.base.Perm (t3 :: t2 :: t1 :: d0) := by
    intro r hr
    obtain ⟨d, hd, hrd⟩ := List.mem_flatMap.mp hr
    exact ((walkD_basedOn S h9 hd) r hrd).2.1
  rw [count_uncovered (above3T t1 t2 t3 d0) (blockRows d0 t1 t2 t3) t3 (above3T_nodup S.nd)
    (fun t ht => canon_ent ht) (fun r hr => (hb r hr).nodup_iff.mpr S.nd)
    (fun r hr => ⟨block_canon_mem S hr, canon_cyc_self ((hb r hr).mem_iff.mpr List.mem_cons_self)⟩)
    (block_canon_nodup S), above3T_length]

end

end SuperpermutationUpperBound43586371.UniR
