import SuperpermutationUpperBound43586371.Uniform.Distinct

/-!
# The loops of the walk are distinct, and the loops without a row (`PROOF.md`, sections 5-6)

For odd `m ≥ 5` the `m (m+12)` rows of `walk d0 A B C` have pairwise distinct C-normal forms
(`walk_canon_nodup`), each an element of `above3T A B C d0` (`walk_canon_mem`); hence exactly
`m (m+1) (m+2) - m (m+12)` loops of `above3T` are not rotations of row bases (`walk_dloops_length`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SuperpermutationUpperBound43586371.Uniform

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

theorem mod_eq_cases (a b m : Nat) (hm : 0 < m) (h : a % m = b % m) (ha : a < 3 * m)
    (hb : b < 3 * m) : a = b ∨ a = b + m ∨ b = a + m ∨ a = b + 2 * m ∨ b = a + 2 * m := by
  have h1 := Nat.div_add_mod a m
  have h2 := Nat.div_add_mod b m
  have h3 : a / m < 3 := (Nat.div_lt_iff_lt_mul hm).mpr (by omega)
  have h4 : b / m < 3 := (Nat.div_lt_iff_lt_mul hm).mpr (by omega)
  generalize a / m = qa at h1 h3
  generalize b / m = qb at h2 h4
  interval_cases qa <;> interval_cases qb <;> omega

section

variable {d0 : List Nat} {A B C : Nat}

/-- The data of period `k`. -/
abbrev P (d0 : List Nat) (A B C k : Nat) : Pd := pdOf (rot d0 (2 * k)) A B C

theorem P_list (hm : 3 ≤ d0.length) (k : Nat) : (P d0 A B C k).list = rot d0 (2 * k) :=
  pdOf_list _ _ _ _ (by simp; omega)

theorem P_mid (hm : 3 ≤ d0.length) (k : Nat) : (P d0 A B C k).mid.length + 3 = d0.length := by
  rw [pdOf_mid_length _ _ _ _ (by simp; omega)]; simp; omega

theorem P_nd (hnd : (C :: B :: A :: d0).Nodup) (hm : 3 ≤ d0.length) (k : Nat) :
    ((P d0 A B C k).C :: (P d0 A B C k).B :: (P d0 A B C k).A :: (P d0 A B C k).list).Nodup := by
  rw [P_list hm]
  exact ((((rot_perm d0 (2 * k)).cons A).cons B).cons C).nodup_iff.mpr hnd

theorem P_e0 (hm : 3 ≤ d0.length) (k : Nat) :
    (P d0 A B C k).e0 = d0[(2 * k) % d0.length]'(Nat.mod_lt _ (by omega)) := by
  have h1 : ((P d0 A B C k).list)[0]? = some (P d0 A B C k).e0 := by simp [Pd.list]
  rw [P_list hm, List.getElem?_eq_getElem (by simp; omega), getElem_rot] at h1
  simpa using h1.symm

theorem P_el (hm : 3 ≤ d0.length) (k : Nat) :
    (P d0 A B C k).el = d0[(2 * k + (d0.length - 1)) % d0.length]'(Nat.mod_lt _ (by omega)) := by
  have hl : ([(P d0 A B C k).e0, (P d0 A B C k).e1] ++ (P d0 A B C k).mid).length = d0.length - 1 := by
    have := P_mid (A := A) (B := B) (C := C) hm k; simp; omega
  have h1 : ((P d0 A B C k).list)[d0.length - 1]? = some (P d0 A B C k).el := by
    rw [← hl]; simp [Pd.list]
  rw [P_list hm, List.getElem?_eq_getElem (by simp; omega), getElem_rot] at h1
  simpa using h1.symm

theorem rot_app_inj (hd : d0.Nodup) (hpos : 0 < d0.length) {a b X : Nat}
    (h : rot d0 a ++ [X] = rot d0 b ++ [X]) : a % d0.length = b % d0.length :=
  rot_mod_inj hd hpos (List.append_cancel_right h)

theorem lasts (p : Pd) :
    (rot p.a1 0).getLast? = some p.B ∧ (rot p.a1 (p.mid.length + 4)).getLast? = some p.e0 ∧
      (rot p.a2 0).getLast? = some p.A ∧ (rot p.a2 (p.mid.length + 4)).getLast? = some p.el := by
  have h1 : rot p.a1 (p.mid.length + 4) = [p.B] ++ ([p.e1] ++ p.mid ++ [p.A, p.el, p.e0]) := by
    have h := rot_append_length ([p.e1] ++ p.mid ++ [p.A, p.el, p.e0]) [p.B]
    simp only [Pd.a1]
    rw [show p.mid.length + 4 = ([p.e1] ++ p.mid ++ [p.A, p.el, p.e0]).length by simp <;> omega]
    simpa using h
  have h2 : rot p.a2 (p.mid.length + 4) = [p.A] ++ ([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]) := by
    have h := rot_append_length ([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]) [p.A]
    simp only [Pd.a2]
    rw [show p.mid.length + 4 = ([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]).length by simp <;> omega]
    simpa using h
  have glast : ∀ (l : List Nat) (x : Nat), (l ++ [x]).getLast? = some x := fun l x => by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rot_zero, show p.a1 = ([p.e1] ++ p.mid ++ [p.A, p.el, p.e0]) ++ [p.B] by simp [Pd.a1]]
    exact glast _ _
  · rw [h1, show [p.B] ++ ([p.e1] ++ p.mid ++ [p.A, p.el, p.e0]) =
      ([p.B] ++ [p.e1] ++ p.mid ++ [p.A, p.el]) ++ [p.e0] by simp]
    exact glast _ _
  · rw [rot_zero, show p.a2 = ([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]) ++ [p.A] by simp [Pd.a2]]
    exact glast _ _
  · rw [h2, show [p.A] ++ ([p.e0, p.e1, p.B] ++ p.mid ++ [p.el]) =
      ([p.A] ++ [p.e0, p.e1, p.B] ++ p.mid) ++ [p.el] by simp]
    exact glast _ _

theorem canon_cyc_self {c : Nat} {x : List Nat} (hc : c ∈ x) : CyclicEq x (canon c x) := by
  obtain ⟨_, _, h⟩ := canon_spec hc
  exact h

/-- Two C-normal forms of rows coincide only for the same period, arrangement and rotation. -/
theorem Xinj (hnd : (C :: B :: A :: d0).Nodup) (hm5 : 5 ≤ d0.length) (hodd : d0.length % 2 = 1)
    {k k' f f' j j' : Nat} (hk : k < d0.length) (hk' : k' < d0.length) (hf : f < 4) (hf' : f' < 4)
    (hj : j < d0.length + 2) (hj' : j' < d0.length + 2)
    (h02 : f = 0 ∨ f = 2 → j = 0 ∨ j = d0.length + 1)
    (h02' : f' = 0 ∨ f' = 2 → j' = 0 ∨ j' = d0.length + 1)
    (h : rot ((P d0 A B C k).arr f) j = rot ((P d0 A B C k').arr f') j') :
    k = k' ∧ f = f' ∧ j = j' := by
  have hm3 : 3 ≤ d0.length := by omega
  have hpos : 0 < d0.length := by omega
  have hd : d0.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).2
  have hpk := P_nd hnd hm3 k
  have hpk' := P_nd hnd hm3 k'
  obtain ⟨hAB, hAC, hBC, hA, hB, hC, -⟩ := (P d0 A B C k).facts hpk
  have hmk := P_mid (A := A) (B := B) (C := C) hm3 k
  have hmk' := P_mid (A := A) (B := B) (C := C) hm3 k'
  -- the two invariants
  have e1 : key1 A B (rot ((P d0 A B C k).arr f) j) = key1 A B (rot ((P d0 A B C k').arr f') j') := by
    rw [h]
  have e2 : key2 A B (rot ((P d0 A B C k).arr f) j) = key2 A B (rot ((P d0 A B C k').arr f') j') := by
    rw [h]
  rw [key1_rot (A := A) (B := B) ((P d0 A B C k).arr_nodup hpk f) ((P d0 A B C k).A_mem_arr f) hAB,
    key1_rot (A := A) (B := B) ((P d0 A B C k').arr_nodup hpk' f') ((P d0 A B C k').A_mem_arr f') hAB] at e1
  rw [key2_rot (A := A) (B := B) ((P d0 A B C k).arr_nodup hpk f) ((P d0 A B C k).B_mem_arr f) hAB,
    key2_rot (A := A) (B := B) ((P d0 A B C k').arr_nodup hpk' f') ((P d0 A B C k').B_mem_arr f') hAB]
    at e2
  have k1 := (P d0 A B C k).key1_arr hpk f hf
  have k1' := (P d0 A B C k').key1_arr hpk' f' hf'
  have k2 := (P d0 A B C k).key2_arr hpk f hf
  have k2' := (P d0 A B C k').key2_arr hpk' f' hf'
  change key1 A B _ = _ at k1 k1'
  change key2 A B _ = _ at k2 k2'
  rw [k1, k1', P_list hm3, P_list hm3, rot_add, rot_add] at e1
  rw [k2, k2', P_list hm3, P_list hm3, rot_add, rot_add] at e2
  have m1 := rot_app_inj hd hpos e1
  have m2 := rot_app_inj hd hpos e2
  -- the offsets as numbers
  have hcA : ∀ (q : Pd), q.mid.length + 3 = d0.length → ∀ g,
      q.cA g = if g ≤ 1 then d0.length - 1 else g - 2 := by
    intro q hq g; simp only [Pd.cA]; split <;> omega
  rw [hcA _ hmk, hcA _ hmk'] at m1
  simp only [Pd.cB] at m2
  have hvlt : ∀ g, g < 4 → (if g ≤ 1 then d0.length - 1 else g - 2) < d0.length := by
    intro g hg; split <;> omega
  have c1 := mod_eq_cases _ _ _ hpos m1 (by have := hvlt f hf; omega) (by have := hvlt f' hf'; omega)
  have c2 := mod_eq_cases _ _ _ hpos m2 (by split <;> omega) (by split <;> omega)
  by_cases hsp : (f = 0 ∧ f' = 2) ∨ (f = 2 ∧ f' = 0)
  · exfalso
    have hl := congrArg List.getLast? h
    have hd0 : ∀ x ∈ d0, x ≠ A ∧ x ≠ B := by
      intro x hx
      exact ⟨fun he => (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).1 (he ▸ hx),
        fun he => (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (he ▸ List.mem_cons_of_mem _ hx)⟩
    have he0 := P_e0 (A := A) (B := B) (C := C) hm3 k
    have he0' := P_e0 (A := A) (B := B) (C := C) hm3 k'
    have hel := P_el (A := A) (B := B) (C := C) hm3 k
    have hel' := P_el (A := A) (B := B) (C := C) hm3 k'
    have hgi : ∀ a b (ha : a < d0.length) (hb : b < d0.length), d0[a] = d0[b] → a = b :=
      fun a b ha hb hab => (List.Nodup.getElem_inj_iff hd).mp hab
    have hmm : (P d0 A B C k').mid.length = (P d0 A B C k).mid.length := by omega
    obtain ⟨l1, l2, l3, l4⟩ := lasts (P d0 A B C k)
    obtain ⟨l1', l2', l3', l4'⟩ := lasts (P d0 A B C k')
    rw [hmm] at l2' l4'
    have hj1 : d0.length + 1 = (P d0 A B C k).mid.length + 4 := by omega
    rcases hsp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases h02 (Or.inl rfl) with rfl | rfl <;> rcases h02' (Or.inr rfl) with rfl | rfl <;>
        simp only [Pd.arr, hj1] at hl
      · rw [l1, l3'] at hl; simp at hl; exact hAB hl.symm
      · rw [l1, l4'] at hl
        simp at hl; rw [hel'] at hl; exact (hd0 _ (List.getElem_mem _)).2 hl.symm
      · rw [l2, l3'] at hl
        simp at hl; rw [he0] at hl; exact (hd0 _ (List.getElem_mem _)).1 hl
      · rw [l2, l4'] at hl
        simp at hl; rw [he0, hel'] at hl
        have := hgi _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) hl
        have c3 := mod_eq_cases _ _ _ hpos this (by omega) (by omega)
        simp at c1
        rcases c1 with c | c | c | c | c <;> rcases c3 with d | d | d | d | d <;> omega
    · rcases h02 (Or.inr rfl) with rfl | rfl <;> rcases h02' (Or.inl rfl) with rfl | rfl <;>
        simp only [Pd.arr, hj1] at hl
      · rw [l3, l1'] at hl; simp at hl; exact hAB hl
      · rw [l3, l2'] at hl
        simp at hl; rw [he0'] at hl; exact (hd0 _ (List.getElem_mem _)).1 hl.symm
      · rw [l4, l1'] at hl
        simp at hl; rw [hel] at hl; exact (hd0 _ (List.getElem_mem _)).2 hl
      · rw [l4, l2'] at hl
        simp at hl; rw [hel, he0'] at hl
        have := hgi _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) hl
        have c3 := mod_eq_cases _ _ _ hpos this (by omega) (by omega)
        simp at c1
        rcases c1 with c | c | c | c | c <;> rcases c3 with d | d | d | d | d <;> omega
  · have hkf : k = k' ∧ f = f' := by
      interval_cases f <;> interval_cases f' <;> simp at hsp c1 c2 ⊢ <;>
        (rcases c1 with c | c | c | c | c <;> rcases c2 with d | d | d | d | d <;> omega)
    obtain ⟨rfl, rfl⟩ := hkf
    refine ⟨rfl, rfl, ?_⟩
    have hlen := (P d0 A B C k).arr_length f
    exact rot_index_eq_of_nodup ((P d0 A B C k).arr_nodup hpk f) (by omega) (by omega) h

theorem walk_eq_range (hm : 3 ≤ d0.length) :
    walk d0 A B C = (List.range d0.length).flatMap fun k =>
      (List.range (d0.length + 12)).map (P d0 A B C k).rowAt := by
  unfold walk
  congr 1; funext k
  rw [Pd.period_eq_range]
  congr 2
  have := P_mid (A := A) (B := B) (C := C) hm k
  simp only [P] at this
  omega

theorem walk_canon_nodup (hnd : (C :: B :: A :: d0).Nodup) (hm5 : 5 ≤ d0.length)
    (hodd : d0.length % 2 = 1) :
    ((walk d0 A B C).map (fun r => canon C r.base)).Nodup := by
  have hm3 : 3 ≤ d0.length := by omega
  rw [walk_eq_range hm3, List.map_flatMap]
  have key : ∀ k i, k < d0.length → i < d0.length + 12 →
      canon C ((P d0 A B C k).rowAt i).base =
        rot ((P d0 A B C k).arr (Pd.famOf d0.length i)) (Pd.jjOf d0.length i) ++ [C] := by
    intro k i hk hi
    have := (P d0 A B C k).canon_rowAt (P_nd hnd hm3 k) i (by have := P_mid (A := A) (B := B) (C := C) hm3 k; omega)
    rwa [P_mid hm3 k] at this
  have inj : ∀ k k' i i', k < d0.length → k' < d0.length → i < d0.length + 12 → i' < d0.length + 12 →
      canon C ((P d0 A B C k).rowAt i).base = canon C ((P d0 A B C k').rowAt i').base → k = k' ∧ i = i' := by
    intro k k' i i' hk hk' hi hi' h
    rw [key k i hk hi, key k' i' hk' hi'] at h
    obtain ⟨h1, h2, h3⟩ := Xinj hnd hm5 hodd hk hk' (Pd.famOf_lt _ _) (Pd.famOf_lt _ _) (Pd.jjOf_lt _ _ hi hm5)
      (Pd.jjOf_lt _ _ hi' hm5) (Pd.jjOf_02 _ _) (Pd.jjOf_02 _ _) (List.append_cancel_right h)
    exact ⟨h1, Pd.famOf_jjOf_inj _ _ _ hm5 hi hi' h2 h3⟩
  refine List.nodup_flatMap.mpr ⟨fun k hk => ?_, ?_⟩
  · rw [List.map_map]
    refine List.Nodup.map_on (fun i hi i' hi' h => ?_) List.nodup_range
    exact (inj k k i i' (List.mem_range.mp hk) (List.mem_range.mp hk) (List.mem_range.mp hi)
      (List.mem_range.mp hi') h).2
  · refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := d0.length))
    intro k k' hk hk' hne t ht ht'
    simp only [List.map_map, List.mem_map, List.mem_range, Function.comp] at ht ht'
    obtain ⟨i, hi, rfl⟩ := ht
    obtain ⟨i', hi', h⟩ := ht'
    exact hne (inj k k' i i' (List.mem_range.mp hk) (List.mem_range.mp hk') hi hi' h.symm).1

theorem walk_canon_mem (hnd : (C :: B :: A :: d0).Nodup) (hm5 : 5 ≤ d0.length)
    (r : Row Nat) (hr : r ∈ walk d0 A B C) : canon C r.base ∈ above3T A B C d0 := by
  have hm3 : 3 ≤ d0.length := by omega
  rw [walk_eq_range hm3] at hr
  obtain ⟨k, hk, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  have hk := List.mem_range.mp hk
  have hi := List.mem_range.mp hi
  have hmk := P_mid (A := A) (B := B) (C := C) hm3 k
  have hc := (P d0 A B C k).canon_rowAt (P_nd hnd hm3 k) i (by omega)
  change canon C _ = _ at hc
  rw [hc]
  generalize hf0 : Pd.famOf ((P d0 A B C k).mid.length + 3) i = f
  generalize hj0 : Pd.jjOf ((P d0 A B C k).mid.length + 3) i = j
  have hf : f < 4 := hf0 ▸ Pd.famOf_lt _ _
  have hj : j < d0.length + 2 := by
    have := Pd.jjOf_lt ((P d0 A B C k).mid.length + 3) i (by omega) (by omega); omega
  rw [(P d0 A B C k).arr_yform f hf, P_list hm3, rot_add]
  refine mem_above3T.mpr ⟨(2 * k + (P d0 A B C k).cA f) % d0.length, Nat.mod_lt _ (by omega),
    Pd.iota f, ?_, ((P d0 A B C k).kappa f + j) % (d0.length + 2), Nat.mod_lt _ (by omega), ?_⟩
  · unfold Pd.iota; split_ifs <;> omega
  · unfold ent
    have hY : (rot (rot d0 (2 * k + (P d0 A B C k).cA f) ++ [A]) (Pd.iota f) ++ [B]).length =
        d0.length + 2 := by simp
    rw [rot_mod, rot_add]
    conv_rhs => rw [← hY, rot_mod]
    rfl

theorem walk_dloops_length (hnd : (C :: B :: A :: d0).Nodup) (h9 : 9 ∉ C :: B :: A :: d0)
    (hm5 : 5 ≤ d0.length) (hodd : d0.length % 2 = 1) :
    ((above3T A B C d0).filter (fun t => !coveredB (walk d0 A B C) t)).length =
      d0.length * ((d0.length + 1) * (d0.length + 2)) - d0.length * (d0.length + 12) := by
  have hm3 : 3 ≤ d0.length := by omega
  have hb := walk_basedOn d0 A B C hm3 hnd h9
  rw [count_uncovered (above3T A B C d0) (walk d0 A B C) C (above3T_nodup hnd)
    (fun t ht => canon_ent ht) (fun r hr => (hb r hr).1.1)
    (fun r hr => ⟨walk_canon_mem hnd hm5 r hr,
      canon_cyc_self ((hb r hr).2.1.mem_iff.mpr List.mem_cons_self)⟩)
    (walk_canon_nodup hnd hm5 hodd), above3T_length, walk_length d0 A B C hm3]

end

end SuperpermutationUpperBound43586371.Uniform
