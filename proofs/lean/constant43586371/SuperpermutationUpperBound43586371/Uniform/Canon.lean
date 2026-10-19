import SuperpermutationUpperBound43586371.Uniform.Walk
import SuperpermutationUpperBound43586371.BlockG

/-!
# Normal forms of cyclic classes, the loops `above3T`, and a counting lemma

`canon c x` is the rotation of `x` that ends with the letter `c`; for a list without repeated letters it is
the same for all rotations (`canon_cyc`).  `above3T a b c d` (constant43586371, `BlockG.lean`) lists the
`m (m+1) (m+2)` loops three levels above `d`; they are distinct, each ends with `c`, and each is a permutation
of `c :: b :: a :: d`.  `count_covered`: if the rows of a walk have distinct normal forms, all in `above3T`,
exactly `|walk|` of the loops of `above3T` are rotations of row bases.
-/

set_option linter.unusedSimpArgs false

namespace SuperpermutationUpperBound43586371.Uniform

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

/-- The rotation of `x` that ends with `c`. -/
def canon (c : Nat) (x : List Nat) : List Nat := rot x (x.idxOf c + 1)

theorem canon_spec {c : Nat} {x : List Nat} (hc : c ∈ x) :
    ∃ P, canon c x = P ++ [c] ∧ CyclicEq x (canon c x) := by
  have hi : x.idxOf c < x.length := List.idxOf_lt_length_of_mem hc
  have hx : x ≠ [] := List.ne_nil_of_mem hc
  refine ⟨x.drop (x.idxOf c + 1) ++ x.take (x.idxOf c), ?_, CyclicEq.of_rot hx _⟩
  unfold canon
  rw [rot_eq_drop_append_take_of_le _ _ (by omega), ← List.take_append_getElem hi,
    List.getElem_idxOf hi]
  simp

theorem canon_eq {c : Nat} {x P : List Nat} (hx : x.Nodup) (h : CyclicEq x (P ++ [c])) :
    canon c x = P ++ [c] := by
  have hc : c ∈ x := h.perm.mem_iff.mpr (by simp)
  obtain ⟨Q, hQ, hcy⟩ := canon_spec hc
  rw [hQ] at hcy ⊢
  have h2 : CyclicEq (Q ++ [c]) (P ++ [c]) := hcy.symm.trans h
  have hnd : (Q ++ [c]).Nodup := hcy.nodup_iff.mp hx
  have hcQ : c ∉ Q := by
    intro hm
    have := List.nodup_append.mp hnd
    exact this.2.2 c hm c (by simp) rfl
  rw [append_satellite_eq_of_cyclicEq hcQ h2]

theorem canon_cyc {c : Nat} {x y : List Nat} (hx : x.Nodup) (hc : c ∈ x) (h : CyclicEq x y) :
    canon c y = canon c x := by
  obtain ⟨Q, hQ, hcy⟩ := canon_spec hc
  rw [hQ] at hcy ⊢
  exact canon_eq (h.nodup_iff.mp hx) (h.symm.trans hcy)

theorem canon_rot {c : Nat} {x : List Nat} (hx : x.Nodup) (hc : c ∈ x) (j : Nat) :
    canon c (rot x j) = canon c x :=
  canon_cyc hx hc (CyclicEq.of_rot (List.ne_nil_of_mem hc) j)

/-- A rotation of `P ++ [c] ++ Q` that ends with `c`. -/
theorem cyc_mid (P Q : List Nat) (c : Nat) : CyclicEq (P ++ [c] ++ Q) (Q ++ P ++ [c]) := by
  have h := CyclicEq.of_rot (x := P ++ [c] ++ Q) (by simp) (P ++ [c]).length
  rw [rot_append_length] at h
  simpa using h

/-- Insertion of a fresh last letter, then a rotation, determines the rotation and the word. -/
theorem ins_uniq {P P' : List Nat} {b k k' : Nat} (hnd : (P ++ [b]).Nodup) (hb' : b ∉ P')
    (hlen : P.length = P'.length) (hk : k < P.length + 1) (hk' : k' < P.length + 1)
    (h : rot (P ++ [b]) k = rot (P' ++ [b]) k') : P = P' ∧ k = k' := by
  have hc : CyclicEq (P' ++ [b]) (P ++ [b]) :=
    ((CyclicEq.of_rot (by simp) k').trans (h ▸ (CyclicEq.of_rot (by simp) k).symm))
  have hPP : P' = P := append_satellite_eq_of_cyclicEq hb' hc
  subst hPP
  exact ⟨rfl, rot_index_eq_of_nodup hnd (by simpa using hk) (by simpa using hk') h⟩

theorem rot_mod_inj {d : List Nat} (hd : d.Nodup) (hpos : 0 < d.length) {i i' : Nat}
    (h : rot d i = rot d i') : i % d.length = i' % d.length := by
  rw [← rot_mod d i, ← rot_mod d i'] at h
  exact rot_index_eq_of_nodup hd (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) h

/-! ### The loops three levels above `d` -/

def ent (a b c : Nat) (d : List Nat) (i j k : Nat) : List Nat :=
  rot (rot (rot d i ++ [a]) j ++ [b]) k ++ [c]

theorem above3T_eq (a b c : Nat) (d : List Nat) :
    above3T a b c d = (List.range d.length).flatMap fun i =>
      (List.range (d.length + 1)).flatMap fun j => (List.range (d.length + 2)).map fun k => ent a b c d i j k :=
  rfl

theorem mem_above3T {a b c : Nat} {d : List Nat} {t : List Nat} :
    t ∈ above3T a b c d ↔ ∃ i < d.length, ∃ j < d.length + 1, ∃ k < d.length + 2, t = ent a b c d i j k := by
  rw [above3T_eq]
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, j, hj, k, hk, rfl⟩; exact ⟨i, hi, j, hj, k, hk, rfl⟩
  · rintro ⟨i, hi, j, hj, k, hk, rfl⟩; exact ⟨i, hi, j, hj, k, hk, rfl⟩

theorem ent_perm (a b c : Nat) (d : List Nat) (i j k : Nat) :
    (ent a b c d i j k).Perm (c :: b :: a :: d) := by
  unfold ent
  refine List.perm_append_comm.trans (List.Perm.cons c ?_)
  refine (rot_perm _ k).trans (List.perm_append_comm.trans (List.Perm.cons b ?_))
  refine (rot_perm _ j).trans (List.perm_append_comm.trans (List.Perm.cons a ?_))
  exact rot_perm d i

theorem above3T_perm {a b c : Nat} {d t : List Nat} (ht : t ∈ above3T a b c d) :
    t.Perm (c :: b :: a :: d) := by
  obtain ⟨i, _, j, _, k, _, rfl⟩ := mem_above3T.mp ht
  exact ent_perm a b c d i j k

theorem above3T_length (a b c : Nat) (d : List Nat) :
    (above3T a b c d).length = d.length * ((d.length + 1) * (d.length + 2)) := by
  rw [above3T_eq, length_flatMap_const _ _ ((d.length + 1) * (d.length + 2)) (fun i _ => by
    rw [length_flatMap_const _ _ (d.length + 2) (fun j _ => by simp)]; simp)]
  simp

theorem ent_inj {a b c : Nat} {d : List Nat} (hnd : (c :: b :: a :: d).Nodup) {i j k i' j' k' : Nat}
    (hi : i < d.length) (hi' : i' < d.length) (hj : j < d.length + 1) (hj' : j' < d.length + 1)
    (hk : k < d.length + 2) (hk' : k' < d.length + 2) (h : ent a b c d i j k = ent a b c d i' j' k') :
    i = i' ∧ j = j' ∧ k = k' := by
  have hc := List.nodup_cons.mp hnd
  have hb := List.nodup_cons.mp hc.2
  have ha := List.nodup_cons.mp hb.2
  unfold ent at h
  have h1 := List.append_cancel_right h
  have hY : ∀ i j, (rot (rot d i ++ [a]) j ++ [b]).Nodup := by
    intro i j
    have : (rot (rot d i ++ [a]) j ++ [b]).Perm (b :: a :: d) :=
      List.perm_append_comm.trans (List.Perm.cons b ((rot_perm _ j).trans
        (List.perm_append_comm.trans (List.Perm.cons a (rot_perm d i)))))
    exact this.nodup_iff.mpr hc.2
  have hbY : b ∉ rot (rot d i' ++ [a]) j' := by
    intro hm
    have hm' := (rot_perm _ j').mem_iff.mp hm
    rcases List.mem_append.mp hm' with hm' | hm'
    · exact hb.1 (List.mem_cons_of_mem _ ((rot_perm d i').mem_iff.mp hm'))
    · simp at hm'; exact hb.1 (by simp [hm'])
  obtain ⟨h2, hkk⟩ := ins_uniq (hY i j) hbY (by simp) (by simp; omega) (by simp; omega) h1
  have haZ : a ∉ rot d i' := fun hm => ha.1 ((rot_perm d i').mem_iff.mp hm)
  have hZ : (rot d i ++ [a]).Nodup := by
    have : (rot d i ++ [a]).Perm (a :: d) :=
      List.perm_append_comm.trans (List.Perm.cons a (rot_perm d i))
    exact this.nodup_iff.mpr hb.2
  obtain ⟨h3, hjj⟩ := ins_uniq hZ haZ (by simp) (by simpa using hj) (by simpa using hj') h2
  exact ⟨rot_index_eq_of_nodup ha.2 hi hi' h3, hjj, hkk⟩

theorem above3T_nodup {a b c : Nat} {d : List Nat} (hnd : (c :: b :: a :: d).Nodup) :
    (above3T a b c d).Nodup := by
  rw [above3T_eq]
  refine List.nodup_flatMap.mpr ⟨fun i hi => List.nodup_flatMap.mpr ⟨fun j hj => ?_, ?_⟩, ?_⟩
  · refine List.Nodup.map_on (fun k hk k' hk' h => ?_) List.nodup_range
    simp only [List.mem_range] at hi hj hk hk'
    exact (ent_inj hnd hi hi hj hj hk hk' h).2.2
  · refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := d.length + 1))
    intro j j' hj hj' hne t ht ht'
    simp only [List.mem_map, List.mem_range] at ht ht' hi hj hj'
    obtain ⟨k, hk, rfl⟩ := ht
    obtain ⟨k', hk', h⟩ := ht'
    exact hne (ent_inj hnd hi hi hj' hj hk' hk h).2.1.symm
  · refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := d.length))
    intro i i' hi hi' hne t ht ht'
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at ht ht' hi hi'
    obtain ⟨j, hj, k, hk, rfl⟩ := ht
    obtain ⟨j', hj', k', hk', h⟩ := ht'
    exact hne (ent_inj hnd hi' hi hj' hj hk' hk h).1.symm

theorem canon_ent {a b c : Nat} {d : List Nat} {t : List Nat} (ht : t ∈ above3T a b c d) :
    ∃ P, t = P ++ [c] := by
  obtain ⟨i, _, j, _, k, _, rfl⟩ := mem_above3T.mp ht
  exact ⟨_, rfl⟩

/-! ### Counting the loops covered by a walk -/

/-- The loops of `S` that are rotations of row bases. -/
def coveredB (W : List (Row Nat)) (t : List Nat) : Bool := decide (∃ r ∈ W, CyclicEq r.base t)

theorem count_covered (S : List (List Nat)) (W : List (Row Nat)) (c : Nat) (hS : S.Nodup)
    (hSc : ∀ t ∈ S, ∃ P, t = P ++ [c]) (hWnd : ∀ r ∈ W, r.base.Nodup)
    (hWS : ∀ r ∈ W, canon c r.base ∈ S ∧ CyclicEq r.base (canon c r.base))
    (hWn : (W.map (fun r => canon c r.base)).Nodup) :
    (S.filter (coveredB W)).length = W.length := by
  have hp : (S.filter (coveredB W)).Perm (W.map (fun r => canon c r.base)) := by
    refine (List.perm_ext_iff_of_nodup (hS.filter _) hWn).mpr ?_
    intro t
    simp only [List.mem_filter, coveredB, decide_eq_true_eq, List.mem_map]
    constructor
    · rintro ⟨htS, r, hr, hrt⟩
      obtain ⟨P, rfl⟩ := hSc t htS
      exact ⟨r, hr, canon_eq (hWnd r hr) hrt⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(hWS r hr).1, r, hr, (hWS r hr).2⟩
  rw [hp.length_eq, List.length_map]

theorem count_uncovered (S : List (List Nat)) (W : List (Row Nat)) (c : Nat) (hS : S.Nodup)
    (hSc : ∀ t ∈ S, ∃ P, t = P ++ [c]) (hWnd : ∀ r ∈ W, r.base.Nodup)
    (hWS : ∀ r ∈ W, canon c r.base ∈ S ∧ CyclicEq r.base (canon c r.base))
    (hWn : (W.map (fun r => canon c r.base)).Nodup) :
    (S.filter (fun t => !coveredB W t)).length = S.length - W.length := by
  have h := List.length_eq_length_filter_add (l := S) (coveredB W)
  rw [count_covered S W c hS hSc hWnd hWS hWn] at h
  omega

end SuperpermutationUpperBound43586371.Uniform
