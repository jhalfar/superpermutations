import SuperpermutationUpperBound305989.Levels
import SuperpermutationUpperBound.Foundation.RowRelabeling

/-!
# Relabelling the letters

Rows, transport, completion, connector cycles and the cycle-cover condition commute with a
relabelling `f` of the letters.  `Foundation/RowRelabeling.lean` has the basic facts
(`Row.map`, `rot_map`, `closedTrail_map`); here are the rest:

* `Transport.rows_map`, `transportWalk_map`: transport with the new letter `f z`;
* `completionWalk_map`, `completionExit_map`, `orbitPorts_map`: completion with `f final`;
* `basedOn_map`, `signedExcess_map`, `circleFamilyValid_map` (the first and the last need `f`
  injective);
* `safeComp_map`: a cycle cover of a trail gives a cycle cover of the relabelled trail by the
  relabelled cycles.

`relab d0 d` is the relabelling that sends the `i`-th letter of `d0` to the `i`-th letter of `d`
and fixes every other letter; for `d` a permutation of a duplicate-free `d0` it is injective
(`relab_injective`) and sends `d0` to `d` (`map_relab_self`).
-/

namespace SuperpermutationUpperBound305989

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

variable {α β : Type}

section maps

variable (f : α → β)

theorem insertLetter_map (x : List α) (z : α) (j : Nat) :
    insertLetter (x.map f) (f z) j = (insertLetter x z j).map f := by
  simp [insertLetter, List.map_take, List.map_drop]

theorem fullAt_map (r : Row α) (z : α) (j : Nat) :
    fullAt (r.map f) (f z) j = (fullAt r z j).map f := by
  simp [fullAt, Row.map, insertLetter_map]

theorem shortAt_map (r : Row α) (z : α) (j : Nat) :
    shortAt (r.map f) (f z) j = (shortAt r z j).map f := by
  simp [shortAt, Row.map, insertLetter_map]

theorem shortLast_map (r : Row α) (z : α) :
    shortLast (r.map f) (f z) = (shortLast r z).map f := by
  simp [shortLast, Row.map, rot_map]

theorem fullPathAt_map (r : Row α) (z : α) (j : Nat) :
    fullPathAt (r.map f) (f z) j = (fullPathAt r z j).map (Row.map f) := by
  unfold fullPathAt
  split <;> simp [fullAt_map]

theorem shortPathAt_map (r : Row α) (z : α) (j : Nat) :
    Transport.shortPathAt (r.map f) (f z) j = (Transport.shortPathAt r z j).map (Row.map f) := by
  unfold Transport.shortPathAt
  by_cases hj : j < r.base.length - 2 <;> simp [hj, shortAt_map, shortLast_map]

theorem portPath_map (r : Row α) (z : α) (j : Nat) :
    Transport.portPath (r.map f) (f z) j = (Transport.portPath r z j).map (Row.map f) := by
  unfold Transport.portPath
  simp only [Row.map_visible, Row.map_base_length]
  split
  · exact fullPathAt_map f r z j
  · exact shortPathAt_map f r z j

@[simp] theorem portTarget_map (r : Row α) (j : Nat) : portTarget (r.map f) j = portTarget r j := by
  simp [portTarget]

theorem transportWalk_map (rs : List (Row α)) (z : α) (p : Nat) :
    transportWalk (rs.map (Row.map f)) (f z) p = (transportWalk rs z p).map (Row.map f) := by
  induction rs generalizing p with
  | nil => rfl
  | cons r rs ih => simp [transportWalk, portPath_map, ih]

theorem fullBases_map (x : List α) (z : α) :
    fullBases (x.map f) (f z) = (fullBases x z).map (List.map f) := by
  simp [fullBases, insertLetter_map]

theorem shortBases_map (x : List α) (z : α) :
    shortBases (x.map f) (f z) = (shortBases x z).map (List.map f) := by
  simp [shortBases, insertLetter_map, rot_map]

theorem rows_map (r : Row α) (z : α) :
    Transport.rows (r.map f) (f z) = (Transport.rows r z).map (Row.map f) := by
  unfold Transport.rows
  simp only [Row.map_visible, Row.map_base_length]
  split
  · simp [fullRows, fullBases_map, Row.map]
  · simp [shortRows, shortBases_map, Row.map]

theorem liftRow_map (r : Row α) (z : α) (j : Nat) :
    Completion.liftRow (r.map f) (f z) j = (Completion.liftRow r z j).map f := by
  simp [Completion.liftRow, Row.map, insertLetter_map]

theorem repairRow_map (r : Row α) (z : α) (j : Nat) :
    Completion.repairRow (r.map f) (f z) j = (Completion.repairRow r z j).map f := by
  simp [Completion.repairRow, Row.map, rot_map]

theorem completion_shortPathAt_map (r : Row α) (z : α) (j : Nat) :
    Completion.shortPathAt (r.map f) (f z) j = (Completion.shortPathAt r z j).map (Row.map f) := by
  unfold Completion.shortPathAt
  by_cases hj : j < r.base.length - 2 <;> simp [hj, liftRow_map, repairRow_map]

theorem completion_portPath_map (r : Row α) (z : α) (j : Nat) :
    Completion.portPath (r.map f) (f z) j = (Completion.portPath r z j).map (Row.map f) := by
  unfold Completion.portPath
  simp only [Row.map_visible, Row.map_base_length]
  split
  · exact fullPathAt_map f r z j
  · exact completion_shortPathAt_map f r z j

theorem completionWalk_map (rs : List (Row α)) (z : α) (q : Nat) :
    completionWalk (rs.map (Row.map f)) (f z) q = (completionWalk rs z q).map (Row.map f) := by
  induction rs generalizing q with
  | nil => rfl
  | cons r rs ih => simp [completionWalk, completion_portPath_map, ih]

@[simp] theorem completionExit_map (rs : List (Row α)) (q : Nat) :
    completionExit (rs.map (Row.map f)) q = completionExit rs q := by
  induction rs generalizing q with
  | nil => rfl
  | cons r rs ih => simp [completionExit, ih]

theorem rep_map (m : Nat) (rs : List (Row α)) :
    rep m (rs.map (Row.map f)) = (rep m rs).map (Row.map f) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [rep, ih]

@[simp] theorem orbitPorts_map (rs : List (Row α)) (m p : Nat) :
    orbitPorts (rs.map (Row.map f)) m p = orbitPorts rs m p := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih => simp [orbitPorts, ih]

theorem fullChart_map (x : List α) (z s : α) :
    Partition.fullChart (x.map f) (f z) (f s) = (Partition.fullChart x z s).map (Row.map f) := by
  simp [Partition.fullChart, Partition.fullChartAt, Row.map, rot_map]

theorem cyclicEq_map {x y : List α} (h : CyclicEq x y) : CyclicEq (x.map f) (y.map f) := by
  obtain ⟨j, hj⟩ := h
  refine ⟨⟨j.val, by simp⟩, ?_⟩
  change rot (x.map f) j.val = y.map f
  rw [rot_map]
  exact congrArg (List.map f) hj

theorem headVertex_map {rs : List (Row α)} {v : List α} (h : HeadVertex rs v) :
    HeadVertex (rs.map (Row.map f)) (v.map f) := by
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨r.map f, List.mem_map.mpr ⟨r, hr, rfl⟩, Row.map_head f r⟩

theorem safeIncidence_map {h : Nat} {rs : List (Row α)} {final : α} {j : Fin h} {c : List α}
    (hs : SafeIncidence rs final j c) :
    SafeIncidence (rs.map (Row.map f)) (f final) j (c.map f) := by
  rcases hs with ⟨hz, v, hv, hcv⟩ | ⟨x, active, sat, hcx, rfl⟩
  · refine Or.inl ⟨List.mem_map.mpr ⟨final, hz, rfl⟩, v.map f, ?_, cyclicEq_map f hcv⟩
    rw [completionWalk_map]
    exact headVertex_map f hv
  · exact Or.inr ⟨x.map f, f active, f sat, cyclicEq_map f hcx, (fullChart_map f x active sat).symm⟩

@[simp] theorem signedExcess_map (rs : List (Row α)) :
    signedExcess (rs.map (Row.map f)) = signedExcess rs := by
  simp [signedExcess, List.map_map, Function.comp_def]

end maps

theorem safeComp_map (f : Nat → Nat) {rs : List (Row Nat)} {final h : Nat}
    {circles : List (List Nat)} (hs : SafeComp rs final h circles) :
    SafeComp (rs.map (Row.map f)) (f final) h (circles.map (List.map f)) := by
  intro j
  obtain ⟨c, hc, hi⟩ := hs j
  exact ⟨c.map f, List.mem_map.mpr ⟨c, hc, rfl⟩, safeIncidence_map f hi⟩

theorem basedOn_map (f : α → β) (hf : ∀ a b, f a = f b → a = b) {A : List α} {s : α}
    {rs : List (Row α)} (hb : BasedOn A s rs) : BasedOn (A.map f) (f s) (rs.map (Row.map f)) := by
  intro r hr
  obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
  obtain ⟨hv, hp, hs, hk⟩ := hb r0 hr0
  refine ⟨Row.map_valid f hf hv, hp.map f, by simp [hs], ?_⟩
  simpa using hk

theorem circleFamilyValid_map (f : α → β) (hf : ∀ a b, f a = f b → a = b) {h : Nat}
    {circles : List (List α)} (hc : CircleFamilyValid h circles) :
    CircleFamilyValid h (circles.map (List.map f)) := by
  intro c hc'
  obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc'
  obtain ⟨hl, hn⟩ := hc c0 hc0
  exact ⟨by simp [hl], hn.map (fun a b h => hf a b h)⟩

theorem basedOn_congr_alphabet {A A' : List Nat} {s : Nat} {rs : List (Row Nat)}
    (hb : BasedOn A s rs) (hA : A.Perm A') : BasedOn A' s rs := by
  intro r hr
  obtain ⟨hv, hp, hs, hk⟩ := hb r hr
  exact ⟨hv, hp.trans hA, hs, hk⟩

/-! ### The relabelling `d0[i] ↦ d[i]` -/

/-- The letter `d0[i]` goes to `d[i]`; letters not in `d0` stay. -/
def relab (d0 d : List Nat) (a : Nat) : Nat := if a ∈ d0 then d.getD (d0.idxOf a) a else a

theorem relab_of_not_mem {d0 d : List Nat} {a : Nat} (ha : a ∉ d0) : relab d0 d a = a := by
  simp [relab, ha]

theorem relab_of_mem {d0 d : List Nat} {a : Nat} (ha : a ∈ d0) (hl : d.length = d0.length) :
    relab d0 d a = d[d0.idxOf a]'(hl ▸ List.idxOf_lt_length_of_mem ha) := by
  simp only [relab, if_pos ha, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem]
  rfl

theorem idxOf_getElem_of_nodup {l : List Nat} (hl : l.Nodup) (i : Nat) (hi : i < l.length) :
    l.idxOf l[i] = i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    cases i with
    | zero => simp
    | succ k =>
      have hk : k < l.length := by simpa using hi
      have hne : a ≠ l[k] := fun he => ha (he ▸ List.getElem_mem hk)
      simp only [List.getElem_cons_succ, List.idxOf_cons, cond_eq_ite, beq_iff_eq, if_neg hne,
        ih hl' k hk]

theorem getElem_idxOf_of_mem {l : List Nat} {a : Nat} (ha : a ∈ l) :
    l[l.idxOf a]'(List.idxOf_lt_length_of_mem ha) = a := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    by_cases hb : b = a
    · subst hb
      simp
    · have ha' : a ∈ l := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hb
        · exact h
      have he : (b :: l).idxOf a = l.idxOf a + 1 := by
        simp [hb]
      simp only [he, List.getElem_cons_succ]
      exact ih ha'

theorem relab_mem {d0 d : List Nat} (hp : d.Perm d0) {a : Nat} (ha : a ∈ d0) :
    relab d0 d a ∈ d0 := by
  rw [relab_of_mem ha hp.length_eq]
  exact hp.mem_iff.mp (List.getElem_mem _)

theorem relab_relab {d0 d : List Nat} (h0 : d0.Nodup) (hp : d.Perm d0) (a : Nat) :
    relab d d0 (relab d0 d a) = a := by
  have hd : d.Nodup := hp.nodup_iff.mpr h0
  by_cases ha : a ∈ d0
  · have hi := List.idxOf_lt_length_of_mem ha
    have hi' : d0.idxOf a < d.length := hp.length_eq ▸ hi
    rw [relab_of_mem ha hp.length_eq]
    have hm : d[d0.idxOf a] ∈ d := List.getElem_mem _
    rw [relab_of_mem hm hp.symm.length_eq]
    simp only [idxOf_getElem_of_nodup hd _ hi']
    exact getElem_idxOf_of_mem ha
  · have ha' : a ∉ d := fun hm => ha (hp.mem_iff.mp hm)
    rw [relab_of_not_mem ha, relab_of_not_mem ha']

theorem relab_injective {d0 d : List Nat} (h0 : d0.Nodup) (hp : d.Perm d0) :
    ∀ a b, relab d0 d a = relab d0 d b → a = b := by
  intro a b he
  rw [← relab_relab h0 hp a, ← relab_relab h0 hp b, he]

theorem map_relab_self {d0 d : List Nat} (h0 : d0.Nodup) (hp : d.Perm d0) :
    d0.map (relab d0 d) = d := by
  apply List.ext_getElem (by simp [hp.length_eq])
  intro i h1 h2
  have hi : i < d0.length := by simpa using h1
  rw [List.getElem_map, relab_of_mem (List.getElem_mem hi) hp.length_eq]
  simp only [idxOf_getElem_of_nodup h0 i hi]

/-- An alphabet that contains `d0` is sent to a permutation of itself. -/
theorem map_relab_perm {d0 d A : List Nat} (h0 : d0.Nodup) (hp : d.Perm d0) (hA : A.Nodup)
    (hsub : ∀ a ∈ d0, a ∈ A) : (A.map (relab d0 d)).Perm A := by
  refine perm_of_nodup_subset_length (hA.map (relab_injective h0 hp)) ?_ (by simp)
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  by_cases h : a ∈ d0
  · exact hsub _ (relab_mem hp h)
  · rw [relab_of_not_mem h]
    exact ha

end SuperpermutationUpperBound305989
