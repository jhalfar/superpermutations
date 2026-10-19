import SuperpermutationUpperBound43586371.Stage

/-!
# A stage with no rows (no seed)

`the no-seed construction` (checked by its referee, my referee notes) starts the nested construction
without any selection: on the letters `z :: a :: rest` there are no rows at all, and every loop on
`a :: rest` is pending, one ordering per cyclic order (`a` first, then any arrangement of `rest`).
`Stage.noSeed` is that stage; its `(rest.length)!` pending loops are exactly the cyclic orders, so the
row count of the closed level is again `h!`.
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

theorem perm_of_mem_permsOf : ∀ (n : Nat) (rem q : List Nat), rem.length = n →
    q ∈ permsOf n rem → q.Perm rem := by
  intro n
  induction n with
  | zero =>
    intro rem q hlen hq
    have hrem : rem = [] := List.length_eq_zero_iff.mp hlen
    subst hrem
    simp [permsOf] at hq
    subst hq
    exact List.Perm.refl _
  | succ n ih =>
    intro rem q hlen hq
    obtain ⟨b, hb, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
    have hlen' : (rem.erase b).length = n := by
      rw [List.length_erase_of_mem hb, hlen]
      rfl
    exact ((ih _ t hlen' ht).cons b).trans (List.perm_cons_erase hb).symm

theorem length_permsOf : ∀ (n : Nat) (rem : List Nat), rem.length = n →
    (permsOf n rem).length = n.factorial := by
  intro n
  induction n with
  | zero => intro rem _; rfl
  | succ n ih =>
    intro rem hlen
    have h := length_flatMap_const rem (fun b => (permsOf n (rem.erase b)).map fun t => b :: t)
      n.factorial (fun b hb => by
        rw [List.length_map]
        apply ih
        rw [List.length_erase_of_mem hb, hlen]
        rfl)
    change (rem.flatMap fun b => (permsOf n (rem.erase b)).map fun t => b :: t).length = _
    rw [h, hlen, Nat.factorial_succ]

/-- One ordering per cyclic order of `a :: rest`: `a` first. -/
def cyclicReps (a : Nat) (rest : List Nat) : List (List Nat) :=
  (permsOf rest.length rest).map fun t => a :: t

theorem exists_cyclicRep {a : Nat} {rest x : List Nat} (hx : x.Perm (a :: rest)) :
    ∃ b ∈ cyclicReps a rest, CyclicEq x b := by
  have ha : a ∈ x := hx.mem_iff.mpr List.mem_cons_self
  obtain ⟨u, v, rfl⟩ := List.append_of_mem ha
  have hc : CyclicEq (u ++ a :: v) (a :: (v ++ u)) := by
    have h := CyclicEq.of_rot (x := u ++ a :: v) (by simp) u.length
    simpa only [rot_append_length, List.cons_append] using h
  have hp : (v ++ u).Perm rest := (List.perm_cons a).mp (hc.perm.symm.trans hx)
  exact ⟨a :: (v ++ u), List.mem_map.mpr ⟨v ++ u, mem_permsOf _ _ _ rfl hp, rfl⟩, hc⟩

/-- The stage with no rows: every loop on `a :: rest` pending. -/
theorem Stage.noSeed {a z : Nat} {rest : List Nat} (hnd : (z :: a :: rest).Nodup)
    (h9 : 9 ∉ z :: a :: rest) (h10 : 10 ∉ z :: a :: rest) (h1 : 1 ≤ rest.length) :
    Stage (a :: rest) z [] [] (cyclicReps a rest) 0 0 0 rest.length.factorial where
  two := by simp only [List.length_cons]; omega
  nodup := hnd
  nine := h9
  ten := h10
  level := ⟨fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h⟩
  valid := fun _ h => by simp at h
  support := fun _ h => by simp at h
  safe := fun _ h => by simp at h
  pend := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
    exact (perm_of_mem_permsOf _ _ _ rfl ht).cons a
  cover := by
    intro y hy
    right
    have hA := (List.nodup_cons.mp hnd)
    obtain ⟨x, hx, hb⟩ := peel hA.2 (List.cons_ne_nil _ _) hA.1 hy
    obtain ⟨b, hbm, hxb⟩ := exists_cyclicRep hx
    exact ⟨b, hbm, (InInsertionBlock.congr_base hxb).mp hb⟩
  rows := rfl
  charge := rfl
  ncirc := rfl
  npend := by
    unfold cyclicReps
    rw [List.length_map, length_permsOf _ _ rfl]

end SuperpermutationUpperBound43586371
