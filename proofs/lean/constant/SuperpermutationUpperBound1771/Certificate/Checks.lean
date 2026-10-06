import SuperpermutationUpperBound1771.Thirteen

/-!
# The finite checks, as decidable statements

Each field of `Cert` and of `GroupFacts` that is not a plain count is derived here from a
statement the kernel can evaluate on the literal data:

* `coveredB`: a list of 2-loops (targets) and a list of pointers of the same length; each
  pointer names a row of a walk or a loop without a row whose base is the target up to
  rotation.
* `canonPart a`: the orderings `0 :: a :: t` of the eight ordinary letters; every 2-loop on 9
  symbols has exactly one such ordering.
* `GroupOK`: everything about one of the 48 groups.
* `BigOK`: the pointer certificate (`PortsCovered`) of one long walk on 11 symbols.
-/

namespace SuperpermutationUpperBound1771

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound.Certificates.CircleBase

/-! ### Pointers to rows and to loops without a row -/

/-- Pointer `(c, o)`: row `o` of walk `c` if there is a walk `c`, else loop `o` of `ds`. -/
def entryOK (chunks : List (List (Row Nat))) (ds : List (List Nat)) (t : List Nat)
    (c o : Nat) : Bool :=
  match chunks[c]? with
  | some rs =>
    match rs[o]? with
    | some r => decide (CyclicEq r.base t)
    | none => false
  | none =>
    match ds[o]? with
    | some d => decide (CyclicEq d t)
    | none => false

theorem entryOK_sound {chunks : List (List (Row Nat))} {ds : List (List Nat)} {t : List Nat}
    {c o : Nat} (h : entryOK chunks ds t c o = true) :
    (∃ r ∈ chunks.flatten, CyclicEq r.base t) ∨ (∃ d ∈ ds, CyclicEq d t) := by
  unfold entryOK at h
  split at h
  · rename_i rs hrs
    split at h
    · rename_i r hr
      exact Or.inl ⟨r, List.mem_flatten.mpr
        ⟨rs, List.mem_of_getElem? hrs, List.mem_of_getElem? hr⟩, of_decide_eq_true h⟩
    · exact absurd h (by simp)
  · split at h
    · rename_i d hd
      exact Or.inr ⟨d, List.mem_of_getElem? hd, of_decide_eq_true h⟩
    · exact absurd h (by simp)

def coveredB (chunks : List (List (Row Nat))) (ds : List (List Nat)) :
    List (List Nat) → List (Nat × Nat) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | t :: ts, p :: ps => entryOK chunks ds t p.1 p.2 && coveredB chunks ds ts ps

theorem coveredB_sound {chunks : List (List (Row Nat))} {ds : List (List Nat)} :
    ∀ (ts : List (List Nat)) (ps : List (Nat × Nat)), coveredB chunks ds ts ps = true →
      ∀ t ∈ ts, (∃ r ∈ chunks.flatten, CyclicEq r.base t) ∨ (∃ d ∈ ds, CyclicEq d t) := by
  intro ts
  induction ts with
  | nil => intro _ _ t ht; simp at ht
  | cons a ts ih =>
    intro ps h t ht
    cases ps with
    | nil => simp [coveredB] at h
    | cons p ps =>
      have h' : (entryOK chunks ds a p.1 p.2 && coveredB chunks ds ts ps) = true := h
      rw [Bool.and_eq_true] at h'
      rcases List.mem_cons.mp ht with rfl | ht
      · exact entryOK_sound h'.1
      · exact ih ps h'.2 t ht

/-! ### One ordering for every 2-loop on 9 symbols -/

/-- All arrangements of the `n` numbers in `rem`. -/
def permsOf : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, rem => rem.flatMap fun a => (permsOf n (rem.erase a)).map fun t => a :: t

theorem mem_permsOf : ∀ (n : Nat) (rem q : List Nat), rem.length = n → q.Perm rem →
    q ∈ permsOf n rem := by
  intro n
  induction n with
  | zero =>
    intro rem q hlen hq
    have hrem : rem = [] := List.length_eq_zero_iff.mp hlen
    subst hrem
    have : q = [] := List.perm_nil.mp hq
    subst this
    simp [permsOf]
  | succ n ih =>
    intro rem q hlen hq
    have hqlen : q.length = n + 1 := by rw [hq.length_eq, hlen]
    obtain ⟨a, q', rfl⟩ := List.exists_cons_of_length_eq_add_one hqlen
    have ha : a ∈ rem := hq.subset (by simp)
    have hq' : q'.Perm (rem.erase a) := (List.cons_perm_iff_perm_erase.mp hq).2
    have hlen' : (rem.erase a).length = n := by
      rw [List.length_erase_of_mem ha, hlen]
      rfl
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨q', ih _ q' hlen' hq', rfl⟩⟩

/-- The orderings that start with `0` and then `a`. -/
def canonPart (a : Nat) : List (List Nat) :=
  (permsOf 6 ([1, 2, 3, 4, 5, 6, 7].erase a)).map fun t => 0 :: a :: t

theorem exists_canonPart {x : List Nat} (hx : x.Perm alph8) :
    ∃ a ∈ [1, 2, 3, 4, 5, 6, 7], ∃ b ∈ canonPart a, CyclicEq b x := by
  have hzero : 0 ∈ x := hx.mem_iff.mpr (by decide)
  obtain ⟨u, v, rfl⟩ := List.append_of_mem hzero
  have hc : CyclicEq (u ++ 0 :: v) (0 :: (v ++ u)) := by
    have h := CyclicEq.of_rot (x := u ++ 0 :: v) (by simp) u.length
    simpa only [rot_append_length, List.cons_append] using h
  have hp : (v ++ u).Perm [1, 2, 3, 4, 5, 6, 7] := (List.perm_cons 0).mp (hc.perm.symm.trans hx)
  have hlen : (v ++ u).length = 6 + 1 := hp.length_eq
  obtain ⟨a, q, hq⟩ := List.exists_cons_of_length_eq_add_one hlen
  rw [hq] at hp hc
  have ha : a ∈ [1, 2, 3, 4, 5, 6, 7] := hp.subset (by simp)
  have hq' : q.Perm ([1, 2, 3, 4, 5, 6, 7].erase a) := (List.cons_perm_iff_perm_erase.mp hp).2
  have hl : ([1, 2, 3, 4, 5, 6, 7].erase a).length = 6 := by
    rw [List.length_erase_of_mem ha]
    rfl
  exact ⟨a, ha, 0 :: a :: q, List.mem_map.mpr ⟨q, mem_permsOf 6 _ q hl hq', rfl⟩, hc.symm⟩

/-- Every 2-loop on 9 symbols is a row of a walk or a loop without a row, from the seven
pointer checks. -/
theorem complete9_of_parts {walks : List (List (Row Nat))} {ds : List (List Nat)}
    (ptrs : Nat → List (Nat × Nat))
    (h : ∀ a ∈ [1, 2, 3, 4, 5, 6, 7], coveredB walks ds (canonPart a) (ptrs a) = true)
    {x : List Nat} (hx : x.Perm alph8) :
    (∃ r ∈ walks.flatten, CyclicEq r.base x) ∨ (∃ d ∈ ds, CyclicEq d x) := by
  obtain ⟨a, ha, b, hb, hbx⟩ := exists_canonPart hx
  rcases coveredB_sound _ _ (h a ha) b hb with ⟨r, hr, hrb⟩ | ⟨d, hd, hdb⟩
  · exact Or.inl ⟨r, hr, hrb.trans hbx⟩
  · exact Or.inr ⟨d, hd, hdb.trans hbx⟩

/-! ### The walks on 9 symbols -/

/-- One closed walk of the 9-symbol selection. -/
def WalkOK (w : List (Row Nat)) : Prop :=
  BasedOn alph8 9 w ∧ ClosedTrail w ∧ (7 : Int) ∣ signedExcess w

instance (w : List (Row Nat)) : Decidable (WalkOK w) := by
  unfold WalkOK BasedOn ClosedTrail CyclicallyCompatible Row.Compatible
  infer_instance

theorem level9_of_walks {walks : List (List (Row Nat))} (h : ∀ w ∈ walks, WalkOK w) :
    Level alph8 7 walks :=
  ⟨fun w hw => (h w hw).2.1, fun w hw => (h w hw).2.2, fun w hw => (h w hw).1⟩

/-! ### One group -/

/-- For every walk a pointer certificate of its nine-fold repetition. -/
def allPortsB (circles : List (List Nat)) :
    List (List (Row Nat)) → List (List MixedPointer) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | w :: ws, m :: ms => decide (PortsCovered (rep 9 w) circles 9 m) && allPortsB circles ws ms

theorem allPortsB_sound {circles : List (List Nat)} :
    ∀ (ws : List (List (Row Nat))) (ms : List (List MixedPointer)),
      allPortsB circles ws ms = true → ∀ w ∈ ws, ∃ m, PortsCovered (rep 9 w) circles 9 m := by
  intro ws
  induction ws with
  | nil => intro _ _ w hw; simp at hw
  | cons a ws ih =>
    intro ms h w hw
    cases ms with
    | nil => simp [allPortsB] at h
    | cons m ms =>
      have h' : (decide (PortsCovered (rep 9 a) circles 9 m) && allPortsB circles ws ms) = true := h
      rw [Bool.and_eq_true] at h'
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨m, of_decide_eq_true h'.1⟩
      · exact ih ms h'.2 w hw

/-- Everything the kernel checks about one group: `ptrs` are the pointers for the loops
above the group's 9-symbol loops, `mixed` the cycle pointers of its walks. -/
def GroupOK (circles : List (List Nat)) (g : Group) (ptrs : List (Nat × Nat))
    (mixed : List (List MixedPointer)) : Prop :=
  (∀ w ∈ g.walks, BasedOn alph10 9 w) ∧
  (∀ w ∈ g.walks, ClosedTrail w) ∧
  (∀ w ∈ g.walks, (orbitPorts w 9 0).Perm (List.range 9)) ∧
  allPortsB circles g.walks mixed = true ∧
  g.walks.flatten.length = 378 ∧
  (g.walks.flatten.map Row.charge).sum = 182 ∧
  (∀ d ∈ g.dloops, d.Perm alph10) ∧
  g.dloops.length = 126 ∧
  coveredB g.walks g.dloops (g.d9.flatMap above) ptrs = true

instance (circles : List (List Nat)) (g : Group) (ptrs : List (Nat × Nat))
    (mixed : List (List MixedPointer)) : Decidable (GroupOK circles g ptrs mixed) := by
  unfold GroupOK BasedOn ClosedTrail CyclicallyCompatible Row.Compatible
  infer_instance

theorem GroupOK.facts {circles : List (List Nat)} {g : Group} {ptrs : List (Nat × Nat)}
    {mixed : List (List MixedPointer)} (h : GroupOK circles g ptrs mixed) :
    GroupFacts circles g := by
  obtain ⟨hb, hc, hp, hs, hn, hq, hd, hdn, hcov⟩ := h
  refine ⟨hb, hc, hp, ?_, hn, hq, hd, hdn, ?_⟩
  · intro w hw
    obtain ⟨m, hm⟩ := allPortsB_sound _ _ hs w hw
    exact hm.safeComp (by decide)
      (fun r hr => ((hb w hw) r (mem_rep hr)).2.1.length_eq)
      (fun r hr => ((hb w hw) r (mem_rep hr)).2.2.2)
  · intro d hd9 t ht
    exact coveredB_sound _ _ hcov t (List.mem_flatMap.mpr ⟨d, hd9, ht⟩)

/-! ### One long walk on 11 symbols -/

/-- The walk number `iw` of the 9-symbol selection, transported from port `p1` and then
from port `p2`. -/
def bigWalk (walks : List (List (Row Nat))) (iw p1 p2 : Nat) : List (Row Nat) :=
  transportWalk (transportWalk (componentAt walks iw) 8 p1) 11 p2

def BigOK (circles : List (List Nat)) (walks : List (List (Row Nat))) (iw p1 p2 : Nat)
    (ptrs : List MixedPointer) : Prop :=
  PortsCovered (bigWalk walks iw p1 p2) circles 9 ptrs

instance (circles : List (List Nat)) (walks : List (List (Row Nat))) (iw p1 p2 : Nat)
    (ptrs : List MixedPointer) : Decidable (BigOK circles walks iw p1 p2 ptrs) := by
  unfold BigOK
  infer_instance

/-- The pointer certificates of all long walks give the cover that `Cert` asks for. -/
theorem bigSafe_of_ptrs {walks : List (List (Row Nat))} {circles : List (List Nat)}
    (L : Level alph8 7 walks)
    (h : ∀ iw < walks.length, ∀ p1 < 7, ∀ p2 < 8,
      ∃ ptrs, BigOK circles walks iw p1 p2 ptrs) :
    ∀ W ∈ transportComps (transportComps walks 8 7) 11 8, SafeComp W 10 9 circles := by
  have L10 : Level alph9 8 (transportComps walks 8 7) :=
    L.transport 8 (by decide) (by decide) (by decide) (by decide)
  have L11 : Level alph10 9 (transportComps (transportComps walks 8 7) 11 8) :=
    L10.transport 11 (by decide) (by decide) (by decide) (by decide)
  intro W hW
  obtain ⟨W1, hW1, p2, hp2, rfl⟩ := mem_transportComps.mp hW
  obtain ⟨rs, hrs, p1, hp1, rfl⟩ := mem_transportComps.mp hW1
  obtain ⟨iw, hiw, rfl⟩ := List.mem_iff_getElem.mp hrs
  obtain ⟨ptrs, hptrs⟩ := h iw hiw p1 hp1 p2 hp2
  have he : bigWalk walks iw p1 p2 = transportWalk (transportWalk walks[iw] 8 p1) 11 p2 := by
    unfold bigWalk
    rw [componentAt_eq_getElem walks iw hiw]
  unfold BigOK at hptrs
  rw [he] at hptrs
  exact hptrs.safeComp (by decide) (L11.len (by decide) _ hW) (L11.kind _ hW)

end SuperpermutationUpperBound1771
