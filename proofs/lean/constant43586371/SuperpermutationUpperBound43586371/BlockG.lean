import SuperpermutationUpperBound43586371.Relabel
import SuperpermutationUpperBound43586371.AllSizes
import SuperpermutationUpperBound43586371.Certificate.Checks

/-!
# The block lemma, for a block at any level

A block is placed by a `Frame`: a canonical loop `d0`, the three tokens `t1, t2, t3` (the letters
added one, two and three levels above `d0`) and the letter `z` added one level above the block.
The block level has the letters `alph = t3 :: t2 :: t1 :: d0` and `h = d0.length + 2` ports; one
transport later the letters are `alph' = z :: alph`.

A block (`BlockData`) is written once, above `d0`: closed walks of full and short rows, each with
its number `g` of start ports (the walk is written `h / g` times, `Repeat.lean`), the loops without
a row, pointers that show that every loop of `above3T t1 t2 t3 d0` is a row base or a loop without a
row, and connector cycles for the completion of the block level.  `BlockOK` collects the checks
(decided by the kernel on the data) and `BlockPorts` the pointer certificates: for every walk, the
walk written `h / g` times is met by the cycles from every port.

From these, for every loop `d` that is a permutation of `d0`, the block relabelled onto `d` by
`relab d0 d`:

* `trailsR d`: the walks transported once (letter `z`) from their start ports, a level on `alph'`
  (`levelR`) with `(h + 1) · nrows` rows of total charge `(h + 1) · nq` (`countsR`);
* `circlesR d`: the cycles extended once by `z`, `h · ncyc` of them, which meet every trail
  (`safeR`);
* `loopsR d`: the `nd` loops without a row, permutations of `alph`;
* `coverR`: every loop of `above3T t1 t2 t3 d` is a loop without a row, or every 2-loop one level
  above it is a row of `trailsR d`.

No hypothesis says which letters a step exchanges (step (B)'s finding): the construction needs only
closed trails, divisible winding, rows over the right alphabet and that every 2-loop has a row.
In step (B) the block was fixed at 14 symbols with its cycles chosen on 16 symbols; here the cycles
are chosen at the completion of the block level and transported once, which is what the nested
ledger counts.
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound.Certificates.CircleBase

/-! ### Facts about levels (from step (B) `Fifteen.lean`) -/

theorem Level.mono {A : List Nat} {h : Nat} {l l' : List (List (Row Nat))} (L : Level A h l')
    (hs : ∀ rs ∈ l, rs ∈ l') : Level A h l :=
  ⟨fun rs hr => L.closed rs (hs rs hr), fun rs hr => L.winding rs (hs rs hr),
    fun rs hr => L.basedOn rs (hs rs hr)⟩

theorem Level.congr {A A' : List Nat} {h h' : Nat} {l : List (List (Row Nat))} (L : Level A h l)
    (hA : A.Perm A') (hh : h = h') : Level A' h' l := by
  subst hh
  exact ⟨L.closed, L.winding, fun rs hr => basedOn_congr_alphabet (L.basedOn rs hr) hA⟩

theorem Level.append {A : List Nat} {h : Nat} {l l' : List (List (Row Nat))} (L : Level A h l)
    (L' : Level A h l') : Level A h (l ++ l') := by
  refine ⟨?_, ?_, ?_⟩
  · intro rs hr
    rcases List.mem_append.mp hr with hr | hr
    · exact L.closed rs hr
    · exact L'.closed rs hr
  · intro rs hr
    rcases List.mem_append.mp hr with hr | hr
    · exact L.winding rs hr
    · exact L'.winding rs hr
  · intro rs hr
    rcases List.mem_append.mp hr with hr | hr
    · exact L.basedOn rs hr
    · exact L'.basedOn rs hr

theorem Level.flatMap {A : List Nat} {h : Nat} {β : Type} (l : List β)
    (f : β → List (List (Row Nat))) (hf : ∀ x ∈ l, Level A h (f x)) : Level A h (l.flatMap f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro rs hr
    obtain ⟨x, hx, hr⟩ := List.mem_flatMap.mp hr
    exact (hf x hx).closed rs hr
  · intro rs hr
    obtain ⟨x, hx, hr⟩ := List.mem_flatMap.mp hr
    exact (hf x hx).winding rs hr
  · intro rs hr
    obtain ⟨x, hx, hr⟩ := List.mem_flatMap.mp hr
    exact (hf x hx).basedOn rs hr

/-- A row that covers a 2-loop gives, one transport later, a row that covers every 2-loop
above it. -/
theorem Level.cover_transport {A : List Nat} {h : Nat} {comps : List (List (Row Nat))}
    (L : Level A h comps) (z : Nat) (hA : A.length = h + 1) (hn : 3 ≤ h + 1)
    {r : Row Nat} {x y : List Nat} (hr : r ∈ comps.flatten) (hrx : CyclicEq r.base x)
    (hb : InInsertionBlock z x y) :
    ∃ t ∈ (transportComps comps z h).flatten, CyclicEq t.base y := by
  have hv := (L.basedOn_flatten r hr).1
  obtain ⟨t, ht, hty⟩ := (Transport.rows_cyclicEq_iff_inInsertionBlock hv z y).mpr
    ((InInsertionBlock.congr_base hrx).mpr hb)
  exact ⟨t, (transportComps_flatten_perm comps z h hn (L.len hA)).mem_iff.mpr
    (List.mem_flatMap.mpr ⟨r, hr, ht⟩), hty⟩

/-- Cycle covers transport with a level. -/
theorem Level.safe_transport {A : List Nat} {h : Nat} {comps : List (List (Row Nat))}
    {circles : List (List Nat)} (L : Level A h comps) (hA : A.length = h + 1) (hn : 3 ≤ h + 1)
    (h10 : 10 ∉ A) (hv : CircleFamilyValid h circles)
    (hs : ∀ rs ∈ comps, SafeComp rs 10 h circles) (z : Nat) :
    ∀ W ∈ transportComps comps z h, SafeComp W 10 (h + 1) (extendCircles circles z) := by
  intro W hW
  obtain ⟨rs, hrs, p, hp, rfl⟩ := mem_transportComps.mp hW
  exact (hs rs hrs).transport z hn hv (L.len hA rs hrs) (L.kind rs hrs) (L.fresh h10 rs hrs) p hp

theorem peel {A : List Nat} {z : Nat} {y : List Nat} (ha : A.Nodup) (hne : A ≠ [])
    (hz : z ∉ A) (hy : y.Perm (z :: A)) : ∃ x, x.Perm A ∧ InInsertionBlock z x y :=
  exists_inInsertionBlock_of_perm_append_satellite ha hne hz
    (hy.trans (List.perm_append_comm (l₁ := [z]) (l₂ := A)))

theorem extend_mem {circles : List (List Nat)} {z : Nat} {L : List Nat}
    (hs : ∀ c ∈ circles, ∀ a ∈ c, a ∈ L) : ∀ c ∈ extendCircles circles z, ∀ a ∈ c, a ∈ z :: L := by
  intro c hc a ha
  simp only [extendCircles, circleExtensions, fullBases, List.mem_flatMap, List.mem_map,
    List.mem_range] at hc
  obtain ⟨c0, hc0, j, _, rfl⟩ := hc
  rcases List.mem_cons.mp ((insertLetter_perm c0 z j).mem_iff.mp ha) with rfl | ha0
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (hs c0 hc0 a ha0)

theorem extend_valid {circles : List (List Nat)} {z h : Nat} {L : List Nat}
    (hv : CircleFamilyValid h circles) (hs : ∀ c ∈ circles, ∀ a ∈ c, a ∈ L) (hz : z ∉ L) :
    CircleFamilyValid (h + 1) (extendCircles circles z) :=
  hv.extend z (fun c hc hm => hz (hs c hc z hm))

theorem extend_length {circles : List (List Nat)} {z h : Nat} (hv : CircleFamilyValid h circles) :
    (extendCircles circles z).length = h * circles.length :=
  extendCircles_length h circles z (fun c hc => (hv c hc).1)

theorem forall_mem_take_drop {Q : List Nat → Prop} {L : List (List Nat)} (s : Nat)
    (h1 : ∀ t ∈ L.take s, Q t) (h2 : ∀ t ∈ L.drop s, Q t) : ∀ t ∈ L, Q t := by
  intro t ht
  rw [← List.take_append_drop s L] at ht
  rcases List.mem_append.mp ht with ht | ht
  · exact h1 t ht
  · exact h2 t ht

theorem forall_mem_of_take_eq {Q : List Nat → Prop} {L : List (List Nat)} (s : Nat)
    (hl : L.length ≤ s) (h1 : ∀ t ∈ L.take s, Q t) : ∀ t ∈ L, Q t := by
  rw [List.take_of_length_le hl] at h1
  exact h1

/-! ### Loops three levels above a loop -/

/-- The 2-loops three levels above the loop `d`: letter `a` in a gap of `d`, then `b`, then `c`. -/
def above3T (a b c : Nat) (d : List Nat) : List (List Nat) :=
  (List.range d.length).flatMap fun i =>
    (List.range (d.length + 1)).flatMap fun j =>
      (List.range (d.length + 2)).map fun k => rot (rot (rot d i ++ [a]) j ++ [b]) k ++ [c]

theorem exists_mem_above3T {a b c : Nat} {d x1 x2 y : List Nat} (h1 : InInsertionBlock a d x1)
    (h2 : InInsertionBlock b x1 x2) (h3 : InInsertionBlock c x2 y) :
    ∃ t ∈ above3T a b c d, CyclicEq t y := by
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := (InInsertionBlock.congr_base hi).mpr h2
  obtain ⟨k, hk⟩ := (InInsertionBlock.congr_base hj).mpr h3
  have hjlt : j.val < d.length + 1 := by simpa using j.isLt
  have hklt : k.val < d.length + 2 := by
    have := k.isLt
    simp at this
    omega
  refine ⟨rot (rot (rot d i.val ++ [a]) j.val ++ [b]) k.val ++ [c], ?_, hk⟩
  exact List.mem_flatMap.mpr ⟨i.val, List.mem_range.mpr i.isLt, List.mem_flatMap.mpr
    ⟨j.val, List.mem_range.mpr hjlt, List.mem_map.mpr ⟨k.val, List.mem_range.mpr hklt, rfl⟩⟩⟩

theorem map_rot3 (f : Nat → Nat) (x : List Nat) (i j k a b c : Nat) :
    (rot (rot (rot x i ++ [a]) j ++ [b]) k ++ [c]).map f =
      rot (rot (rot (x.map f) i ++ [f a]) j ++ [f b]) k ++ [f c] := by
  rw [List.map_append, ← rot_map, List.map_append, ← rot_map, List.map_append, ← rot_map]
  rfl

theorem above3T_map (f : Nat → Nat) {a b c : Nat} (ha : f a = a) (hb : f b = b) (hc : f c = c)
    (d : List Nat) : above3T a b c (d.map f) = (above3T a b c d).map (List.map f) := by
  simp only [above3T, List.length_map, List.map_flatMap, List.map_map, Function.comp_def,
    map_rot3, ha, hb, hc]

/-! ### Repeated walks from several start ports (from step (B) `BlockB.lean`) -/

theorem transportWalk_reps_inventory (rs : List (Row Nat)) (newOrd : Nat) (h m : Nat)
    (ps : List Nat) (hn : 3 ≤ h + 1) (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hports : (ps.flatMap (orbitPorts rs m)).Perm (List.range h)) :
    (ps.flatMap (fun p => transportWalk (rep m rs) newOrd p)).Perm
      (Transport.packingRows rs newOrd) := by
  have he : ps.flatMap (fun p => transportWalk (rep m rs) newOrd p) =
      (ps.flatMap (orbitPorts rs m)).flatMap (fun q => transportWalk rs newOrd q) := by
    rw [List.flatMap_assoc]
    congr 1
    funext p
    exact transportWalk_rep rs newOrd m p
  rw [he]
  have h1 := hports.flatMap_right (fun q => transportWalk rs newOrd q)
  have h2 := transportWalk_inventory rs newOrd h hn hlen
  have h3 : (List.finRange h).flatMap (fun p => transportWalk rs newOrd p.val) =
      (List.range h).flatMap (fun q => transportWalk rs newOrd q) := by
    rw [← map_val_finRange h, List.flatMap_map]
  rw [h3] at h2
  exact h1.trans h2

theorem flatMap_flatten_perm_packingRows (items : List (List (Row Nat) × Nat))
    (F : List (Row Nat) × Nat → List (List (Row Nat))) (z : Nat)
    (hF : ∀ wg ∈ items, (F wg).flatten.Perm (Transport.packingRows wg.1 z)) :
    (items.flatMap F).flatten.Perm (Transport.packingRows (items.map Prod.fst).flatten z) := by
  induction items with
  | nil => simp [Transport.packingRows]
  | cons wg rest ih =>
    have hp : Transport.packingRows ((wg :: rest).map Prod.fst).flatten z =
        Transport.packingRows wg.1 z ++ Transport.packingRows (rest.map Prod.fst).flatten z := by
      simp [Transport.packingRows, List.flatten_cons, List.flatMap_append]
    rw [List.flatMap_cons, List.flatten_append, hp]
    exact (hF wg (by simp)).append (ih (fun wg' hwg' => hF wg' (by simp [hwg'])))

/-! ### Frames -/

/-- Where a block sits: canonical loop `d0`, tokens `t1, t2, t3`, next letter `z`. -/
structure Frame where
  d0 : List Nat
  t1 : Nat
  t2 : Nat
  t3 : Nat
  z : Nat

namespace Frame

variable (F : Frame)

/-- The letters at the level of the block. -/
def alph : List Nat := F.t3 :: F.t2 :: F.t1 :: F.d0

/-- The letters one level above the block. -/
def alph' : List Nat := F.z :: F.alph

/-- The number of ports at the level of the block. -/
def h : Nat := F.d0.length + 2

/-- The letters are distinct and different from the satellite 9 and the completion letter 10. -/
def OK : Prop := F.alph'.Nodup ∧ 9 ∉ F.alph' ∧ 10 ∉ F.alph'

theorem alph_length : F.alph.length = F.h + 1 := by simp [alph, h]

theorem hn : 3 ≤ F.h + 1 := by unfold h; omega

variable {F}

theorem OK.fresh (hF : F.OK) : F.z ∉ F.alph := by
  have h := hF.1; unfold alph' at h; exact (List.nodup_cons.mp h).1
theorem OK.alph_nodup (hF : F.OK) : F.alph.Nodup := by
  have h := hF.1; unfold alph' at h; exact (List.nodup_cons.mp h).2
theorem OK.nine (hF : F.OK) : 9 ∉ F.alph := by
  intro h; apply hF.2.1; simp [alph', h]
theorem OK.ten (hF : F.OK) : 10 ∉ F.alph := by
  intro h; apply hF.2.2; simp [alph', h]
theorem OK.z9 (hF : F.OK) : F.z ≠ 9 := by
  intro h; apply hF.2.1; rw [← h]; simp [alph']
theorem OK.z10 (hF : F.OK) : F.z ≠ 10 := by
  intro h; apply hF.2.2; rw [← h]; simp [alph']

theorem OK.sub (hF : F.OK) : ∀ a ∈ F.d0, a ∈ F.alph' := by
  intro a ha
  simp [alph', alph, ha]

theorem OK.parts (hF : F.OK) : F.t3 ∉ F.t2 :: F.t1 :: F.d0 ∧ F.t2 ∉ F.t1 :: F.d0 ∧
    F.t1 ∉ F.d0 ∧ F.d0.Nodup := by
  have h := hF.alph_nodup
  unfold alph at h
  obtain ⟨h3, h⟩ := List.nodup_cons.mp h
  obtain ⟨h2, h⟩ := List.nodup_cons.mp h
  obtain ⟨h1, h⟩ := List.nodup_cons.mp h
  exact ⟨h3, h2, h1, h⟩

theorem OK.d0_nodup (hF : F.OK) : F.d0.Nodup := hF.parts.2.2.2

theorem OK.t3_d0 (hF : F.OK) : F.t3 ∉ F.d0 := fun h => hF.parts.1 (by simp [h])
theorem OK.t2_d0 (hF : F.OK) : F.t2 ∉ F.d0 := fun h => hF.parts.2.1 (by simp [h])
theorem OK.t1_d0 (hF : F.OK) : F.t1 ∉ F.d0 := hF.parts.2.2.1
theorem OK.z_d0 (hF : F.OK) : F.z ∉ F.d0 := fun h => hF.fresh (by simp [alph, h])
theorem OK.nine_d0 (hF : F.OK) : 9 ∉ F.d0 := fun h => hF.nine (by simp [alph, h])
theorem OK.ten_d0 (hF : F.OK) : 10 ∉ F.d0 := fun h => hF.ten (by simp [alph, h])

theorem OK.alph'_nodup (hF : F.OK) : F.alph'.Nodup := hF.1

end Frame

/-! ### Blocks -/

/-- A block above the canonical loop of its frame. -/
structure BlockData where
  /-- the closed walks, each with its number of start ports -/
  items : List (List (Row Nat) × Nat)
  dloops : List (List Nat)
  ptrs : List (Nat × Nat)
  /-- connector cycles for the completion of the block level -/
  cyc : List (List Nat)
  nrows : Nat
  nq : Nat
  nd : Nat
  ncyc : Nat

/-- The checks on one walk. -/
def BWalkOK (F : Frame) (wg : List (Row Nat) × Nat) : Prop :=
  BasedOn F.alph 9 wg.1 ∧ ClosedTrail wg.1 ∧ 0 < F.h / wg.2 ∧
    (F.h : Int) ∣ ((F.h / wg.2 : Nat) : Int) * signedExcess wg.1 ∧
    ((List.range wg.2).flatMap (orbitPorts wg.1 (F.h / wg.2))).Perm (List.range F.h)

namespace BlockData

def walks (B : BlockData) : List (List (Row Nat)) := B.items.map Prod.fst

end BlockData

/-- Everything the kernel checks about a block. -/
structure BlockOK (F : Frame) (B : BlockData) : Prop where
  frame : F.OK
  walks : ∀ wg ∈ B.items, BWalkOK F wg
  dloops : ∀ e ∈ B.dloops, e.Perm F.alph
  cover : ∀ t ∈ above3T F.t1 F.t2 F.t3 F.d0,
    (∃ r ∈ B.walks.flatten, CyclicEq r.base t) ∨ (∃ e ∈ B.dloops, CyclicEq e t)
  nrows : B.walks.flatten.length = B.nrows
  nq : (B.walks.flatten.map Row.charge).sum = B.nq
  nd : B.dloops.length = B.nd
  valid : CircleFamilyValid F.h B.cyc
  support : ∀ c ∈ B.cyc, ∀ a ∈ c, a ∈ 10 :: F.alph
  ncyc : B.cyc.length = B.ncyc

/-- The pointer certificates: every walk, written `h / g` times, is met by the cycles from every
port of the block level. -/
def BlockPorts (F : Frame) (B : BlockData) : Prop :=
  ∀ wg ∈ B.items, ∃ m, PortsCovered (rep (F.h / wg.2) wg.1) B.cyc F.h m

/-- A checked block with its frame. -/
structure BlockCert where
  F : Frame
  B : BlockData
  ok : BlockOK F B
  ports : BlockPorts F B

namespace BlockData

variable (B : BlockData) (F : Frame)

/-- The trails one level above the block: every walk, written `h / g` times, transported from its
`g` start ports. -/
def trails : List (List (Row Nat)) :=
  B.items.flatMap fun wg =>
    (List.range wg.2).map fun p => transportWalk (rep (F.h / wg.2) wg.1) F.z p

/-- Their connector cycles: the block cycles extended once. -/
def circles : List (List Nat) := extendCircles B.cyc F.z

variable {B F}

theorem mem_trails {W : List (Row Nat)} (hW : W ∈ B.trails F) :
    ∃ wg ∈ B.items, ∃ p, p < wg.2 ∧ W = transportWalk (rep (F.h / wg.2) wg.1) F.z p := by
  obtain ⟨wg, hwg, hW⟩ := List.mem_flatMap.mp hW
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hW
  exact ⟨wg, hwg, p, List.mem_range.mp hp, rfl⟩

theorem item_len (hB : BlockOK F B) {wg : List (Row Nat) × Nat} (hwg : wg ∈ B.items) :
    ∀ r ∈ wg.1, r.base.length = F.h + 1 :=
  fun r hr => ((hB.walks wg hwg).1 r hr).2.1.length_eq.trans F.alph_length

theorem item_kind (hB : BlockOK F B) {wg : List (Row Nat) × Nat} (hwg : wg ∈ B.items) :
    ∀ r ∈ wg.1, r.visible = r.base.length ∨ r.visible = r.base.length - 2 :=
  fun r hr => ((hB.walks wg hwg).1 r hr).2.2.2

theorem start_lt (hB : BlockOK F B) {wg : List (Row Nat) × Nat} (hwg : wg ∈ B.items) {p : Nat}
    (hp : p < wg.2) : p < F.h := by
  have h := (hB.walks wg hwg).2.2.1
  have : wg.2 ≤ F.h := by
    by_contra hc
    have h0 : F.h / wg.2 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  omega

/-- The trails of one walk list its transported rows once. -/
theorem item_inventory (hB : BlockOK F B) {wg : List (Row Nat) × Nat} (hwg : wg ∈ B.items) :
    ((List.range wg.2).map fun p => transportWalk (rep (F.h / wg.2) wg.1) F.z p).flatten.Perm
      (Transport.packingRows wg.1 F.z) := by
  have h := transportWalk_reps_inventory wg.1 F.z F.h (F.h / wg.2) (List.range wg.2) F.hn
    (item_len hB hwg) (hB.walks wg hwg).2.2.2.2
  rw [List.flatMap_def] at h
  exact h

theorem walks_basedOn (hB : BlockOK F B) : BasedOn F.alph 9 B.walks.flatten := by
  intro r hr
  obtain ⟨w, hw, hrw⟩ := List.mem_flatten.mp hr
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hw
  exact (hB.walks wg hwg).1 r hrw

theorem trails_perm (hB : BlockOK F B) :
    (B.trails F).flatten.Perm (Transport.packingRows B.walks.flatten F.z) :=
  flatMap_flatten_perm_packingRows B.items _ F.z (fun _ hwg => item_inventory hB hwg)

/-- The canonical trails one level above the block are a level. -/
theorem level (hB : BlockOK F B) : Level F.alph' (F.h + 1) (B.trails F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨wg, hwg, p, hp, rfl⟩ := mem_trails hW
    obtain ⟨hb, hc, hm, hdiv, _⟩ := hB.walks wg hwg
    exact (transported_rep_closed hc hm F.z F.h F.hn (item_len hB hwg) (item_kind hB hwg)
      hdiv p (start_lt hB hwg hp)).1
  · intro W hW
    obtain ⟨wg, hwg, p, hp, rfl⟩ := mem_trails hW
    obtain ⟨hb, hc, hm, hdiv, _⟩ := hB.walks wg hwg
    exact (transported_rep_closed hc hm F.z F.h F.hn (item_len hB hwg) (item_kind hB hwg)
      hdiv p (start_lt hB hwg hp)).2
  · intro W hW r hr
    obtain ⟨wg, hwg, p, hp, rfl⟩ := mem_trails hW
    have hm : r ∈ ((List.range wg.2).map fun p =>
        transportWalk (rep (F.h / wg.2) wg.1) F.z p).flatten :=
      List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩, hr⟩
    exact ((hB.walks wg hwg).1.transport hB.frame.fresh hB.frame.z9) r
      ((item_inventory hB hwg).mem_iff.mp hm)

/-- The canonical trails are met by the extended block cycles. -/
theorem safe (hB : BlockOK F B) (hP : BlockPorts F B) :
    ∀ W ∈ B.trails F, SafeComp W 10 (F.h + 1) (B.circles F) := by
  intro W hW
  obtain ⟨wg, hwg, p, hp, rfl⟩ := mem_trails hW
  obtain ⟨m, hm⟩ := hP wg hwg
  have hlen : ∀ r ∈ rep (F.h / wg.2) wg.1, r.base.length = F.h + 1 :=
    fun r hr => item_len hB hwg r (mem_rep hr)
  have hkind : ∀ r ∈ rep (F.h / wg.2) wg.1,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2 :=
    fun r hr => item_kind hB hwg r (mem_rep hr)
  have hfresh : ∀ r ∈ rep (F.h / wg.2) wg.1, 10 ∉ r.base := fun r hr hm10 =>
    hB.frame.ten (((hB.walks wg hwg).1 r (mem_rep hr)).2.1.mem_iff.mp hm10)
  exact (hm.safeComp F.hn hlen hkind).transport F.z F.hn hB.valid hlen hkind hfresh p
    (start_lt hB hwg hp)

theorem trails_counts (hB : BlockOK F B) :
    (B.trails F).flatten.length = (F.h + 1) * B.nrows ∧
      ((B.trails F).flatten.map Row.charge).sum = (F.h + 1) * B.nq := by
  have hp := trails_perm hB
  have hc := Transport.packingRows_counts B.walks.flatten F.z F.alph.length
    (fun r hr => (walks_basedOn hB).ready hB.frame.fresh hB.frame.z9 r hr)
  rw [hB.nrows, F.alph_length] at hc
  rw [hB.nq] at hc
  exact ⟨hp.length_eq.trans hc.1, ((hp.map Row.charge).sum_eq).trans hc.2.1⟩

theorem circles_valid (hB : BlockOK F B) : CircleFamilyValid (F.h + 1) (B.circles F) :=
  extend_valid hB.valid hB.support (by
    intro hm
    rcases List.mem_cons.mp hm with h | h
    · exact hB.frame.z10 h
    · exact hB.frame.fresh h)

theorem circles_support (hB : BlockOK F B) : ∀ c ∈ B.circles F, ∀ a ∈ c, a ∈ 10 :: F.alph' := by
  intro c hc a ha
  have h := extend_mem hB.support c hc a ha
  simp only [Frame.alph', List.mem_cons] at h ⊢
  tauto

theorem circles_length (hB : BlockOK F B) : (B.circles F).length = F.h * B.ncyc := by
  unfold circles
  rw [extend_length hB.valid, hB.ncyc]

/-- A row of a walk gives rows of the trails above every 2-loop one level above its base. -/
theorem row_cover (hB : BlockOK F B) {r : Row Nat} {t y : List Nat} (hr : r ∈ B.walks.flatten)
    (hrt : CyclicEq r.base t) (hb : InInsertionBlock F.z t y) :
    ∃ r' ∈ (B.trails F).flatten, CyclicEq r'.base y := by
  obtain ⟨t', ht', hty⟩ := (Transport.rows_cyclicEq_iff_inInsertionBlock
    ((walks_basedOn hB) r hr).1 F.z y).mpr ((InInsertionBlock.congr_base hrt).mpr hb)
  exact ⟨t', (trails_perm hB).mem_iff.mpr (List.mem_flatMap.mpr ⟨r, hr, ht'⟩), hty⟩

/-! ### The block relabelled onto a loop `d` -/

variable (B F)

def trailsR (d : List Nat) : List (List (Row Nat)) :=
  (B.trails F).map (List.map (Row.map (relab F.d0 d)))

def circlesR (d : List Nat) : List (List Nat) :=
  (B.circles F).map (List.map (relab F.d0 d))

def loopsR (d : List Nat) : List (List Nat) :=
  B.dloops.map (List.map (relab F.d0 d))

variable {B F}

theorem relab_fix (hB : BlockOK F B) {d : List Nat} {a : Nat} (ha : a ∉ F.d0) :
    relab F.d0 d a = a := relab_of_not_mem ha

theorem relab_inj (hB : BlockOK F B) {d : List Nat} (hd : d.Perm F.d0) :
    ∀ a b, relab F.d0 d a = relab F.d0 d b → a = b :=
  relab_injective hB.frame.d0_nodup hd

theorem alph'_relab (hB : BlockOK F B) {d : List Nat} (hd : d.Perm F.d0) :
    (F.alph'.map (relab F.d0 d)).Perm F.alph' :=
  map_relab_perm hB.frame.d0_nodup hd hB.frame.alph'_nodup hB.frame.sub

theorem alph_relab (hB : BlockOK F B) {d : List Nat} (hd : d.Perm F.d0) :
    (F.alph.map (relab F.d0 d)).Perm F.alph :=
  map_relab_perm hB.frame.d0_nodup hd hB.frame.alph_nodup (fun a ha => by simp [Frame.alph, ha])

theorem levelR (hB : BlockOK F B) {d : List Nat} (hd : d.Perm F.d0) :
    Level F.alph' (F.h + 1) (B.trailsR F d) := by
  have L := level hB
  refine ⟨?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨W0, hW0, rfl⟩ := List.mem_map.mp hW
    exact closedTrail_map _ (L.closed W0 hW0)
  · intro W hW
    obtain ⟨W0, hW0, rfl⟩ := List.mem_map.mp hW
    rw [signedExcess_map]
    exact L.winding W0 hW0
  · intro W hW
    obtain ⟨W0, hW0, rfl⟩ := List.mem_map.mp hW
    have hb := basedOn_map (relab F.d0 d) (relab_inj hB hd) (L.basedOn W0 hW0)
    rw [relab_fix hB hB.frame.nine_d0] at hb
    exact basedOn_congr_alphabet hb (alph'_relab hB hd)

theorem safeR (hB : BlockOK F B) (hP : BlockPorts F B) (d : List Nat) :
    ∀ W ∈ B.trailsR F d, SafeComp W 10 (F.h + 1) (B.circlesR F d) := by
  intro W hW
  obtain ⟨W0, hW0, rfl⟩ := List.mem_map.mp hW
  have h := safeComp_map (relab F.d0 d) (safe hB hP W0 hW0)
  rwa [relab_fix hB hB.frame.ten_d0] at h

theorem circlesR_valid (hB : BlockOK F B) {d : List Nat} (hd : d.Perm F.d0) :
    CircleFamilyValid (F.h + 1) (B.circlesR F d) :=
  circleFamilyValid_map _ (relab_inj hB hd) (circles_valid hB)

theorem circlesR_support (hB : BlockOK F B) {d : List Nat} (hd : d.Perm F.d0) :
    ∀ c ∈ B.circlesR F d, ∀ a ∈ c, a ∈ 10 :: F.alph' := by
  intro c hc a ha
  obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
  obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
  by_cases hm : a0 ∈ F.d0
  · exact List.mem_cons_of_mem _ (hB.frame.sub _ (relab_mem hd hm))
  · rw [relab_fix hB hm]
    exact circles_support hB c0 hc0 a0 ha0

theorem circlesR_length (hB : BlockOK F B) (d : List Nat) :
    (B.circlesR F d).length = F.h * B.ncyc := by
  unfold circlesR
  rw [List.length_map, circles_length hB]

theorem countsR (hB : BlockOK F B) (d : List Nat) :
    (B.trailsR F d).flatten.length = (F.h + 1) * B.nrows ∧
      ((B.trailsR F d).flatten.map Row.charge).sum = (F.h + 1) * B.nq := by
  have he : (B.trailsR F d).flatten = (B.trails F).flatten.map (Row.map (relab F.d0 d)) := by
    unfold trailsR
    rw [List.map_flatten]
  rw [he, List.length_map, List.map_map]
  have hc : (Row.charge ∘ Row.map (relab F.d0 d)) = Row.charge := by
    funext r
    simp
  rw [hc]
  exact trails_counts hB

theorem loopsR_perm (hB : BlockOK F B) {d : List Nat} (hd : d.Perm F.d0) :
    ∀ e ∈ B.loopsR F d, e.Perm F.alph := by
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  exact ((hB.dloops e0 he0).map _).trans (alph_relab hB hd)

theorem loopsR_length (hB : BlockOK F B) (d : List Nat) : (B.loopsR F d).length = B.nd := by
  unfold loopsR
  rw [List.length_map, hB.nd]

/-- Every loop three levels above `d` is a loop without a row of the block above `d`, or every
2-loop one level above it is a row of the block's trails. -/
theorem coverR (hB : BlockOK F B) {d : List Nat} (hd : d.Perm F.d0) {t : List Nat}
    (ht : t ∈ above3T F.t1 F.t2 F.t3 d) :
    (∀ y, InInsertionBlock F.z t y → ∃ r ∈ (B.trailsR F d).flatten, CyclicEq r.base y) ∨
      (∃ e ∈ B.loopsR F d, CyclicEq e t) := by
  let σ := relab F.d0 d
  rw [← map_relab_self hB.frame.d0_nodup hd, above3T_map σ (relab_fix hB hB.frame.t1_d0)
    (relab_fix hB hB.frame.t2_d0) (relab_fix hB hB.frame.t3_d0)] at ht
  obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
  rcases hB.cover t0 ht0 with ⟨r, hr, hrt⟩ | ⟨e, he, het⟩
  · left
    intro y hb
    have hv : (r.map σ).Valid := Row.map_valid σ (relab_inj hB hd) ((walks_basedOn hB) r hr).1
    have hc : CyclicEq (r.map σ).base (t0.map σ) := cyclicEq_map σ hrt
    obtain ⟨t', ht', hty⟩ := (Transport.rows_cyclicEq_iff_inInsertionBlock hv F.z y).mpr
      ((InInsertionBlock.congr_base hc).mpr hb)
    have hz : σ F.z = F.z := relab_fix hB hB.frame.z_d0
    rw [← hz, rows_map] at ht'
    obtain ⟨t'', ht'', rfl⟩ := List.mem_map.mp ht'
    have hm : t'' ∈ (B.trails F).flatten := (trails_perm hB).mem_iff.mpr
      (List.mem_flatMap.mpr ⟨r, hr, ht''⟩)
    obtain ⟨W, hW, htW⟩ := List.mem_flatten.mp hm
    exact ⟨t''.map σ, List.mem_flatten.mpr ⟨W.map (Row.map σ), List.mem_map.mpr ⟨W, hW, rfl⟩,
      List.mem_map.mpr ⟨t'', htW, rfl⟩⟩, hty⟩
  · right
    exact ⟨e.map σ, List.mem_map.mpr ⟨e, he, rfl⟩, cyclicEq_map σ het⟩

end BlockData

end SuperpermutationUpperBound43586371
