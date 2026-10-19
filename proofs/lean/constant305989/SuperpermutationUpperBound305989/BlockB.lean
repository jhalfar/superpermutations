import SuperpermutationUpperBound305989.Relabel
import SuperpermutationUpperBound305989.AllSizes
import SuperpermutationUpperBound305989.Certificate.Checks

/-!
# The block lemma: a (10,3) block above every loop without a row

On 14 symbols (alphabet `alphabet 2 = 14 :: 13 :: 12 :: alph10`) the 2-loops above one loop `d`
on 11 symbols are the 1,320 loops `above3 d` (letters 12, 13, 14 inserted one after the other).
A block (`BlockData`) is written once, above the canonical loop `alph10`: closed walks of full and
short rows, loops without a row, for each walk the number `g` of ports at which its transports
start (the walk is written `12 / g` times, `Repeat.lean`), pointers that show that every loop of
`above3 alph10` is a row base or a loop without a row, and connector cycles on 16 symbols.

`BlockOK` collects the checks on the canonical block (`decide +kernel`), and `portsB` the pointer
certificates of its trails on 15 symbols.  From these:

* `BlockData.level15`, `safe15`, `counts15`: the canonical block transported to 15 symbols
  (walks from their start ports, loops without a row as full charts) is a level with 17,160 rows
  of total charge 4,810, and its trails are met by the 26 cycles and the 440 loop words.
* for every loop `d` that is a permutation of `alph10`, the same block relabelled by
  `relab alph10 d` (`blockComps d`): `blockLevel`, `blockSafe`, `blockCounts`, and
  `blockCover`: every 2-loop on 15 symbols above a loop of `above3 d` is a row of it.

There is no hypothesis about which letters a step exchanges: the Lean construction needs only
closed trails, divisible winding, rows over the right alphabet, and that every 2-loop has a row.
-/

namespace SuperpermutationUpperBound305989

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound.Certificates.CircleBase

/-! ### Loops above a loop, three letters up -/

/-- The 2-loops on 14 symbols above the loop `d` on 11 symbols: letter 12 in a gap of `d`, then
13, then 14. -/
def above3 (d : List Nat) : List (List Nat) :=
  (List.range d.length).flatMap fun i =>
    (List.range (d.length + 1)).flatMap fun j =>
      (List.range (d.length + 2)).map fun k => rot (rot (rot d i ++ [12]) j ++ [13]) k ++ [14]

theorem exists_mem_above3 {d x1 x2 y : List Nat} (h1 : InInsertionBlock 12 d x1)
    (h2 : InInsertionBlock 13 x1 x2) (h3 : InInsertionBlock 14 x2 y) :
    ∃ t ∈ above3 d, CyclicEq t y := by
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := (InInsertionBlock.congr_base hi).mpr h2
  obtain ⟨k, hk⟩ := (InInsertionBlock.congr_base hj).mpr h3
  have hjlt : j.val < d.length + 1 := by simpa using j.isLt
  have hklt : k.val < d.length + 2 := by
    have := k.isLt
    simp at this
    omega
  refine ⟨rot (rot (rot d i.val ++ [12]) j.val ++ [13]) k.val ++ [14], ?_, hk⟩
  exact List.mem_flatMap.mpr ⟨i.val, List.mem_range.mpr i.isLt, List.mem_flatMap.mpr
    ⟨j.val, List.mem_range.mpr hjlt, List.mem_map.mpr ⟨k.val, List.mem_range.mpr hklt, rfl⟩⟩⟩

theorem map_rot3 (f : Nat → Nat) (x : List Nat) (i j k a b c : Nat) :
    (rot (rot (rot x i ++ [a]) j ++ [b]) k ++ [c]).map f =
      rot (rot (rot (x.map f) i ++ [f a]) j ++ [f b]) k ++ [f c] := by
  rw [List.map_append, ← rot_map, List.map_append, ← rot_map, List.map_append, ← rot_map]
  rfl

theorem above3_map (f : Nat → Nat) (h12 : f 12 = 12) (h13 : f 13 = 13) (h14 : f 14 = 14)
    (d : List Nat) : above3 (d.map f) = (above3 d).map (List.map f) := by
  simp only [above3, List.length_map, List.map_flatMap, List.map_map, Function.comp_def,
    map_rot3, h12, h13, h14]

/-! ### Repeated walks from several start ports -/

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

/-! ### Pointer certificates for a list of trails -/

def portsB (circles : List (List Nat)) (h : Nat) :
    List (List (Row Nat)) → List (List MixedPointer) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | W :: Ws, m :: ms => decide (PortsCovered W circles h m) && portsB circles h Ws ms

theorem portsB_sound {circles : List (List Nat)} {h : Nat} :
    ∀ (Ws : List (List (Row Nat))) (ms : List (List MixedPointer)),
      portsB circles h Ws ms = true → ∀ W ∈ Ws, ∃ m, PortsCovered W circles h m := by
  intro Ws
  induction Ws with
  | nil => intro _ _ W hW; simp at hW
  | cons a Ws ih =>
    intro ms hb W hW
    cases ms with
    | nil => simp [portsB] at hb
    | cons m ms =>
      have h' : (decide (PortsCovered a circles h m) && portsB circles h Ws ms) = true := hb
      rw [Bool.and_eq_true] at h'
      rcases List.mem_cons.mp hW with rfl | hW
      · exact ⟨m, of_decide_eq_true h'.1⟩
      · exact ih ms h'.2 W hW

/-! ### The block -/

/-- A block above the canonical loop `alph10` on 14 symbols. -/
structure BlockData where
  /-- the closed walks, each with its number of start ports -/
  items : List (List (Row Nat) × Nat)
  dloops : List (List Nat)
  ptrs : List (Nat × Nat)
  /-- connector cycles on 16 symbols for the trails on 15 symbols -/
  cyc : List (List Nat)

namespace BlockData

variable (B : BlockData)

def walks : List (List (Row Nat)) := B.items.map Prod.fst

/-- The trails on 15 symbols that come from walk `w` with `g` start ports. -/
def itemTrails (wg : List (Row Nat) × Nat) : List (List (Row Nat)) :=
  (List.range wg.2).map fun p => transportWalk (rep (12 / wg.2) wg.1) 15 p

def trails15 : List (List (Row Nat)) := B.items.flatMap itemTrails

def charts15 : List (List (Row Nat)) := B.dloops.map fun e => Partition.fullChart e 15 9

def comps15 : List (List (Row Nat)) := B.trails15 ++ B.charts15

def circles16 : List (List Nat) := B.cyc ++ B.dloops

end BlockData

/-- Everything the kernel checks about the canonical block. -/
def BlockOK (B : BlockData) : Prop :=
  (∀ wg ∈ B.items, BasedOn (alphabet 2) 9 wg.1 ∧ ClosedTrail wg.1 ∧ 0 < 12 / wg.2 ∧
    (12 : Int) ∣ ((12 / wg.2 : Nat) : Int) * signedExcess wg.1 ∧
    ((List.range wg.2).flatMap (orbitPorts wg.1 (12 / wg.2))).Perm (List.range 12)) ∧
  (∀ e ∈ B.dloops, e.Perm (alphabet 2)) ∧
  coveredB B.walks B.dloops (above3 alph10) B.ptrs = true ∧
  B.walks.flatten.length = 880 ∧ (B.walks.flatten.map Row.charge).sum = 370 ∧
  B.dloops.length = 440 ∧
  CircleFamilyValid 13 B.cyc ∧ (∀ c ∈ B.cyc, ∀ a ∈ c, a < 16 ∧ a ≠ 9) ∧ B.cyc.length = 26

instance (B : BlockData) : Decidable (BlockOK B) := by
  unfold BlockOK BasedOn ClosedTrail CyclicallyCompatible Row.Compatible CircleFamilyValid
  infer_instance

namespace BlockData

variable {B : BlockData}

theorem alphabet2_length : (alphabet 2).length = 13 := rfl

theorem mem_trails15 {W : List (Row Nat)} (hW : W ∈ B.trails15) :
    ∃ wg ∈ B.items, ∃ p, p < wg.2 ∧ W = transportWalk (rep (12 / wg.2) wg.1) 15 p := by
  obtain ⟨wg, hwg, hW⟩ := List.mem_flatMap.mp hW
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hW
  exact ⟨wg, hwg, p, List.mem_range.mp hp, rfl⟩

theorem item_len (hB : BlockOK B) {wg : List (Row Nat) × Nat} (hwg : wg ∈ B.items) :
    ∀ r ∈ wg.1, r.base.length = 12 + 1 :=
  fun r hr => ((hB.1 wg hwg).1 r hr).2.1.length_eq

theorem item_kind (hB : BlockOK B) {wg : List (Row Nat) × Nat} (hwg : wg ∈ B.items) :
    ∀ r ∈ wg.1, r.visible = r.base.length ∨ r.visible = r.base.length - 2 :=
  fun r hr => ((hB.1 wg hwg).1 r hr).2.2.2

/-- The trails of one walk list its transported rows once. -/
theorem item_inventory (hB : BlockOK B) {wg : List (Row Nat) × Nat} (hwg : wg ∈ B.items) :
    (itemTrails wg).flatten.Perm (Transport.packingRows wg.1 15) := by
  have h := transportWalk_reps_inventory wg.1 15 12 (12 / wg.2) (List.range wg.2) (by decide)
    (item_len hB hwg) (hB.1 wg hwg).2.2.2.2
  rw [List.flatMap_def] at h
  exact h

theorem start_lt (hB : BlockOK B) {wg : List (Row Nat) × Nat} (hwg : wg ∈ B.items) {p : Nat}
    (hp : p < wg.2) : p < 12 := by
  have h := (hB.1 wg hwg).2.2.1
  have : wg.2 ≤ 12 := by
    by_contra hc
    have h0 : 12 / wg.2 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  omega

theorem dloop_perm (hB : BlockOK B) {e : List Nat} (he : e ∈ B.dloops) : e.Perm (alphabet 2) :=
  hB.2.1 e he

theorem chart_basedOn {e : List Nat} (hp : e.Perm (alphabet 2)) :
    BasedOn (alphabet 3) 9 (Partition.fullChart e 15 9) := by
  intro r hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  have h15 : 15 ∉ e := fun hm => (by decide : 15 ∉ alphabet 2) (hp.mem_iff.mp hm)
  have h9 : 9 ∉ e := fun hm => (by decide : 9 ∉ alphabet 2) (hp.mem_iff.mp hm)
  refine ⟨Partition.fullChartAt_valid (hp.nodup_iff.mpr (by decide)) h15 h9 (by decide) j,
    ?_, rfl, Or.inl ?_⟩
  · exact ((rot_perm e j).append_right [15]).trans
      ((hp.append_right [15]).trans List.perm_append_comm)
  · simp [Partition.fullChartAt]

theorem chart_charge (x : List Nat) :
    ((Partition.fullChart x 15 9).map Row.charge).sum = 0 :=
  Cert.sum_map_eq_zero _ _ (Partition.fullChart_charge x 15 9)

/-- The canonical block on 15 symbols is a level. -/
theorem level15 (hB : BlockOK B) : Level (alphabet 3) 13 B.comps15 := by
  refine ⟨?_, ?_, ?_⟩
  · intro W hW
    rcases List.mem_append.mp hW with hW | hW
    · obtain ⟨wg, hwg, p, hp, rfl⟩ := mem_trails15 hW
      obtain ⟨hb, hc, hm, hdiv, _⟩ := hB.1 wg hwg
      exact (transported_rep_closed hc hm 15 12 (by decide) (item_len hB hwg) (item_kind hB hwg)
        hdiv p (start_lt hB hwg hp)).1
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hW
      have hl : e.length = 13 := (dloop_perm hB he).length_eq
      exact Partition.fullChart_closedTrail e 15 9 (by omega)
  · intro W hW
    rcases List.mem_append.mp hW with hW | hW
    · obtain ⟨wg, hwg, p, hp, rfl⟩ := mem_trails15 hW
      obtain ⟨hb, hc, hm, hdiv, _⟩ := hB.1 wg hwg
      exact (transported_rep_closed hc hm 15 12 (by decide) (item_len hB hwg) (item_kind hB hwg)
        hdiv p (start_lt hB hwg hp)).2
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hW
      have hl : e.length = 13 := (dloop_perm hB he).length_eq
      have hx : signedExcess (Partition.fullChart e 15 9) = 13 := by
        unfold signedExcess
        rw [chart_charge, Partition.fullChart_length, hl]
        rfl
      rw [hx]
      norm_num
  · intro W hW
    rcases List.mem_append.mp hW with hW | hW
    · obtain ⟨wg, hwg, p, hp, rfl⟩ := mem_trails15 hW
      intro r hr
      have hm : r ∈ (itemTrails wg).flatten := List.mem_flatten.mpr
        ⟨_, List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩, hr⟩
      exact ((hB.1 wg hwg).1.transport (by decide) (by decide)) r
        ((item_inventory hB hwg).mem_iff.mp hm)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hW
      exact chart_basedOn (dloop_perm hB he)

/-- The canonical trails on 15 symbols are met by the cycles on 16 symbols. -/
theorem safe15 (hB : BlockOK B) (hP : ∀ W ∈ B.trails15, ∃ m, PortsCovered W B.cyc 13 m) :
    ∀ W ∈ B.comps15, SafeComp W 10 13 B.circles16 := by
  have L := level15 hB
  intro W hW
  rcases List.mem_append.mp hW with hW' | hW'
  · obtain ⟨m, hm⟩ := hP W hW'
    exact (hm.safeComp (by decide) (L.len rfl W hW) (L.kind W hW)).mono
      (fun c hc => List.mem_append_left _ hc)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hW'
    have hl : e.length = 13 := (dloop_perm hB he).length_eq
    exact SafeComp.fullChart e 15 9 10 13 B.circles16 (List.mem_append_right _ he)
      (by intro h0; rw [h0] at hl; simp at hl)

theorem circles16_valid (hB : BlockOK B) : CircleFamilyValid 13 B.circles16 := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hB.2.2.2.2.2.2.1 c hc
  · have hp := dloop_perm hB hc
    exact ⟨hp.length_eq, hp.nodup_iff.mpr (by decide)⟩

theorem circles16_support (hB : BlockOK B) : ∀ c ∈ B.circles16, ∀ a ∈ c, a < 16 ∧ a ≠ 9 := by
  intro c hc a ha
  rcases List.mem_append.mp hc with hc | hc
  · exact hB.2.2.2.2.2.2.2.1 c hc a ha
  · exact (by decide : ∀ b ∈ alphabet 2, b < 16 ∧ b ≠ 9) a ((dloop_perm hB hc).mem_iff.mp ha)

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

theorem walks_basedOn (hB : BlockOK B) : BasedOn (alphabet 2) 9 B.walks.flatten := by
  intro r hr
  obtain ⟨w, hw, hrw⟩ := List.mem_flatten.mp hr
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hw
  exact (hB.1 wg hwg).1 r hrw

theorem trails15_perm (hB : BlockOK B) :
    B.trails15.flatten.Perm (Transport.packingRows B.walks.flatten 15) :=
  flatMap_flatten_perm_packingRows B.items itemTrails 15 (fun _ hwg => item_inventory hB hwg)

theorem trails15_counts (hB : BlockOK B) : B.trails15.flatten.length = 11440 ∧
    (B.trails15.flatten.map Row.charge).sum = 4810 := by
  have hp := trails15_perm hB
  have hc := Transport.packingRows_counts B.walks.flatten 15 13
    (fun r hr => (walks_basedOn hB).ready (by decide) (by decide) r hr)
  have h880 := hB.2.2.2.1
  have h370 := hB.2.2.2.2.1
  rw [h880] at hc
  rw [h370] at hc
  exact ⟨hp.length_eq.trans hc.1, ((hp.map Row.charge).sum_eq).trans hc.2.1⟩

theorem charts15_counts (hB : BlockOK B) : B.charts15.flatten.length = 5720 ∧
    (B.charts15.flatten.map Row.charge).sum = 0 := by
  constructor
  · unfold charts15
    rw [← List.flatMap_def, length_flatMap_const B.dloops _ 13, hB.2.2.2.2.2.1]
    intro x hx
    rw [Partition.fullChart_length]
    exact (dloop_perm hB hx).length_eq
  · apply Cert.sum_map_eq_zero
    intro r hr
    obtain ⟨W, hW, hrW⟩ := List.mem_flatten.mp hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hW
    exact Partition.fullChart_charge x 15 9 r hrW

theorem counts15 (hB : BlockOK B) : B.comps15.flatten.length = 17160 ∧
    (B.comps15.flatten.map Row.charge).sum = 4810 := by
  have he : B.comps15.flatten = B.trails15.flatten ++ B.charts15.flatten := by
    unfold comps15
    rw [List.flatten_append]
  rw [he, List.length_append, List.map_append, List.sum_append, (trails15_counts hB).1,
    (trails15_counts hB).2, (charts15_counts hB).1, (charts15_counts hB).2]
  exact ⟨rfl, rfl⟩

/-- Every 2-loop on 15 symbols above a loop of `above3 alph10` is a row of the canonical block. -/
theorem cover15 (hB : BlockOK B) {t y : List Nat}
    (ht : (∃ r ∈ B.walks.flatten, CyclicEq r.base t) ∨ (∃ e ∈ B.dloops, CyclicEq e t))
    (hb : InInsertionBlock 15 t y) : ∃ r ∈ B.comps15.flatten, CyclicEq r.base y := by
  rcases ht with ⟨r, hr, hrt⟩ | ⟨e, he, het⟩
  · obtain ⟨t', ht', hty⟩ := (Transport.rows_cyclicEq_iff_inInsertionBlock
      ((walks_basedOn hB) r hr).1 15 y).mpr ((InInsertionBlock.congr_base hrt).mpr hb)
    have hm : t' ∈ B.trails15.flatten := (trails15_perm hB).mem_iff.mpr
      (List.mem_flatMap.mpr ⟨r, hr, ht'⟩)
    obtain ⟨W, hW, htW⟩ := List.mem_flatten.mp hm
    exact ⟨t', List.mem_flatten.mpr ⟨W, List.mem_append_left _ hW, htW⟩, hty⟩
  · obtain ⟨t', ht', hty⟩ := (Partition.fullChart_cyclicEq_iff_inInsertionBlock e y 15 9).mpr
      ((InInsertionBlock.congr_base het).mpr hb)
    exact ⟨t', List.mem_flatten.mpr ⟨_, List.mem_append_right _
      (List.mem_map.mpr ⟨e, he, rfl⟩), ht'⟩, hty⟩

end BlockData

/-! ### The block relabelled onto a loop `d` -/

namespace BlockData

variable (B : BlockData)

/-- The block above the loop `d` on 15 symbols: the canonical one relabelled. -/
def blockComps (d : List Nat) : List (List (Row Nat)) :=
  B.comps15.map (List.map (Row.map (relab alph10 d)))

/-- Its connector cycles on 16 symbols. -/
def blockCircles (d : List Nat) : List (List Nat) :=
  B.circles16.map (List.map (relab alph10 d))

variable {B}

theorem alph10_nodup : alph10.Nodup := by decide

theorem relab_fix {d : List Nat} {a : Nat} (ha : a ∉ alph10) : relab alph10 d a = a :=
  relab_of_not_mem ha

theorem relab_inj {d : List Nat} (hd : d.Perm alph10) :
    ∀ a b, relab alph10 d a = relab alph10 d b → a = b :=
  relab_injective alph10_nodup hd

theorem alphabet3_relab {d : List Nat} (hd : d.Perm alph10) :
    ((alphabet 3).map (relab alph10 d)).Perm (alphabet 3) :=
  map_relab_perm alph10_nodup hd (alphabet_nodup 3) (by decide)

theorem blockLevel (hB : BlockOK B) {d : List Nat} (hd : d.Perm alph10) :
    Level (alphabet 3) 13 (B.blockComps d) := by
  have L := level15 hB
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
    have hb := basedOn_map (relab alph10 d) (relab_inj hd) (L.basedOn W0 hW0)
    rw [relab_fix (by decide : (9 : Nat) ∉ alph10)] at hb
    exact basedOn_congr_alphabet hb (alphabet3_relab hd)

theorem blockSafe (hB : BlockOK B) (hP : ∀ W ∈ B.trails15, ∃ m, PortsCovered W B.cyc 13 m)
    {d : List Nat} : ∀ W ∈ B.blockComps d, SafeComp W 10 13 (B.blockCircles d) := by
  intro W hW
  obtain ⟨W0, hW0, rfl⟩ := List.mem_map.mp hW
  have h := safeComp_map (relab alph10 d) (safe15 hB hP W0 hW0)
  rwa [relab_fix (by decide : (10 : Nat) ∉ alph10)] at h

theorem blockCircles_valid (hB : BlockOK B) {d : List Nat} (hd : d.Perm alph10) :
    CircleFamilyValid 13 (B.blockCircles d) :=
  circleFamilyValid_map _ (relab_inj hd) (circles16_valid hB)

theorem blockCircles_support (hB : BlockOK B) {d : List Nat} (hd : d.Perm alph10) :
    ∀ c ∈ B.blockCircles d, ∀ a ∈ c, a < 16 ∧ a ≠ 9 := by
  intro c hc a ha
  obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
  obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
  by_cases hm : a0 ∈ alph10
  · exact (by decide : ∀ b ∈ alph10, b < 16 ∧ b ≠ 9) _ (relab_mem hd hm)
  · rw [relab_fix hm]
    exact circles16_support hB c0 hc0 a0 ha0

theorem blockCircles_length (hB : BlockOK B) (d : List Nat) :
    (B.blockCircles d).length = 466 := by
  unfold blockCircles circles16
  rw [List.length_map, List.length_append, hB.2.2.2.2.2.2.2.2, hB.2.2.2.2.2.1]

theorem blockCounts (hB : BlockOK B) (d : List Nat) :
    (B.blockComps d).flatten.length = 17160 ∧
      ((B.blockComps d).flatten.map Row.charge).sum = 4810 := by
  have he : (B.blockComps d).flatten = B.comps15.flatten.map (Row.map (relab alph10 d)) := by
    unfold blockComps
    rw [List.map_flatten]
  rw [he, List.length_map, List.map_map]
  have hc : (Row.charge ∘ Row.map (relab alph10 d)) = Row.charge := by
    funext r
    simp
  rw [hc]
  exact counts15 hB

/-- Every 2-loop on 15 symbols above a loop of `above3 d` is a row of the block above `d`. -/
theorem blockCover (hB : BlockOK B) {d : List Nat} (hd : d.Perm alph10) {t y : List Nat}
    (ht : t ∈ above3 d) (hb : InInsertionBlock 15 t y) :
    ∃ r ∈ (B.blockComps d).flatten, CyclicEq r.base y := by
  let σ := relab alph10 d
  have hfix : ∀ a, a ∉ alph10 → σ a = a := fun a ha => relab_fix ha
  rw [← map_relab_self alph10_nodup hd, above3_map σ (hfix 12 (by decide)) (hfix 13 (by decide))
    (hfix 14 (by decide))] at ht
  obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
  have hcov := coveredB_sound _ _ hB.2.2.1 t0 ht0
  rcases hcov with ⟨r, hr, hrt⟩ | ⟨e, he, het⟩
  · -- the relabelled row `r.map σ` is a row of the relabelled walk
    have hv : (r.map σ).Valid := Row.map_valid σ (relab_inj hd) ((walks_basedOn hB) r hr).1
    have hc : CyclicEq (r.map σ).base (t0.map σ) := cyclicEq_map σ hrt
    obtain ⟨t', ht', hty⟩ := (Transport.rows_cyclicEq_iff_inInsertionBlock hv 15 y).mpr
      ((InInsertionBlock.congr_base hc).mpr hb)
    have h15 : σ 15 = 15 := hfix 15 (by decide)
    rw [← h15, rows_map] at ht'
    obtain ⟨t'', ht'', rfl⟩ := List.mem_map.mp ht'
    have hm : t'' ∈ B.trails15.flatten := (trails15_perm hB).mem_iff.mpr
      (List.mem_flatMap.mpr ⟨r, hr, ht''⟩)
    obtain ⟨W, hW, htW⟩ := List.mem_flatten.mp hm
    refine ⟨t''.map σ, List.mem_flatten.mpr ⟨W.map (Row.map σ), ?_, ?_⟩, hty⟩
    · exact List.mem_map.mpr ⟨W, List.mem_append_left _ hW, rfl⟩
    · exact List.mem_map.mpr ⟨t'', htW, rfl⟩
  · have hc : CyclicEq (e.map σ) (t0.map σ) := cyclicEq_map σ het
    obtain ⟨t', ht', hty⟩ := (Partition.fullChart_cyclicEq_iff_inInsertionBlock (e.map σ) y 15 9).mpr
      ((InInsertionBlock.congr_base hc).mpr hb)
    have h15 : σ 15 = 15 := hfix 15 (by decide)
    have h9 : σ 9 = 9 := hfix 9 (by decide)
    rw [← h15, ← h9, fullChart_map] at ht'
    obtain ⟨t'', ht'', rfl⟩ := List.mem_map.mp ht'
    refine ⟨t''.map σ, List.mem_flatten.mpr ⟨(Partition.fullChart e 15 9).map (Row.map σ), ?_,
      List.mem_map.mpr ⟨t'', ht'', rfl⟩⟩, hty⟩
    exact List.mem_map.mpr ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩), rfl⟩

end BlockData

end SuperpermutationUpperBound305989
