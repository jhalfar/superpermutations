import SuperpermutationUpperBound1771.WordOfLevel

/-!
# The selection with blocks, from 9 to 13 symbols

The selection has three kinds of 2-loops on 11 symbols.

* Loops above a loop of the 9-symbol selection that carries a row.  Their rows are the
  9-symbol rows transported twice (`big11`).
* Loops above one of the 336 loops of the 9-symbol selection without a row.  They come in 48
  groups.  A group has three short closed walks (`Group.walks`) and loops without a row
  (`Group.dloops`), and together these account for every loop above the seven 9-symbol loops
  of the group (`Group.d9`).

One transport later the long walks are transported again, each short walk is written nine
times and transported from port 0, and every loop without a row becomes a full chart, as in
`Partition/SprintBase.lean`.  `Cert` lists the finite facts; everything else here is proved
from them.  The letters: 0..7 ordinary, 9 the satellite, 8, 11, 12 added by the transports,
10 the completion letter.
-/

namespace SuperpermutationUpperBound1771

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

def alph8 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def alph9 : List Nat := 8 :: alph8
def alph10 : List Nat := 11 :: alph9
def alph11 : List Nat := 12 :: alph10

/-- The finite data of one of the 48 groups. -/
structure Group where
  walks : List (List (Row Nat))
  dloops : List (List Nat)
  d9 : List (List Nat)

/-- The 2-loops on 11 symbols above the 9-symbol loop `d`: letter 8 in a gap of `d`, then
letter 11 in a gap of the result. -/
def above (d : List Nat) : List (List Nat) :=
  (List.range d.length).flatMap fun i =>
    (List.range (d.length + 1)).map fun j => rot (rot d i ++ [8]) j ++ [11]

theorem exists_mem_above {d x1 y : List Nat} (h1 : InInsertionBlock 8 d x1)
    (h2 : InInsertionBlock 11 x1 y) : ∃ t ∈ above d, CyclicEq t y := by
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := (InInsertionBlock.congr_base hi).mpr h2
  refine ⟨rot (rot d i.val ++ [8]) j.val ++ [11], ?_, hj⟩
  have hjlt : j.val < d.length + 1 := by
    have := j.isLt
    simpa using this
  exact List.mem_flatMap.mpr ⟨i.val, List.mem_range.mpr i.isLt,
    List.mem_map.mpr ⟨j.val, List.mem_range.mpr hjlt, rfl⟩⟩

/-- What the kernel checks establish for one group. -/
structure GroupFacts (circles : List (List Nat)) (g : Group) : Prop where
  basedOn : ∀ w ∈ g.walks, BasedOn alph10 9 w
  closed : ∀ w ∈ g.walks, ClosedTrail w
  ports : ∀ w ∈ g.walks, (orbitPorts w 9 0).Perm (List.range 9)
  safe : ∀ w ∈ g.walks, SafeComp (rep 9 w) 10 9 circles
  rowCount : g.walks.flatten.length = 378
  charge : (g.walks.flatten.map Row.charge).sum = 182
  dperm : ∀ d ∈ g.dloops, d.Perm alph10
  dcount : g.dloops.length = 126
  cover : ∀ d ∈ g.d9, ∀ t ∈ above d,
    (∃ r ∈ g.walks.flatten, CyclicEq r.base t) ∨ (∃ e ∈ g.dloops, CyclicEq e t)

/-- The finite certificate of the selection. -/
structure Cert where
  walks9 : List (List (Row Nat))
  groups : List Group
  circles : List (List Nat)
  level9 : Level alph8 7 walks9
  rowCount9 : walks9.flatten.length = 4704
  charge9 : (walks9.flatten.map Row.charge).sum = 2352
  complete9 : ∀ x : List Nat, x.Perm alph8 →
    (∃ r ∈ walks9.flatten, CyclicEq r.base x) ∨ (∃ d ∈ groups.flatMap Group.d9, CyclicEq d x)
  groupCount : groups.length = 48
  groupFacts : ∀ g ∈ groups, GroupFacts circles g
  circles_valid : CircleFamilyValid 9 circles
  circles_support : ∀ c ∈ circles, ∀ a ∈ c, a ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11]
  circleCount : circles.length = 203
  bigSafe : ∀ W ∈ transportComps (transportComps walks9 8 7) 11 8, SafeComp W 10 9 circles

namespace Cert

variable (C : Cert)

def big10 : List (List (Row Nat)) := transportComps C.walks9 8 7
def big11 : List (List (Row Nat)) := transportComps C.big10 11 8
def big12 : List (List (Row Nat)) := transportComps C.big11 12 9
def small11 : List (List (Row Nat)) := C.groups.flatMap Group.walks
def d11 : List (List Nat) := C.groups.flatMap Group.dloops
def small12 : List (List (Row Nat)) := C.small11.map fun w => transportWalk (rep 9 w) 12 0
def charts12 : List (List (Row Nat)) := C.d11.map fun x => Partition.fullChart x 12 9
def comps12 : List (List (Row Nat)) := C.big12 ++ C.small12 ++ C.charts12
def circles12 : List (List Nat) := extendCircles C.circles 12 ++ C.d11

/-! ### The long walks -/

theorem level10 : Level alph9 8 C.big10 :=
  C.level9.transport 8 (by decide) (by decide) (by decide) (by decide)

theorem level11 : Level alph10 9 C.big11 :=
  C.level10.transport 11 (by decide) (by decide) (by decide) (by decide)

theorem level12big : Level alph11 10 C.big12 :=
  C.level11.transport 12 (by decide) (by decide) (by decide) (by decide)

theorem big10_counts : C.big10.flatten.length = 37632 ∧
    (C.big10.flatten.map Row.charge).sum = 18816 := by
  have h := C.level9.transport_counts 8 (by decide) (by decide) (by decide) (by decide)
  rw [C.rowCount9, C.charge9] at h
  exact h

theorem big11_counts : C.big11.flatten.length = 338688 ∧
    (C.big11.flatten.map Row.charge).sum = 169344 := by
  have h := C.level10.transport_counts 11 (by decide) (by decide) (by decide) (by decide)
  rw [C.big10_counts.1, C.big10_counts.2] at h
  exact h

theorem big12_counts : C.big12.flatten.length = 3386880 ∧
    (C.big12.flatten.map Row.charge).sum = 1693440 := by
  have h := C.level11.transport_counts 12 (by decide) (by decide) (by decide) (by decide)
  rw [C.big11_counts.1, C.big11_counts.2] at h
  exact h

/-! ### The short walks and the loops without a row -/

theorem mem_small11 {w : List (Row Nat)} (hw : w ∈ C.small11) :
    ∃ g ∈ C.groups, w ∈ g.walks := List.mem_flatMap.mp hw

theorem mem_d11 {x : List Nat} (hx : x ∈ C.d11) : ∃ g ∈ C.groups, x ∈ g.dloops :=
  List.mem_flatMap.mp hx

theorem small_len {w : List (Row Nat)} (hw : w ∈ C.small11) :
    ∀ r ∈ w, r.base.length = 9 + 1 := by
  obtain ⟨g, hg, hwg⟩ := C.mem_small11 hw
  exact fun r hr => ((C.groupFacts g hg).basedOn w hwg r hr).2.1.length_eq

theorem small_kind {w : List (Row Nat)} (hw : w ∈ C.small11) :
    ∀ r ∈ w, r.visible = r.base.length ∨ r.visible = r.base.length - 2 := by
  obtain ⟨g, hg, hwg⟩ := C.mem_small11 hw
  exact fun r hr => ((C.groupFacts g hg).basedOn w hwg r hr).2.2.2

/-- The nine-fold short walk transported from port 0 lists its transported rows once. -/
theorem small_inventory {w : List (Row Nat)} (hw : w ∈ C.small11) :
    (transportWalk (rep 9 w) 12 0).Perm (Transport.packingRows w 12) := by
  obtain ⟨g, hg, hwg⟩ := C.mem_small11 hw
  exact transportWalk_rep_inventory w 12 9 9 0 (by decide) (C.small_len hw)
    ((C.groupFacts g hg).ports w hwg)

theorem d11_perm {x : List Nat} (hx : x ∈ C.d11) : x.Perm alph10 := by
  obtain ⟨g, hg, hxg⟩ := C.mem_d11 hx
  exact (C.groupFacts g hg).dperm x hxg

theorem sum_map_eq_zero {β : Type} (l : List β) (f : β → Nat) (hf : ∀ x ∈ l, f x = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, hf a (by simp), Nat.zero_add]
    exact ih (fun x hx => hf x (by simp [hx]))

theorem chart_charge (x : List Nat) :
    ((Partition.fullChart x 12 9).map Row.charge).sum = 0 :=
  sum_map_eq_zero _ _ (Partition.fullChart_charge x 12 9)

theorem level12 : Level alph11 10 C.comps12 := by
  have hbig := C.level12big
  refine ⟨?_, ?_, ?_⟩
  · intro rs hrs
    rcases List.mem_append.mp hrs with hrs | hrs
    · rcases List.mem_append.mp hrs with hrs | hrs
      · exact hbig.closed rs hrs
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrs
        obtain ⟨g, hg, hwg⟩ := C.mem_small11 hw
        exact (transported_rep_closed ((C.groupFacts g hg).closed w hwg) (m := 9) (by decide)
          12 9 (by decide) (C.small_len hw) (C.small_kind hw) (Dvd.intro _ rfl) 0
          (by decide)).1
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hrs
      have hl : x.length = 10 := (C.d11_perm hx).length_eq
      exact Partition.fullChart_closedTrail x 12 9 (by omega)
  · intro rs hrs
    rcases List.mem_append.mp hrs with hrs | hrs
    · rcases List.mem_append.mp hrs with hrs | hrs
      · exact hbig.winding rs hrs
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrs
        obtain ⟨g, hg, hwg⟩ := C.mem_small11 hw
        exact (transported_rep_closed ((C.groupFacts g hg).closed w hwg) (m := 9) (by decide)
          12 9 (by decide) (C.small_len hw) (C.small_kind hw) (Dvd.intro _ rfl) 0
          (by decide)).2
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hrs
      have hl : x.length = 10 := (C.d11_perm hx).length_eq
      have he : signedExcess (Partition.fullChart x 12 9) = 10 := by
        unfold signedExcess
        rw [chart_charge, Partition.fullChart_length, hl]
        rfl
      rw [he]
      exact dvd_refl _
  · intro rs hrs
    rcases List.mem_append.mp hrs with hrs | hrs
    · rcases List.mem_append.mp hrs with hrs | hrs
      · exact hbig.basedOn rs hrs
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrs
        obtain ⟨g, hg, hwg⟩ := C.mem_small11 hw
        intro r hr
        exact ((C.groupFacts g hg).basedOn w hwg).transport (by decide) (by decide) r
          ((C.small_inventory hw).mem_iff.mp hr)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hrs
      have hp := C.d11_perm hx
      intro r hr
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
      have h12 : 12 ∉ x := fun hm => (by decide : 12 ∉ alph10) (hp.mem_iff.mp hm)
      have h9 : 9 ∉ x := fun hm => (by decide : 9 ∉ alph10) (hp.mem_iff.mp hm)
      refine ⟨Partition.fullChartAt_valid (hp.nodup_iff.mpr (by decide)) h12 h9 (by decide) j,
        ?_, rfl, Or.inl ?_⟩
      · exact ((rot_perm x j).append_right [12]).trans
          ((hp.append_right [12]).trans List.perm_append_comm)
      · simp [Partition.fullChartAt]

/-! ### Every 2-loop on 12 symbols carries a row -/

/-- On 11 symbols every 2-loop is a row of a long walk, a row of a short walk, or a loop
without a row. -/
theorem complete11 {x : List Nat} (hx : x.Perm alph10) :
    (∃ r ∈ C.big11.flatten, CyclicEq r.base x) ∨
      (∃ w ∈ C.small11, ∃ r ∈ w, CyclicEq r.base x) ∨ (∃ d ∈ C.d11, CyclicEq d x) := by
  have hp1 : x.Perm (alph9 ++ [11]) := hx.trans
    (List.perm_append_comm (l₁ := [11]) (l₂ := alph9))
  obtain ⟨x1, hx1, hb1⟩ := exists_inInsertionBlock_of_perm_append_satellite
    (by decide : alph9.Nodup) (by decide : alph9 ≠ []) (by decide : 11 ∉ alph9) hp1
  have hp0 : x1.Perm (alph8 ++ [8]) := hx1.trans
    (List.perm_append_comm (l₁ := [8]) (l₂ := alph8))
  obtain ⟨x0, hx0, hb0⟩ := exists_inInsertionBlock_of_perm_append_satellite
    (by decide : alph8.Nodup) (by decide : alph8 ≠ []) (by decide : 8 ∉ alph8) hp0
  rcases C.complete9 x0 hx0 with ⟨r, hr, hcyc⟩ | ⟨d, hd, hcyc⟩
  · left
    have hv := (C.level9.basedOn_flatten r hr).1
    obtain ⟨t1, ht1, hc1⟩ := (Transport.rows_cyclicEq_iff_inInsertionBlock hv 8 x1).mpr
      ((InInsertionBlock.congr_base hcyc).mpr hb0)
    have hm1 : t1 ∈ C.big10.flatten :=
      (transportComps_flatten_perm C.walks9 8 7 (by decide)
        (C.level9.len (by decide))).mem_iff.mpr (List.mem_flatMap.mpr ⟨r, hr, ht1⟩)
    have hv1 := (C.level10.basedOn_flatten t1 hm1).1
    obtain ⟨t2, ht2, hc2⟩ := (Transport.rows_cyclicEq_iff_inInsertionBlock hv1 11 x).mpr
      ((InInsertionBlock.congr_base hc1).mpr hb1)
    exact ⟨t2, (transportComps_flatten_perm C.big10 11 8 (by decide)
      (C.level10.len (by decide))).mem_iff.mpr (List.mem_flatMap.mpr ⟨t1, hm1, ht2⟩), hc2⟩
  · right
    obtain ⟨g, hg, hdg⟩ := List.mem_flatMap.mp hd
    obtain ⟨t, ht, htx⟩ := exists_mem_above ((InInsertionBlock.congr_base hcyc).mpr hb0) hb1
    rcases (C.groupFacts g hg).cover d hdg t ht with ⟨r, hr, hrt⟩ | ⟨e, he, het⟩
    · left
      obtain ⟨w, hw, hrw⟩ := List.mem_flatten.mp hr
      exact ⟨w, List.mem_flatMap.mpr ⟨g, hg, hw⟩, r, hrw, hrt.trans htx⟩
    · right
      exact ⟨e, List.mem_flatMap.mpr ⟨g, hg, he⟩, het.trans htx⟩

theorem complete12 : BlockComplete alph11 C.comps12.flatten := by
  intro y hy
  have hp : y.Perm (alph10 ++ [12]) := hy.trans
    (List.perm_append_comm (l₁ := [12]) (l₂ := alph10))
  obtain ⟨x, hx, hb⟩ := exists_inInsertionBlock_of_perm_append_satellite
    (by decide : alph10.Nodup) (by decide : alph10 ≠ []) (by decide : 12 ∉ alph10) hp
  have hflat : ∀ {t : Row Nat} {W : List (Row Nat)}, W ∈ C.comps12 → t ∈ W →
      t ∈ C.comps12.flatten := fun hW ht => List.mem_flatten.mpr ⟨_, hW, ht⟩
  rcases C.complete11 hx with ⟨r, hr, hcyc⟩ | ⟨w, hw, r, hr, hcyc⟩ | ⟨d, hd, hcyc⟩
  · have hv := (C.level11.basedOn_flatten r hr).1
    obtain ⟨t, ht, hty⟩ := (Transport.rows_cyclicEq_iff_inInsertionBlock hv 12 y).mpr
      ((InInsertionBlock.congr_base hcyc).mpr hb)
    have hm : t ∈ C.big12.flatten :=
      (transportComps_flatten_perm C.big11 12 9 (by decide)
        (C.level11.len (by decide))).mem_iff.mpr (List.mem_flatMap.mpr ⟨r, hr, ht⟩)
    obtain ⟨W, hW, htW⟩ := List.mem_flatten.mp hm
    exact ⟨t, hflat (List.mem_append_left _ (List.mem_append_left _ hW)) htW, hty⟩
  · obtain ⟨g, hg, hwg⟩ := C.mem_small11 hw
    have hv := ((C.groupFacts g hg).basedOn w hwg r hr).1
    obtain ⟨t, ht, hty⟩ := (Transport.rows_cyclicEq_iff_inInsertionBlock hv 12 y).mpr
      ((InInsertionBlock.congr_base hcyc).mpr hb)
    have hm : t ∈ transportWalk (rep 9 w) 12 0 :=
      (C.small_inventory hw).mem_iff.mpr (List.mem_flatMap.mpr ⟨r, hr, ht⟩)
    exact ⟨t, hflat (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨w, hw, rfl⟩))) hm, hty⟩
  · obtain ⟨t, ht, hty⟩ := (Partition.fullChart_cyclicEq_iff_inInsertionBlock d y 12 9).mpr
      ((InInsertionBlock.congr_base hcyc).mpr hb)
    exact ⟨t, hflat (List.mem_append_right _ (List.mem_map.mpr ⟨d, hd, rfl⟩)) ht, hty⟩

end Cert

end SuperpermutationUpperBound1771
