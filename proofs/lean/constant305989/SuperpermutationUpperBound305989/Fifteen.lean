import SuperpermutationUpperBound305989.BlockB

/-!
# Fifteen symbols: the selection of step (A) with a block above every loop without a row

In step (A) each of the 6,048 loops without a row on 11 symbols (`Cert.d11`) becomes a full
chart on 12 symbols.  Here it stays without a row for three transports, and on 14 symbols the
1,320 loops above it are filled by the block of `BlockB.lean`, relabelled onto it.  On 15 symbols
the level is

* `core15`: the long and the short walks on 12 symbols (`Cert.big12 ++ Cert.small12`)
  transported three times (letters 13, 14, 15);
* `blocks15`: for every loop `d` of `Cert.d11`, the block above `d` on 15 symbols
  (`BlockData.blockComps d`).

Its connector cycles for the completion on 16 symbols (`circles15`) are the cycles of the long
and short walks (`Cert.circles` with letter 12, and `Cert.gcircles`) extended three times, and
for every `d` the 26 block cycles and 440 loop words relabelled onto `d`.

Counts: 13! rows of total charge 3,084,943,680 = 11771/23760 · 13!, and 5,039,928 cycles
= 23333/2217600 · 12!.
-/

namespace SuperpermutationUpperBound305989

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

/-- The checked block: data, the checks on 14 symbols, the pointer certificates on 16. -/
structure BlockCert where
  data : BlockData
  ok : BlockOK data
  ports : ∀ W ∈ data.trails15, ∃ m, PortsCovered W data.cyc 13 m

theorem Level.mono {A : List Nat} {h : Nat} {l l' : List (List (Row Nat))} (L : Level A h l')
    (hs : ∀ rs ∈ l, rs ∈ l') : Level A h l :=
  ⟨fun rs hr => L.closed rs (hs rs hr), fun rs hr => L.winding rs (hs rs hr),
    fun rs hr => L.basedOn rs (hs rs hr)⟩

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

theorem extend_support {circles : List (List Nat)} {z : Nat}
    (hs : ∀ c ∈ circles, ∀ a ∈ c, a < z ∧ a ≠ 9) (hz9 : z ≠ 9) :
    ∀ c ∈ extendCircles circles z, ∀ a ∈ c, a < z + 1 ∧ a ≠ 9 := by
  intro c hc a ha
  simp only [extendCircles, circleExtensions, fullBases, List.mem_flatMap, List.mem_map,
    List.mem_range] at hc
  obtain ⟨c0, hc0, j, _, rfl⟩ := hc
  rcases List.mem_cons.mp ((insertLetter_perm c0 z j).mem_iff.mp ha) with rfl | ha0
  · exact ⟨by omega, hz9⟩
  · have := hs c0 hc0 a ha0
    omega

theorem extend_valid {circles : List (List Nat)} {z h : Nat} (hv : CircleFamilyValid h circles)
    (hs : ∀ c ∈ circles, ∀ a ∈ c, a < z ∧ a ≠ 9) : CircleFamilyValid (h + 1) (extendCircles circles z) :=
  hv.extend z (fun c hc hm => Nat.lt_irrefl _ (hs c hc z hm).1)

theorem extend_length {circles : List (List Nat)} {z h : Nat} (hv : CircleFamilyValid h circles) :
    (extendCircles circles z).length = h * circles.length :=
  extendCircles_length h circles z (fun c hc => (hv c hc).1)

namespace Cert

variable (C : Cert) (K : BlockCert)

/-! ### The long and short walks, transported three times -/

def core12 : List (List (Row Nat)) := C.big12 ++ C.small12
def core13 : List (List (Row Nat)) := transportComps C.core12 13 10
def core14 : List (List (Row Nat)) := transportComps C.core13 14 11
def core15 : List (List (Row Nat)) := transportComps C.core14 15 12

theorem level_core12 : Level (alphabet 0) 10 C.core12 :=
  C.level12.mono (fun _ h => List.mem_append_left _ h)

theorem level_core13 : Level (alphabet 1) 11 C.core13 :=
  C.level_core12.transport 13 rfl (by decide) (by decide) (by decide)

theorem level_core14 : Level (alphabet 2) 12 C.core14 :=
  C.level_core13.transport 14 rfl (by decide) (by decide) (by decide)

theorem level_core15 : Level (alphabet 3) 13 C.core15 :=
  C.level_core14.transport 15 rfl (by decide) (by decide) (by decide)

theorem core12_counts : C.core12.flatten.length = 3568320 ∧
    (C.core12.flatten.map Row.charge).sum = 1780800 := by
  unfold core12
  rw [List.flatten_append, List.length_append, List.map_append, List.sum_append,
    C.big12_counts.1, C.big12_counts.2, C.small12_counts.1, C.small12_counts.2]
  exact ⟨rfl, rfl⟩

theorem core15_counts : C.core15.flatten.length = 6123237120 ∧
    (C.core15.flatten.map Row.charge).sum = 3055852800 := by
  have h13 := C.level_core12.transport_counts 13 rfl (by decide) (by decide) (by decide)
  have h14 := C.level_core13.transport_counts 14 rfl (by decide) (by decide) (by decide)
  have h15 := C.level_core14.transport_counts 15 rfl (by decide) (by decide) (by decide)
  rw [C.core12_counts.1, C.core12_counts.2] at h13
  change C.core13.flatten.length = _ ∧ (C.core13.flatten.map Row.charge).sum = _ at h13
  rw [h13.1, h13.2] at h14
  change C.core14.flatten.length = _ ∧ (C.core14.flatten.map Row.charge).sum = _ at h14
  rw [h14.1, h14.2] at h15
  exact h15

/-! ### The blocks -/

def blocks15 : List (List (Row Nat)) := C.d11.flatMap fun d => K.data.blockComps d

def comps15 : List (List (Row Nat)) := C.core15 ++ C.blocks15 K

theorem mem_blocks15 {W : List (Row Nat)} (hW : W ∈ C.blocks15 K) :
    ∃ d ∈ C.d11, W ∈ K.data.blockComps d := List.mem_flatMap.mp hW

theorem blocks15_counts : (C.blocks15 K).flatten.length = 103783680 ∧
    ((C.blocks15 K).flatten.map Row.charge).sum = 29090880 := by
  have he : (C.blocks15 K).flatten = C.d11.flatMap (fun d => (K.data.blockComps d).flatten) :=
    flatten_flatMap C.d11 _
  constructor
  · rw [he, length_flatMap_const C.d11 _ 17160 (fun d _ => (BlockData.blockCounts K.ok d).1),
      C.d11_length]
  · rw [he, List.map_flatMap, sum_flatMap_const C.d11 _ 4810
      (fun d _ => (BlockData.blockCounts K.ok d).2), C.d11_length]

theorem counts15 : (C.comps15 K).flatten.length = 6227020800 ∧
    ((C.comps15 K).flatten.map Row.charge).sum = 3084943680 := by
  unfold comps15
  rw [List.flatten_append, List.length_append, List.map_append, List.sum_append,
    C.core15_counts.1, C.core15_counts.2, (C.blocks15_counts K).1, (C.blocks15_counts K).2]
  exact ⟨rfl, rfl⟩

theorem level15 : Level (alphabet 3) 13 (C.comps15 K) := by
  have Lc := C.level_core15
  have Lb : ∀ W ∈ C.blocks15 K, ∃ d ∈ C.d11, W ∈ K.data.blockComps d := fun W hW =>
    C.mem_blocks15 K hW
  refine ⟨?_, ?_, ?_⟩
  · intro W hW
    rcases List.mem_append.mp hW with hW | hW
    · exact Lc.closed W hW
    · obtain ⟨d, hd, hWd⟩ := Lb W hW
      exact (BlockData.blockLevel K.ok (C.d11_perm hd)).closed W hWd
  · intro W hW
    rcases List.mem_append.mp hW with hW | hW
    · exact Lc.winding W hW
    · obtain ⟨d, hd, hWd⟩ := Lb W hW
      exact (BlockData.blockLevel K.ok (C.d11_perm hd)).winding W hWd
  · intro W hW
    rcases List.mem_append.mp hW with hW | hW
    · exact Lc.basedOn W hW
    · obtain ⟨d, hd, hWd⟩ := Lb W hW
      exact (BlockData.blockLevel K.ok (C.d11_perm hd)).basedOn W hWd

/-! ### Every 2-loop on 15 symbols has a row -/

/-- On 12 symbols every 2-loop is a row of a long or short walk, or lies above a loop
without a row. -/
theorem cover12 {x1 : List Nat} (hx1 : x1.Perm alph11) :
    (∃ t ∈ C.core12.flatten, CyclicEq t.base x1) ∨ (∃ d ∈ C.d11, InInsertionBlock 12 d x1) := by
  obtain ⟨x, hx, hb⟩ := peel (by decide : alph10.Nodup) (by decide) (by decide : 12 ∉ alph10) hx1
  rcases C.complete11 hx with ⟨r, hr, hcyc⟩ | ⟨w, hw, r, hr, hcyc⟩ | ⟨d, hd, hcyc⟩
  · left
    have hv := (C.level11.basedOn_flatten r hr).1
    obtain ⟨t, ht, hty⟩ := (Transport.rows_cyclicEq_iff_inInsertionBlock hv 12 x1).mpr
      ((InInsertionBlock.congr_base hcyc).mpr hb)
    have hm : t ∈ C.big12.flatten :=
      (transportComps_flatten_perm C.big11 12 9 (by decide)
        (C.level11.len (by decide))).mem_iff.mpr (List.mem_flatMap.mpr ⟨r, hr, ht⟩)
    obtain ⟨W, hW, htW⟩ := List.mem_flatten.mp hm
    exact ⟨t, List.mem_flatten.mpr ⟨W, List.mem_append_left _ hW, htW⟩, hty⟩
  · left
    obtain ⟨g, hg, hwg⟩ := C.mem_small11 hw
    have hv := ((C.groupFacts g hg).basedOn w hwg r hr).1
    obtain ⟨t, ht, hty⟩ := (Transport.rows_cyclicEq_iff_inInsertionBlock hv 12 x1).mpr
      ((InInsertionBlock.congr_base hcyc).mpr hb)
    have hm : t ∈ transportWalk (rep 9 w) 12 0 :=
      (C.small_inventory hw).mem_iff.mpr (List.mem_flatMap.mpr ⟨r, hr, ht⟩)
    exact ⟨t, List.mem_flatten.mpr ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨w, hw, rfl⟩),
      hm⟩, hty⟩
  · right
    exact ⟨d, hd, (InInsertionBlock.congr_base hcyc).mpr hb⟩

theorem complete15 : BlockComplete (alphabet 3) (C.comps15 K).flatten := by
  intro y hy
  obtain ⟨x, hx, hb⟩ := peel (z := 15) (alphabet_nodup 2) (alphabet_ne 2) (by decide) hy
  obtain ⟨x2, hx2, hb2⟩ := peel (z := 14) (alphabet_nodup 1) (alphabet_ne 1) (by decide) hx
  obtain ⟨x1, hx1, hb1⟩ := peel (z := 13) (alphabet_nodup 0) (alphabet_ne 0) (by decide) hx2
  rcases C.cover12 hx1 with ⟨t, ht, htx⟩ | ⟨d, hd, hdb⟩
  · obtain ⟨t2, ht2, h2⟩ := C.level_core12.cover_transport 13 rfl (by decide) ht htx hb1
    obtain ⟨t3, ht3, h3⟩ := C.level_core13.cover_transport 14 rfl (by decide) ht2 h2 hb2
    obtain ⟨t4, ht4, h4⟩ := C.level_core14.cover_transport 15 rfl (by decide) ht3 h3 hb
    obtain ⟨W, hW, htW⟩ := List.mem_flatten.mp ht4
    exact ⟨t4, List.mem_flatten.mpr ⟨W, List.mem_append_left _ hW, htW⟩, h4⟩
  · obtain ⟨t, ht, htx⟩ := exists_mem_above3 hdb hb1 hb2
    obtain ⟨r, hr, hry⟩ := BlockData.blockCover K.ok (C.d11_perm hd) ht
      ((InInsertionBlock.congr_base htx).mpr hb)
    obtain ⟨W, hW, hrW⟩ := List.mem_flatten.mp hr
    exact ⟨r, List.mem_flatten.mpr ⟨W, List.mem_append_right _
      (List.mem_flatMap.mpr ⟨d, hd, hW⟩), hrW⟩, hry⟩

/-! ### The connector cycles on 16 symbols -/

def coreCircles12 : List (List Nat) := extendCircles C.circles 12 ++ C.gcircles
def coreCircles13 : List (List Nat) := extendCircles C.coreCircles12 13
def coreCircles14 : List (List Nat) := extendCircles C.coreCircles13 14
def coreCircles15 : List (List Nat) := extendCircles C.coreCircles14 15

def circles15 : List (List Nat) := C.coreCircles15 ++ C.d11.flatMap fun d => K.data.blockCircles d

theorem coreCircles12_valid : CircleFamilyValid 10 C.coreCircles12 := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact C.extended_valid c hc
  · exact C.gcircles_valid c hc

theorem coreCircles12_support : ∀ c ∈ C.coreCircles12, ∀ a ∈ c, a < 13 ∧ a ≠ 9 := by
  intro c hc a ha
  have h := C.circles12_support c (List.mem_append_left _ hc) a ha
  exact (by decide : ∀ b ∈ letters12, b < 13 ∧ b ≠ 9) a h

theorem coreCircles13_support : ∀ c ∈ C.coreCircles13, ∀ a ∈ c, a < 14 ∧ a ≠ 9 :=
  extend_support C.coreCircles12_support (by decide)
theorem coreCircles14_support : ∀ c ∈ C.coreCircles14, ∀ a ∈ c, a < 15 ∧ a ≠ 9 :=
  extend_support C.coreCircles13_support (by decide)
theorem coreCircles15_support : ∀ c ∈ C.coreCircles15, ∀ a ∈ c, a < 16 ∧ a ≠ 9 :=
  extend_support C.coreCircles14_support (by decide)

theorem coreCircles13_valid : CircleFamilyValid 11 C.coreCircles13 :=
  extend_valid C.coreCircles12_valid C.coreCircles12_support
theorem coreCircles14_valid : CircleFamilyValid 12 C.coreCircles14 :=
  extend_valid C.coreCircles13_valid C.coreCircles13_support
theorem coreCircles15_valid : CircleFamilyValid 13 C.coreCircles15 :=
  extend_valid C.coreCircles14_valid C.coreCircles14_support

theorem coreCircles15_length : C.coreCircles15.length = 2221560 := by
  have h12 : C.coreCircles12.length = 1683 := by
    unfold coreCircles12
    rw [List.length_append, extend_length C.circles_valid, C.circleCount, C.gcircleCount]
  change (extendCircles C.coreCircles14 15).length = _
  rw [extend_length C.coreCircles14_valid]
  change 12 * (extendCircles C.coreCircles13 14).length = _
  rw [extend_length C.coreCircles13_valid]
  change 12 * (11 * (extendCircles C.coreCircles12 13).length) = _
  rw [extend_length C.coreCircles12_valid, h12]

theorem circles15_length : (C.circles15 K).length = 5039928 := by
  unfold circles15
  rw [List.length_append, C.coreCircles15_length,
    length_flatMap_const C.d11 _ 466 (fun d _ => BlockData.blockCircles_length K.ok d),
    C.d11_length]

theorem circles15_valid : CircleFamilyValid 13 (C.circles15 K) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact C.coreCircles15_valid c hc
  · obtain ⟨d, hd, hcd⟩ := List.mem_flatMap.mp hc
    exact BlockData.blockCircles_valid K.ok (C.d11_perm hd) c hcd

theorem circles15_support : ∀ c ∈ C.circles15 K, ∀ a ∈ c, a < 16 ∧ a ≠ 9 := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact C.coreCircles15_support c hc
  · obtain ⟨d, hd, hcd⟩ := List.mem_flatMap.mp hc
    exact BlockData.blockCircles_support K.ok (C.d11_perm hd) c hcd

theorem safe_core12 : ∀ rs ∈ C.core12, SafeComp rs 10 10 C.coreCircles12 := by
  intro rs hrs
  have hleft : ∀ c ∈ extendCircles C.circles 12, c ∈ C.coreCircles12 :=
    fun c hc => List.mem_append_left _ hc
  have hright : ∀ c ∈ C.gcircles, c ∈ C.coreCircles12 :=
    fun c hc => List.mem_append_right _ hc
  have L := C.level_core12
  rcases List.mem_append.mp hrs with hrs' | hrs'
  · obtain ⟨W, hW, p, hp, rfl⟩ := mem_transportComps.mp hrs'
    exact ((C.bigSafe W hW).transport 12 (by decide) C.circles_valid
      (C.level11.len (by decide) W hW) (C.level11.kind W hW)
      (C.level11.fresh (by decide) W hW) p hp).mono hleft
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrs'
    obtain ⟨g, hg, hwg⟩ := C.mem_small11 hw
    obtain ⟨m, hm⟩ := C.smallPorts g hg w hwg
    exact (hm.safeComp (by decide) (L.len (by decide) _ hrs) (L.kind _ hrs)).mono hright

theorem safe_core15 : ∀ W ∈ C.core15, SafeComp W 10 13 C.coreCircles15 :=
  C.level_core14.safe_transport rfl (by decide) (by decide) C.coreCircles14_valid
    (C.level_core13.safe_transport rfl (by decide) (by decide) C.coreCircles13_valid
      (C.level_core12.safe_transport rfl (by decide) (by decide) C.coreCircles12_valid
        C.safe_core12 13) 14) 15

theorem safe15 : ∀ W ∈ C.comps15 K, SafeComp W 10 13 (C.circles15 K) := by
  intro W hW
  rcases List.mem_append.mp hW with hW | hW
  · exact (C.safe_core15 W hW).mono (fun c hc => List.mem_append_left _ hc)
  · obtain ⟨d, hd, hWd⟩ := C.mem_blocks15 K hW
    exact (BlockData.blockSafe K.ok K.ports W hWd).mono
      (fun c hc => List.mem_append_right _ (List.mem_flatMap.mpr ⟨d, hd, hc⟩))

end Cert

end SuperpermutationUpperBound305989
