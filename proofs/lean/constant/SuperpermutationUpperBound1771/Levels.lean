import SuperpermutationUpperBound1771.Repeat
import SuperpermutationUpperBound.Partition.Basic
import SuperpermutationUpperBound.Partition.FullCharts
import SuperpermutationUpperBound.Completion.Counts
import SuperpermutationUpperBound.Completion.PartitionCoverage
import SuperpermutationUpperBound.Completion.Alphabet
import SuperpermutationUpperBound.Certificates.CirclePointers

/-!
# One level of the construction, as a list of closed trails

A level is a list of closed trails (`comps`) of full and short rows over a common alphabet,
each with signed excess divisible by the number of ports.  Transport and completion act on
the list: every trail is transported, or completed, from every port.  The statements are the
list forms of the lemmas in `CircleTransport/TrackCounts.lean` and `PairPaths.lean`; the
satellite is `9` throughout, as in the rest of the development.

`SafeComp` is `SafeCircleCover` for a single trail, and `PortsCovered` is the pointer
certificate for one trail.
-/

namespace SuperpermutationUpperBound1771

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound.Certificates.CircleBase

/-- Every trail transported from every port. -/
def transportComps (comps : List (List (Row Nat))) (z h : Nat) : List (List (Row Nat)) :=
  comps.flatMap (fun rs => (List.range h).map (fun p => transportWalk rs z p))

/-- Every trail completed from every port. -/
def completionComps (comps : List (List (Row Nat))) (z h : Nat) : List (List (Row Nat)) :=
  comps.flatMap (fun rs => (List.range h).map (fun q => completionWalk rs z q))

theorem mem_transportComps {comps : List (List (Row Nat))} {z h : Nat} {W : List (Row Nat)} :
    W ∈ transportComps comps z h ↔ ∃ rs ∈ comps, ∃ p, p < h ∧ W = transportWalk rs z p := by
  simp only [transportComps, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨rs, hrs, p, hp, rfl⟩
    exact ⟨rs, hrs, p, hp, rfl⟩
  · rintro ⟨rs, hrs, p, hp, rfl⟩
    exact ⟨rs, hrs, p, hp, rfl⟩

theorem mem_completionComps {comps : List (List (Row Nat))} {z h : Nat} {W : List (Row Nat)} :
    W ∈ completionComps comps z h ↔ ∃ rs ∈ comps, ∃ q, q < h ∧ W = completionWalk rs z q := by
  simp only [completionComps, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨rs, hrs, p, hp, rfl⟩
    exact ⟨rs, hrs, p, hp, rfl⟩
  · rintro ⟨rs, hrs, p, hp, rfl⟩
    exact ⟨rs, hrs, p, hp, rfl⟩

/-- Closed trails over the alphabet `A`, with `h` ports and divisible signed excess. -/
structure Level (A : List Nat) (h : Nat) (comps : List (List (Row Nat))) : Prop where
  closed : ∀ rs ∈ comps, ClosedTrail rs
  winding : ∀ rs ∈ comps, (h : Int) ∣ signedExcess rs
  basedOn : ∀ rs ∈ comps, BasedOn A 9 rs

variable {A : List Nat} {h : Nat} {comps : List (List (Row Nat))}

theorem Level.basedOn_flatten (L : Level A h comps) : BasedOn A 9 comps.flatten := by
  intro r hr
  obtain ⟨rs, hrs, hr⟩ := List.mem_flatten.mp hr
  exact L.basedOn rs hrs r hr

theorem Level.len (L : Level A h comps) (hA : A.length = h + 1) :
    ∀ rs ∈ comps, ∀ r ∈ rs, r.base.length = h + 1 :=
  fun rs hrs r hr => (L.basedOn rs hrs r hr).2.1.length_eq.trans hA

theorem Level.kind (L : Level A h comps) :
    ∀ rs ∈ comps, ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2 :=
  fun rs hrs r hr => (L.basedOn rs hrs r hr).2.2.2

theorem Level.fresh (L : Level A h comps) {z : Nat} (hz : z ∉ A) :
    ∀ rs ∈ comps, ∀ r ∈ rs, z ∉ r.base :=
  fun rs hrs r hr hm => hz ((L.basedOn rs hrs r hr).2.1.mem_iff.mp hm)

/-! ### Transport -/

theorem range_transportWalk_perm (rs : List (Row Nat)) (z h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1) :
    ((List.range h).map (fun p => transportWalk rs z p)).flatten.Perm
      (Transport.packingRows rs z) := by
  have h2 := transportWalk_inventory rs z h hn hlen
  have h3 : (List.finRange h).flatMap (fun p => transportWalk rs z p.val) =
      ((List.range h).map (fun p => transportWalk rs z p)).flatten := by
    rw [← List.flatMap_def, ← map_val_finRange h, List.flatMap_map]
  rw [h3] at h2
  exact h2

theorem transportComps_flatten_perm (comps : List (List (Row Nat))) (z h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ rs ∈ comps, ∀ r ∈ rs, r.base.length = h + 1) :
    (transportComps comps z h).flatten.Perm (Transport.packingRows comps.flatten z) := by
  induction comps with
  | nil => simp [transportComps, Transport.packingRows]
  | cons rs rest ih =>
    have h1 := range_transportWalk_perm rs z h hn (hlen rs (by simp))
    have h2 := ih (fun rs' hrs' => hlen rs' (by simp [hrs']))
    have he : (transportComps (rs :: rest) z h).flatten =
        ((List.range h).map (fun p => transportWalk rs z p)).flatten ++
          (transportComps rest z h).flatten := by
      simp [transportComps, List.flatMap_cons, List.flatten_append]
    have hp : Transport.packingRows (rs :: rest).flatten z =
        Transport.packingRows rs z ++ Transport.packingRows rest.flatten z := by
      simp [Transport.packingRows, List.flatten_cons, List.flatMap_append]
    rw [he, hp]
    exact h1.append h2

/-- Transport of a level is a level, one letter and one port larger. -/
theorem Level.transport (L : Level A h comps) (z : Nat) (hA : A.length = h + 1)
    (hn : 3 ≤ h + 1) (hz : z ∉ A) (hz9 : z ≠ 9) :
    Level (z :: A) (h + 1) (transportComps comps z h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨rs, hrs, p, hp, rfl⟩ := mem_transportComps.mp hW
    exact transportWalk_closedTrail (L.closed rs hrs) z h hn (L.len hA rs hrs) (L.kind rs hrs)
      (L.winding rs hrs) p hp
  · intro W hW
    obtain ⟨rs, hrs, p, hp, rfl⟩ := mem_transportComps.mp hW
    exact transportWalk_winding_divisible rs z h hn (L.len hA rs hrs) (L.kind rs hrs)
      (L.winding rs hrs) p hp
  · intro W hW r hr
    obtain ⟨rs, hrs, p, hp, rfl⟩ := mem_transportComps.mp hW
    have hperm := range_transportWalk_perm rs z h hn (L.len hA rs hrs)
    have hm : r ∈ Transport.packingRows rs z :=
      hperm.mem_iff.mp (List.mem_flatten.mpr
        ⟨_, List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩, hr⟩)
    exact (L.basedOn rs hrs).transport hz hz9 r hm

theorem Level.transport_counts (L : Level A h comps) (z : Nat) (hA : A.length = h + 1)
    (hn : 3 ≤ h + 1) (hz : z ∉ A) (hz9 : z ≠ 9) :
    (transportComps comps z h).flatten.length = (h + 1) * comps.flatten.length ∧
    ((transportComps comps z h).flatten.map Row.charge).sum =
      (h + 1) * (comps.flatten.map Row.charge).sum := by
  have hp := transportComps_flatten_perm comps z h hn (L.len hA)
  have hc := Transport.packingRows_counts comps.flatten z A.length
    (L.basedOn_flatten.ready hz hz9)
  rw [hA] at hc
  exact ⟨hp.length_eq.trans hc.1, ((hp.map Row.charge).sum_eq).trans hc.2.1⟩

/-! ### Completion -/

/-- `Iterated.completionWalk_closed` for an arbitrary completion letter. -/
theorem completionWalk_closed {rs : List (Row Nat)} (hc : ClosedTrail rs) (final : Nat)
    (h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hw : (h : Int) ∣ signedExcess rs) (p : Nat) (hp : p < h) :
    ClosedTrail (completionWalk rs final p) := by
  have hne := completionWalk_nonempty rs final p hc.1
  have hchain : RowTrailCompatible (rs.head hc.1) rs.tail := by
    cases rs with
    | nil => exact False.elim (hc.1 rfl)
    | cons r rs => exact closedTrail_internal hc
  have hi := completionWalk_internal rs hc.1 final (h + 1) p hn (by omega) hlen hkind hchain
  have hb : ((completionWalk rs final p).getLast hne).Compatible
      ((completionWalk rs final p).head hne) := by
    change _ = _
    rw [completionWalk_last_tail rs hc.1 final (h + 1) p hn (by omega) hlen hkind,
      completionWalk_head rs hc.1 final (h + 1) p hn (by omega) hlen hkind,
      completionExit_eq_self_of_winding rs h hn hlen hkind hw p hp,
      closedTrail_last_compatible_head hc]
  have hr := pathRunsTo_of_path_spec _ _ hne hi hb
  obtain ⟨a, as, he⟩ := List.exists_cons_of_ne_nil hne
  simp only [he, List.head_cons] at hr
  rw [he]
  exact closedTrail_of_pathRunsTo hr

theorem range_completionWalk_perm (rs : List (Row Nat)) (z h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ((List.range h).map (fun q => completionWalk rs z q)).flatten.Perm
      (rs.flatMap (fun r => Completion.completeRows r z)) := by
  have h2 := completionWalk_inventory rs z (h + 1) hn hlen hkind
  have h3 : (List.finRange (h + 1 - 1)).flatMap (fun q => completionWalk rs z q.val) =
      ((List.range h).map (fun q => completionWalk rs z q)).flatten := by
    rw [← List.flatMap_def, show List.range h = List.range (h + 1 - 1) by simp,
      ← map_val_finRange (h + 1 - 1), List.flatMap_map]
  rw [h3] at h2
  exact h2

theorem completionComps_flatten_perm (comps : List (List (Row Nat))) (z h : Nat)
    (hn : 3 ≤ h + 1) (hlen : ∀ rs ∈ comps, ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ rs ∈ comps, ∀ r ∈ rs,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    (completionComps comps z h).flatten.Perm (Completion.packingRows comps.flatten z) := by
  induction comps with
  | nil => simp [completionComps, Completion.packingRows]
  | cons rs rest ih =>
    have h1 := range_completionWalk_perm rs z h hn (hlen rs (by simp)) (hkind rs (by simp))
    have h2 := ih (fun rs' hrs' => hlen rs' (by simp [hrs']))
      (fun rs' hrs' => hkind rs' (by simp [hrs']))
    have he : (completionComps (rs :: rest) z h).flatten =
        ((List.range h).map (fun q => completionWalk rs z q)).flatten ++
          (completionComps rest z h).flatten := by
      simp [completionComps, List.flatMap_cons, List.flatten_append]
    have hp : Completion.packingRows (rs :: rest).flatten z =
        rs.flatMap (fun r => Completion.completeRows r z) ++
          Completion.packingRows rest.flatten z := by
      simp [Completion.packingRows, List.flatten_cons, List.flatMap_append]
    rw [he, hp]
    exact h1.append h2

theorem Level.completion_closed (L : Level A h comps) (z : Nat) (hA : A.length = h + 1)
    (hn : 3 ≤ h + 1) : ∀ W ∈ completionComps comps z h, ClosedTrail W := by
  intro W hW
  obtain ⟨rs, hrs, q, hq, rfl⟩ := mem_completionComps.mp hW
  exact completionWalk_closed (L.closed rs hrs) z h hn (L.len hA rs hrs) (L.kind rs hrs)
    (L.winding rs hrs) q hq

/-! ### Connector cycles for one trail -/

/-- `SafeCircleCover` for a single trail: from every port, a cycle is incident. -/
def SafeComp (rs : List (Row Nat)) (final h : Nat) (circles : List (List Nat)) : Prop :=
  ∀ j : Fin h, ∃ c ∈ circles, SafeIncidence rs final j c

theorem SafeComp.mono {rs : List (Row Nat)} {final h : Nat} {circles circles' : List (List Nat)}
    (hs : SafeComp rs final h circles) (hsub : ∀ c ∈ circles, c ∈ circles') :
    SafeComp rs final h circles' := by
  intro j
  obtain ⟨c, hc, hi⟩ := hs j
  exact ⟨c, hsub c hc, hi⟩

theorem SafeComp.transport {rs : List (Row Nat)} {final h : Nat} {circles : List (List Nat)}
    (hs : SafeComp rs final h circles) (newOrd : Nat) (hn : 3 ≤ h + 1)
    (hvalid : CircleFamilyValid h circles)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hfresh : ∀ r ∈ rs, final ∉ r.base) (p : Nat) (hp : p < h) :
    SafeComp (transportWalk rs newOrd p) final (h + 1) (extendCircles circles newOrd) := by
  have ht := SafeCircleCover.transport (fun _ : Unit => rs) newOrd final h hn circles hvalid
    (fun _ => hlen) (fun _ => hkind) (fun _ => hfresh) (fun _ => hs)
  exact fun q => ht ((), ⟨p, hp⟩) q

theorem SafeComp.sound {rs : List (Row Nat)} {final h : Nat} {circles : List (List Nat)}
    (hs : SafeComp rs final h circles) (hv : CircleFamilyValid h circles) (hn : 3 ≤ h + 1)
    (q : Fin h) :
    ∃ c ∈ circles, ∃ v, HeadVertex (completionWalk rs final q.val) v ∧ CircleVertex c v := by
  have hc : SafeCircleCover (fun _ : Unit => rs) final h circles := fun _ => hs
  obtain ⟨c, hcm, v, hv', hcv⟩ := hc.sound hv hn ((), q)
  exact ⟨c, hcm, v, hv', hcv⟩

/-- A full chart is covered by the cycle of its base word. -/
theorem SafeComp.fullChart (x : List Nat) (active satellite final h : Nat)
    (circles : List (List Nat)) (hx : x ∈ circles) (hne : x ≠ []) :
    SafeComp (Partition.fullChart x active satellite) final h circles :=
  fun _ => ⟨x, hx, Or.inr ⟨x, active, satellite,
    ⟨⟨0, List.length_pos_iff.mpr hne⟩, List.rotateLeft_zero⟩, rfl⟩⟩

/-- The pointer certificate for one trail `W`: for every port a valid pointer
(`MixedPointer.Valid`, with `W` as the only component). -/
def PortsCovered (W : List (Row Nat)) (circles : List (List Nat)) (h : Nat)
    (ptrs : List MixedPointer) : Prop :=
  ∀ j < h, ∃ p ∈ ptrs, p.component = 0 ∧ p.port = j ∧ p.Valid [W] circles 10 h

instance (W : List (Row Nat)) (circles : List (List Nat)) (h : Nat) (ptrs : List MixedPointer) :
    Decidable (PortsCovered W circles h ptrs) := by
  unfold PortsCovered
  infer_instance

theorem PortsCovered.safeComp {W : List (Row Nat)} {circles : List (List Nat)} {h : Nat}
    {ptrs : List MixedPointer} (hp : PortsCovered W circles h ptrs) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ W, r.base.length = h + 1)
    (hkind : ∀ r ∈ W, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    SafeComp W 10 h circles := by
  intro j
  obtain ⟨p, _, hc, hpj, hv⟩ := hp j.val j.isLt
  have hcomp : componentAt [W] p.component = W := by rw [hc]; rfl
  have hs := p.sound hv hn (by rw [hcomp]; exact hlen) (by rw [hcomp]; exact hkind)
  have he : (⟨p.port, hv.2.1⟩ : Fin h) = j := Fin.ext hpj
  rw [he] at hs
  rw [hcomp] at hs
  exact ⟨circleAt circles p.circle, circleAt_mem circles p.circle hv.2.2.1, hs⟩

end SuperpermutationUpperBound1771
