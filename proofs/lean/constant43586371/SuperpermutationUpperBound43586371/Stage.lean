import SuperpermutationUpperBound43586371.BlockUp

/-!
# Stages: a level with loops still waiting for a block

A `Stage A0 z comps circles pending R Q c P` is the state of the construction one level after
some loops were left without a row:

* `comps` is a level on the letters `z :: A0` (`h = A0.length` ports), met by `circles`;
* `pending` are loops on `A0` (one level lower) that have no row;
* every 2-loop on `z :: A0` is a row, or lies one level above a pending loop;
* `R`, `Q`, `c`, `P` count the rows, their total charge, the cycles and the pending loops.

`Stage.advance` carries a stage three levels up and puts a block (`BlockFam`, `BlockUp.lean`)
above every pending loop: the old trails are transported three times and the cycles extended
three times (the pending loops stay without a row for two levels), the block trails come in at
the last level, and the loops without a row of the blocks become the new pending loops.
`Stage.close` makes every pending loop a full chart one level up, met by the cycle of its own
word, which gives a `Closed` level (every 2-loop has a row).

The first stage is the selection of step (A) on 12 symbols (`Cert.stage12`): its long and short
walks, with the 6,048 loops of `Cert.d11` pending.  This is the recursion of
the derivation of the nested constants, written as a statement about levels.
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

theorem not_mem_ten {a : Nat} {L : List Nat} (h10 : a ≠ 10) (h : a ∉ L) : a ∉ 10 :: L := by
  intro hm
  rcases List.mem_cons.mp hm with hm | hm
  · exact h10 hm
  · exact h hm

theorem extend_mem10 {circles : List (List Nat)} {z : Nat} {L : List Nat}
    (hs : ∀ c ∈ circles, ∀ a ∈ c, a ∈ 10 :: L) :
    ∀ c ∈ extendCircles circles z, ∀ a ∈ c, a ∈ 10 :: z :: L := by
  intro c hc a ha
  have h := extend_mem hs c hc a ha
  simp only [List.mem_cons] at h ⊢
  tauto

structure Stage (A0 : List Nat) (z : Nat) (comps : List (List (Row Nat)))
    (circles : List (List Nat)) (pending : List (List Nat)) (R Q c P : Nat) : Prop where
  two : 2 ≤ A0.length
  nodup : (z :: A0).Nodup
  nine : 9 ∉ z :: A0
  ten : 10 ∉ z :: A0
  level : Level (z :: A0) A0.length comps
  valid : CircleFamilyValid A0.length circles
  support : ∀ c ∈ circles, ∀ a ∈ c, a ∈ 10 :: z :: A0
  safe : ∀ rs ∈ comps, SafeComp rs 10 A0.length circles
  pend : ∀ e ∈ pending, e.Perm A0
  cover : ∀ y : List Nat, y.Perm (z :: A0) →
    (∃ r ∈ comps.flatten, CyclicEq r.base y) ∨ (∃ e ∈ pending, InInsertionBlock z e y)
  rows : comps.flatten.length = R
  charge : (comps.flatten.map Row.charge).sum = Q
  ncirc : circles.length = c
  npend : pending.length = P

/-- A level on `A` with `h` ports in which every 2-loop has a row, met by its cycles. -/
structure Closed (A : List Nat) (h : Nat) (comps : List (List (Row Nat)))
    (circles : List (List Nat)) (R Q c : Nat) : Prop where
  hA : A.length = h + 1
  two : 2 ≤ h
  nodup : A.Nodup
  nine : 9 ∉ A
  ten : 10 ∉ A
  level : Level A h comps
  complete : BlockComplete A comps.flatten
  valid : CircleFamilyValid h circles
  support : ∀ c ∈ circles, ∀ a ∈ c, a ∈ 10 :: A
  safe : ∀ rs ∈ comps, SafeComp rs 10 h circles
  rows : comps.flatten.length = R
  charge : (comps.flatten.map Row.charge).sum = Q
  ncirc : circles.length = c

namespace Stage

/-- The old trails, three levels up. -/
def comps3 (comps : List (List (Row Nat))) (K : BlockFam) (h : Nat) : List (List (Row Nat)) :=
  transportComps (transportComps (transportComps comps K.F.t2 h) K.F.t3 (h + 1)) K.F.z (h + 1 + 1)

/-- The old cycles, extended three times. -/
def circles3 (circles : List (List Nat)) (K : BlockFam) : List (List Nat) :=
  extendCircles (extendCircles (extendCircles circles K.F.t2) K.F.t3) K.F.z

def advComps (comps : List (List (Row Nat))) (pending : List (List Nat)) (K : BlockFam)
    (h : Nat) : List (List (Row Nat)) :=
  comps3 comps K h ++ pending.flatMap (K.trailsR)

def advCircles (circles : List (List Nat)) (pending : List (List Nat)) (K : BlockFam) :
    List (List Nat) :=
  circles3 circles K ++ pending.flatMap (K.circlesR)

def advPending (pending : List (List Nat)) (K : BlockFam) : List (List Nat) :=
  pending.flatMap (K.loopsR)

def closeComps (comps : List (List (Row Nat))) (pending : List (List Nat)) (z : Nat) :
    List (List (Row Nat)) :=
  comps ++ pending.map (fun e => Partition.fullChart e z 9)

theorem congr {A0 : List Nat} {z : Nat} {comps : List (List (Row Nat))}
    {circles : List (List Nat)} {pending : List (List Nat)} {R Q c P R' Q' c' P' : Nat}
    (S : Stage A0 z comps circles pending R Q c P) (hR : R = R') (hQ : Q = Q') (hc : c = c')
    (hP : P = P') : Stage A0 z comps circles pending R' Q' c' P' := by
  subst hR hQ hc hP
  exact S

variable {A0 : List Nat} {z : Nat} {comps : List (List (Row Nat))} {circles : List (List Nat)}
  {pending : List (List Nat)} {R Q c P : Nat}

/-- Three levels up, with the block `K` above every pending loop. -/
theorem advance (S : Stage A0 z comps circles pending R Q c P) (K : BlockFam)
    (hd0 : K.F.d0.Perm A0) (ht1 : K.F.t1 = z) :
    Stage (K.F.t3 :: K.F.t2 :: z :: A0) K.F.z (advComps comps pending K A0.length)
      (advCircles circles pending K) (advPending pending K)
      ((A0.length + 3) * ((A0.length + 2) * ((A0.length + 1) * R)) +
        P * ((A0.length + 3) * K.nrows))
      ((A0.length + 3) * ((A0.length + 2) * ((A0.length + 1) * Q)) +
        P * ((A0.length + 3) * K.nq))
      ((A0.length + 2) * ((A0.length + 1) * (A0.length * c)) +
        P * K.ncirc)
      (P * K.nd) := by
  have hF := K.frame
  have hlen : K.F.d0.length = A0.length := hd0.length_eq
  have hFh : K.F.h + 1 = A0.length + 3 := by unfold Frame.h; omega
  have hAp0 : K.F.alph.Perm (K.F.t3 :: K.F.t2 :: z :: A0) := by
    unfold Frame.alph
    rw [ht1]
    exact ((hd0.cons _).cons _).cons _
  have hAp : K.F.alph'.Perm (K.F.z :: K.F.t3 :: K.F.t2 :: z :: A0) := hAp0.cons _
  have hnew : (K.F.z :: K.F.t3 :: K.F.t2 :: z :: A0).Nodup := hAp.nodup_iff.mp hF.alph'_nodup
  have n1 := List.nodup_cons.mp hnew
  have n2 := List.nodup_cons.mp n1.2
  have n3 := List.nodup_cons.mp n2.2
  have h9 : ∀ a ∈ K.F.z :: K.F.t3 :: K.F.t2 :: z :: A0, a ≠ 9 :=
    fun a ha he => hF.2.1 (hAp.mem_iff.mpr (he ▸ ha))
  have h10 : ∀ a ∈ K.F.z :: K.F.t3 :: K.F.t2 :: z :: A0, a ≠ 10 :=
    fun a ha he => hF.2.2 (hAp.mem_iff.mpr (he ▸ ha))
  have hn : 3 ≤ A0.length + 1 := by have := S.two; omega
  have hpe : ∀ e ∈ pending, e.Perm K.F.d0 := fun e he => (S.pend e he).trans hd0.symm
  -- levels
  have L0 := S.level
  have L1 := L0.transport K.F.t2 rfl hn n3.1 (h9 _ (by simp))
  have L2 := L1.transport K.F.t3 rfl (by omega) n2.1 (h9 _ (by simp))
  have L3 := L2.transport K.F.z rfl (by omega) n1.1 (h9 _ (by simp))
  have LB : Level (K.F.z :: K.F.t3 :: K.F.t2 :: z :: A0) (A0.length + 3)
      (pending.flatMap (K.trailsR)) :=
    Level.flatMap pending _ (fun e he => (K.level e (hpe e he)).congr hAp hFh)
  -- cycles
  have V1 := extend_valid S.valid S.support (not_mem_ten (h10 _ (by simp)) n3.1)
  have s1 := extend_mem10 (z := K.F.t2) S.support
  have V2 := extend_valid V1 s1 (not_mem_ten (h10 _ (by simp)) n2.1)
  have s2 := extend_mem10 (z := K.F.t3) s1
  have V3 := extend_valid V2 s2 (not_mem_ten (h10 _ (by simp)) n1.1)
  have s3 := extend_mem10 (z := K.F.z) s2
  have hten1 : 10 ∉ K.F.t2 :: z :: A0 :=
    fun hm => h10 10 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)) rfl
  have hten2 : 10 ∉ K.F.t3 :: K.F.t2 :: z :: A0 := fun hm => h10 10 (List.mem_cons_of_mem _ hm) rfl
  have S1 := L0.safe_transport rfl hn S.ten S.valid S.safe K.F.t2
  have S2 := L1.safe_transport rfl (by omega) hten1 V1 S1 K.F.t3
  have S3 := L2.safe_transport rfl (by omega) hten2 V2 S2 K.F.z
  refine ⟨by simp only [List.length_cons]; omega, hnew, fun hm => h9 9 hm rfl, fun hm => h10 10 hm rfl,
    L3.append LB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- valid
    intro cc hc
    rcases List.mem_append.mp hc with hc | hc
    · exact V3 cc hc
    · obtain ⟨e, he, hce⟩ := List.mem_flatMap.mp hc
      have := K.valid e (hpe e he) cc hce
      rw [hFh] at this
      exact this
  · -- support
    intro cc hc a ha
    rcases List.mem_append.mp hc with hc | hc
    · exact s3 cc hc a ha
    · obtain ⟨e, he, hce⟩ := List.mem_flatMap.mp hc
      have h := K.support e (hpe e he) cc hce a ha
      rcases List.mem_cons.mp h with h | h
      · subst h; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hAp.mem_iff.mp h)
  · -- safe
    intro W hW
    rcases List.mem_append.mp hW with hW | hW
    · exact (S3 W hW).mono (fun cc hc => List.mem_append_left _ hc)
    · obtain ⟨e, he, hWe⟩ := List.mem_flatMap.mp hW
      have h := K.safe e (hpe e he) W hWe
      rw [hFh] at h
      exact h.mono (fun cc hc => List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hc⟩))
  · -- pending
    intro e' he'
    obtain ⟨e, he, he'⟩ := List.mem_flatMap.mp he'
    exact (K.loops_perm e (hpe e he) e' he').trans hAp0
  · -- cover
    intro y hy
    obtain ⟨x3, hx3, hb⟩ := peel n1.2 (List.cons_ne_nil _ _) n1.1 hy
    obtain ⟨x2, hx2, hb2⟩ := peel n2.2 (List.cons_ne_nil _ _) n2.1 hx3
    obtain ⟨x1, hx1, hb1⟩ := peel n3.2 (List.cons_ne_nil _ _) n3.1 hx2
    rcases S.cover x1 hx1 with ⟨r, hr, hrx⟩ | ⟨e, he, heb⟩
    · obtain ⟨t2, ht2, h2⟩ := L0.cover_transport K.F.t2 rfl hn hr hrx hb1
      obtain ⟨t3, ht3, h3⟩ := L1.cover_transport K.F.t3 rfl (by omega) ht2 h2 hb2
      obtain ⟨t4, ht4, h4⟩ := L2.cover_transport K.F.z rfl (by omega) ht3 h3 hb
      left
      obtain ⟨W, hW, htW⟩ := List.mem_flatten.mp ht4
      exact ⟨t4, List.mem_flatten.mpr ⟨W, List.mem_append_left _ hW, htW⟩, h4⟩
    · rw [← ht1] at heb
      obtain ⟨t, ht, htx⟩ := exists_mem_above3T heb hb1 hb2
      have hbt : InInsertionBlock K.F.z t y := (InInsertionBlock.congr_base htx).mpr hb
      rcases K.cover e (hpe e he) t ht with hrow | ⟨e', he', het⟩
      · left
        obtain ⟨r, hr, hry⟩ := hrow y hbt
        obtain ⟨W, hW, hrW⟩ := List.mem_flatten.mp hr
        exact ⟨r, List.mem_flatten.mpr ⟨W, List.mem_append_right _
          (List.mem_flatMap.mpr ⟨e, he, hW⟩), hrW⟩, hry⟩
      · right
        exact ⟨e', List.mem_flatMap.mpr ⟨e, he, he'⟩, (InInsertionBlock.congr_base het).mpr hbt⟩
  · -- rows
    have c1 := L0.transport_counts K.F.t2 rfl hn n3.1 (h9 _ (by simp))
    have c2 := L1.transport_counts K.F.t3 rfl (by omega) n2.1 (h9 _ (by simp))
    have c3 := L2.transport_counts K.F.z rfl (by omega) n1.1 (h9 _ (by simp))
    have hbl : (pending.flatMap (K.trailsR)).flatten.length =
        P * ((A0.length + 3) * K.nrows) := by
      rw [flatten_flatMap, length_flatMap_const pending _ ((K.F.h + 1) * K.nrows)
        (fun e _ => K.rows e), S.npend, hFh]
    unfold advComps comps3
    rw [List.flatten_append, List.length_append, hbl, c3.1, c2.1, c1.1, S.rows]
  · -- charge
    have c1 := L0.transport_counts K.F.t2 rfl hn n3.1 (h9 _ (by simp))
    have c2 := L1.transport_counts K.F.t3 rfl (by omega) n2.1 (h9 _ (by simp))
    have c3 := L2.transport_counts K.F.z rfl (by omega) n1.1 (h9 _ (by simp))
    have hbl : ((pending.flatMap (K.trailsR)).flatten.map Row.charge).sum =
        P * ((A0.length + 3) * K.nq) := by
      rw [flatten_flatMap, List.map_flatMap, sum_flatMap_const pending _ ((K.F.h + 1) * K.nq)
        (fun e _ => K.charge e), S.npend, hFh]
    unfold advComps comps3
    rw [List.flatten_append, List.map_append, List.sum_append, hbl, c3.2, c2.2, c1.2, S.charge]
  · -- cycles
    have hbl : (pending.flatMap (K.circlesR)).length = P * K.ncirc := by
      rw [length_flatMap_const pending _ K.ncirc (fun e _ => K.ncircR e), S.npend]
    unfold advCircles circles3
    rw [List.length_append, hbl, extend_length V2, extend_length V1, extend_length S.valid,
      S.ncirc]
  · -- pending
    unfold advPending
    rw [length_flatMap_const pending _ K.nd (fun e _ => K.nloops e), S.npend]

theorem chart_basedOn {A0 : List Nat} {z : Nat} {e : List Nat} (hp : e.Perm A0)
    (hnd : (z :: A0).Nodup) (h9 : 9 ∉ z :: A0) :
    BasedOn (z :: A0) 9 (Partition.fullChart e z 9) := by
  intro r hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  have hz : z ∉ e := fun hm => (List.nodup_cons.mp hnd).1 (hp.mem_iff.mp hm)
  have he9 : 9 ∉ e := fun hm => h9 (List.mem_cons_of_mem _ (hp.mem_iff.mp hm))
  have h9z : (9 : Nat) ≠ z := by intro h; apply h9; rw [h]; exact List.mem_cons_self
  refine ⟨Partition.fullChartAt_valid (hp.nodup_iff.mpr (List.nodup_cons.mp hnd).2) hz he9 h9z j,
    ?_, rfl, Or.inl ?_⟩
  · exact ((rot_perm e j).append_right [z]).trans ((hp.append_right [z]).trans List.perm_append_comm)
  · simp [Partition.fullChartAt]

/-- Every pending loop becomes a full chart; every 2-loop now has a row. -/
theorem close (S : Stage A0 z comps circles pending R Q c P) :
    Closed (z :: A0) A0.length (closeComps comps pending z) (circles ++ pending)
      (R + P * A0.length) Q (c + P) := by
  have hcharts : Level (z :: A0) A0.length (pending.map (fun e => Partition.fullChart e z 9)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro W hW
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hW
      exact Partition.fullChart_closedTrail e z 9 (by rw [(S.pend e he).length_eq]; have := S.two; omega)
    · intro W hW
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hW
      have hx : signedExcess (Partition.fullChart e z 9) = A0.length := by
        unfold signedExcess
        rw [Partition.fullChart_charge_sum, Partition.fullChart_length, (S.pend e he).length_eq]
        simp
      rw [hx]
    · intro W hW
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hW
      exact chart_basedOn (S.pend e he) S.nodup S.nine
  refine ⟨rfl, S.two, S.nodup, S.nine, S.ten, S.level.append hcharts, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rcases S.cover y hy with ⟨r, hr, hry⟩ | ⟨e, he, heb⟩
    · obtain ⟨W, hW, hrW⟩ := List.mem_flatten.mp hr
      exact ⟨r, List.mem_flatten.mpr ⟨W, List.mem_append_left _ hW, hrW⟩, hry⟩
    · obtain ⟨r, hr, hry⟩ := (Partition.fullChart_cyclicEq_iff_inInsertionBlock e y z 9).mpr heb
      exact ⟨r, List.mem_flatten.mpr ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩),
        hr⟩, hry⟩
  · intro cc hc
    rcases List.mem_append.mp hc with hc | hc
    · exact S.valid cc hc
    · have hp := S.pend cc hc
      exact ⟨hp.length_eq, hp.nodup_iff.mpr (List.nodup_cons.mp S.nodup).2⟩
  · intro cc hc a ha
    rcases List.mem_append.mp hc with hc | hc
    · exact S.support cc hc a ha
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ((S.pend cc hc).mem_iff.mp ha))
  · intro W hW
    rcases List.mem_append.mp hW with hW | hW
    · exact (S.safe W hW).mono (fun cc hc => List.mem_append_left _ hc)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hW
      have hl := (S.pend e he).length_eq
      exact SafeComp.fullChart e z 9 10 A0.length _ (List.mem_append_right _ he)
        (by intro h0; have := S.two; rw [h0, List.length_nil] at hl; omega)
  · unfold closeComps
    rw [List.flatten_append, List.length_append, S.rows, ← List.flatMap_def,
      length_flatMap_const pending _ A0.length (fun e he => by
        rw [Partition.fullChart_length, (S.pend e he).length_eq]), S.npend]
  · unfold closeComps
    rw [List.flatten_append, List.map_append, List.sum_append, S.charge]
    have h0 : ((pending.map (fun e => Partition.fullChart e z 9)).flatten.map Row.charge).sum = 0 :=
      Cert.sum_map_eq_zero _ _ (fun r hr => by
        obtain ⟨W, hW, hrW⟩ := List.mem_flatten.mp hr
        obtain ⟨e, _, rfl⟩ := List.mem_map.mp hW
        exact Partition.fullChart_charge e z 9 r hrW)
    rw [h0, Nat.add_zero]
  · rw [List.length_append, S.ncirc, S.npend]

end Stage

/-! ### The first stage: step (A) on 12 symbols, the loops of `d11` pending -/

namespace Cert

variable (C : Cert)

def core12 : List (List (Row Nat)) := C.big12 ++ C.small12

def coreCircles12 : List (List Nat) := extendCircles C.circles 12 ++ C.gcircles

theorem level_core12 : Level (alphabet 0) 10 C.core12 :=
  C.level12.mono (fun _ h => List.mem_append_left _ h)

theorem core12_counts : C.core12.flatten.length = 3568320 ∧
    (C.core12.flatten.map Row.charge).sum = 1780800 := by
  unfold core12
  rw [List.flatten_append, List.length_append, List.map_append, List.sum_append,
    C.big12_counts.1, C.big12_counts.2, C.small12_counts.1, C.small12_counts.2]
  exact ⟨rfl, rfl⟩

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

theorem coreCircles12_valid : CircleFamilyValid 10 C.coreCircles12 := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact C.extended_valid c hc
  · exact C.gcircles_valid c hc

theorem coreCircles12_support : ∀ c ∈ C.coreCircles12, ∀ a ∈ c, a ∈ 10 :: 12 :: alph10 := by
  intro c hc a ha
  have h := C.circles12_support c (List.mem_append_left _ hc) a ha
  exact (by decide : ∀ b ∈ letters12, b ∈ 10 :: 12 :: alph10) a h

theorem coreCircles12_length : C.coreCircles12.length = 1683 := by
  unfold coreCircles12
  rw [List.length_append, extend_length C.circles_valid, C.circleCount, C.gcircleCount]

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

/-- The selection of step (A) on 12 symbols as a stage: long and short walks, the 6,048 loops
of `d11` pending. -/
theorem stage12 : Stage alph10 12 C.core12 C.coreCircles12 C.d11 3568320 1780800 1683 6048 where
  two := by decide
  nodup := by decide
  nine := by decide
  ten := by decide
  level := C.level_core12
  valid := C.coreCircles12_valid
  support := C.coreCircles12_support
  safe := C.safe_core12
  pend := fun e he => C.d11_perm he
  cover := fun y hy => C.cover12 hy
  rows := C.core12_counts.1
  charge := C.core12_counts.2
  ncirc := C.coreCircles12_length
  npend := C.d11_length

end Cert

end SuperpermutationUpperBound43586371
