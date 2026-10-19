import SuperpermutationUpperBound43586371.Uniform.Ports
import SuperpermutationUpperBound43586371.Stage

/-!
# The blocks as functions of the frame (`PROOF.md`, sections 1 and 6-8)

For a frame with `m = |d0|` odd, `m ≥ 5`: `walkData F` is the block with the one walk
`walk d0 t1 t2 t3` (started at one port), the loops of `above3T` that are not rotations of its rows, and the one
cycle `cycle0`; `walkData_ok` proves every field of constant43586371's `BlockOK` for all such `m`, and `walk_safeB` the cycle
condition.  `emptyData F` is the block without walks.  `famS` turns a checked block with a `SafeComp` cycle
condition (instead of constant43586371's pointer certificates) into the `BlockFam` that `Stage.advance` uses.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SuperpermutationUpperBound43586371.Uniform

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

/-! ### A block family from a `SafeComp` cycle condition -/

/-- The cycle condition as `SafeComp` statements (constant43586371's `BlockPorts` with the pointers replaced). -/
def BlockSafe (F : Frame) (B : BlockData) : Prop :=
  ∀ wg ∈ B.items, SafeComp (rep (F.h / wg.2) wg.1) 10 F.h B.cyc

namespace BlockDataS

variable {B : BlockData} {F : Frame}

theorem safeS (hB : BlockOK F B) (hS : BlockSafe F B) :
    ∀ W ∈ B.trails F, SafeComp W 10 (F.h + 1) (B.circles F) := by
  intro W hW
  obtain ⟨wg, hwg, p, hp, rfl⟩ := BlockData.mem_trails hW
  have hlen : ∀ r ∈ rep (F.h / wg.2) wg.1, r.base.length = F.h + 1 :=
    fun r hr => BlockData.item_len hB hwg r (mem_rep hr)
  have hkind : ∀ r ∈ rep (F.h / wg.2) wg.1,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2 :=
    fun r hr => BlockData.item_kind hB hwg r (mem_rep hr)
  have hfresh : ∀ r ∈ rep (F.h / wg.2) wg.1, 10 ∉ r.base := fun r hr hm10 =>
    hB.frame.ten (((hB.walks wg hwg).1 r (mem_rep hr)).2.1.mem_iff.mp hm10)
  exact (hS wg hwg).transport F.z F.hn hB.valid hlen hkind hfresh p (BlockData.start_lt hB hwg hp)

theorem safeRS (hB : BlockOK F B) (hS : BlockSafe F B) (d : List Nat) :
    ∀ W ∈ B.trailsR F d, SafeComp W 10 (F.h + 1) (B.circlesR F d) := by
  intro W hW
  obtain ⟨W0, hW0, rfl⟩ := List.mem_map.mp hW
  have h := safeComp_map (relab F.d0 d) (safeS hB hS W0 hW0)
  rwa [BlockData.relab_fix hB hB.frame.ten_d0] at h

end BlockDataS

/-- The block family of a checked block with `SafeComp` cycles. -/
def famS (F : Frame) (B : BlockData) (hB : BlockOK F B) (hS : BlockSafe F B) : BlockFam where
  F := F
  trailsR := B.trailsR F
  circlesR := B.circlesR F
  loopsR := B.loopsR F
  nrows := B.nrows
  nq := B.nq
  ncirc := F.h * B.ncyc
  nd := B.nd
  frame := hB.frame
  level := fun _ hd => BlockData.levelR hB hd
  safe := fun d _ => BlockDataS.safeRS hB hS d
  valid := fun _ hd => BlockData.circlesR_valid hB hd
  support := fun _ hd => BlockData.circlesR_support hB hd
  rows := fun d => (BlockData.countsR hB d).1
  charge := fun d => (BlockData.countsR hB d).2
  ncircR := fun d => BlockData.circlesR_length hB d
  loops_perm := fun _ hd => BlockData.loopsR_perm hB hd
  nloops := fun d => BlockData.loopsR_length hB d
  cover := fun _ hd _ ht => BlockData.coverR hB hd ht

/-! ### The walk block -/

/-- The block with the one walk `W(m)`, for a frame with `m = |d0|`. -/
def walkData (F : Frame) : BlockData where
  items := [(walk F.d0 F.t1 F.t2 F.t3, 1)]
  dloops := (above3T F.t1 F.t2 F.t3 F.d0).filter (fun t => !coveredB (walk F.d0 F.t1 F.t2 F.t3) t)
  ptrs := []
  cyc := [cycle0 F.d0 F.t1 F.t2 F.t3]
  nrows := F.d0.length * (F.d0.length + 12)
  nq := 8 * F.d0.length
  nd := F.d0.length * ((F.d0.length + 1) * (F.d0.length + 2)) - F.d0.length * (F.d0.length + 12)
  ncyc := 1

theorem frame_alph (F : Frame) : F.alph = F.t3 :: F.t2 :: F.t1 :: F.d0 := rfl

theorem walkData_ok (F : Frame) (hF : F.OK) (hm5 : 5 ≤ F.d0.length) (hodd : F.d0.length % 2 = 1) :
    BlockOK F (walkData F) := by
  have hnd : (F.t3 :: F.t2 :: F.t1 :: F.d0).Nodup := hF.alph_nodup
  have h9 : 9 ∉ F.t3 :: F.t2 :: F.t1 :: F.d0 := hF.nine
  have h10 : 10 ∉ F.t3 :: F.t2 :: F.t1 :: F.d0 := hF.ten
  have hm3 : 3 ≤ F.d0.length := by omega
  have hh : F.h = F.d0.length + 2 := rfl
  have hwf : (walkData F).walks.flatten = walk F.d0 F.t1 F.t2 F.t3 := by
    simp [walkData, BlockData.walks]
  refine ⟨hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro wg hwg
    simp only [walkData, List.mem_singleton] at hwg
    subst hwg
    refine ⟨walk_basedOn _ _ _ _ hm3 hnd h9, walk_closed _ _ _ _ (by omega), ?_, ?_, ?_⟩
    · simp [hh]
    · simp only [Nat.div_one]; exact dvd_mul_right _ _
    · simp only [Nat.div_one, List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [hh]
      exact walk_orbit_perm hm3 hodd hnd h9 0 (by omega)
  · intro e he
    exact above3T_perm (List.mem_filter.mp he).1
  · intro t ht
    by_cases hc : coveredB (walk F.d0 F.t1 F.t2 F.t3) t = true
    · left
      rw [hwf]
      simpa [coveredB] using hc
    · right
      refine ⟨t, List.mem_filter.mpr ⟨ht, by simpa using hc⟩, CyclicEq.refl ?_⟩
      obtain ⟨P, rfl⟩ := canon_ent ht
      simp
  · rw [hwf, walk_length _ _ _ _ hm3]; rfl
  · rw [hwf, walk_charge]; rfl
  · exact walk_dloops_length hnd h9 hm5 hodd
  · intro c hc
    simp only [walkData, List.mem_singleton] at hc
    subst hc
    obtain ⟨h1, h2, _⟩ := cycle0_valid hm3 hnd h9 h10
    exact ⟨h1, h2⟩
  · intro c hc a ha
    simp only [walkData, List.mem_singleton] at hc
    subst hc
    exact (cycle0_valid hm3 hnd h9 h10).2.2 a ha

theorem walk_safeB (F : Frame) (hF : F.OK) (hm5 : 5 ≤ F.d0.length) (hodd : F.d0.length % 2 = 1) :
    BlockSafe F (walkData F) := by
  intro wg hwg
  simp only [walkData, List.mem_singleton] at hwg
  subst hwg
  simp only [Nat.div_one]
  exact walk_safe (by omega) hodd hF.alph_nodup hF.nine

/-! ### The empty block -/

def emptyData (F : Frame) : BlockData where
  items := []
  dloops := above3T F.t1 F.t2 F.t3 F.d0
  ptrs := []
  cyc := []
  nrows := 0
  nq := 0
  nd := F.d0.length * ((F.d0.length + 1) * (F.d0.length + 2))
  ncyc := 0

theorem emptyData_ok (F : Frame) (hF : F.OK) : BlockOK F (emptyData F) := by
  refine ⟨hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro wg hwg; simp [emptyData] at hwg
  · intro e he; exact above3T_perm he
  · intro t ht
    right
    refine ⟨t, ht, CyclicEq.refl ?_⟩
    obtain ⟨P, rfl⟩ := canon_ent ht
    simp
  · simp [emptyData, BlockData.walks]
  · simp [emptyData, BlockData.walks]
  · exact above3T_length _ _ _ _
  · intro c hc; simp [emptyData] at hc
  · intro c hc; simp [emptyData] at hc

theorem empty_safeB (F : Frame) : BlockSafe F (emptyData F) := by
  intro wg hwg; simp [emptyData] at hwg

end SuperpermutationUpperBound43586371.Uniform
