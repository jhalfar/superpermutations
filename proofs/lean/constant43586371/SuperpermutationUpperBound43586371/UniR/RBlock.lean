import SuperpermutationUpperBound43586371.UniR.RPorts
import SuperpermutationUpperBound43586371.Uniform.Block

/-!
# The block R'(m) as constant43586371's `BlockData`, for every m ≥ 7 (`PROOF_R.md`)

`rData F`: one item per walk `d ∈ Dl m` (the walk with `gpR m` start ports), the loops of `above3T` without a
row, the shared cycles `cyclesR`.  `rData_ok` proves every field of `BlockOK`, `rData_safe` the cycle condition;
`rFam` is the resulting `BlockFam`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SuperpermutationUpperBound43586371.UniR

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound43586371.Uniform

/-- Rows of R'(m). -/
def rowsR (m : Nat) : Nat := (Dl m).length * (Pm m * (m + 12))

/-- Total charge of R'(m). -/
def chargeR (m : Nat) : Nat := (Dl m).length * (8 * Pm m)

/-- Number of shared cycles. -/
def ncycR (m : Nat) : Nat := if m % 2 = 1 then 2 else 8

def rData (F : Frame) : BlockData where
  items := (Dl F.d0.length).map fun d => (walkD F.d0 F.t1 F.t2 F.t3 d, gpR F.d0.length)
  dloops := (above3T F.t1 F.t2 F.t3 F.d0).filter (fun t => !Uniform.coveredB (blockRows F.d0 F.t1 F.t2 F.t3) t)
  ptrs := []
  cyc := cyclesR F.d0 F.t1 F.t2
  nrows := rowsR F.d0.length
  nq := chargeR F.d0.length
  nd := F.d0.length * ((F.d0.length + 1) * (F.d0.length + 2)) - rowsR F.d0.length
  ncyc := ncycR F.d0.length

theorem rData_walks (F : Frame) : (rData F).walks.flatten = blockRows F.d0 F.t1 F.t2 F.t3 := by
  simp [rData, BlockData.walks, blockRows, List.flatMap_def, Function.comp_def]

theorem setting_of (F : Frame) (hF : F.OK) (hm : 7 ≤ F.d0.length) : Setting F.d0 F.t1 F.t2 F.t3 :=
  ⟨hF.alph_nodup, hm⟩

theorem cycR_ok (d0 : List Nat) (τ i0 ε : Nat) (hd : d0.Nodup) (hτ : τ ∉ d0) (h10 : 10 ∉ τ :: d0) :
    (cycR d0 τ i0 ε).length = d0.length + 2 ∧ (cycR d0 τ i0 ε).Nodup ∧
      ∀ a ∈ cycR d0 τ i0 ε, a = 10 ∨ a = τ ∨ a ∈ d0 := by
  have hp : (rot (rot d0 i0 ++ [τ]) ε).Perm (τ :: d0) :=
    (rot_perm _ _).trans (List.perm_append_comm.trans ((rot_perm d0 i0).cons τ))
  refine ⟨by simp [cycR], ?_, ?_⟩
  · refine List.nodup_cons.mpr ⟨fun hm => h10 (hp.mem_iff.mp hm), hp.nodup_iff.mpr ?_⟩
    exact List.nodup_cons.mpr ⟨hτ, hd⟩
  · intro a ha
    rcases List.mem_cons.mp ha with h | h
    · left; exact h
    · right; simpa using hp.mem_iff.mp h

theorem rData_ncyc (F : Frame) : (cyclesR F.d0 F.t1 F.t2).length = ncycR F.d0.length := by
  unfold cyclesR ncycR; split_ifs <;> simp

theorem rData_ok (F : Frame) (hF : F.OK) (hm : 7 ≤ F.d0.length) : BlockOK F (rData F) := by
  have S := setting_of F hF hm
  have h9 : 9 ∉ F.t3 :: F.t2 :: F.t1 :: F.d0 := hF.nine
  have h10 : 10 ∉ F.t3 :: F.t2 :: F.t1 :: F.d0 := hF.ten
  set m := F.d0.length with hmdef
  have hh : F.h = m + 2 := rfl
  refine ⟨hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rData_ncyc F⟩
  · intro wg hwg
    simp only [rData, List.mem_map] at hwg
    obtain ⟨d, hd, rfl⟩ := hwg
    obtain ⟨hg3, hg5, hσ, hs⟩ := mem_Dl hd
    have hP := Pm_spec m
    refine ⟨walkD_basedOn S h9 hd, ?_, ?_, ?_, ?_⟩
    · exact walkR_closed _ _ _ _ _ _ _ (by omega) (by omega) (by unfold Pm; split_ifs <;> omega)
        (by rcases hP with ⟨_, h⟩ | ⟨_, h⟩
            · rw [h]; exact Nat.mul_mod_left 2 m
            · rw [show 2 * Pm m = m from h]; exact Nat.mod_self m)
    · simp only [hh, gpR]; split_ifs <;> omega
    · -- divisibility
      have hlen := walkR_length F.d0 d.1 (rA d.2.1 F.t1 F.t2) (rB d.2.1 F.t1 F.t2) F.t3 d.2.2 (Pm m) (by omega)
      have hch := walkR_charge F.d0 d.1 (rA d.2.1 F.t1 F.t2) (rB d.2.1 F.t1 F.t2) F.t3 d.2.2 (Pm m)
        (by omega) (by omega)
      show ((F.h : Nat) : Int) ∣ ((F.h / gpR m : Nat) : Int) * signedExcess (walkD F.d0 F.t1 F.t2 F.t3 d)
      unfold signedExcess
      rw [show (walkD F.d0 F.t1 F.t2 F.t3 d) = walkR F.d0 d.1 (rA d.2.1 F.t1 F.t2) (rB d.2.1 F.t1 F.t2) F.t3
        d.2.2 (Pm m) from rfl, hlen, hch, hh]
      unfold gpR
      rcases hP with ⟨hmo, hPm⟩ | ⟨hme, hPm⟩
      · rw [if_pos hmo, Nat.div_one]; exact dvd_mul_right _ _
      · rw [if_neg (by omega)]
        obtain ⟨u, hu⟩ : ∃ u, F.d0.length = 2 * u := ⟨F.d0.length / 2, by omega⟩
        have hPu : Pm m = u := by omega
        rw [hPu]
        simp only [hmdef, hu, show (2 * u + 2) / 2 = u + 1 by omega]
        refine ⟨(u : Int) * (u + 2), ?_⟩
        push_cast
        ring
    · -- the start ports cover all ports once
      have hex := walkD_exit S h9 hd
      show ((List.range (gpR m)).flatMap (orbitPorts (walkD F.d0 F.t1 F.t2 F.t3 d) (F.h / gpR m))).Perm
        (List.range F.h)
      rw [hh]
      unfold gpR
      split_ifs with hmo
      · rw [Nat.div_one, show List.range 1 = [0] from rfl, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          orbit_eq (by omega) hex _ 0 (by omega)]
        rw [if_pos hmo]
        exact orbit_perm _ 0 (by omega) (by omega)
      · have e : ((List.range 2).flatMap fun p => orbitPorts (walkD F.d0 F.t1 F.t2 F.t3 d) ((m + 2) / 2) p) =
            (List.range 2).flatMap fun p => (List.range ((m + 2) / 2)).map (fun i => (p + 2 * i) % (m + 2)) := by
          refine List.flatMap_congr (fun p hp => ?_)
          rw [orbit_eq (by omega) hex _ p (by simp at hp; omega)]
          rw [if_neg hmo]
        rw [e]
        exact orbit_even_perm _ (by omega) (by omega)
  · intro e he
    exact above3T_perm (List.mem_filter.mp he).1
  · intro t ht
    by_cases hc : Uniform.coveredB (blockRows F.d0 F.t1 F.t2 F.t3) t = true
    · left
      rw [rData_walks]
      simpa [Uniform.coveredB] using hc
    · right
      refine ⟨t, List.mem_filter.mpr ⟨ht, by simpa using hc⟩, CyclicEq.refl ?_⟩
      obtain ⟨P, rfl⟩ := canon_ent ht
      simp
  · rw [rData_walks, blockRows_length S]; rfl
  · rw [rData_walks, blockRows_charge S]; rfl
  · show ((above3T F.t1 F.t2 F.t3 F.d0).filter _).length = _
    rw [block_dloops_length S h9, blockRows_length S]; rfl
  · intro c hc
    have hd := S.d0_nodup
    unfold rData cyclesR at hc
    simp only at hc
    split_ifs at hc
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨h1, h2, _⟩ := cycR_ok F.d0 F.t1 0 0 hd S.t1_d0 (by simp at h10 ⊢; tauto)
        exact ⟨by rw [h1]; rfl, h2⟩
      · obtain ⟨h1, h2, _⟩ := cycR_ok F.d0 F.t2 0 0 hd S.t2_d0 (by simp at h10 ⊢; tauto)
        exact ⟨by rw [h1]; rfl, h2⟩
    · simp only [List.mem_flatMap, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hc
      obtain ⟨τ, hτ, i0, -, ε, -, rfl⟩ := hc
      rcases hτ with rfl | rfl
      · obtain ⟨h1, h2, _⟩ := cycR_ok F.d0 F.t1 i0 ε hd S.t1_d0 (by simp at h10 ⊢; tauto)
        exact ⟨by rw [h1]; rfl, h2⟩
      · obtain ⟨h1, h2, _⟩ := cycR_ok F.d0 F.t2 i0 ε hd S.t2_d0 (by simp at h10 ⊢; tauto)
        exact ⟨by rw [h1]; rfl, h2⟩
  · intro c hc a ha
    have hd := S.d0_nodup
    have key : ∀ τ i0 ε, (τ = F.t1 ∨ τ = F.t2) → a ∈ cycR F.d0 τ i0 ε → a ∈ 10 :: F.alph := by
      intro τ i0 ε hτ ha'
      have hτd : τ ∉ F.d0 := by rcases hτ with rfl | rfl; exact S.t1_d0; exact S.t2_d0
      have h10' : 10 ∉ τ :: F.d0 := by rcases hτ with rfl | rfl <;> simp at h10 ⊢ <;> tauto
      rcases (cycR_ok F.d0 τ i0 ε hd hτd h10').2.2 a ha' with h | h | h
      · rw [h]; exact List.mem_cons_self
      · rcases hτ with rfl | rfl <;> rw [h] <;> simp [Frame.alph]
      · simp [Frame.alph, h]
    unfold rData cyclesR at hc
    simp only at hc
    split_ifs at hc
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact key _ _ _ (Or.inl rfl) ha
      · exact key _ _ _ (Or.inr rfl) ha
    · simp only [List.mem_flatMap, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hc
      obtain ⟨τ, hτ, i0, -, ε, -, rfl⟩ := hc
      exact key _ _ _ hτ ha

theorem rData_safe (F : Frame) (hF : F.OK) (hm : 7 ≤ F.d0.length) : BlockSafe F (rData F) := by
  intro wg hwg
  simp only [rData, List.mem_map] at hwg
  obtain ⟨d, hd, rfl⟩ := hwg
  exact walkD_safe (setting_of F hF hm) hF.nine hd

/-- The block family R'(m). -/
def rFam (F : Frame) (hF : F.OK) (hm : 7 ≤ F.d0.length) : BlockFam :=
  famS F (rData F) (rData_ok F hF hm) (rData_safe F hF hm)

end SuperpermutationUpperBound43586371.UniR
