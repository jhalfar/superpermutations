import SuperpermutationUpperBound43586371.Uniform.WalkLoops

/-!
# Ports and the single cycle (`PROOF.md`, sections 7-8)

A full row moves a completion port by `h - 1`, a short row by `1` (mod `h = m + 2`).  Over the walk the shift is
`4 (mod m + 2)`, so for odd `m` the passes of the walk written `h` times start at all ports once
(`walk_orbit_perm`).  The completion of the `h`-fold walk from any port contains the first completed row of the
walk at port `0`, whose head `c0` is a cycle of length `h` through `10`: one cycle meets every trail
(`walk_safe`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SuperpermutationUpperBound43586371.Uniform

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

/-- The port shift of one row. -/
def stepOf (r : Row Nat) : Nat := if r.visible = r.base.length then r.base.length - 2 else 1

theorem exit_sum (h : Nat) (hh : 0 < h) :
    ∀ (rs : List (Row Nat)), (∀ r ∈ rs, r.base.length = h + 1) →
      ∀ q, q < h → completionExit rs q = (q + (rs.map stepOf).sum) % h := by
  intro rs
  induction rs with
  | nil => intro _ q hq; simp [completionExit, Nat.mod_eq_of_lt hq]
  | cons r rest ih =>
    intro hl q hq
    have hr := hl r (by simp)
    have hpt : portTarget r q = (q + stepOf r) % h := by
      unfold portTarget stepOf
      rw [hr]
      split <;> simp
    simp only [completionExit, List.map_cons, List.sum_cons]
    rw [hpt, ih (fun x hx => hl x (by simp [hx])) _ (Nat.mod_lt _ hh), Nat.mod_add_mod, Nat.add_assoc]

theorem sweep_steps (s : List Nat) (T J : Nat) (hs : 2 ≤ s.length) (hJ : 1 ≤ J) :
    ((sweep s T J).map stepOf).sum = J * (s.length - 1) + 1 := by
  unfold sweep
  rw [List.range_succ, List.map_append, List.map_append, List.sum_append]
  have h0 : ∀ i ∈ List.range J, stepOf (sweepRow s T J i) = s.length - 1 := by
    intro i hi
    have hi := List.mem_range.mp hi
    unfold sweepRow stepOf
    by_cases h : i = 0
    · simp [h, fullRow]
    · simp [h, hi, fullRow]
  have hz : ((List.range J).map (sweepRow s T J)).map stepOf = (List.range J).map (fun _ => s.length - 1) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i hi => h0 i hi)
  rw [hz]
  simp [sweepRow, show J ≠ 0 by omega, shortRow, stepOf] <;> omega

theorem Pd.period_steps (p : Pd) :
    ((p.period).map stepOf).sum = (p.mid.length + 11) * (p.mid.length + 4) + 4 := by
  simp only [Pd.period, List.map_append, List.sum_append]
  rw [sweep_steps _ _ _ (by simp [Pd.len_arrW]) (by omega), sweep_steps _ _ _ (by simp [Pd.len_arrU]) (by omega),
    sweep_steps _ _ _ (by simp [Pd.len_arrY]) (by omega), sweep_steps _ _ _ (by simp [Pd.len_arrV]) (by omega),
    Pd.len_arrW, Pd.len_arrU, Pd.len_arrY, Pd.len_arrV]
  rw [show p.mid.length + 5 - 1 = p.mid.length + 4 by omega]
  ring

theorem walk_steps (d0 : List Nat) (A B C : Nat) (hm : 3 ≤ d0.length) :
    ((walk d0 A B C).map stepOf).sum = d0.length * ((d0.length + 8) * (d0.length + 1) + 4) := by
  unfold walk
  rw [List.map_flatMap, sum_flatMap_const _ _ ((d0.length + 8) * (d0.length + 1) + 4) (fun k _ => by
    rw [Pd.period_steps, pdOf_mid_length _ _ _ _ (by simp; omega)]; simp
    rw [show d0.length - 3 + 11 = d0.length + 8 by omega, show d0.length - 3 + 4 = d0.length + 1 by omega])]
  simp

theorem walk_baselen {d0 : List Nat} {A B C : Nat} (hm : 3 ≤ d0.length)
    (hnd : (C :: B :: A :: d0).Nodup) (h9 : 9 ∉ C :: B :: A :: d0) :
    ∀ r ∈ walk d0 A B C, r.base.length = (d0.length + 2) + 1 := by
  intro r hr
  have := ((walk_basedOn d0 A B C hm hnd h9) r hr).2.1.length_eq
  simp at this; omega

theorem walk_exit {d0 : List Nat} {A B C : Nat} (hm : 3 ≤ d0.length)
    (hnd : (C :: B :: A :: d0).Nodup) (h9 : 9 ∉ C :: B :: A :: d0) (q : Nat) (hq : q < d0.length + 2) :
    completionExit (walk d0 A B C) q = (q + 4) % (d0.length + 2) := by
  rw [exit_sum (d0.length + 2) (by omega) _ (walk_baselen hm hnd h9) q hq, walk_steps d0 A B C hm]
  have he : d0.length * ((d0.length + 8) * (d0.length + 1) + 4) =
      4 + (d0.length + 2) * (d0.length * d0.length + 7 * d0.length - 2) := by
    have h2 : 2 ≤ d0.length * d0.length + 7 * d0.length := by nlinarith
    zify [h2]
    ring
  rw [he, ← Nat.add_assoc, Nat.add_mul_mod_self_left]

theorem orbit_eq {rs : List (Row Nat)} {h s : Nat} (hh : 0 < h)
    (hex : ∀ q, q < h → completionExit rs q = (q + s) % h) :
    ∀ M p, p < h → orbitPorts rs M p = (List.range M).map (fun i => (p + s * i) % h) := by
  intro M
  induction M with
  | zero => intro p _; rfl
  | succ M ih =>
    intro p hp
    rw [orbitPorts, hex p hp, ih _ (Nat.mod_lt _ hh), List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp [Nat.mod_eq_of_lt hp]
    · refine List.map_congr_left (fun i _ => ?_)
      simp only [Function.comp, Nat.mod_add_mod]
      congr 1; rw [Nat.succ_eq_add_one]; ring

theorem orbit_perm (h p : Nat) (hh : 0 < h) (hodd : h % 2 = 1) :
    ((List.range h).map (fun i => (p + 4 * i) % h)).Perm (List.range h) := by
  have hcop : Nat.gcd h 4 = 1 := by
    have h2 : Nat.Coprime h 2 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega))
    exact Nat.Coprime.pow_right 2 h2
  have hnd : ((List.range h).map (fun i => (p + 4 * i) % h)).Nodup := by
    refine List.Nodup.map_on (fun i hi i' hi' he => ?_) List.nodup_range
    have hi := List.mem_range.mp hi
    have hi' := List.mem_range.mp hi'
    have h1 : 4 * i ≡ 4 * i' [MOD h] := Nat.ModEq.add_left_cancel' p he
    have h2 := Nat.ModEq.cancel_left_of_coprime hcop h1
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h2
  refine (hnd.subperm (fun x hx => ?_)).perm_of_length_le (by simp)
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact List.mem_range.mpr (Nat.mod_lt _ hh)

theorem walk_orbit_perm {d0 : List Nat} {A B C : Nat} (hm : 3 ≤ d0.length) (hodd : d0.length % 2 = 1)
    (hnd : (C :: B :: A :: d0).Nodup) (h9 : 9 ∉ C :: B :: A :: d0) (p : Nat) (hp : p < d0.length + 2) :
    (orbitPorts (walk d0 A B C) (d0.length + 2) p).Perm (List.range (d0.length + 2)) := by
  rw [orbit_eq (by omega) (walk_exit hm hnd h9) _ p hp]
  exact orbit_perm _ p (by omega) (by omega)

theorem completionWalk_rep (rs : List (Row Nat)) (f : Nat) :
    ∀ M p, completionWalk (rep M rs) f p = (orbitPorts rs M p).flatMap (fun q => completionWalk rs f q) := by
  intro M
  induction M with
  | zero => intro p; rfl
  | succ M ih =>
    intro p
    rw [rep, completionWalk_append, ih]
    rfl

/-! ### The cycle -/

/-- The first row of the walk. -/
def walkFirst (d0 : List Nat) (A B C : Nat) : Row Nat := (pdOf d0 A B C).first

/-- The single cycle: the head of the first completed row at port 0. -/
def cycle0 (d0 : List Nat) (A B C : Nat) : List Nat := (fullAt (walkFirst d0 A B C) 10 0).head

theorem walk_cons (d0 : List Nat) (A B C : Nat) (hm : 1 ≤ d0.length) :
    ∃ rest, walk d0 A B C = walkFirst d0 A B C :: rest := by
  unfold walk
  obtain ⟨n, hn⟩ : ∃ n, d0.length = n + 1 := ⟨d0.length - 1, by omega⟩
  rw [hn, List.range_succ_eq_map, List.flatMap_cons]
  have h := (pdOf (rot d0 (2 * 0)) A B C).period_head
  match hq : (pdOf (rot d0 (2 * 0)) A B C).period, h with
  | r :: rest, h =>
    simp at h
    exact ⟨rest ++ _, by rw [h]; rfl⟩

theorem walkFirst_full (d0 : List Nat) (A B C : Nat) :
    (walkFirst d0 A B C).visible = (walkFirst d0 A B C).base.length := by
  simp [walkFirst, Pd.first, fullRow]

theorem walkFirst_base (d0 : List Nat) (A B C : Nat) :
    ∃ x, (walkFirst d0 A B C).base = x ++ [B] := ⟨_, rfl⟩

theorem mem_completion_first (d0 : List Nat) (A B C : Nat) (hm : 1 ≤ d0.length) :
    fullAt (walkFirst d0 A B C) 10 0 ∈ completionWalk (walk d0 A B C) 10 0 := by
  obtain ⟨rest, hw⟩ := walk_cons d0 A B C hm
  rw [hw, completionWalk]
  apply List.mem_append_left
  simp [Completion.portPath, walkFirst_full, Transport.fullPathAt]

theorem cycle0_eq (d0 : List Nat) (A B C : Nat) :
    cycle0 d0 A B C = 10 :: (walkFirst d0 A B C).base.take ((walkFirst d0 A B C).base.length - 2) := by
  have hl : 2 ≤ (walkFirst d0 A B C).base.length := by simp [walkFirst, Pd.first, fullRow, Pd.arrW]
  simp only [cycle0, Row.head, fullAt, insertLetter, List.take_zero, List.drop_zero, List.nil_append,
    List.singleton_append, List.length_cons]
  rw [show (walkFirst d0 A B C).base.length + 1 - 2 = ((walkFirst d0 A B C).base.length - 2) + 1 by omega,
    List.take_succ_cons]

theorem walk_safe {d0 : List Nat} {A B C : Nat} (hm : 3 ≤ d0.length) (hodd : d0.length % 2 = 1)
    (hnd : (C :: B :: A :: d0).Nodup) (h9 : 9 ∉ C :: B :: A :: d0) :
    SafeComp (rep (d0.length + 2) (walk d0 A B C)) 10 (d0.length + 2) [cycle0 d0 A B C] := by
  intro j
  refine ⟨cycle0 d0 A B C, List.mem_singleton_self _, Or.inl ⟨?_, cycle0 d0 A B C, ?_, ?_⟩⟩
  · rw [cycle0_eq]; exact List.mem_cons_self
  · refine ⟨fullAt (walkFirst d0 A B C) 10 0, ?_, rfl⟩
    rw [completionWalk_rep]
    refine List.mem_flatMap.mpr ⟨0, ?_, mem_completion_first d0 A B C (by omega)⟩
    exact (walk_orbit_perm hm hodd hnd h9 j.val j.isLt).mem_iff.mpr (List.mem_range.mpr (by omega))
  · exact CyclicEq.refl (by rw [cycle0_eq]; simp)

theorem walkFirst_mem (d0 : List Nat) (A B C : Nat) (hm : 1 ≤ d0.length) :
    walkFirst d0 A B C ∈ walk d0 A B C := by
  obtain ⟨rest, hw⟩ := walk_cons d0 A B C hm
  rw [hw]; exact List.mem_cons_self

theorem cycle0_valid {d0 : List Nat} {A B C : Nat} (hm : 3 ≤ d0.length)
    (hnd : (C :: B :: A :: d0).Nodup) (h9 : 9 ∉ C :: B :: A :: d0) (h10 : 10 ∉ C :: B :: A :: d0) :
    (cycle0 d0 A B C).length = d0.length + 2 ∧ (cycle0 d0 A B C).Nodup ∧
      ∀ a ∈ cycle0 d0 A B C, a ∈ 10 :: C :: B :: A :: d0 := by
  have hb := (walk_basedOn d0 A B C hm hnd h9) _ (walkFirst_mem d0 A B C (by omega))
  have hlen : (walkFirst d0 A B C).base.length = d0.length + 3 := by
    have := hb.2.1.length_eq; simp at this; omega
  have hndb : (walkFirst d0 A B C).base.Nodup := hb.2.1.nodup_iff.mpr hnd
  have h10b : 10 ∉ (walkFirst d0 A B C).base := fun hm' => h10 (hb.2.1.mem_iff.mp hm')
  rw [cycle0_eq, hlen]
  refine ⟨by simp; omega, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨fun hm' => h10b (List.mem_of_mem_take hm'), hndb.sublist (List.take_sublist _ _)⟩
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hb.2.1.mem_iff.mp (List.mem_of_mem_take ha))

end SuperpermutationUpperBound43586371.Uniform
