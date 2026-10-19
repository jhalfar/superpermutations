import SuperpermutationUpperBound43586371.Uniform.Block
import SuperpermutationUpperBound43586371.Uniform.Arith
import SuperpermutationUpperBound43586371.NoSeed

/-!
# The stages for every number of levels (`PROOF.md`, section 9)

No seed on `m0 + 1` letters (`0` and `1..8, 11..m0+2`), then pairs of levels: the walk block at odd `a`, the
empty block at `a + 3`.  The letters stay `range (a + 3)` without `9, 10` (`LetOK`); the new letters of a level
are `a+3, a+4, a+5`.  `stages m0 K` gives a stage at `a = m0 + 6K` with the invariants (I1)-(I3) of
`Arith.lean`, and `closed_level` the closed level on `a + 1` letters with `a!` rows.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SuperpermutationUpperBound43586371.Uniform

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

/-- The letters of a stage: with `9` and `10` exactly `0, ..., |A0| + 2`. -/
def LetOK (A0 : List Nat) (z : Nat) : Prop := (10 :: ((z :: A0) ++ [9])).Perm (List.range (A0.length + 3))

section Letters

variable {A0 : List Nat} {z : Nat}

theorem LetOK.full_nodup (h : LetOK A0 z) : (10 :: ((z :: A0) ++ [9])).Nodup :=
  h.nodup_iff.mpr List.nodup_range

theorem LetOK.nodup (h : LetOK A0 z) : (z :: A0).Nodup :=
  (List.nodup_cons.mp h.full_nodup).2.sublist (List.sublist_append_left _ _)

theorem LetOK.ten (h : LetOK A0 z) : 10 ∉ z :: A0 := fun hm =>
  (List.nodup_cons.mp h.full_nodup).1 (List.mem_append_left _ hm)

theorem LetOK.nine (h : LetOK A0 z) : 9 ∉ z :: A0 := fun hm =>
  (List.nodup_append.mp (List.nodup_cons.mp h.full_nodup).2).2.2 9 hm 9 (by simp) rfl

theorem LetOK.lt (h : LetOK A0 z) : ∀ x ∈ z :: A0, x < A0.length + 3 := fun x hx =>
  List.mem_range.mp (h.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_append_left _ hx)))

/-- The frame of the block above the pending loops of a stage on `z :: A0`. -/
def frameAt (A0 : List Nat) (z : Nat) : Frame := ⟨A0, z, A0.length + 3, A0.length + 4, A0.length + 5⟩

theorem frameAt_ok (h : LetOK A0 z) (h8 : 8 ≤ A0.length) : (frameAt A0 z).OK := by
  have hnd := h.nodup
  have hlt := h.lt
  have h9 := h.nine
  have h10 := h.ten
  refine ⟨?_, ?_, ?_⟩
  · show ((A0.length + 5) :: (A0.length + 4) :: (A0.length + 3) :: z :: A0).Nodup
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hnd⟩⟩⟩
    · intro hm
      rcases List.mem_cons.mp hm with hm | hm
      · omega
      rcases List.mem_cons.mp hm with hm | hm
      · omega
      · have := hlt _ hm; omega
    · intro hm
      rcases List.mem_cons.mp hm with hm | hm
      · omega
      · have := hlt _ hm; omega
    · intro hm; have := hlt _ hm; omega
  · show 9 ∉ (A0.length + 5) :: (A0.length + 4) :: (A0.length + 3) :: z :: A0
    intro hm
    simp only [List.mem_cons] at hm
    rcases hm with hm | hm | hm | hm
    · omega
    · omega
    · omega
    · exact h9 (by simpa using hm)
  · show 10 ∉ (A0.length + 5) :: (A0.length + 4) :: (A0.length + 3) :: z :: A0
    intro hm
    simp only [List.mem_cons] at hm
    rcases hm with hm | hm | hm | hm
    · omega
    · omega
    · omega
    · exact h10 (by simpa using hm)

theorem LetOK.next (h : LetOK A0 z) :
    LetOK ((A0.length + 4) :: (A0.length + 3) :: z :: A0) (A0.length + 5) := by
  unfold LetOK
  have e : List.range (((A0.length + 4) :: (A0.length + 3) :: z :: A0).length + 3) =
      List.range (A0.length + 3) ++ [A0.length + 3, A0.length + 4, A0.length + 5] := by
    rw [show ((A0.length + 4) :: (A0.length + 3) :: z :: A0).length + 3 = A0.length + 3 + 1 + 1 + 1 by
      simp, List.range_succ, List.range_succ, List.range_succ]
    simp
  rw [e]
  refine List.Perm.trans ?_ (h.append_right _)
  rw [← Multiset.coe_eq_coe]
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

end Letters

/-! ### The two blocks of a double step -/

def walkFam (A0 : List Nat) (z : Nat) (h : LetOK A0 z) (h8 : 8 ≤ A0.length) (hodd : A0.length % 2 = 1) :
    BlockFam :=
  famS (frameAt A0 z) (walkData (frameAt A0 z)) (walkData_ok _ (frameAt_ok h h8) (by simp [frameAt]; omega)
    hodd) (walk_safeB _ (frameAt_ok h h8) (by simp [frameAt]; omega) hodd)

def emptyFam (A0 : List Nat) (z : Nat) (h : LetOK A0 z) (h8 : 8 ≤ A0.length) : BlockFam :=
  famS (frameAt A0 z) (emptyData (frameAt A0 z)) (emptyData_ok _ (frameAt_ok h h8)) (empty_safeB _)

/-- The invariants of a stage at `a = |A0|` letters (`PROOF.md`, section 9). -/
structure Inv (m0 : Nat) (A0 : List Nat) (z R Q c P : Nat) : Prop where
  let_ok : LetOK A0 z
  I1 : R + P * A0.length = A0.length.factorial
  I2 : m0 * Q + m0 * A0.length * c + 10 * A0.length * P ≤ 10 * A0.length.factorial
  I3 : P ^ 6 * (A0.length + 1) ≤ (m0 + 1) * ((A0.length - 1).factorial) ^ 6

theorem double_step (m0 : Nat) {A0 : List Nat} {z : Nat} {comps : List (List (Row Nat))}
    {circles : List (List Nat)} {pending : List (List Nat)} {R Q c P : Nat}
    (S : Stage A0 z comps circles pending R Q c P) (hI : Inv m0 A0 z R Q c P)
    (hm : m0 ≤ A0.length) (h8 : 8 ≤ A0.length) (hodd : A0.length % 2 = 1) :
    ∃ A0' z' comps' circles' pending' R' Q' c' P', Stage A0' z' comps' circles' pending' R' Q' c' P' ∧
      Inv m0 A0' z' R' Q' c' P' ∧ A0'.length = A0.length + 6 := by
  have hL1 := hI.let_ok.next
  have S1 := S.advance (walkFam A0 z hI.let_ok h8 hodd) (List.Perm.refl _) rfl
  have S2 := S1.advance (emptyFam _ _ hL1 (by simp; omega)) (List.Perm.refl _) rfl
  have ws : WalkStep A0.length R Q c P _ _ _ _ := ⟨rfl, rfl, rfl, rfl⟩
  have es : EmptyStep (A0.length + 3)
      ((A0.length + 3) * ((A0.length + 2) * ((A0.length + 1) * R)) + P * ((A0.length + 3) * (A0.length * (A0.length + 12))))
      ((A0.length + 3) * ((A0.length + 2) * ((A0.length + 1) * Q)) + P * ((A0.length + 3) * (8 * A0.length)))
      ((A0.length + 2) * ((A0.length + 1) * (A0.length * c)) + P * ((A0.length + 2) * 1))
      (P * (A0.length * ((A0.length + 1) * (A0.length + 2)) - A0.length * (A0.length + 12))) _ _ _ _ :=
    ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨_, _, _, _, _, _, _, _, _, S2, ⟨hL1.next, ?_, ?_, ?_⟩, ?_⟩
  · have e := empty_I1 es (walk_I1 (by omega) ws hI.I1)
    simpa [walkFam, emptyFam, famS, walkData, emptyData, frameAt, Frame.h] using e
  · have e := empty_I2 es (walk_I2 (by omega) hm ws hI.I2)
    simpa [walkFam, emptyFam, famS, walkData, emptyData, frameAt, Frame.h] using e
  · have e := step_I3 (P1 := P * (A0.length * ((A0.length + 1) * (A0.length + 2)) - A0.length * (A0.length + 12)))
      (by omega) rfl rfl hI.I3
    simpa [walkFam, emptyFam, famS, walkData, emptyData, frameAt, Frame.h] using e
  · simp

/-! ### The first stage: no seed -/

/-- The old letters of the first stage: `1..8, 11..m0+2`. -/
def rest0 (m0 : Nat) : List Nat := List.range' 2 7 ++ List.range' 11 (m0 - 8)

theorem rest0_length (m0 : Nat) : (rest0 m0).length = 7 + (m0 - 8) := by simp [rest0]

theorem letOK0 (m0 : Nat) (h11 : 11 ≤ m0) : LetOK (1 :: rest0 m0) 0 := by
  unfold LetOK
  have e : List.range ((1 :: rest0 m0).length + 3) =
      (0 :: 1 :: List.range' 2 7) ++ [9, 10] ++ List.range' 11 (m0 - 8) := by
    rw [List.range_eq_range', show (1 :: rest0 m0).length + 3 = 9 + (2 + (m0 - 8)) by
      simp [rest0]; omega, ← List.range'_append, ← List.range'_append]
    simp [List.range'_succ]
  rw [e, ← Multiset.coe_eq_coe]
  simp only [rest0, ← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

theorem stage0 (m0 : Nat) (h11 : 11 ≤ m0) :
    ∃ comps circles pending R Q c P, Stage (1 :: rest0 m0) 0 comps circles pending R Q c P ∧
      Inv m0 (1 :: rest0 m0) 0 R Q c P := by
  have hL := letOK0 m0 h11
  have hlen : (1 :: rest0 m0).length = m0 := by simp [rest0]; omega
  have S := Stage.noSeed (a := 1) (z := 0) (rest := rest0 m0) hL.nodup hL.nine hL.ten
    (by rw [rest0_length]; omega)
  refine ⟨_, _, _, _, _, _, _, S, hL, ?_, ?_, ?_⟩
  · rw [hlen, show (rest0 m0).length = m0 - 1 by rw [rest0_length]; omega, fact_pred m0 (by omega)]
    ring
  · rw [hlen, show (rest0 m0).length = m0 - 1 by rw [rest0_length]; omega, fact_pred m0 (by omega)]
    ring_nf; omega
  · rw [hlen, show (rest0 m0).length = m0 - 1 by rw [rest0_length]; omega]
    ring_nf; omega

/-- A stage after `K` double steps, at `m0 + 6K` letters. -/
theorem stages (m0 : Nat) (h11 : 11 ≤ m0) (hodd : m0 % 2 = 1) :
    ∀ K, ∃ A0 z comps circles pending R Q c P, Stage A0 z comps circles pending R Q c P ∧
      Inv m0 A0 z R Q c P ∧ A0.length = m0 + 6 * K := by
  intro K
  induction K with
  | zero =>
    obtain ⟨comps, circles, pending, R, Q, c, P, S, hI⟩ := stage0 m0 h11
    exact ⟨_, _, comps, circles, pending, R, Q, c, P, S, hI, by simp [rest0]; omega⟩
  | succ K ih =>
    obtain ⟨A0, z, comps, circles, pending, R, Q, c, P, S, hI, hlen⟩ := ih
    obtain ⟨A0', z', comps', circles', pending', R', Q', c', P', S', hI', hlen'⟩ :=
      double_step m0 S hI (by omega) (by omega) (by omega)
    exact ⟨A0', z', comps', circles', pending', R', Q', c', P', S', hI', by omega⟩

/-- The closed level after `K` double steps: `a = m0 + 6K`, `a!` rows of total charge `Q`, `c + P`
cycles, with `m0 (Q + a c) ≤ 10 a!` and `(a P)^6 (a+1) ≤ (m0+1) (a!)^6`. -/
theorem closed_level (m0 : Nat) (h11 : 11 ≤ m0) (hodd : m0 % 2 = 1) (K : Nat) :
    ∃ A comps circles Q c P, Closed A (m0 + 6 * K) comps circles (m0 + 6 * K).factorial Q (c + P) ∧
      (10 :: (A ++ [9])).Perm (List.range (m0 + 6 * K + 3)) ∧
      m0 * (Q + (m0 + 6 * K) * c) ≤ 10 * (m0 + 6 * K).factorial ∧
      ((m0 + 6 * K) * P) ^ 6 * (m0 + 6 * K + 1) ≤ (m0 + 1) * ((m0 + 6 * K).factorial) ^ 6 := by
  obtain ⟨A0, z, comps, circles, pending, R, Q, c, P, S, hI, hlen⟩ := stages m0 h11 hodd K
  have C := S.close
  rw [hI.I1, hlen] at C
  refine ⟨z :: A0, _, _, Q, c, P, C, ?_, ?_, ?_⟩
  · have := hI.let_ok; unfold LetOK at this; rwa [hlen] at this
  · have := hI.I2; rw [hlen] at this; nlinarith
  · have h3 := hI.I3
    rw [hlen] at h3
    have hf := fact_pred (m0 + 6 * K) (by omega)
    calc ((m0 + 6 * K) * P) ^ 6 * (m0 + 6 * K + 1) = (m0 + 6 * K) ^ 6 * (P ^ 6 * (m0 + 6 * K + 1)) := by ring
      _ ≤ (m0 + 6 * K) ^ 6 * ((m0 + 1) * ((m0 + 6 * K - 1).factorial) ^ 6) := Nat.mul_le_mul_left _ h3
      _ = (m0 + 1) * ((m0 + 6 * K) * (m0 + 6 * K - 1).factorial) ^ 6 := by ring
      _ = (m0 + 1) * ((m0 + 6 * K).factorial) ^ 6 := by rw [← hf]

end SuperpermutationUpperBound43586371.Uniform
