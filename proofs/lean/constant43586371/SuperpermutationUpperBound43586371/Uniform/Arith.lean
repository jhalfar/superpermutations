import Mathlib.Tactic

/-!
# The arithmetic of one double step (walk at odd `a`, empty block at `a + 3`) (`PROOF.md`, section 9)

Stage counts `(R, Q, c, P)` at `a` letters (`a = |A0|`) satisfy
(I1) `R + P a = a!`, (I2) `m0 Q + m0 a c + 10 a P ≤ 10 a!`, (I3) `P^6 (a+1) ≤ (m0+1) ((a-1)!)^6`;
`Stage.advance` with the walk block and then the empty block gives the counts at `a + 6`, and all three stay
true (`step_I1`, `step_I2`, `step_I3`).
-/

namespace SuperpermutationUpperBound43586371.Uniform

theorem fact3 (a : Nat) : (a + 3).factorial = (a + 3) * ((a + 2) * ((a + 1) * a.factorial)) := by
  rw [show a + 3 = (a + 2) + 1 by omega, Nat.factorial_succ, show a + 2 = (a + 1) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]

theorem fact_pred (a : Nat) (ha : 1 ≤ a) : a.factorial = a * (a - 1).factorial := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  simp [Nat.factorial_succ]

/-- The counts after a walk block at `a` (`N = a (a+12)` rows, charge `8a`, one cycle, `D = L - N`). -/
structure WalkStep (a R Q c P R1 Q1 c1 P1 : Nat) : Prop where
  hR : R1 = (a + 3) * ((a + 2) * ((a + 1) * R)) + P * ((a + 3) * (a * (a + 12)))
  hQ : Q1 = (a + 3) * ((a + 2) * ((a + 1) * Q)) + P * ((a + 3) * (8 * a))
  hc : c1 = (a + 2) * ((a + 1) * (a * c)) + P * ((a + 2) * 1)
  hP : P1 = P * (a * ((a + 1) * (a + 2)) - a * (a + 12))

/-- The counts after an empty block at `b`. -/
structure EmptyStep (b R Q c P R1 Q1 c1 P1 : Nat) : Prop where
  hR : R1 = (b + 3) * ((b + 2) * ((b + 1) * R)) + P * ((b + 3) * 0)
  hQ : Q1 = (b + 3) * ((b + 2) * ((b + 1) * Q)) + P * ((b + 3) * 0)
  hc : c1 = (b + 2) * ((b + 1) * (b * c)) + P * ((b + 2) * 0)
  hP : P1 = P * (b * ((b + 1) * (b + 2)))

theorem walk_NL (a : Nat) (ha : 3 ≤ a) : a * (a + 12) ≤ a * ((a + 1) * (a + 2)) := by
  apply Nat.mul_le_mul_left; nlinarith

theorem walk_I1 {a R Q c P R1 Q1 c1 P1 : Nat} (ha : 3 ≤ a) (h : WalkStep a R Q c P R1 Q1 c1 P1)
    (I1 : R + P * a = a.factorial) : R1 + P1 * (a + 3) = (a + 3).factorial := by
  obtain ⟨D, hD⟩ : ∃ D, a * ((a + 1) * (a + 2)) = D + a * (a + 12) :=
    ⟨_, (Nat.sub_add_cancel (walk_NL a ha)).symm⟩
  rw [h.hR, h.hP, hD, Nat.add_sub_cancel, fact3, ← I1]
  have : D = a * ((a + 1) * (a + 2)) - a * (a + 12) := by omega
  have hL : D + a * (a + 12) = a * ((a + 1) * (a + 2)) := hD.symm
  nlinarith [hL]

theorem walk_I2 {a m0 R Q c P R1 Q1 c1 P1 : Nat} (ha : 3 ≤ a) (hm : m0 ≤ a)
    (h : WalkStep a R Q c P R1 Q1 c1 P1)
    (I2 : m0 * Q + m0 * a * c + 10 * a * P ≤ 10 * a.factorial) :
    m0 * Q1 + m0 * (a + 3) * c1 + 10 * (a + 3) * P1 ≤ 10 * (a + 3).factorial := by
  obtain ⟨D, hD⟩ : ∃ D, a * ((a + 1) * (a + 2)) = D + a * (a + 12) :=
    ⟨_, (Nat.sub_add_cancel (walk_NL a ha)).symm⟩
  rw [h.hQ, h.hc, h.hP, hD, Nat.add_sub_cancel, fact3]
  set X := (a + 3) * ((a + 2) * (a + 1)) with hX
  have e : m0 * ((a + 3) * ((a + 2) * ((a + 1) * Q)) + P * ((a + 3) * (8 * a))) +
      m0 * (a + 3) * ((a + 2) * ((a + 1) * (a * c)) + P * ((a + 2) * 1)) + 10 * (a + 3) * (P * D) +
      10 * (a + 3) * P * (a * (a + 12)) =
      X * (m0 * Q + m0 * a * c + 10 * a * P) + (a + 3) * P * (m0 * (9 * a + 2)) := by
    rw [hX, Nat.add_assoc (_ + _), show 10 * (a + 3) * (P * D) + 10 * (a + 3) * P * (a * (a + 12)) =
      10 * (a + 3) * P * (D + a * (a + 12)) by ring, ← hD]
    ring
  have h1 : X * (m0 * Q + m0 * a * c + 10 * a * P) ≤ X * (10 * a.factorial) := Nat.mul_le_mul_left _ I2
  have h2 : (a + 3) * P * (m0 * (9 * a + 2)) ≤ (a + 3) * P * (10 * (a * (a + 12))) := by
    apply Nat.mul_le_mul_left
    nlinarith
  have h3 : X * (10 * a.factorial) = 10 * ((a + 3) * ((a + 2) * ((a + 1) * a.factorial))) := by
    rw [hX]; ring
  have h4 : 10 * (a + 3) * P * (a * (a + 12)) = (a + 3) * P * (10 * (a * (a + 12))) := by ring
  omega

theorem empty_I1 {b R Q c P R1 Q1 c1 P1 : Nat} (h : EmptyStep b R Q c P R1 Q1 c1 P1)
    (I1 : R + P * b = b.factorial) : R1 + P1 * (b + 3) = (b + 3).factorial := by
  rw [h.hR, h.hP, fact3, ← I1]; ring

theorem empty_I2 {b m0 R Q c P R1 Q1 c1 P1 : Nat} (h : EmptyStep b R Q c P R1 Q1 c1 P1)
    (I2 : m0 * Q + m0 * b * c + 10 * b * P ≤ 10 * b.factorial) :
    m0 * Q1 + m0 * (b + 3) * c1 + 10 * (b + 3) * P1 ≤ 10 * (b + 3).factorial := by
  rw [h.hQ, h.hc, h.hP, fact3]
  have h1 := Nat.mul_le_mul_left ((b + 3) * ((b + 2) * (b + 1))) I2
  have e1 : m0 * ((b + 3) * ((b + 2) * ((b + 1) * Q)) + P * ((b + 3) * 0)) +
      m0 * (b + 3) * ((b + 2) * ((b + 1) * (b * c)) + P * ((b + 2) * 0)) +
      10 * (b + 3) * (P * (b * ((b + 1) * (b + 2)))) =
      (b + 3) * ((b + 2) * (b + 1)) * (m0 * Q + m0 * b * c + 10 * b * P) := by ring
  have e2 : 10 * ((b + 3) * ((b + 2) * ((b + 1) * b.factorial))) =
      (b + 3) * ((b + 2) * (b + 1)) * (10 * b.factorial) := by ring
  rw [e1, e2]; exact h1

theorem pow7 (a : Nat) : a ^ 6 * (a + 7) ≤ (a + 1) ^ 7 := by
  have e : (a + 1) ^ 7 = a ^ 6 * (a + 7) + (21 * a ^ 5 + 35 * a ^ 4 + 35 * a ^ 3 + 21 * a ^ 2 + 7 * a + 1) := by
    ring
  omega

/-- The decay over one walk block: `D^6 (a+7) ≤ L^6 (a+1)`. -/
theorem decay_key (a : Nat) (ha : 3 ≤ a) :
    (a * ((a + 1) * (a + 2)) - a * (a + 12)) ^ 6 * (a + 7) ≤ (a * ((a + 1) * (a + 2))) ^ 6 * (a + 1) := by
  obtain ⟨D, hD⟩ : ∃ D, a * ((a + 1) * (a + 2)) = D + a * (a + 12) :=
    ⟨_, (Nat.sub_add_cancel (walk_NL a ha)).symm⟩
  rw [hD, Nat.add_sub_cancel]
  set L := D + a * (a + 12) with hL
  have h1 : D * (a + 1) ≤ L * a := by
    have hle : L ≤ a * (a + 12) * (a + 1) := by
      rw [← hD]; nlinarith
    nlinarith
  have h2 : (D * (a + 1)) ^ 6 ≤ (L * a) ^ 6 := Nat.pow_le_pow_left h1 6
  have h3 : D ^ 6 * (a + 7) * (a + 1) ^ 6 ≤ L ^ 6 * (a + 1) * (a + 1) ^ 6 := by
    calc D ^ 6 * (a + 7) * (a + 1) ^ 6 = (D * (a + 1)) ^ 6 * (a + 7) := by ring
      _ ≤ (L * a) ^ 6 * (a + 7) := Nat.mul_le_mul_right _ h2
      _ = L ^ 6 * (a ^ 6 * (a + 7)) := by ring
      _ ≤ L ^ 6 * (a + 1) ^ 7 := Nat.mul_le_mul_left _ (pow7 a)
      _ = L ^ 6 * (a + 1) * (a + 1) ^ 6 := by ring
  exact Nat.le_of_mul_le_mul_right h3 (by positivity)

theorem step_I3 {a m0 P P1 P2 : Nat} (ha : 3 ≤ a)
    (hP1 : P1 = P * (a * ((a + 1) * (a + 2)) - a * (a + 12)))
    (hP2 : P2 = P1 * ((a + 3) * ((a + 3 + 1) * (a + 3 + 2))))
    (I3 : P ^ 6 * (a + 1) ≤ (m0 + 1) * ((a - 1).factorial) ^ 6) :
    P2 ^ 6 * (a + 6 + 1) ≤ (m0 + 1) * ((a + 6 - 1).factorial) ^ 6 := by
  have hf : (a + 6 - 1).factorial =
      ((a + 3) * ((a + 3 + 1) * (a + 3 + 2))) * ((a * ((a + 1) * (a + 2))) * (a - 1).factorial) := by
    rw [show a + 6 - 1 = (a - 1) + 6 by omega]
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.factorial_succ]
    ring
  rw [hP2, hP1, hf]
  set D := a * ((a + 1) * (a + 2)) - a * (a + 12)
  set L := a * ((a + 1) * (a + 2))
  set L1 := (a + 3) * ((a + 3 + 1) * (a + 3 + 2))
  set F := (a - 1).factorial
  have hk := decay_key a ha
  have h1 : P ^ 6 * D ^ 6 * (a + 7) * (a + 1) ≤ (m0 + 1) * F ^ 6 * L ^ 6 * (a + 1) := by
    calc P ^ 6 * D ^ 6 * (a + 7) * (a + 1) = (P ^ 6 * (a + 1)) * (D ^ 6 * (a + 7)) := by ring
      _ ≤ ((m0 + 1) * F ^ 6) * (L ^ 6 * (a + 1)) := Nat.mul_le_mul I3 hk
      _ = (m0 + 1) * F ^ 6 * L ^ 6 * (a + 1) := by ring
  have h2 : P ^ 6 * D ^ 6 * (a + 7) ≤ (m0 + 1) * F ^ 6 * L ^ 6 :=
    Nat.le_of_mul_le_mul_right h1 (by omega)
  calc (P * D * L1) ^ 6 * (a + 6 + 1) = L1 ^ 6 * (P ^ 6 * D ^ 6 * (a + 7)) := by ring
    _ ≤ L1 ^ 6 * ((m0 + 1) * F ^ 6 * L ^ 6) := Nat.mul_le_mul_left _ h2
    _ = (m0 + 1) * (L1 * (L * F)) ^ 6 := by ring

end SuperpermutationUpperBound43586371.Uniform
