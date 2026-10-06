import LowerBounds.ChainCapacityC

/-!
# The slack of a window in closed form

The written proof defines the slack of a window as a sum over its intervals and runs:

  `slack_int = Σ_j [(k-3)(ε_j - 1) + (k-5)(p_j - 1)] + 2 Σ_t (k - 4 - f_t)`,

`p_j` the number of pieces of interval `j`, `ε_j` the sum of (deficit − 1) over its pieces,
`f_t` the length of run `t`.  `ChainCapacityC.WindowBound` uses the closed form

  `slack_int = (k-3) δ - 2 r - 2 (k-4)`.

This file proves that the two agree (`slackInt_eq`), for every way of writing a list of
deficits as intervals separated by runs of zeros, and restates the window bound with the sum
(`windowBound_iff_slackInt`).  Nothing else depends on this file.
-/

namespace SuperpermLowerBounds

namespace ChainC

/-- The list of deficits that starts with the interval `I0` and continues with, for every
entry `(f, I)` of the list, a run of `f` full pieces and the interval `I`. -/
def assemble : List ℕ → List (ℕ × List ℕ) → List ℕ
  | I0, [] => I0
  | I0, (f, I) :: rest => I0 ++ List.replicate f 0 ++ assemble I rest

/-- `(k-3)(ε - 1) + (k-5)(p - 1)` for an interval with `p` pieces and `ε = Σ (deficit - 1)`. -/
def intervalSlack (k : ℕ) (I : List ℕ) : ℤ :=
  ((k : ℤ) - 3) * (((I.sum : ℕ) : ℤ) - ((I.length : ℕ) : ℤ) - 1) +
    ((k : ℤ) - 5) * (((I.length : ℕ) : ℤ) - 1)

/-- `slack_int` as in the written proof: the sum over the intervals and over the runs. -/
def slackInt (k : ℕ) : List ℕ → List (ℕ × List ℕ) → ℤ
  | I0, [] => intervalSlack k I0
  | I0, (f, I) :: rest =>
    intervalSlack k I0 + 2 * ((k : ℤ) - 4 - (f : ℤ)) + slackInt k I rest

/-- **The slack in closed form.** -/
theorem slackInt_eq (k : ℕ) : ∀ (I0 : List ℕ) (rest : List (ℕ × List ℕ)),
    slackInt k I0 rest =
      ((k : ℤ) - 3) * (((assemble I0 rest).sum : ℕ) : ℤ) -
        2 * (((assemble I0 rest).length : ℕ) : ℤ) - 2 * ((k : ℤ) - 4)
  | I0, [] => by
    simp only [slackInt, assemble, intervalSlack]
    ring
  | I0, (f, I) :: rest => by
    have ih := slackInt_eq k I rest
    have hsum : (assemble I0 ((f, I) :: rest)).sum = I0.sum + (assemble I rest).sum := by
      simp [assemble]
    have hlen : (assemble I0 ((f, I) :: rest)).length =
        I0.length + f + (assemble I rest).length := by
      simp only [assemble, List.length_append, List.length_replicate]
    rw [hsum, hlen]
    simp only [slackInt, intervalSlack]
    rw [ih]
    push_cast
    ring

/-- The window bound of `ChainCapacityC` is `q · slack_int + bn ≥ cn · δ` with the slack of
the written proof. -/
theorem windowBound_iff_slackInt {k cn bn q : ℕ} (hk : 4 ≤ k) (I0 : List ℕ)
    (rest : List (ℕ × List ℕ)) :
    WindowBound k cn bn q (assemble I0 rest) ↔
      (cn : ℤ) * (((assemble I0 rest).sum : ℕ) : ℤ) ≤
        (q : ℤ) * slackInt k I0 rest + (bn : ℤ) := by
  rw [slackInt_eq]
  unfold WindowBound
  generalize (assemble I0 rest).sum = S
  generalize (assemble I0 rest).length = L
  have hcast : q * (2 * L + 2 * (k - 4)) + cn * S ≤ q * ((k - 3) * S) + bn ↔
      (((q * (2 * L + 2 * (k - 4)) + cn * S : ℕ)) : ℤ) ≤ ((q * ((k - 3) * S) + bn : ℕ) : ℤ) :=
    Nat.cast_le.symm
  rw [hcast]
  push_cast [Nat.cast_sub (by omega : 3 ≤ k), Nat.cast_sub hk]
  constructor <;> intro h <;> linarith

end ChainC

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.ChainC.slackInt_eq
#print axioms SuperpermLowerBounds.ChainC.windowBound_iff_slackInt
