import SuperpermutationUpperBound1771.Corollaries
import Challenge

/-!
# Audit file for the coefficient 1771/3456

This file restates the results in the vocabulary of Pantone's `Challenge.lean` only (`Covers`, `HasWord`, `F3`),
in the shape of his `Finite` and `Eventual` with the constants `1771/3456` and `25/1152`, and asks Lean to accept
the theorems of `SuperpermutationUpperBound1771` as proofs of exactly these statements.  Nothing here is a new
proof.  A reader who wants to know what has been proven needs to read only this file and `Challenge.lean`.
-/

open SuperpermutationBounds

/-! The three definitions the statements rest on, pinned here by `rfl`, so that this file does not depend on
which copy of `Challenge.lean` the imported module was compiled from. -/

example {K : ℕ} (w : List (Fin K)) :
    Covers w = ∀ p : List (Fin K), p.length = K → p.Nodup → ∃ u v : List (Fin K), w = u ++ p ++ v := rfl

example (K : ℕ) :
    F3 K = (Nat.factorial K : ℚ) + (Nat.factorial (K - 1) : ℚ) + (Nat.factorial (K - 2) : ℚ) := rfl

example (K bound : ℕ) :
    HasWord K bound = ∃ w : List (Fin K), Covers w ∧ w.length ≤ bound := rfl

/-- The cost of `Challenge.lean` with `1771/3456` in place of `43/80` and `25/1152` in place of `17/240`,
written with natural-number parameters. -/
def Cost1771 (m a : ℕ) : ℚ :=
  (((m + 2).factorial + (m + 1).factorial + m.factorial : ℕ) : ℚ)
    + (1771 / 3456 : ℚ) * ((m - 1).factorial : ℚ)
    + ((a - 2 : ℕ) : ℚ) * (25 / 1152 : ℚ) * ((m - 1).factorial : ℚ) / ((m - 1 : ℕ) : ℚ)
    + ((m - a : ℕ) : ℚ) *
        min ((25 / 1152 : ℚ) * ((m - 1).factorial : ℚ) / ((m - 1 : ℕ) : ℚ))
          (((m + 1).factorial : ℚ) / ((a + 1).factorial : ℚ))

/-- 13 symbols. -/
example : HasWord 13 6747849960 := SuperpermutationUpperBound1771.word_thirteen

/-- Every size from 13 symbols on. -/
example : ∀ m a : ℕ, 11 ≤ m → 2 ≤ a → a ≤ m →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost1771 m a :=
  fun m a hm ha ham => SuperpermutationUpperBound1771.finite_bound m hm a ha ham

/-- The eventual coefficient, in the shape of `SuperpermutationBounds.Eventual`. -/
example : ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, 13 ≤ N ∧
    ∀ K : ℕ, N ≤ K → ∃ w : List (Fin K),
      Covers w ∧ (w.length : ℚ) ≤
        F3 K + ((1771 / 3456 : ℚ) + ε) * (Nat.factorial (K - 3) : ℚ) :=
  SuperpermutationUpperBound1771.eventual_bound

/-- Three values of the bound, for 14, 15 and 16 symbols. -/
example : HasWord 14 93905309790 := SuperpermutationUpperBound1771.hasWord_fourteen
example : HasWord 15 1401331300446 := SuperpermutationUpperBound1771.hasWord_fifteen
example : HasWord 16 22320908101800 := SuperpermutationUpperBound1771.hasWord_sixteen

#print axioms SuperpermutationUpperBound1771.word_thirteen
#print axioms SuperpermutationUpperBound1771.finite_bound
#print axioms SuperpermutationUpperBound1771.eventual_bound
#print axioms SuperpermutationUpperBound1771.hasWord_fourteen
#print axioms SuperpermutationUpperBound1771.hasWord_fifteen
#print axioms SuperpermutationUpperBound1771.hasWord_sixteen
