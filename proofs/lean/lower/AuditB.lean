import LowerBounds.TheoremBWords
import Challenge

/-!
# Audit file for the lower bound with denominator k² - 4k + 1 ("Theorem B")

The statements are written out without any definition of this project: a list over `Fin k` in which every list of
`k` different letters occurs as a contiguous part has at least so many letters.  Lean is asked to accept the
theorems of `LowerBounds/TheoremBWords.lean` as proofs of exactly these statements.  Nothing here is a new proof.
-/

open SuperpermutationBounds

example {K : ℕ} (w : List (Fin K)) :
    Covers w = ∀ p : List (Fin K), p.length = K → p.Nodup → ∃ u v : List (Fin K), w = u ++ p ++ v := rfl

/-- The general statement, written out in full.  The division is the division of natural numbers, so the last
summand is the ceiling of `2((k-2)! - (k-2)) / (k² - 4k + 1)`. -/
example (k : ℕ) (hk : 7 ≤ k) (w : List (Fin k))
    (hw : ∀ p : List (Fin k), p.length = k → p.Nodup → ∃ u v : List (Fin k), w = u ++ p ++ v) :
    k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3
      + (2 * ((k - 2).factorial - (k - 2)) + (k * k - 4 * k + 1) - 1) / (k * k - 4 * k + 1) ≤ w.length :=
  SuperpermLowerBounds.covers_length_ge_boundB hk w hw

/-- The eight values, written out in full. -/
example :
    (∀ w : List (Fin 7), (∀ p : List (Fin 7), p.length = 7 → p.Nodup → ∃ u v : List (Fin 7), w = u ++ p ++ v) →
      5895 ≤ w.length) ∧
    (∀ w : List (Fin 8), (∀ p : List (Fin 8), p.length = 8 → p.Nodup → ∃ u v : List (Fin 8), w = u ++ p ++ v) →
      46129 ≤ w.length) ∧
    (∀ w : List (Fin 9), (∀ p : List (Fin 9), p.length = 9 → p.Nodup → ∃ u v : List (Fin 9), w = u ++ p ++ v) →
      408465 ≤ w.length) ∧
    (∀ w : List (Fin 10), (∀ p : List (Fin 10), p.length = 10 → p.Nodup → ∃ u v : List (Fin 10), w = u ++ p ++ v) →
      4033329 ≤ w.length) ∧
    (∀ w : List (Fin 11), (∀ p : List (Fin 11), p.length = 11 → p.Nodup → ∃ u v : List (Fin 11), w = u ++ p ++ v) →
      43917793 ≤ w.length) ∧
    (∀ w : List (Fin 12), (∀ p : List (Fin 12), p.length = 12 → p.Nodup → ∃ u v : List (Fin 12), w = u ++ p ++ v) →
      522622030 ≤ w.length) ∧
    (∀ w : List (Fin 13), (∀ p : List (Fin 13), p.length = 13 → p.Nodup → ∃ u v : List (Fin 13), w = u ++ p ++ v) →
      6746615766 ≤ w.length) ∧
    (∀ w : List (Fin 14), (∀ p : List (Fin 14), p.length = 14 → p.Nodup → ∃ u v : List (Fin 14), w = u ++ p ++ v) →
      93891107960 ≤ w.length) :=
  SuperpermLowerBounds.covers_boundB_numerical_bounds

#print axioms SuperpermLowerBounds.covers_length_ge_boundB
#print axioms SuperpermLowerBounds.covers_boundB_numerical_bounds
