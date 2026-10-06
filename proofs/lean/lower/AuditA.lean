import LowerBounds.TheoremAWords
import Challenge

/-!
# Audit file for the lower bound with denominator k(k-3) ("Theorem A")

The statements are written out without any definition of this project: a list over `Fin k` in which every list of
`k` different letters occurs as a contiguous part has at least so many letters.  Lean is asked to accept the
theorems of `LowerBounds/TheoremAWords.lean` as proofs of exactly these statements.  Nothing here is a new proof.
-/

open SuperpermutationBounds

example {K : ℕ} (w : List (Fin K)) :
    Covers w = ∀ p : List (Fin K), p.length = K → p.Nodup → ∃ u v : List (Fin K), w = u ++ p ++ v := rfl

/-- The general statement, written out in full.  The division is the division of natural numbers, so the last
summand is the ceiling of `2((k-2)! - (k-2)) / (k(k-3))`. -/
example (k : ℕ) (hk : 5 ≤ k) (w : List (Fin k))
    (hw : ∀ p : List (Fin k), p.length = k → p.Nodup → ∃ u v : List (Fin k), w = u ++ p ++ v) :
    k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3
      + (2 * ((k - 2).factorial - (k - 2)) + k * (k - 3) - 1) / (k * (k - 3)) ≤ w.length :=
  SuperpermLowerBounds.covers_length_ge_kisicBound hk w hw

/-- The ten values, written out in full. -/
example :
    (∀ w : List (Fin 5), (∀ p : List (Fin 5), p.length = 5 → p.Nodup → ∃ u v : List (Fin 5), w = u ++ p ++ v) →
      153 ≤ w.length) ∧
    (∀ w : List (Fin 6), (∀ p : List (Fin 6), p.length = 6 → p.Nodup → ∃ u v : List (Fin 6), w = u ++ p ++ v) →
      870 ≤ w.length) ∧
    (∀ w : List (Fin 7), (∀ p : List (Fin 7), p.length = 7 → p.Nodup → ∃ u v : List (Fin 7), w = u ++ p ++ v) →
      5893 ≤ w.length) ∧
    (∀ w : List (Fin 8), (∀ p : List (Fin 8), p.length = 8 → p.Nodup → ∃ u v : List (Fin 8), w = u ++ p ++ v) →
      46121 ≤ w.length) ∧
    (∀ w : List (Fin 9), (∀ p : List (Fin 9), p.length = 9 → p.Nodup → ∃ u v : List (Fin 9), w = u ++ p ++ v) →
      408433 ≤ w.length) ∧
    (∀ w : List (Fin 10), (∀ p : List (Fin 10), p.length = 10 → p.Nodup → ∃ u v : List (Fin 10), w = u ++ p ++ v) →
      4033159 ≤ w.length) ∧
    (∀ w : List (Fin 11), (∀ p : List (Fin 11), p.length = 11 → p.Nodup → ∃ u v : List (Fin 11), w = u ++ p ++ v) →
      43916736 ≤ w.length) ∧
    (∀ w : List (Fin 12), (∀ p : List (Fin 12), p.length = 12 → p.Nodup → ∃ u v : List (Fin 12), w = u ++ p ++ v) →
      522614409 ≤ w.length) ∧
    (∀ w : List (Fin 13), (∀ p : List (Fin 13), p.length = 13 → p.Nodup → ∃ u v : List (Fin 13), w = u ++ p ++ v) →
      6746553315 ≤ w.length) ∧
    (∀ w : List (Fin 14), (∀ p : List (Fin 14), p.length = 14 → p.Nodup → ∃ u v : List (Fin 14), w = u ++ p ++ v) →
      93890534411 ≤ w.length) :=
  SuperpermLowerBounds.covers_kisic_numerical_bounds

#print axioms SuperpermLowerBounds.covers_length_ge_kisicBound
#print axioms SuperpermLowerBounds.covers_kisic_numerical_bounds
