import LowerBounds.TheoremCWords
import Challenge

/-!
# Audit file for the conditional lower bound "Theorem C"

The conclusions are written out without any definition of this project.  The one hypothesis, `HStatement`, is a
statement about the chains of Liu's library; it is pinned here by `rfl` to its definition, and so is the linear
inequality `WindowBound` it asks for.  Lean is asked to accept the theorems of `LowerBounds/TheoremCWords.lean` as
proofs of exactly these statements.  Nothing here is a new proof, and nothing here proves `HStatement`.
-/

open SuperpermutationBounds Hunter PreimageChain SuperpermLowerBounds

example {K : ℕ} (w : List (Fin K)) :
    Covers w = ∀ p : List (Fin K), p.length = K → p.Nodup → ∃ u v : List (Fin K), w = u ++ p ++ v := rfl

/-- The hypothesis: for every strongly exitless path and every exact weight-three chain of it whose list of piece
deficits is a window, the window inequality holds. -/
example (k cn bn q : ℕ) :
    HStatement k cn bn q =
      ∀ (p : HPath k), p.StronglyExitless → ∀ chain : ExactWeightThreePieceChain p,
        ChainC.IsWindow (chain.pieces.map ComponentIntervalPiece.deficit) →
        ChainC.WindowBound k cn bn q (chain.pieces.map ComponentIntervalPiece.deficit) := rfl

/-- The window inequality: with `r` pieces and total deficit `δ`, `q(2r + 2(k-4)) + cn·δ ≤ q(k-3)δ + bn`. -/
example (k cn bn q : ℕ) (ds : List ℕ) :
    ChainC.WindowBound k cn bn q ds =
      (q * (2 * ds.length + 2 * (k - 4)) + cn * ds.sum ≤ q * ((k - 3) * ds.sum) + bn) := rfl

/-- The general statement, written out in full (c = cn / q, b = bn / q; the division of natural numbers at the end
is a ceiling). -/
example (k cn bn q : ℕ) (hk : 5 ≤ k) (hq : 0 < q)
    (h1 : bn + cn * k ≤ q * k * (k - 5))
    (h2 : bn + 4 * cn + 2 * q * k ≤ 4 * q * (k - 3) + (q * (k - 5) - cn) * (k - 2))
    (h3 : 2 * q * (k - 2) + bn + cn * (k - 1) ≤ q * (k * k - 4 * k + 1))
    (hH : HStatement k cn bn q) (w : List (Fin k))
    (hw : ∀ p : List (Fin k), p.length = k → p.Nodup → ∃ u v : List (Fin k), w = u ++ p ++ v) :
    k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3
      + (2 * q * (k - 2).factorial - (2 * q * (k - 2) + bn) + (q * (k * k - 4 * k + 1) - cn * (k - 1)) - 1)
          / (q * (k * k - 4 * k + 1) - cn * (k - 1)) ≤ w.length :=
  covers_length_ge_boundC hk ⟨hq, h1, h2, h3⟩ hH w hw

/-- The seven instances, each with its hypothesis. -/
example : HStatement 8 9 292 20 → ∀ w : List (Fin 8),
    (∀ p : List (Fin 8), p.length = 8 → p.Nodup → ∃ u v : List (Fin 8), w = u ++ p ++ v) → 46133 ≤ w.length :=
  covers_boundC_8

example : HStatement 9 1 38 10 → ∀ w : List (Fin 9),
    (∀ p : List (Fin 9), p.length = 9 → p.Nodup → ∃ u v : List (Fin 9), w = u ++ p ++ v) → 408469 ≤ w.length :=
  covers_boundC_9

example : HStatement 10 47 704 200 → ∀ w : List (Fin 10),
    (∀ p : List (Fin 10), p.length = 10 → p.Nodup → ∃ u v : List (Fin 10), w = u ++ p ++ v) → 4033377 ≤ w.length :=
  covers_boundC_10

example : HStatement 11 7 296 80 → ∀ w : List (Fin 11),
    (∀ p : List (Fin 11), p.length = 11 → p.Nodup → ∃ u v : List (Fin 11), w = u ++ p ++ v) → 43917898 ≤ w.length :=
  covers_boundC_11

example : HStatement 12 19 1064 500 → ∀ w : List (Fin 12),
    (∀ p : List (Fin 12), p.length = 12 → p.Nodup → ∃ u v : List (Fin 12), w = u ++ p ++ v) → 522622354 ≤ w.length :=
  covers_boundC_12

example : HStatement 13 61 1192 400 → ∀ w : List (Fin 13),
    (∀ p : List (Fin 13), p.length = 13 → p.Nodup → ∃ u v : List (Fin 13), w = u ++ p ++ v) → 6746626424 ≤ w.length :=
  covers_boundC_13

example : HStatement 14 19 1368 400 → ∀ w : List (Fin 14),
    (∀ p : List (Fin 14), p.length = 14 → p.Nodup → ∃ u v : List (Fin 14), w = u ++ p ++ v) → 93891137847 ≤ w.length :=
  covers_boundC_14

#print axioms SuperpermLowerBounds.covers_length_ge_boundC
#print axioms SuperpermLowerBounds.covers_boundC_8
#print axioms SuperpermLowerBounds.covers_boundC_9
#print axioms SuperpermLowerBounds.covers_boundC_10
#print axioms SuperpermLowerBounds.covers_boundC_14
