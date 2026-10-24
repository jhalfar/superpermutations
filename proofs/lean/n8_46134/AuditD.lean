import LowerBounds.DFinal
import LowerBounds.DFinalNative
import Challenge

/-!
Audit file (2026-10-07) for the bound 46,134 on 8 symbols (Theorem D and the three
searches).  The statements are written out, and Lean is asked
to accept the theorems of the development as proofs of exactly these statements.  Nothing here is
a new proof.

Two levels of trust, kept apart:

* **Level 1** (no `native_decide`; axioms `propext`, `Classical.choice`, `Quot.sound`): the bound
  from three hypotheses.  It is stated twice: with the hypotheses as statements about the exact
  weight-three chains of strongly exitless paths, written in the objects of the preimage-chain
  library; and with the hypotheses as three equations about the search function of
  `LowerBounds/DSearch.lean`.
* **Level 2** (with `native_decide`): the bound with no hypothesis, written with no definition of
  this project.  It depends in addition on three axioms, one for each search evaluated as compiled
  code; `#print axioms` lists them.
-/

open SuperpermutationBounds Hunter PreimageChain

example {K : ℕ} (w : List (Fin K)) :
    Covers w = ∀ p : List (Fin K), p.length = K → p.Nodup → ∃ u v : List (Fin K), w = u ++ p ++ v := rfl

/-! ### Level 1 -/

/-- From (H1), (H2), (H3), written out. -/
example
    (h1 : ∀ (p : HPath 8), p.StronglyExitless → ∀ chain : ExactWeightThreePieceChain p,
      4 * chain.pieces.length ≤ 9 * (chain.pieces.map ComponentIntervalPiece.deficit).sum + 56)
    (h2 : ∀ (p : HPath 8), p.StronglyExitless → ∀ chain : ExactWeightThreePieceChain p,
      17 * chain.pieces.length ≤
        38 * (chain.pieces.map ComponentIntervalPiece.deficit).sum + 264)
    (h3 : ∀ (p : HPath 8), p.StronglyExitless → ∀ chain : ExactWeightThreePieceChain p,
      9 * (chain.pieces.map ComponentIntervalPiece.deficit).sum + 54 ≤ 4 * chain.pieces.length →
      38 * (chain.pieces.map ComponentIntervalPiece.deficit).sum + 258 ≤
        17 * chain.pieces.length →
      4 * chain.pieces.length = 9 * (chain.pieces.map ComponentIntervalPiece.deficit).sum + 56) :
    ∀ w : List (Fin 8),
      (∀ p : List (Fin 8), p.length = 8 → p.Nodup → ∃ u v : List (Fin 8), w = u ++ p ++ v) →
      46134 ≤ w.length :=
  SuperpermLowerBounds.covers_boundD_8 h1 h2 h3

/-- From three equations about the search function (the ones that level 2 evaluates). -/
example
    (h1 : SuperpermLowerBounds.S.lineSearch 8 2097152 4 9 56 400 40 251 = false)
    (h2 : SuperpermLowerBounds.S.lineSearch 8 2097152 17 38 264 400 40 251 = false)
    (h3 : SuperpermLowerBounds.S.zoneSearch 8 2097152 4 9 56 2 17 38 264 6 400 40 251 = false) :
    ∀ w : List (Fin 8),
      (∀ p : List (Fin 8), p.length = 8 → p.Nodup → ∃ u v : List (Fin 8), w = u ++ p ++ v) →
      46134 ≤ w.length :=
  SuperpermLowerBounds.covers_boundD_8_of_search (by norm_num) (by norm_num) (by norm_num) h1 h2 h3

/-! ### Level 2 -/

/-- The final statement, with no definition of this project and no hypothesis. -/
example : ∀ w : List (Fin 8),
    (∀ p : List (Fin 8), p.length = 8 → p.Nodup → ∃ u v : List (Fin 8), w = u ++ p ++ v) →
    46134 ≤ w.length :=
  SuperpermLowerBounds.covers_lower_bound_8_native

/-! ### Axioms -/

-- level 1
#print axioms SuperpermLowerBounds.covers_boundD_8
#print axioms SuperpermLowerBounds.covers_boundD_8_of_search
#print axioms SuperpermLowerBounds.theoremD_pathwise
#print axioms SuperpermLowerBounds.superperm_boundD
-- level 2
#print axioms SuperpermLowerBounds.covers_lower_bound_8_native
