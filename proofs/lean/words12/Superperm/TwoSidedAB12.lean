import LowerBounds.TheoremAWords
import LowerBounds.TheoremBWords
import Superperm.Upper12

/-!
# Twelve symbols: lower and upper bounds in one statement, with the lower bounds of Theorems A and B

The upper bound is the literal word of `Superperm/Upper12.lean`.  The lower bounds are the values for 12
symbols of `SuperpermLowerBounds.superperm_kisic_numerical_bounds` (`LowerBounds/TheoremA.lean`) and of
`SuperpermLowerBounds.superperm_boundB_numerical_bounds` (`LowerBounds/TheoremB.lean`).
`Superperm/TwoSided12.lean` has the same statement with the lower bound 522,610,764 of the preimage-chain
project.
-/

namespace SuperpermBridge

open SuperpermutationBounds

/-- 522,614,409 ≤ L(12) ≤ 522,737,175. -/
theorem ssuper_twelve_kisic : 522614409 ≤ Hunter.Ssuper 12 ∧ Hunter.Ssuper 12 ≤ 522737175 :=
  ⟨SuperpermLowerBounds.superperm_kisic_numerical_bounds.2.2.2.2.2.2.2.1,
    hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_twelve⟩

/-- 522,622,030 ≤ L(12) ≤ 522,737,175. -/
theorem ssuper_twelve_boundB : 522622030 ≤ Hunter.Ssuper 12 ∧ Hunter.Ssuper 12 ≤ 522737175 :=
  ⟨SuperpermLowerBounds.superperm_boundB_numerical_bounds.2.2.2.2.2.1,
    hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_twelve⟩

/-- The same two statements about words over `Fin 12`, with no reference to `Hunter.Ssuper`. -/
theorem words_twelve_kisic : (∃ w : List (Fin 12), Covers w ∧ w.length = 522737175) ∧
    ∀ w : List (Fin 12), Covers w → 522614409 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_twelve,
    SuperpermLowerBounds.covers_kisic_numerical_bounds.2.2.2.2.2.2.2.1⟩

theorem words_twelve_boundB : (∃ w : List (Fin 12), Covers w ∧ w.length = 522737175) ∧
    ∀ w : List (Fin 12), Covers w → 522622030 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_twelve,
    SuperpermLowerBounds.covers_boundB_numerical_bounds.2.2.2.2.2.1⟩

end SuperpermBridge

#print axioms SuperpermBridge.ssuper_twelve_kisic
#print axioms SuperpermBridge.ssuper_twelve_boundB
#print axioms SuperpermBridge.words_twelve_kisic
#print axioms SuperpermBridge.words_twelve_boundB
