import LowerBounds.SFinalSmall
import Superperm.Upper12

/-!
# Twelve symbols: lower and upper bound in one statement, with the lower bound of Theorem C

The upper bound is the literal word of `Superperm/Upper12.lean`.  The lower bound 522,622,378 is the value for
12 symbols of `LowerBounds/SFinalSmall.lean` of `../lower` (a generated file: Theorem C with the small
certificates of the finite search, which the default level of `../lower/build.sh` checks).
`Superperm/TwoSidedAB12.lean` has the same statement with the values of Theorems A and B, and
`Superperm/TwoSided12.lean` with the lower bound 522,610,764 of the preimage-chain project.
-/

namespace SuperpermBridge

open SuperpermutationBounds

/-- 522,622,378 ≤ L(12) ≤ 522,737,175. -/
theorem ssuper_twelve_boundC : 522622378 ≤ Hunter.Ssuper 12 ∧ Hunter.Ssuper 12 ≤ 522737175 :=
  ⟨SuperpermLowerBounds.ssuper_lower_bound_12_small,
    hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_twelve⟩

/-- The same statement about words over `Fin 12`, with no reference to `Hunter.Ssuper`. -/
theorem words_twelve_boundC : (∃ w : List (Fin 12), Covers w ∧ w.length = 522737175) ∧
    ∀ w : List (Fin 12), Covers w → 522622378 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_twelve, SuperpermLowerBounds.covers_lower_bound_12_small⟩

end SuperpermBridge

#print axioms SuperpermBridge.ssuper_twelve_boundC
#print axioms SuperpermBridge.words_twelve_boundC
