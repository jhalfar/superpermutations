import LowerBounds.TheoremAWords
import Superperm.Upper
import Superperm.Upper10b
import Superperm.Upper11

/-!
# Lower and upper bounds in one statement, with the lower bounds of Theorem A

The upper bounds are the literal words of `Superperm/Upper.lean`, `Upper10b.lean` and `Upper11.lean`.
The lower bounds are the values of `SuperpermLowerBounds.superperm_kisic_numerical_bounds`
(`LowerBounds/TheoremA.lean`) for 9, 10 and 11 symbols.  `Superperm/TwoSidedB.lean` has the same statements
with the larger values of Theorem B, and `Superperm/TwoSided.lean`, `TwoSided10b.lean` and `TwoSided11.lean`
of the words have them with the lower bounds 408,418, 4,033,080 and 43,916,235 of the preimage-chain project.
-/

namespace SuperpermBridge

open SuperpermutationBounds

/-- 408,433 ≤ L(9) ≤ 408,731. -/
theorem ssuper_nine_kisic : 408433 ≤ Hunter.Ssuper 9 ∧ Hunter.Ssuper 9 ≤ 408731 :=
  ⟨SuperpermLowerBounds.superperm_kisic_numerical_bounds.2.2.2.2.1,
    hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_nine⟩

/-- 4,033,159 ≤ L(10) ≤ 4,034,855. -/
theorem ssuper_ten_kisic : 4033159 ≤ Hunter.Ssuper 10 ∧ Hunter.Ssuper 10 ≤ 4034855 :=
  ⟨SuperpermLowerBounds.superperm_kisic_numerical_bounds.2.2.2.2.2.1,
    hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_ten_b⟩

/-- 43,916,736 ≤ L(11) ≤ 43,930,578. -/
theorem ssuper_eleven_kisic : 43916736 ≤ Hunter.Ssuper 11 ∧ Hunter.Ssuper 11 ≤ 43930578 :=
  ⟨SuperpermLowerBounds.superperm_kisic_numerical_bounds.2.2.2.2.2.2.1,
    hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_eleven⟩

/-- The same three statements about words over `Fin k`, with no reference to `Hunter.Ssuper`: a covering
word of the stated length exists, and no covering word is shorter than the lower bound. -/
theorem words_nine_kisic : (∃ w : List (Fin 9), Covers w ∧ w.length = 408731) ∧
    ∀ w : List (Fin 9), Covers w → 408433 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_nine, SuperpermLowerBounds.covers_kisic_numerical_bounds.2.2.2.2.1⟩

theorem words_ten_kisic : (∃ w : List (Fin 10), Covers w ∧ w.length = 4034855) ∧
    ∀ w : List (Fin 10), Covers w → 4033159 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_ten_b, SuperpermLowerBounds.covers_kisic_numerical_bounds.2.2.2.2.2.1⟩

theorem words_eleven_kisic : (∃ w : List (Fin 11), Covers w ∧ w.length = 43930578) ∧
    ∀ w : List (Fin 11), Covers w → 43916736 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_eleven, SuperpermLowerBounds.covers_kisic_numerical_bounds.2.2.2.2.2.2.1⟩

end SuperpermBridge

#print axioms SuperpermBridge.ssuper_nine_kisic
#print axioms SuperpermBridge.ssuper_ten_kisic
#print axioms SuperpermBridge.ssuper_eleven_kisic
#print axioms SuperpermBridge.words_nine_kisic
#print axioms SuperpermBridge.words_ten_kisic
#print axioms SuperpermBridge.words_eleven_kisic
