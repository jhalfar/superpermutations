import Superperm.Bridge
import Superperm.Upper
import PreimageChain.SuperpermNumericalBounds

/-!
# Lower and upper bounds in one statement

The lower bounds are `PreimageChain.superperm_numerical_bounds_closed` (Haruhiyuki's
preimage-chain project on top of the Hunter–Raudvere library); the upper bounds are the
literal words of `Superperm/Upper.lean`.  `Superperm/Bridge.lean` connects the two
vocabularies.

Building this file needs the 151 modules of the two lower-bound libraries
(`build.sh` compiles them from their sources).
-/

namespace SuperpermBridge

open SuperpermutationBounds

/-- 5,892 ≤ L(7) ≤ 5,905. -/
theorem ssuper_seven : 5892 ≤ Hunter.Ssuper 7 ∧ Hunter.Ssuper 7 ≤ 5905 :=
  ⟨PreimageChain.superperm_numerical_bounds_closed.2.2.1,
    hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_seven⟩

/-- 46,118 ≤ L(8) ≤ 46,181. -/
theorem ssuper_eight : 46118 ≤ Hunter.Ssuper 8 ∧ Hunter.Ssuper 8 ≤ 46181 :=
  ⟨PreimageChain.superperm_numerical_bounds_closed.2.2.2.1,
    hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_eight⟩

/-- 408,418 ≤ L(9) ≤ 408,731. -/
theorem ssuper_nine : 408418 ≤ Hunter.Ssuper 9 ∧ Hunter.Ssuper 9 ≤ 408731 :=
  ⟨PreimageChain.superperm_numerical_bounds_closed.2.2.2.2.1,
    hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_nine⟩

/-- The same three statements about words over `Fin k`, with no reference to either library's
own notion of a superpermutation: a covering word of the stated length exists, and no covering
word is shorter than the lower bound. -/
theorem words_seven : (∃ w : List (Fin 7), Covers w ∧ w.length = 5905) ∧
    ∀ w : List (Fin 7), Covers w → 5892 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_seven, (hunter_le_ssuper_iff (by decide)).mp ssuper_seven.1⟩

theorem words_eight : (∃ w : List (Fin 8), Covers w ∧ w.length = 46181) ∧
    ∀ w : List (Fin 8), Covers w → 46118 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_eight, (hunter_le_ssuper_iff (by decide)).mp ssuper_eight.1⟩

theorem words_nine : (∃ w : List (Fin 9), Covers w ∧ w.length = 408731) ∧
    ∀ w : List (Fin 9), Covers w → 408418 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_nine, (hunter_le_ssuper_iff (by decide)).mp ssuper_nine.1⟩

end SuperpermBridge

#print axioms SuperpermBridge.ssuper_seven
#print axioms SuperpermBridge.ssuper_eight
#print axioms SuperpermBridge.ssuper_nine
#print axioms SuperpermBridge.words_seven
#print axioms SuperpermBridge.words_eight
#print axioms SuperpermBridge.words_nine
