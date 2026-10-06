import LowerBounds.SFinal
import Superperm.Upper
import Superperm.Upper10b
import Superperm.Upper11

/-!
# Lower and upper bounds in one statement, with the lower bounds of Theorem C

The upper bounds are the literal words of `Superperm/Upper.lean`, `Upper10b.lean` and `Upper11.lean`.
The lower bounds are the best values of `LowerBounds/SFinal.lean` (a generated file: Theorem C with the
certificates of the finite search) for 8, 9, 10 and 11 symbols.  `Superperm/TwoSidedA.lean` and
`TwoSidedB.lean` have the same statements with the values of Theorems A and B.
-/

namespace SuperpermBridge

open SuperpermutationBounds

/-- 46,133 ≤ L(8) ≤ 46,181. -/
theorem ssuper_eight_boundC : 46133 ≤ Hunter.Ssuper 8 ∧ Hunter.Ssuper 8 ≤ 46181 :=
  ⟨SuperpermLowerBounds.ssuper_lower_bound_8, hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_eight⟩

/-- 408,469 ≤ L(9) ≤ 408,731. -/
theorem ssuper_nine_boundC : 408469 ≤ Hunter.Ssuper 9 ∧ Hunter.Ssuper 9 ≤ 408731 :=
  ⟨SuperpermLowerBounds.ssuper_lower_bound_9, hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_nine⟩

/-- 4,033,378 ≤ L(10) ≤ 4,034,855. -/
theorem ssuper_ten_boundC : 4033378 ≤ Hunter.Ssuper 10 ∧ Hunter.Ssuper 10 ≤ 4034855 :=
  ⟨SuperpermLowerBounds.ssuper_lower_bound_10, hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_ten_b⟩

/-- 43,917,903 ≤ L(11) ≤ 43,930,578. -/
theorem ssuper_eleven_boundC : 43917903 ≤ Hunter.Ssuper 11 ∧ Hunter.Ssuper 11 ≤ 43930578 :=
  ⟨SuperpermLowerBounds.ssuper_lower_bound_11, hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_eleven⟩

/-- The same four statements about words over `Fin k`, with no reference to `Hunter.Ssuper`: a covering
word of the stated length exists, and no covering word is shorter than the lower bound. -/
theorem words_eight_boundC : (∃ w : List (Fin 8), Covers w ∧ w.length = 46181) ∧
    ∀ w : List (Fin 8), Covers w → 46133 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_eight, SuperpermLowerBounds.covers_lower_bound_8⟩

theorem words_nine_boundC : (∃ w : List (Fin 9), Covers w ∧ w.length = 408731) ∧
    ∀ w : List (Fin 9), Covers w → 408469 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_nine, SuperpermLowerBounds.covers_lower_bound_9⟩

theorem words_ten_boundC : (∃ w : List (Fin 10), Covers w ∧ w.length = 4034855) ∧
    ∀ w : List (Fin 10), Covers w → 4033378 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_ten_b, SuperpermLowerBounds.covers_lower_bound_10⟩

theorem words_eleven_boundC : (∃ w : List (Fin 11), Covers w ∧ w.length = 43930578) ∧
    ∀ w : List (Fin 11), Covers w → 43917903 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_eleven, SuperpermLowerBounds.covers_lower_bound_11⟩

end SuperpermBridge

#print axioms SuperpermBridge.ssuper_eight_boundC
#print axioms SuperpermBridge.ssuper_nine_boundC
#print axioms SuperpermBridge.ssuper_ten_boundC
#print axioms SuperpermBridge.ssuper_eleven_boundC
#print axioms SuperpermBridge.words_eight_boundC
#print axioms SuperpermBridge.words_nine_boundC
#print axioms SuperpermBridge.words_ten_boundC
#print axioms SuperpermBridge.words_eleven_boundC
