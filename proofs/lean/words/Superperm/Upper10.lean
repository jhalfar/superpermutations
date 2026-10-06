import Superperm.N10.Main

/-!
# The upper bound for ten symbols from a literal word

rumstd's word of 4,034,873 letters, checked in the Lean kernel.  Pantone's Lean theorem
`word_ten_structural` has 4,035,009.
-/

namespace LiteralSuperperm

open SuperpermutationBounds

/-- A superpermutation on 10 symbols with 4,034,873 letters. -/
theorem hasWord_ten : HasWord 10 4034873 := N10.hasWord

theorem exists_word_ten : ∃ w : List (Fin 10), Covers w ∧ w.length = 4034873 :=
  ⟨N10.word, N10.word_covers, N10.word_length⟩

end LiteralSuperperm

#print axioms LiteralSuperperm.hasWord_ten
#print axioms LiteralSuperperm.exists_word_ten
