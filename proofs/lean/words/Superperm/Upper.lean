import Superperm.N7.Main
import Superperm.N8.Main
import Superperm.N9.Main

/-!
# Upper bounds from literal words

Statements in the vocabulary of Pantone's `Challenge.lean`
(`SuperpermutationBounds.Covers`, `SuperpermutationBounds.HasWord`).
Each is proven by checking one literal word in the Lean kernel
(`Superperm/Literal.lean` for the checker and its soundness proof,
`Superperm/N7`, `N8`, `N9` for the words and their certificates).

| n | letters | word | Pantone's Lean theorem |
|---|---|---|---|
| 7 | 5,905 | Teodorescu (Aug 2026) | none |
| 8 | 46,181 | Pantone | `word_eight`, 46,181 (structural proof) |
| 9 | 408,731 | rumstd | `word_nine`, 408,743 |
-/

namespace LiteralSuperperm

open SuperpermutationBounds

/-- A superpermutation on 7 symbols with 5,905 letters. -/
theorem hasWord_seven : HasWord 7 5905 := N7.hasWord

/-- A superpermutation on 8 symbols with 46,181 letters (a second, independent proof of
Pantone's `word_eight`, from the literal word). -/
theorem hasWord_eight : HasWord 8 46181 := N8.hasWord

/-- A superpermutation on 9 symbols with 408,731 letters (Pantone's `word_nine` has 408,743). -/
theorem hasWord_nine : HasWord 9 408731 := N9.hasWord

/-- The same with the exact lengths. -/
theorem exists_word_seven : ∃ w : List (Fin 7), Covers w ∧ w.length = 5905 :=
  ⟨N7.word, N7.word_covers, N7.word_length⟩

theorem exists_word_eight : ∃ w : List (Fin 8), Covers w ∧ w.length = 46181 :=
  ⟨N8.word, N8.word_covers, N8.word_length⟩

theorem exists_word_nine : ∃ w : List (Fin 9), Covers w ∧ w.length = 408731 :=
  ⟨N9.word, N9.word_covers, N9.word_length⟩

end LiteralSuperperm

#print axioms LiteralSuperperm.hasWord_seven
#print axioms LiteralSuperperm.hasWord_eight
#print axioms LiteralSuperperm.hasWord_nine
#print axioms LiteralSuperperm.exists_word_seven
#print axioms LiteralSuperperm.exists_word_eight
#print axioms LiteralSuperperm.exists_word_nine
