import Superperm.N10b.Main

/-!
# Ten symbols, 4,034,855 letters

The word `words/superpermutation-10-4034855.txt.xz` of github.com/jhalfar/superpermutations, checked in the
Lean kernel like the words of `Superperm/Upper.lean`.  rumstd's 4,034,873 is `Superperm/Upper10.lean`;
Pantone's Lean theorem `word_ten_structural` has 4,035,009.
-/

namespace LiteralSuperperm

open SuperpermutationBounds

/-- A superpermutation on 10 symbols with 4,034,855 letters. -/
theorem hasWord_ten_b : HasWord 10 4034855 := N10b.hasWord

theorem exists_word_ten_b : ∃ w : List (Fin 10), Covers w ∧ w.length = 4034855 :=
  ⟨N10b.word, N10b.word_covers, N10b.word_length⟩

end LiteralSuperperm

#print axioms LiteralSuperperm.hasWord_ten_b
#print axioms LiteralSuperperm.exists_word_ten_b
