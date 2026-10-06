import Superperm.N9cyc.Main
import Superperm.N10cyc.Main

/-!
# Nine and ten symbols again, by the method of `Superperm/Cyc.lean`

The statements are those of `hasWord_nine` (`Superperm/Upper.lean`) and `hasWord_ten_b`
(`Superperm/Upper10b.lean`), for the same two words; only the certificate differs
(one table entry for every rotation class, the word as a literal tree of blocks).
-/

namespace LiteralSuperperm

open SuperpermutationBounds

theorem hasWord_nine_cyc : HasWord 9 408731 := N9cyc.hasWord

theorem exists_word_nine_cyc : ∃ w : List (Fin 9), Covers w ∧ w.length = 408731 :=
  ⟨N9cyc.word, N9cyc.word_covers, N9cyc.word_length⟩

theorem hasWord_ten_cyc : HasWord 10 4034855 := N10cyc.hasWord

theorem exists_word_ten_cyc : ∃ w : List (Fin 10), Covers w ∧ w.length = 4034855 :=
  ⟨N10cyc.word, N10cyc.word_covers, N10cyc.word_length⟩

end LiteralSuperperm

#print axioms LiteralSuperperm.hasWord_nine_cyc
#print axioms LiteralSuperperm.hasWord_ten_cyc
