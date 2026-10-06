import Superperm.Bridge
import Superperm.Upper11
import PreimageChain.SuperpermNumericalBounds

/-! Lower and upper bound for eleven symbols: the lower bound is the seventh statement of
`PreimageChain.superperm_numerical_bounds_closed`, the upper bound the word of 43,930,578 letters. -/

namespace SuperpermBridge

open SuperpermutationBounds

/-- 43,916,235 ≤ L(11) ≤ 43,930,578. -/
theorem ssuper_eleven : 43916235 ≤ Hunter.Ssuper 11 ∧ Hunter.Ssuper 11 ≤ 43930578 :=
  ⟨PreimageChain.superperm_numerical_bounds_closed.2.2.2.2.2.2.1,
    hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_eleven⟩

/-- The same for words over `Fin 11`: a covering word of 43,930,578 letters exists and none has fewer
than 43,916,235. -/
theorem words_eleven : (∃ w : List (Fin 11), Covers w ∧ w.length = 43930578) ∧
    ∀ w : List (Fin 11), Covers w → 43916235 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_eleven, (hunter_le_ssuper_iff (by decide)).mp ssuper_eleven.1⟩

end SuperpermBridge

#print axioms SuperpermBridge.ssuper_eleven
#print axioms SuperpermBridge.words_eleven
