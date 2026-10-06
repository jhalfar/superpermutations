import Superperm.Bridge
import Superperm.Upper12
import PreimageChain.SuperpermNumericalBounds

/-! Lower and upper bound for twelve symbols: the lower bound is the eighth statement of
`PreimageChain.superperm_numerical_bounds_closed`, the upper bound the word of 522,737,175 letters. -/

namespace SuperpermBridge

open SuperpermutationBounds

/-- 522,610,764 ≤ L(12) ≤ 522,737,175. -/
theorem ssuper_twelve : 522610764 ≤ Hunter.Ssuper 12 ∧ Hunter.Ssuper 12 ≤ 522737175 :=
  ⟨PreimageChain.superperm_numerical_bounds_closed.2.2.2.2.2.2.2.1,
    hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_twelve⟩

/-- The same for words over `Fin 12`: a covering word of 522,737,175 letters exists and none has fewer
than 522,610,764. -/
theorem words_twelve : (∃ w : List (Fin 12), Covers w ∧ w.length = 522737175) ∧
    ∀ w : List (Fin 12), Covers w → 522610764 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_twelve, (hunter_le_ssuper_iff (by decide)).mp ssuper_twelve.1⟩

end SuperpermBridge

#print axioms SuperpermBridge.ssuper_twelve
#print axioms SuperpermBridge.words_twelve
