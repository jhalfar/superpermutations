import Superperm.Bridge
import Superperm.Upper10
import PreimageChain.SuperpermNumericalBounds

/-! Lower and upper bound for ten symbols in one statement (see `Superperm/TwoSided.lean`). -/

namespace SuperpermBridge

open SuperpermutationBounds

/-- 4,033,080 ≤ L(10) ≤ 4,034,873. -/
theorem ssuper_ten : 4033080 ≤ Hunter.Ssuper 10 ∧ Hunter.Ssuper 10 ≤ 4034873 :=
  ⟨PreimageChain.superperm_numerical_bounds_closed.2.2.2.2.2.1,
    hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_ten⟩

theorem words_ten : (∃ w : List (Fin 10), Covers w ∧ w.length = 4034873) ∧
    ∀ w : List (Fin 10), Covers w → 4033080 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_ten, (hunter_le_ssuper_iff (by decide)).mp ssuper_ten.1⟩

end SuperpermBridge

#print axioms SuperpermBridge.ssuper_ten
#print axioms SuperpermBridge.words_ten
