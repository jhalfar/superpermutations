import Superperm.Bridge
import Superperm.Upper10b
import PreimageChain.SuperpermNumericalBounds

/-! Lower and upper bound for ten symbols with the word of 4,034,855 letters (see `Superperm/TwoSided.lean`). -/

namespace SuperpermBridge

open SuperpermutationBounds

/-- 4,033,080 ≤ L(10) ≤ 4,034,855. -/
theorem ssuper_ten_b : 4033080 ≤ Hunter.Ssuper 10 ∧ Hunter.Ssuper 10 ≤ 4034855 :=
  ⟨PreimageChain.superperm_numerical_bounds_closed.2.2.2.2.2.1,
    hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_ten_b⟩

theorem words_ten_b : (∃ w : List (Fin 10), Covers w ∧ w.length = 4034855) ∧
    ∀ w : List (Fin 10), Covers w → 4033080 ≤ w.length :=
  ⟨LiteralSuperperm.exists_word_ten_b, (hunter_le_ssuper_iff (by decide)).mp ssuper_ten_b.1⟩

end SuperpermBridge

#print axioms SuperpermBridge.ssuper_ten_b
#print axioms SuperpermBridge.words_ten_b
