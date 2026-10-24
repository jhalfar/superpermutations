import LowerBounds.D8
import LowerBounds.DModel

/-!
# 46,134 for 8 symbols: the statement with the searches as hypotheses

`covers_boundD_8_of_model`: from the three statements about model chains.

`covers_boundD_8_of_search`: from three equations `search … = false` about the function of
`DSearch.lean`.  This is the whole deduction; it uses no `native_decide`.  What remains is to
evaluate the three searches (`DLine1Native.lean`, `DLine2Native.lean`, `DZoneNative.lean`; the
result is in `DFinalNative.lean`).
-/

namespace SuperpermLowerBounds

/-- (H1), (H2), (H3) for model chains give 46,134. -/
theorem covers_boundD_8_of_model (h1 : ModelLine 8 4 9 56) (h2 : ModelLine 8 17 38 264)
    (h3 : ModelZone8) :
    ∀ w : List (Fin 8), SuperpermutationBounds.Covers w → 46134 ≤ w.length :=
  covers_boundD_8 (chainLine_of_model (by norm_num) h1) (chainLine_of_model (by norm_num) h2)
    (zone8_of_model h3)

/-- **Three searches that answer `false` give 46,134.**  The parameters `sz` (size of the table
of marks), `f` (fuel), `d`, `n` (depth and number of the parts) are arbitrary, `n > 0`. -/
theorem covers_boundD_8_of_search {sz₁ f₁ d₁ n₁ sz₂ f₂ d₂ n₂ sz₃ f₃ d₃ n₃ : ℕ} (hn₁ : 0 < n₁)
    (hn₂ : 0 < n₂) (hn₃ : 0 < n₃) (h1 : S.lineSearch 8 sz₁ 4 9 56 f₁ d₁ n₁ = false)
    (h2 : S.lineSearch 8 sz₂ 17 38 264 f₂ d₂ n₂ = false)
    (h3 : S.zoneSearch 8 sz₃ 4 9 56 2 17 38 264 6 f₃ d₃ n₃ = false) :
    ∀ w : List (Fin 8), SuperpermutationBounds.Covers w → 46134 ≤ w.length :=
  covers_boundD_8_of_model (modelLine_of_search (by norm_num) (by norm_num) hn₁ h1)
    (modelLine_of_search (by norm_num) (by norm_num) hn₂ h2)
    (modelZone8_of_search hn₁ hn₂ hn₃ h1 h2 h3)

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_boundD_8_of_model
#print axioms SuperpermLowerBounds.covers_boundD_8_of_search
