import K6.Cap
import K6.CapEval

/-!
# Chain caps on 6 symbols, checked by the kernel

`chainCap6`: a chain on 6 symbols (rows joined by seams of weight 3, blocks in pairwise different
rotation classes; `IsModelChain` of `SModelDef.lean`) with `x ≤ 20` holes has at most `W6[x]` rows,
`W6 = 4 4 7 7 10 10 11 13 14 15 16 17 19 19 22 23 24 25 26 27 28`.
-/

namespace K6

open SuperpermLowerBounds SuperpermLowerBounds.PS

theorem tabB : TabAgrees TB_0_20 (seqBad [W6] 0 0 20 0) = true := by decide +kernel

theorem tabK : TabAgrees TK_0_20 (seqKeepN [W6] 0 0 20 0) = true := by decide +kernel

/-- **Chain caps on 6 symbols.** -/
theorem chainCap6 : ChainCapK 6 (capF [W6] 0) 20 :=
  chainCapK_of_capParts tabB tabK capEval

/-- **Chain caps on 6 symbols**, for chains of words. -/
theorem wcap6 : WCap 6 (capF [W6] 0) 20 :=
  wcap_of_capParts tabB tabK capEval

end K6

#print axioms K6.chainCap6
#print axioms K6.wcap6
