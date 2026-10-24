import LowerBounds.DTheorem
import LowerBounds.DModel
import LowerBounds.DSmallSearch

/-!
# Theorem D on 5 symbols, with the search evaluated by the kernel

A test of the whole new chain of proofs with no `native_decide`: the prefix search
(`DSearch.lean`) is evaluated by the kernel (`decide +kernel`), its soundness (`DSound.lean`,
`DModel.lean`) gives a chain line, and Theorem D (`DTheorem.lean`) gives a bound for
superpermutations.

On 5 symbols the line `2 r ≤ 3 δ + 6` (5 chains searched, `DSmallSearch.lean`) gives
`153 ≤ Ssuper 5`, the true value.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace SuperpermLowerBounds

open Hunter

theorem chainLine_5_2_3_6 : ChainLine 5 2 3 6 :=
  chainLine_of_model (by norm_num)
    (modelLine_of_search (by norm_num) (by norm_num) (by norm_num) lineSearch_5_2_3_6)

/-- Theorem D with the line `(2, 3, 6)`: every superpermutation on 5 symbols has at least 153
letters. -/
theorem ssuper_ge_153_D : 153 ≤ Ssuper 5 := by
  have h := superperm_boundD (k := 5) (by norm_num) [(2, 3, 6)]
    (by
      intro l hl
      rw [List.mem_singleton] at hl
      subst hl
      exact ⟨by norm_num, by norm_num, chainLine_5_2_3_6⟩)
    1
    (by
      intro p hp
      have hp0 : p = 0 := by omega
      subst hp0
      exact ⟨(2, 3, 6), List.mem_singleton_self _, by decide⟩)
  have e : hpv 5 + 1 = 153 := by decide
  rw [e] at h
  exact h

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.chainLine_5_2_3_6
#print axioms SuperpermLowerBounds.ssuper_ge_153_D
