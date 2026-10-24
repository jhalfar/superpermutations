/-
Written by make_final.py for the certificate C14_843_63334_16000 (s_plan2.py of proofs/lean/lower).
-/
import LowerBounds.SSound
import LowerBounds.SRun
import LowerBounds.SModel
import LowerBounds.SBridgeTheoremC
import LowerBounds.SGen.C14_843_63334_16000

-- bound 93,891,141,126 for k = 14 (c = 843/16000, b = 63334/16000)

namespace SuperpermLowerBounds

open Hunter PreimageChain SuperpermutationBounds

theorem wstatement_14_843_63334_16000 : S.WStatement 14 843 63334 16000 :=
  S.wstatement_of_search (A := 175157) (q2 := 32000) (C1 := 320000) (C2 := 352000) (fuel := 17472)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    S.runSearch_14 SGen.search_C14_843_63334_16000

theorem modelStatement_14_843_63334_16000 : ModelStatement 14 843 63334 16000 :=
  modelStatement_of_wstatement wstatement_14_843_63334_16000

theorem conditionsC_14_843_63334_16000 : ConditionsC 14 843 63334 16000 := ⟨by decide, by decide, by decide, by decide⟩

theorem boundC_14_843_63334_16000 : boundC 14 843 63334 16000 = 93891141126 := by decide

/-- Every word over 14 symbols that contains every permutation of the symbols as a factor has at
least 93,891,141,126 letters. -/
theorem covers_length_ge_93891141126 : ∀ w : List (Fin 14), Covers w → 93891141126 ≤ w.length :=
  boundC_14_843_63334_16000 ▸ covers_length_ge_boundC_of_model (by decide) conditionsC_14_843_63334_16000 modelStatement_14_843_63334_16000

/-- The shortest superpermutation on 14 symbols has at least 93,891,141,126 letters. -/
theorem ssuper_ge_93891141126 : 93891141126 ≤ Ssuper 14 :=
  boundC_14_843_63334_16000 ▸ superperm_boundC_of_model (by decide) conditionsC_14_843_63334_16000 modelStatement_14_843_63334_16000

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_length_ge_93891141126
#print axioms SuperpermLowerBounds.ssuper_ge_93891141126
