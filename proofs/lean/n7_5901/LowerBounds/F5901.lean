import LowerBounds.A16Final

/-!
# 5,901 for 7 symbols from the finite statements (level 1, conditional)

`covers_5901_of_statements`: every word over `Fin 7` that contains all permutations has at least 5,901
letters, given the caps and profile statements of the proof of 5,899 (`Caps`, `Profiles`), table T'
(`KS.TableT`; only its ring row is used), Theorem K16 (`K16.TheoremK16`) and the joint statements of Table C
(`K16.Joint16`).  The searches that give these statements are parts B16 and C16 (of my plan of the Lean proof, not in this repository).

No `native_decide`.
-/

namespace SuperpermLowerBounds

open T5899

/-- **Every word over `Fin 7` that contains all permutations has at least 5,901 letters**, from the
finite statements. -/
theorem covers_5901_of_statements (hC : Caps) (hF : Profiles) (hT : KS.TableT)
    (hK : K16.TheoremK16) (hJ : K16.Joint16) :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5901 ≤ w.length := by
  have e1 : (7 - 2).factorial + 16 = 136 := by decide
  have e2 : hpv 7 + 16 + 1 = 5901 := by decide
  have h := covers_length_gt_of_no_stdConfig (k := 7) (by norm_num) 16
    (by rw [e1]; exact A16.no_config_136 hC hF hT hK hJ)
  rw [e2] at h
  exact h

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_5901_of_statements
