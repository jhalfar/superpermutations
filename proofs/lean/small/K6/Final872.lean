import K6.TightConf
import K6.TightAll

/-!
# L(6) ≥ 872, checked by the kernel alone

`no_config_28`: no valid standard configuration on 6 symbols has cost at most `4! + 4 = 28`
(defect 4); from `no_config_28_of_parts` and the 72 parts of the search, each evaluated by the
kernel (`TightAll.lean`).  With Theorems W and N (`covers_length_gt_of_no_stdConfig`): every word
over 6 symbols that contains all 720 permutations has at least `hpv 6 + 4 + 1 = 872` letters.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace K6

open SuperpermLowerBounds

/-- **No valid configuration on 6 symbols of defect 4.** -/
theorem no_config_28 (c : NConfig 6) (hv : c.Valid) : ¬ c.cost ≤ (6 - 2).factorial + 4 :=
  no_config_28_of_parts tightAll1 tightAll2 tightAll3 c hv

/-- **L(6) ≥ 872**: a word over 6 symbols that contains every permutation as a contiguous part
has at least 872 letters (`Covers` is the definition of Pantone's `Challenge.lean`). -/
theorem covers_872 :
    ∀ w : List (Fin 6), SuperpermutationBounds.Covers w → 872 ≤ w.length := by
  have h := covers_length_gt_of_no_stdConfig (k := 6) (by norm_num) 4 no_config_28
  have e : hpv 6 + 4 + 1 = 872 := by decide
  rw [e] at h
  exact h

end K6

#print axioms K6.no_config_28
#print axioms K6.covers_872
