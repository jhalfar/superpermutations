import K6.Knap
import LowerBounds.NTheorem

/-!
# L(6) ≥ 871, checked by the kernel alone

`no_config_27`: no valid standard configuration on 6 symbols has cost at most `4! + 3 = 27`
(defect 3).  With Theorems W and N in Lean (`covers_length_gt_of_no_stdConfig`,
`NTheorem.lean`): every word over 6 symbols that contains all 720 permutations has at least
`hpv 6 + 3 + 1 = 871` letters.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace K6

open SuperpermLowerBounds Hunter PreimageChain

theorem all4 {f : ℕ → Bool} {n : ℕ} (h : (List.range n).all f = true) {i : ℕ} (hi : i < n) :
    f i = true := List.all_eq_true.mp h i (List.mem_range.mpr hi)

/-- **No valid configuration on 6 symbols of defect 3.** -/
theorem no_config_27 (c : NConfig 6) (hv : c.Valid) : ¬ c.cost ≤ (6 - 2).factorial + 3 := by
  intro hc
  have hf : (6 - 2).factorial = 24 := by decide
  have hc' : c.cost ≤ 24 + 3 := by omega
  obtain ⟨ht, hH, h6, hE, hK⟩ := fam_tables hv hc'
  have hK' := hK (by omega)
  have h1 := all4 chk3 (i := (opens c).length) (by omega)
  have ht0 : ((opens c).length == 0) = false := by
    simp only [beq_eq_false_iff_ne]
    omega
  rw [ht0, Bool.false_or] at h1
  have h2 := all4 h1 (i := (closeds c).length) (by omega)
  have h3 := all4 h2 (i := rowsHoles 6 (opens c).flatten) (by omega)
  have h4 := all4 h3 (i := rowsHoles 6 (closeds c).flatten) (by omega)
  have hle : (rowsHoles 6 (opens c).flatten + rowsHoles 6 (closeds c).flatten +
      5 * ((opens c).length - 1) ≤ 15) = True := by simp only [eq_iff_iff, iff_true]; omega
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    decide_eq_true_eq] at h4
  rcases h4 with h4 | h4
  · omega
  · push_cast at hE
    linarith

/-- **L(6) ≥ 871**: a word over 6 symbols that contains every permutation as a contiguous part
has at least 871 letters (`Covers` is the definition of Pantone's `Challenge.lean`). -/
theorem covers_871 :
    ∀ w : List (Fin 6), SuperpermutationBounds.Covers w → 871 ≤ w.length := by
  have h := covers_length_gt_of_no_stdConfig (k := 6) (by norm_num) 3 no_config_27
  have e : hpv 6 + 3 + 1 = 871 := by decide
  rw [e] at h
  exact h

end K6

#print axioms K6.no_config_27
#print axioms K6.covers_871
