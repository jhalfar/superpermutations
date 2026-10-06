import LowerBounds.TheoremB
import Superperm.Bridge

/-!
# Theorem B for covering words over `Fin k`

The same bounds in the vocabulary of `Challenge.lean` of the upper-bound project: a word
`w : List (Fin k)` with `SuperpermutationBounds.Covers w` contains every duplicate-free list
of length `k` as a factor.  `SuperpermBridge.hunter_le_ssuper_iff` translates
`L ≤ Hunter.Ssuper k` into `∀ w, Covers w → L ≤ w.length`.
-/

namespace SuperpermLowerBounds

open SuperpermutationBounds

/-- Theorem B for covering words. -/
theorem covers_length_ge_boundB {k : ℕ} (hk : 7 ≤ k) :
    ∀ w : List (Fin k), Covers w → boundB k ≤ w.length :=
  (SuperpermBridge.hunter_le_ssuper_iff (by omega)).mp (superperm_boundB hk)

/-- The values of Theorem B for covering words on 7 to 14 symbols. -/
theorem covers_boundB_numerical_bounds :
    (∀ w : List (Fin 7), Covers w → 5895 ≤ w.length) ∧
    (∀ w : List (Fin 8), Covers w → 46129 ≤ w.length) ∧
    (∀ w : List (Fin 9), Covers w → 408465 ≤ w.length) ∧
    (∀ w : List (Fin 10), Covers w → 4033329 ≤ w.length) ∧
    (∀ w : List (Fin 11), Covers w → 43917793 ≤ w.length) ∧
    (∀ w : List (Fin 12), Covers w → 522622030 ≤ w.length) ∧
    (∀ w : List (Fin 13), Covers w → 6746615766 ≤ w.length) ∧
    (∀ w : List (Fin 14), Covers w → 93891107960 ≤ w.length) := by
  obtain ⟨h7, h8, h9, h10, h11, h12, h13, h14⟩ := superperm_boundB_numerical_bounds
  exact ⟨(SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h7,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h8,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h9,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h10,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h11,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h12,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h13,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h14⟩

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_length_ge_boundB
#print axioms SuperpermLowerBounds.covers_boundB_numerical_bounds
