import LowerBounds.TheoremA
import Superperm.Bridge

/-!
# Theorem A for covering words over `Fin k`

The same bounds in the vocabulary of `Challenge.lean` of the upper-bound project: a word
`w : List (Fin k)` with `SuperpermutationBounds.Covers w` contains every duplicate-free list
of length `k` as a factor.  `SuperpermBridge.hunter_le_ssuper_iff` translates
`L ≤ Hunter.Ssuper k` into `∀ w, Covers w → L ≤ w.length`.
-/

namespace SuperpermLowerBounds

open SuperpermutationBounds

/-- Theorem A for covering words. -/
theorem covers_length_ge_kisicBound {k : ℕ} (hk : 5 ≤ k) :
    ∀ w : List (Fin k), Covers w → kisicBound k ≤ w.length :=
  (SuperpermBridge.hunter_le_ssuper_iff (by omega)).mp (superperm_kisic_bound hk)

/-- The values of Theorem A for covering words on 5 to 14 symbols. -/
theorem covers_kisic_numerical_bounds :
    (∀ w : List (Fin 5), Covers w → 153 ≤ w.length) ∧
    (∀ w : List (Fin 6), Covers w → 870 ≤ w.length) ∧
    (∀ w : List (Fin 7), Covers w → 5893 ≤ w.length) ∧
    (∀ w : List (Fin 8), Covers w → 46121 ≤ w.length) ∧
    (∀ w : List (Fin 9), Covers w → 408433 ≤ w.length) ∧
    (∀ w : List (Fin 10), Covers w → 4033159 ≤ w.length) ∧
    (∀ w : List (Fin 11), Covers w → 43916736 ≤ w.length) ∧
    (∀ w : List (Fin 12), Covers w → 522614409 ≤ w.length) ∧
    (∀ w : List (Fin 13), Covers w → 6746553315 ≤ w.length) ∧
    (∀ w : List (Fin 14), Covers w → 93890534411 ≤ w.length) := by
  obtain ⟨h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := superperm_kisic_numerical_bounds
  exact ⟨(SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h5,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h6,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h7,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h8,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h9,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h10,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h11,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h12,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h13,
    (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp h14⟩

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_length_ge_kisicBound
#print axioms SuperpermLowerBounds.covers_kisic_numerical_bounds
