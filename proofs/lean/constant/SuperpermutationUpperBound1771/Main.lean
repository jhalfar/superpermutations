import SuperpermutationUpperBound1771.GenericBounds
import SuperpermutationUpperBound1771.Main13

/-!
# The bounds for every size from 13 symbols on, and the coefficient 1771/3456

The statements are in the vocabulary of `Challenge.lean` (`SuperpermutationBounds.Covers`,
`SuperpermutationBounds.F3`) and have the shape of `finite_bound` and `eventual_bound` of
`Solution.lean`, with `1771/3456 = 53/108 + 25/1152` in place of `43/80 = 7/15 + 17/240`
and `25/1152` in place of `17/240`.  They start at 13 symbols (`m ≥ 11`), where the selection
with blocks has been transported once.
-/

namespace SuperpermutationUpperBound1771

open SuperpermutationUpperBound

private theorem covers_of_construction {K : ℕ} {w : List (Fin K)}
    (h : IsSuperpermutation w) : SuperpermutationBounds.Covers w := by
  intro p hlength hnodup
  obtain ⟨u, v, heq⟩ := h p ⟨hlength, hnodup⟩
  exact ⟨u, v, heq.symm⟩

/-- The finite bound for `m + 2 ≥ 13` symbols and every parameter `2 ≤ a ≤ m`. -/
theorem finite_bound (m : Nat) (hm : 11 ≤ m) (a : Nat) (ha : 2 ≤ a) (ham : a ≤ m) :
    ∃ w : List (Fin (m + 2)), SuperpermutationBounds.Covers w ∧
      (w.length : ℚ) ≤
        (((m + 2).factorial + (m + 1).factorial + m.factorial : Nat) : ℚ)
          + (1771 / 3456 : ℚ) * ((m - 1).factorial : ℚ)
          + ((a - 2 : Nat) : ℚ) * (25 / 1152 : ℚ) * ((m - 1).factorial : ℚ)
              / ((m - 1 : Nat) : ℚ)
          + ((m - a : Nat) : ℚ) *
              min ((25 / 1152 : ℚ) * ((m - 1).factorial : ℚ) / ((m - 1 : Nat) : ℚ))
                (((m + 1).factorial : ℚ) / ((a + 1).factorial : ℚ)) := by
  obtain ⟨w, hw, hl⟩ := Bounds.finite_of_cert Certificate.cert m hm a ha ham
  refine ⟨w, covers_of_construction hw, ?_⟩
  simpa only [Bounds.bound, F3, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega] using hl

/-- For every positive rational ε, eventually length at most
`F3(K) + (1771/3456 + ε) (K-3)!`. -/
theorem eventual_bound :
    ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, 13 ≤ N ∧
      ∀ K : ℕ, N ≤ K → ∃ w : List (Fin K), SuperpermutationBounds.Covers w ∧
        (w.length : ℚ) ≤
          SuperpermutationBounds.F3 K +
            ((1771 / 3456 : ℚ) + ε) * (Nat.factorial (K - 3) : ℚ) := by
  intro ε hε
  obtain ⟨N, hN, hall⟩ := Bounds.asymptotic_of_cert Certificate.cert ε hε
  refine ⟨N, hN, ?_⟩
  intro K hK
  obtain ⟨w, hw, hl⟩ := hall K hK
  refine ⟨w, covers_of_construction hw, ?_⟩
  simpa only [SuperpermutationBounds.F3, F3, Fourth, Nat.cast_add] using hl

end SuperpermutationUpperBound1771

#print axioms SuperpermutationUpperBound1771.word_thirteen
#print axioms SuperpermutationUpperBound1771.finite_bound
#print axioms SuperpermutationUpperBound1771.eventual_bound
