import SuperpermutationUpperBound305989.GenericBoundsB
import SuperpermutationUpperBound305989.Certificate.Cert
import SuperpermutationUpperBound305989.Certificate.BlockCert
import Challenge

/-!
# The bounds for every size from 16 symbols on, and the coefficient 305989/604800

The statements are in the vocabulary of `Challenge.lean` (`SuperpermutationBounds.Covers`,
`SuperpermutationBounds.F3`) and have the shape of `finite_bound` and `eventual_bound` of
`Solution.lean`, with `305989/604800 = 11771/23760 + 23333/2217600` in place of
`43/80 = 7/15 + 17/240` and `23333/2217600` in place of `17/240`.  They start at 16 symbols
(`m ≥ 14`): the construction is the selection of step (A) (`Certificate.cert`) with the (10,3)
block of step (B) (`Certificate.blockCert`) above each of its 6,048 loops without a row on
14 symbols, transported to 15 symbols and completed.
-/

namespace SuperpermutationUpperBound305989

open SuperpermutationUpperBound

private theorem covers_of_construction {K : ℕ} {w : List (Fin K)}
    (h : IsSuperpermutation w) : SuperpermutationBounds.Covers w := by
  intro p hlength hnodup
  obtain ⟨u, v, heq⟩ := h p ⟨hlength, hnodup⟩
  exact ⟨u, v, heq.symm⟩

/-- The finite bound for `m + 2 ≥ 16` symbols and every parameter `2 ≤ a ≤ m`. -/
theorem finite_bound16 (m : Nat) (hm : 14 ≤ m) (a : Nat) (ha : 2 ≤ a) (ham : a ≤ m) :
    ∃ w : List (Fin (m + 2)), SuperpermutationBounds.Covers w ∧
      (w.length : ℚ) ≤
        (((m + 2).factorial + (m + 1).factorial + m.factorial : Nat) : ℚ)
          + (305989 / 604800 : ℚ) * ((m - 1).factorial : ℚ)
          + ((a - 2 : Nat) : ℚ) * (23333 / 2217600 : ℚ) * ((m - 1).factorial : ℚ)
              / ((m - 1 : Nat) : ℚ)
          + ((m - a : Nat) : ℚ) *
              min ((23333 / 2217600 : ℚ) * ((m - 1).factorial : ℚ) / ((m - 1 : Nat) : ℚ))
                (((m + 1).factorial : ℚ) / ((a + 1).factorial : ℚ)) := by
  obtain ⟨w, hw, hl⟩ :=
    BoundsB.finite_of_cert Certificate.cert Certificate.blockCert m hm a ha ham
  refine ⟨w, covers_of_construction hw, ?_⟩
  simpa only [BoundsB.bound, F3, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega] using hl

/-- For every positive rational ε, eventually length at most
`F3(K) + (305989/604800 + ε) (K-3)!`. -/
theorem eventual_bound16 :
    ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, 16 ≤ N ∧
      ∀ K : ℕ, N ≤ K → ∃ w : List (Fin K), SuperpermutationBounds.Covers w ∧
        (w.length : ℚ) ≤
          SuperpermutationBounds.F3 K +
            ((305989 / 604800 : ℚ) + ε) * (Nat.factorial (K - 3) : ℚ) := by
  intro ε hε
  obtain ⟨N, hN, hall⟩ := BoundsB.asymptotic_of_cert Certificate.cert Certificate.blockCert ε hε
  refine ⟨N, hN, ?_⟩
  intro K hK
  obtain ⟨w, hw, hl⟩ := hall K hK
  refine ⟨w, covers_of_construction hw, ?_⟩
  simpa only [SuperpermutationBounds.F3, F3, Fourth, Nat.cast_add] using hl

end SuperpermutationUpperBound305989

#print axioms SuperpermutationUpperBound305989.finite_bound16
#print axioms SuperpermutationUpperBound305989.eventual_bound16
