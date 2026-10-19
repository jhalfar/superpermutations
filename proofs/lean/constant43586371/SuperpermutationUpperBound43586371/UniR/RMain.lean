import SuperpermutationUpperBound43586371.UniR.RIterate
import SuperpermutationUpperBound43586371.Uniform.Bounds
import Challenge

/-!
# The finite theorem with the R'(m) blocks at every level

`finite_boundR m0 K n a`: for `m0 ≥ 11`, `n ≥ m0 + 3K + 3` and `2 ≤ a ≤ n - 2` there is a word on `n` symbols
containing every permutation, of length at most
`ubound (kappaR m0 K) (gammaR m0 K) (n - 2) a`
`= n! + (n-1)! + (n-2)! + κ (n-3)! + (a-2) γ (n-3)!/(n-3) + (n-2-a) min(γ (n-3)!/(n-3), (n-1)!/(a+1)!)`,
where `κ = kappaR m0 K` and `γ = gammaR m0 K` are computed exactly from the count recursion `cntR`
(`bound_R.py` evaluates them).
-/

namespace SuperpermutationUpperBound43586371.UniR

open SuperpermutationUpperBound
open SuperpermutationUpperBound43586371.Uniform

/-- The coefficient of `(n-3)!` after `K` levels from `m0`. -/
def kappaR (m0 K : Nat) : ℚ :=
  ((cntR m0 K).2.1 : ℚ) / (m0 + 3 * K).factorial +
    (((cntR m0 K).2.2.1 + (cntR m0 K).2.2.2 : Nat) : ℚ) / (m0 + 3 * K - 1).factorial

/-- The cycle ratio after `K` levels from `m0`. -/
def gammaR (m0 K : Nat) : ℚ :=
  (((cntR m0 K).2.2.1 + (cntR m0 K).2.2.2 : Nat) : ℚ) / (m0 + 3 * K - 1).factorial

private theorem covers_of_construction {K : ℕ} {w : List (Fin K)}
    (h : IsSuperpermutation w) : SuperpermutationBounds.Covers w := by
  intro p hlength hnodup
  obtain ⟨u, v, heq⟩ := h p ⟨hlength, hnodup⟩
  exact ⟨u, v, heq.symm⟩

/-- **The finite bound with the R'(m) blocks.** -/
theorem finite_boundR (m0 K n a : Nat) (h11 : 11 ≤ m0) (hn : m0 + 3 * K + 3 ≤ n) (ha : 2 ≤ a)
    (han : a ≤ n - 2) :
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      (w.length : ℚ) ≤ ubound (kappaR m0 K) (gammaR m0 K) (n - 2) a := by
  obtain ⟨A, comps, circles, C, hfull⟩ := closedR m0 h11 K
  obtain ⟨w, hw, hl⟩ := finite_of_closed C hfull (n - 2) a (by omega) ha han
  have hn2 : n - 2 + 2 = n := by omega
  have hout : ∃ w : Word (n - 2 + 2), IsSuperpermutation w ∧
      (w.length : ℚ) ≤ ubound (kappaR m0 K) (gammaR m0 K) (n - 2) a := ⟨w, hw, hl⟩
  rw [hn2] at hout
  obtain ⟨w, hw, hl⟩ := hout
  exact ⟨w, covers_of_construction hw, hl⟩

end SuperpermutationUpperBound43586371.UniR
