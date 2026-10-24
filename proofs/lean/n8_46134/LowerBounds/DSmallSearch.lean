import LowerBounds.DSearch

/-!
# A small search evaluated by the kernel

The prefix search of `DSearch.lean` on 5 symbols for the line `2 r ≤ 3 δ + 6`, evaluated by
`decide +kernel` (no `native_decide`).  This file imports `DSearch.lean` only, so that the
evaluation runs in a small process; `DSmall.lean` uses the equation.
-/

namespace SuperpermLowerBounds

/-- The line search for `2 r ≤ 3 δ + 6` on 5 symbols (5 chains searched), by the kernel. -/
theorem lineSearch_5_2_3_6 : S.lineSearch 5 625 2 3 6 20 0 1 = false := by decide +kernel

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.lineSearch_5_2_3_6
