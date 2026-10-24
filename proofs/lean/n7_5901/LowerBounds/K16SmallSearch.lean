import LowerBounds.K16Search

/-!
# Small searches with Rule JS, evaluated by the kernel (5 symbols)

The searches of `KSmallSearch.lean` (5,900) repeated with the search of `K16Search.lean`, Rule JS on:
the true caps on 5 symbols give `false`, a lowered entry gives `true` (the search with Rule JS still
finds the violations).  `decide +kernel`, no `native_decide`.
-/

namespace SuperpermLowerBounds
namespace K16
namespace Small

/-- Chain caps on 5 symbols for 0 to 3 holes. -/
def M5 : List Nat := [3, 3, 5, 5]

/-- Caps on 5 symbols for sequences with one link of weight 4, for 0 and 1 holes. -/
def P5 : List Nat := [6, 6]

theorem chain5_js : seqSearchA 5 [M5] 0 0 2 2 3 5 true 30 0 1 0 1 = false := by decide +kernel

theorem chain5_js_low : seqSearchA 5 [[3, 3, 4]] 0 0 2 2 3 5 true 30 0 1 0 1 = true := by
  decide +kernel

theorem chain5_js_parts : seqSearchA 5 [M5] 0 0 3 2 3 5 true 30 2 3 0 3 = false := by
  decide +kernel

theorem chain5_js_level_low : seqSearchA 5 [[3, 3, 5, 4]] 0 3 3 2 3 5 true 30 0 1 0 1 = true := by
  decide +kernel

theorem path5_js : seqSearchA 5 [M5, P5] 1 0 1 20 29 60 true 30 0 1 0 1 = false := by
  decide +kernel

theorem path5_js_low : seqSearchA 5 [M5, [6, 5]] 1 0 1 20 29 60 true 30 0 1 0 1 = true := by
  decide +kernel

/-- Without Rule JS the search is that of 5,900 (same answers). -/
theorem path5_nojs : seqSearchA 5 [M5, P5] 1 0 1 10 15 30 false 30 0 1 0 1 = false := by
  decide +kernel

end Small
end K16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K16.Small.chain5_js
#print axioms SuperpermLowerBounds.K16.Small.path5_js_low
