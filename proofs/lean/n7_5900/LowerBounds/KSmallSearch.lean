import LowerBounds.KSearch

/-!
# Small searches with the reversal cut, evaluated by the kernel (5 symbols)

The search of `KSearch.lean` with arithmetic tables (`seqSearchA`) on 5 symbols, evaluated by
`decide +kernel` (no `native_decide`).  This file imports `KSearch.lean` only, so that the
evaluation runs in a small process; `KSmall.lean` uses the equations, and `KTestNative.lean`
repeats them with the compiled search.

The tables are the true caps on 5 symbols for a few holes (those of `PSmallSearch.lean`): chains
`3 3 5 5`, sequences with one link of weight 4 `6 6`.  The rule is evaluated with the plain
potential `1, 0, 0` and with the potentials of the statements of 5,900, with all levels and with
one level above a given row, in one part and in parts, once with the true table (answer `false`)
and once with an entry lowered (answer `true`).
-/

namespace SuperpermLowerBounds
namespace KS
namespace Small

/-- Chain caps on 5 symbols for 0 to 3 holes. -/
def M5 : List Nat := [3, 3, 5, 5]

/-- Caps on 5 symbols for sequences with one link of weight 4, for 0 and 1 holes. -/
def P5 : List Nat := [6, 6]

/-- Chains with at most 2 holes, potential 2, 3, 5. -/
theorem chain5 : seqSearchA 5 [M5] 0 0 2 2 3 5 30 0 1 0 1 = false := by decide +kernel

/-- The same with the plain rule. -/
theorem chain5_plain : seqSearchA 5 [M5] 0 0 2 1 0 0 30 0 1 0 1 = false := by decide +kernel

/-- With the cap at 2 holes lowered to 4 a chain is found. -/
theorem chain5_low : seqSearchA 5 [[3, 3, 4]] 0 0 2 2 3 5 30 0 1 0 1 = true := by decide +kernel

/-- Chains with at most 3 holes, in 3 parts cut at depth 2 (14 kept prefixes; 34 with the plain
rule). -/
theorem chain5_parts : seqSearchA 5 [M5] 0 0 3 2 3 5 30 2 3 0 3 = false := by decide +kernel

/-- Chains with 3 holes, given the caps to 2 holes. -/
theorem chain5_level : seqSearchA 5 [M5] 0 3 3 2 3 5 30 0 1 0 1 = false := by decide +kernel

/-- With the cap at 3 holes lowered to 4 a chain is found at that level. -/
theorem chain5_level_low : seqSearchA 5 [[3, 3, 5, 4]] 0 3 3 2 3 5 30 0 1 0 1 = true := by
  decide +kernel

/-- Sequences with one link of weight 4 and at most 1 hole, potential 10, 15, 30 (8 kept
prefixes). -/
theorem path5 : seqSearchA 5 [M5, P5] 1 0 1 10 15 30 30 0 1 0 1 = false := by decide +kernel

/-- With the cap at 1 hole lowered to 5 a sequence is found. -/
theorem path5_low : seqSearchA 5 [M5, [6, 5]] 1 0 1 10 15 30 30 0 1 0 1 = true := by
  decide +kernel

end Small
end KS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.KS.Small.chain5
#print axioms SuperpermLowerBounds.KS.Small.chain5_parts
#print axioms SuperpermLowerBounds.KS.Small.chain5_level
#print axioms SuperpermLowerBounds.KS.Small.path5
#print axioms SuperpermLowerBounds.KS.Small.path5_low
