import LowerBounds.PSearch

/-!
# Small searches evaluated by the kernel (5 symbols)

The searches of `PSearch.lean` with arithmetic tables (`…SearchA`) on 5 symbols, evaluated by
`decide +kernel` (no `native_decide`).  This file imports `PSearch.lean` only, so that the
evaluation runs in a small process; `PSmall.lean` uses the equations, and `PTestNative.lean`
repeats them with the compiled search.

The tables are the true caps on 5 symbols for a few holes (found with the compiled search,
`scratchP/PK1.lean`): chains `3 3 5 5`, sequences with one link of weight 4 `6 6`, rings
`3 1 2 1`.  Every kind of rule is evaluated once with the true table (answer `false`) and once
with an entry lowered or a profile that exists (answer `true`).
-/

namespace SuperpermLowerBounds
namespace PS
namespace Small

/-- Chain caps on 5 symbols for 0 to 3 holes. -/
def M5 : List Nat := [3, 3, 5, 5]

/-- Caps on 5 symbols for sequences with one link of weight 4, for 0 and 1 holes. -/
def P5 : List Nat := [6, 6]

/-- Ring caps on 5 symbols for 0 to 3 holes. -/
def R5 : List Nat := [3, 1, 2, 1]

/-- Chains with at most 2 holes (13 kept prefixes). -/
theorem chain5 : seqSearchA 5 [M5] 0 0 2 30 0 1 0 1 = false := by decide +kernel

/-- With the cap at 2 holes lowered to 4 a chain is found. -/
theorem chain5_low : seqSearchA 5 [[3, 3, 4]] 0 0 2 30 0 1 0 1 = true := by decide +kernel

/-- Chains with at most 3 holes, in 3 parts cut at depth 2 (34 kept prefixes). -/
theorem chain5_parts : seqSearchA 5 [M5] 0 0 3 30 2 3 0 3 = false := by decide +kernel

/-- Sequences with one link of weight 4 and at most 1 hole (8 kept prefixes). -/
theorem path5 : seqSearchA 5 [M5, P5] 1 0 1 30 0 1 0 1 = false := by decide +kernel

/-- With the cap at 1 hole lowered to 5 a sequence is found. -/
theorem path5_low : seqSearchA 5 [M5, [6, 5]] 1 0 1 30 0 1 0 1 = true := by decide +kernel

/-- Rings with at most 3 holes (24 kept prefixes). -/
theorem ring5 : ringSearchA 5 M5 R5 3 30 0 1 0 1 = false := by decide +kernel

/-- With the cap at 2 holes lowered to 1 a ring is found. -/
theorem ring5_low : ringSearchA 5 M5 [3, 1, 1] 2 30 0 1 0 1 = true := by decide +kernel

/-- No chain with 5 rows and at most 2 holes beside a chain with 2 rows and no hole (22 kept
prefixes). -/
theorem prof5 : profSearchA 5 M5 [(5, 2), (2, 0)] 30 0 1 0 1 = false := by decide +kernel

/-- A chain with 5 rows and at most 2 holes beside a chain with 1 row and no hole exists. -/
theorem prof5_ex : profSearchA 5 M5 [(5, 2), (1, 0)] 30 0 1 0 1 = true := by decide +kernel

end Small
end PS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.PS.Small.chain5
#print axioms SuperpermLowerBounds.PS.Small.chain5_parts
#print axioms SuperpermLowerBounds.PS.Small.path5
#print axioms SuperpermLowerBounds.PS.Small.ring5
#print axioms SuperpermLowerBounds.PS.Small.prof5
#print axioms SuperpermLowerBounds.PS.Small.prof5_ex
