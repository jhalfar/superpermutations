import LowerBounds.A16Arith

/-!
# Tests of the knapsack of A16 (kernel only)

Each line shows that a bound of `A16Arith.lean` is tight or that a joint statement is needed: the same
check with one link less for the kernel, or without the joint statement, is false.
-/

namespace SuperpermLowerBounds
namespace A16

/-- Corollary K16 is tight: a sequence of weight 96 can have value 39. -/
example : SK 0 96 = 39 := by decide +kernel
/-- T1: a kernel with 7 links and an item `E`, and a kernel and a sequence item with 7 links, reach 40. -/
example : chk1 7 (IS 0) = false := by decide +kernel
example : chk1 0 (IS 7) = false := by decide +kernel
/-- T2: a kernel with 7 links and a ring reach 40. -/
example : chk1 7 IR = false := by decide +kernel
/-- T3': a kernel with 5 links and two rings reach 40. -/
example : chk1 5 (NR 2) = false := by decide +kernel
/-- T4': a kernel with 4 links, a ring and a sequence item reach 40. -/
example : chk2 4 IR (IS 0) = false := by decide +kernel
/-- T5: a kernel with 3 links and two sequence items reach 40. -/
example : chk1 3 (NS 2) = false := by decide +kernel
/-- T6': a kernel with 2 links and three rings reach 40. -/
example : chk1 2 (NR 3) = false := by decide +kernel
/-- T7: a kernel with 1 link, two rings and a sequence item reach 40. -/
example : chk2 1 (NR 2) (IS 0) = false := by decide +kernel
/-- T8: a kernel, a ring and two items `E` reach 40. -/
example : chk2 0 IR (NS 2) = false := by decide +kernel
/-- T9': a kernel and four rings reach 40. -/
example : chk1 0 (NR 4) = false := by decide +kernel
/-- Lemma EPS16 is needed: three items `E` and a kernel reach 40 by the tables. -/
example : chk1 0 (NS 3) = false := by decide +kernel

end A16
end SuperpermLowerBounds
