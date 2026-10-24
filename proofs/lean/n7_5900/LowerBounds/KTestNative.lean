import LowerBounds.KSearch
import LowerBounds.KSmallSearch
import LowerBounds.KTestTables
import LowerBounds.PTables

/-!
# Tests of the compiled search of `KSearch.lean` (not part of any proof)

**Trusted here.**  Every theorem of this file is proved by `native_decide` (compiled code, one
axiom per theorem).  Nothing depends on this file.  It checks the compiled search against known
answers:

1. the eight statements of `KSmallSearch.lean`, which the kernel has evaluated, give the same
   answers when compiled, with the arithmetic tables and with the compiled tables;
2. on 7 symbols the reference statements for 8 and for 7 links pass, with the plain rule and with
   the reversal cut, in one part and in parts (the counting copy `KCount.lean` visits 32,407,
   29,066,365 and 24,856,368 kept prefixes there, as the reference programs do); the chain caps of
   set B to 14 holes pass; a chain with 31 rows and 14 holes and sequences with one link of weight
   4 above lowered caps are found.
-/

namespace SuperpermLowerBounds
namespace KS
namespace Test

open Small T5899 T5900

/-! ### The kernel statements, by compiled evaluation -/

theorem a1 : seqSearchA 5 [M5] 0 0 2 2 3 5 30 0 1 0 1 = false := by native_decide
theorem a2 : seqSearchA 5 [M5] 0 0 2 1 0 0 30 0 1 0 1 = false := by native_decide
theorem a3 : seqSearchA 5 [[3, 3, 4]] 0 0 2 2 3 5 30 0 1 0 1 = true := by native_decide
theorem a4 : seqSearchA 5 [M5] 0 0 3 2 3 5 30 2 3 0 3 = false := by native_decide
theorem a5 : seqSearchA 5 [M5] 0 3 3 2 3 5 30 0 1 0 1 = false := by native_decide
theorem a6 : seqSearchA 5 [[3, 3, 5, 4]] 0 3 3 2 3 5 30 0 1 0 1 = true := by native_decide
theorem a7 : seqSearchA 5 [M5, P5] 1 0 1 10 15 30 30 0 1 0 1 = false := by native_decide
theorem a8 : seqSearchA 5 [M5, [6, 5]] 1 0 1 10 15 30 30 0 1 0 1 = true := by native_decide

/-! ### The same with the compiled tables -/

theorem b1 : seqSearch 5 [M5] 0 0 2 2 3 5 30 0 1 0 1 = false := by native_decide
theorem b2 : seqSearch 5 [M5] 0 0 2 1 0 0 30 0 1 0 1 = false := by native_decide
theorem b3 : seqSearch 5 [[3, 3, 4]] 0 0 2 2 3 5 30 0 1 0 1 = true := by native_decide
theorem b4 : seqSearch 5 [M5] 0 0 3 2 3 5 30 2 3 0 3 = false := by native_decide
theorem b5 : seqSearch 5 [M5] 0 3 3 2 3 5 30 0 1 0 1 = false := by native_decide
theorem b6 : seqSearch 5 [[3, 3, 5, 4]] 0 3 3 2 3 5 30 0 1 0 1 = true := by native_decide
theorem b7 : seqSearch 5 [M5, P5] 1 0 1 10 15 30 30 0 1 0 1 = false := by native_decide
theorem b8 : seqSearch 5 [M5, [6, 5]] 1 0 1 10 15 30 30 0 1 0 1 = true := by native_decide

/-! ### Known results on 7 symbols -/

/-- 8 links on the reference table, plain rule (32,407 kept prefixes). -/
theorem c1 : seqSearch 7 Du8 8 0 42 1 0 0 400 0 1 0 1 = false := by native_decide
/-- 7 links on the reference table, plain rule (29,066,365 kept prefixes). -/
theorem c2 : seqSearch 7 Du7 7 0 48 1 0 0 400 0 1 0 1 = false := by native_decide
/-- 7 links on the reference table, potential 2, 3, 5 (24,856,368 kept prefixes). -/
theorem c3 : seqSearch 7 Du7 7 0 48 2 3 5 400 0 1 0 1 = false := by native_decide
/-- The same in 7 parts cut at depth 6. -/
theorem c4 : seqSearch 7 Du7 7 0 48 2 3 5 400 6 7 0 7 = false := by native_decide
/-- A chain with 31 rows and 14 holes on 7 symbols exists. -/
theorem c5 : seqSearch 7 [Mtab.set 14 30] 0 0 14 2 3 5 400 0 1 0 1 = true := by native_decide
/-- It is found at the level 14 alone, given the levels below. -/
theorem c6 : seqSearch 7 [Mtab.set 14 30] 0 14 14 2 3 5 400 0 1 0 1 = true := by native_decide
/-- The chain caps on 7 symbols up to 14 holes pass. -/
theorem c7 : seqSearch 7 Ptabs 0 0 14 2 3 5 400 6 11 0 11 = false := by native_decide
/-- A sequence with one link of weight 4, no hole and 10 rows on 7 symbols exists. -/
theorem c8 : seqSearch 7 (Ptabs.set 1 ((Ptabs.getD 1 []).set 0 9)) 1 0 0 10 15 30 400 0 1 0 1
    = true := by native_decide
/-- A sequence with one link of weight 4, 4 holes and 18 rows on 7 symbols exists. -/
theorem c9 : seqSearch 7 (Ptabs.set 1 ((Ptabs.getD 1 []).set 4 17)) 1 0 4 10 15 30 400 0 1 0 1
    = true := by native_decide

end Test
end KS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.KS.Test.a1
#print axioms SuperpermLowerBounds.KS.Test.b8
#print axioms SuperpermLowerBounds.KS.Test.c9
