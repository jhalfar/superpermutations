import LowerBounds.PSmallSearch
import LowerBounds.PTables

/-!
# Tests of the native evaluation of the search of `PSearch.lean`

**Trusted here:** every theorem of this file is proved by `native_decide` and so trusts the Lean
compiler, the C compiler of the Lean toolchain and the loaded library
`build/native/PSearch.dll` (compiled from `PSearch.lean` by `p_native_build.sh`).  Nothing else
in the development imports this file.

1. The nine statements that `PSmallSearch.lean` proves by the kernel (`decide +kernel`), again by
   compiled evaluation, with the arithmetic tables (`…SearchA`, the same statements) and with the
   compiled tables (`…Search`).  A false statement cannot pass the kernel, so if the two ways of
   evaluation disagreed, one of the proofs would fail.
2. Searches with known results on 6 and 7 symbols: `false` means exhausted, `true` means found.
   The true chain table on 6 symbols up to 20 holes passes; with its entry at 14 holes lowered to
   21 the known chain with 22 rows is found.  On 7 symbols the known chain with 31 rows and 14
   holes, the known ring with 65 rows and 40 holes, a chain with 66 rows and 36 holes and two
   disjoint chains with 31 rows and 14 holes are found when the tables are lowered or the profile
   asks for them.
-/

namespace SuperpermLowerBounds
namespace PS
namespace Test

open Small T5899

/-! ### The kernel statements, by compiled evaluation -/

theorem a1 : seqSearchA 5 [M5] 0 0 2 30 0 1 0 1 = false := by native_decide
theorem a2 : seqSearchA 5 [[3, 3, 4]] 0 0 2 30 0 1 0 1 = true := by native_decide
theorem a3 : seqSearchA 5 [M5] 0 0 3 30 2 3 0 3 = false := by native_decide
theorem a4 : seqSearchA 5 [M5, P5] 1 0 1 30 0 1 0 1 = false := by native_decide
theorem a5 : seqSearchA 5 [M5, [6, 5]] 1 0 1 30 0 1 0 1 = true := by native_decide
theorem a6 : ringSearchA 5 M5 R5 3 30 0 1 0 1 = false := by native_decide
theorem a7 : ringSearchA 5 M5 [3, 1, 1] 2 30 0 1 0 1 = true := by native_decide
theorem a8 : profSearchA 5 M5 [(5, 2), (2, 0)] 30 0 1 0 1 = false := by native_decide
theorem a9 : profSearchA 5 M5 [(5, 2), (1, 0)] 30 0 1 0 1 = true := by native_decide

/-! ### The same with the compiled tables -/

theorem b1 : seqSearch 5 [M5] 0 0 2 30 0 1 0 1 = false := by native_decide
theorem b2 : seqSearch 5 [[3, 3, 4]] 0 0 2 30 0 1 0 1 = true := by native_decide
theorem b3 : seqSearch 5 [M5] 0 0 3 30 2 3 0 3 = false := by native_decide
theorem b4 : seqSearch 5 [M5, P5] 1 0 1 30 0 1 0 1 = false := by native_decide
theorem b5 : seqSearch 5 [M5, [6, 5]] 1 0 1 30 0 1 0 1 = true := by native_decide
theorem b6 : ringSearch 5 M5 R5 3 30 0 1 0 1 = false := by native_decide
theorem b7 : ringSearch 5 M5 [3, 1, 1] 2 30 0 1 0 1 = true := by native_decide
theorem b8 : profSearch 5 M5 [(5, 2), (2, 0)] 30 0 1 0 1 = false := by native_decide
theorem b9 : profSearch 5 M5 [(5, 2), (1, 0)] 30 0 1 0 1 = true := by native_decide

/-! ### Known results on 6 and 7 symbols -/

/-- The true chain caps on 6 symbols for 0 to 20 holes (`scratchP/caps6.txt`). -/
def M6 : List Nat := [4, 4, 7, 7, 10, 10, 11, 13, 14, 15, 16, 17, 19, 19, 22, 22, 22, 24, 24, 25, 25]

/-- The chain table on 6 symbols passes, in 7 parts (with the arithmetic tables as well). -/
theorem c1 : seqSearch 6 [M6] 0 0 20 100 6 7 0 7 = false := by native_decide
theorem c2 : seqSearchA 6 [M6] 0 0 20 100 0 1 0 1 = false := by native_decide
/-- A chain with 22 rows and 14 holes on 6 symbols exists. -/
theorem c3 : seqSearch 6 [M6.set 14 21] 0 0 20 100 0 1 0 1 = true := by native_decide
/-- A chain with 31 rows and 14 holes on 7 symbols exists. -/
theorem c4 : seqSearch 7 [Mtab.set 14 30] 0 0 14 400 0 1 0 1 = true := by native_decide
/-- The chain caps on 7 symbols up to 14 holes pass. -/
theorem c5 : seqSearch 7 Ptabs 0 0 14 400 6 11 0 11 = false := by native_decide
/-- A ring with 65 rows and 40 holes on 7 symbols exists. -/
theorem c6 : ringSearch 7 Mtab (PRtab.set 40 64) 40 400 0 1 0 1 = true := by native_decide
/-- The ring caps on 7 symbols up to 40 holes pass. -/
theorem c7 : ringSearch 7 Mtab PRtab 40 400 0 1 0 1 = false := by native_decide
/-- A chain with 66 rows and 36 holes on 7 symbols exists. -/
theorem c8 : profSearch 7 Mtab [(66, 36)] 400 0 1 0 1 = true := by native_decide
/-- Two disjoint chains with 31 rows and 14 holes on 7 symbols exist. -/
theorem c9 : profSearch 7 Mtab [(31, 14), (31, 14)] 400 0 1 0 1 = true := by native_decide

end Test
end PS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.PS.Test.a1
#print axioms SuperpermLowerBounds.PS.Test.b9
#print axioms SuperpermLowerBounds.PS.Test.c9
