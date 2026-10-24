import LowerBounds.DSearch

/-!
# Test of the native evaluation of the prefix search

**Trusted here:** every theorem proved by `native_decide` in this file trusts the Lean compiler,
the C compiler of the Lean toolchain and the loaded library `DSearch.dll`, `.so` or `.dylib` (compiled
from `DSearch.lean` by `build.sh`).  Nothing else in the development imports this file.

The first group of statements is proved by the kernel (`decide +kernel`), the second group
repeats them with `native_decide`: both must be accepted.  The third group are searches whose
results are known from a C program of mine: `true` means found, `false` means
exhausted.  (If the two ways of evaluation disagreed on a statement, one of its two proofs would
fail: a false statement cannot pass the kernel.)
-/

namespace SuperpermLowerBounds
namespace S
namespace Test

/-! ### By the kernel -/

theorem k1 : lineSearch 5 625 2 3 6 20 0 1 = false := by decide +kernel
theorem k2 : lineSearch 5 625 2 3 5 20 0 1 = true := by decide +kernel
theorem k3 : lineSearch 5 625 2 3 6 20 3 3 = false := by decide +kernel
theorem k4 : zoneSearch 5 625 2 3 6 1 1 1 3 1 20 0 1 = false := by decide +kernel
theorem k5 : zoneSearch 5 625 2 3 6 2 1 1 3 1 20 0 1 = true := by decide +kernel

/-! ### The same by compiled evaluation -/

theorem n1 : lineSearch 5 625 2 3 6 20 0 1 = false := by native_decide
theorem n2 : lineSearch 5 625 2 3 5 20 0 1 = true := by native_decide
theorem n3 : lineSearch 5 625 2 3 6 20 3 3 = false := by native_decide
theorem n4 : zoneSearch 5 625 2 3 6 1 1 1 3 1 20 0 1 = false := by native_decide
theorem n5 : zoneSearch 5 625 2 3 6 2 1 1 3 1 20 0 1 = true := by native_decide

/-! ### Larger searches with results known from `chain.c` -/

/-- 104,307 nodes in `chain.c`. -/
theorem n6 : lineSearch 8 2097152 3 7 28 400 30 16 = false := by native_decide
/-- Violated by a chain of 31 rows and 14 holes. -/
theorem n7 : lineSearch 7 117649 50 86 345 400 0 1 = true := by native_decide
/-- 2,973 nodes in `chain.c`. -/
theorem n8 : lineSearch 7 117649 50 86 346 400 20 7 = false := by native_decide
theorem n9 : zoneSearch 6 7776 2 3 8 1 4 5 20 2 100 5 4 = false := by native_decide
theorem n10 : zoneSearch 6 7776 2 3 8 2 4 5 20 4 100 5 4 = true := by native_decide
/-- 15,746,559 nodes in `chain.c`; here in 61 parts. -/
theorem n11 : lineSearch 8 2097152 7 16 82 400 40 61 = false := by native_decide

end Test
end S
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.S.Test.k1
#print axioms SuperpermLowerBounds.S.Test.k4
#print axioms SuperpermLowerBounds.S.Test.n1
#print axioms SuperpermLowerBounds.S.Test.n11
