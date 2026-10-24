import LowerBounds.KSearch
import LowerBounds.KTables

/-!
# Statements of part B of 5,900, evaluated as compiled code

**Trusted here.**  Every theorem of this file is proved by `native_decide`: Lean does not check
the computation in its kernel but runs it as compiled code and records the result as an axiom
(`SuperpermLowerBounds.KS.<name>._native.native_decide.ax_1_1`, listed by `#print axioms`).  So
this file trusts, in addition to the kernel: the Lean compiler (from `PSearch.lean` and
`KSearch.lean` to C), the C compiler of the Lean toolchain (`leanc`, clang), the Lean runtime
(natural numbers, integers, arrays, byte arrays, tasks), and that the library loaded with
`--load-dynlib` (the library `KSearch` that `build.sh` makes) was compiled from these
two files as they are.  The search and the proof that its answer `false` means what is claimed
(`KSound.lean`, `KRev.lean`, `KPot.lean`, `KRules.lean`, `KFinal.lean`) are checked by the kernel
and do not depend on this file.

What is evaluated (the reference run of the first and the second program found no violation, with
the number of kept prefixes given):

* `c59`: chains, level 59 (321,229,855 kept prefixes in all)
* `c62`: chains, levels 62 to 75 (3,319,568,194 kept prefixes in all)
* `ring`: rings to 69 holes (3,156,668,409 kept prefixes in all)
* `k6`: 6 links, all levels to 54 holes (at most 4,551,813,305, the number on the reference table, kept prefixes in all)
* `c76`: chains, level 76 (6,065,162,755 kept prefixes in all)

This file imports `KSearch.lean` and the tables `KTables.lean` only.  No file of level 1 imports
it.
-/

namespace SuperpermLowerBounds
namespace KS

open T5900

theorem c59 : seqSearch 7 Ttab 0 59 59 2 3 5 400 8 61 0 61 = false := by
  native_decide

theorem c62 : seqSearch 7 Ttab 0 62 75 2 3 5 400 12 499 0 499 = false := by
  native_decide

theorem ring : PS.ringSearch 7 (Ttab.getD 0 []) TRtab 69 400 16 1009 0 1009 = false := by
  native_decide

theorem k6 : seqSearch 7 Ttab 6 0 54 1 0 0 400 10 251 0 251 = false := by
  native_decide

theorem c76 : seqSearch 7 Ttab 0 76 76 2 3 5 400 12 499 0 499 = false := by
  native_decide

end KS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.KS.c59
#print axioms SuperpermLowerBounds.KS.c62
#print axioms SuperpermLowerBounds.KS.ring
#print axioms SuperpermLowerBounds.KS.k6
#print axioms SuperpermLowerBounds.KS.c76
