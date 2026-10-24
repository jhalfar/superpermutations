import LowerBounds.KSearch
import LowerBounds.KTables

/-!
# A statement of part B of 5,900, evaluated as compiled code

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

* `k3`: 3 links, levels 55 to 72 (445,234,933,436 kept prefixes in all)

This file imports `KSearch.lean` and the tables `KTables.lean` only.  No file of level 1 imports
it.
-/

namespace SuperpermLowerBounds
namespace KS

open T5900

theorem k3 : seqSearch 7 Dtab 3 55 72 10 16 30 400 13 1021 0 1021 = false := by
  native_decide

end KS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.KS.k3
