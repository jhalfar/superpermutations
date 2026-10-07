import LowerBounds.PSearch
import LowerBounds.PTables

/-!
# FR: rings, evaluated as compiled code

**Trusted here.**  Every theorem of this file is proved by `native_decide`: Lean does not check
the computation in its kernel but runs it as compiled code and records the result as an axiom
(`SuperpermLowerBounds.PS.<name>._native.native_decide.ax_1_1`, listed by `#print axioms`).  So
this file trusts, in addition to the kernel: the Lean compiler (from `PSearch.lean` to C), the C
compiler of the Lean toolchain (`leanc`, clang), the Lean runtime (natural numbers, arrays, byte
arrays, tasks), and that the library loaded with `--load-dynlib` (`build/native/PSearch.dll`, made
by `p_native_build.sh`) was compiled from `PSearch.lean` as it is.  The search itself and the
proof that its answer `false` means what is claimed (`PSound.lean`, `PSeq.lean`, `PEnc.lean`,
`PLevels.lean`, `PRules.lean`) are checked by the kernel and do not depend on this file.

What is evaluated: `ringSearch 7 Mtab PRtab 77 400 16 1009 0 1009` (rings with at most 77 holes, fuel 400,
cut at depth 16 into 1009 parts).  Reference: `scratchP/pproto.c` (mode `ring`) and the counting copy
`PCount.lean` visit 460,113,709 kept prefixes and find no ring above the table.

This file imports `PSearch.lean` and the tables `PTables.lean` only.  No file of level 1 imports
it.
-/

namespace SuperpermLowerBounds
namespace PS

open T5899

/-- 460,113,709 kept prefixes. -/
theorem ring : ringSearch 7 Mtab PRtab 77 400 16 1009 0 1009 = false := by
  native_decide

end PS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.PS.ring
