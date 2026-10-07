import LowerBounds.PSearch
import LowerBounds.PTables

/-!
# F5 and F4: sequences with 5 and with 4 links of weight 4, evaluated as compiled code

**Trusted here.**  Every theorem of this file is proved by `native_decide`: Lean does not check
the computation in its kernel but runs it as compiled code and records the result as an axiom
(`SuperpermLowerBounds.PS.<name>._native.native_decide.ax_1_1`, listed by `#print axioms`).  So
this file trusts, in addition to the kernel: the Lean compiler (from `PSearch.lean` to C), the C
compiler of the Lean toolchain (`leanc`, clang), the Lean runtime (natural numbers, arrays, byte
arrays, tasks), and that the library loaded with `--load-dynlib` (`build/native/PSearch.dll`, made
by `p_native_build.sh`) was compiled from `PSearch.lean` as it is.  The search itself and the
proof that its answer `false` means what is claimed (`PSound.lean`, `PSeq.lean`, `PEnc.lean`,
`PLevels.lean`, `PRules.lean`) are checked by the kernel and do not depend on this file.

What is evaluated: `seqSearch 7 Ptabs 5 0 54 400 0 1 0 1` and `seqSearch 7 Ptabs 4 0 60 400 0 1 0 1`
(levels 0 to 54 and 0 to 60, fuel 400, one part).  Reference: `scratchP/pproto.c` (mode `tabs`) and the
counting copy `PCount.lean` visit 102,853 and 4,289,217 kept prefixes and find no violation.

This file imports `PSearch.lean` and the tables `PTables.lean` only.  No file of level 1 imports
it.
-/

namespace SuperpermLowerBounds
namespace PS

open T5899

/-- 102,853 kept prefixes. -/
theorem f5 : seqSearch 7 Ptabs 5 0 54 400 0 1 0 1 = false := by
  native_decide

/-- 4,289,217 kept prefixes. -/
theorem f4 : seqSearch 7 Ptabs 4 0 60 400 0 1 0 1 = false := by
  native_decide

end PS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.PS.f5
#print axioms SuperpermLowerBounds.PS.f4
