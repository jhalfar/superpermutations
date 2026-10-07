import LowerBounds.PSearch
import LowerBounds.PTables

/-!
# F1: sequences with 1 link of weight 4, parts 2520 to 5038 of 5039, evaluated as compiled code

**Trusted here.**  Every theorem of this file is proved by `native_decide`: Lean does not check
the computation in its kernel but runs it as compiled code and records the result as an axiom
(`SuperpermLowerBounds.PS.<name>._native.native_decide.ax_1_1`, listed by `#print axioms`).  So
this file trusts, in addition to the kernel: the Lean compiler (from `PSearch.lean` to C), the C
compiler of the Lean toolchain (`leanc`, clang), the Lean runtime (natural numbers, arrays, byte
arrays, tasks), and that the library loaded with `--load-dynlib` (`build/native/PSearch.dll`, made
by `p_native_build.sh`) was compiled from `PSearch.lean` as it is.  The search itself and the
proof that its answer `false` means what is claimed (`PSound.lean`, `PSeq.lean`, `PEnc.lean`,
`PLevels.lean`, `PRules.lean`) are checked by the kernel and do not depend on this file.

What is evaluated: `seqSearch 7 Ptabs 1 0 78 400 14 5039 2520 5039` (levels 0 to 78, fuel 400, cut at
depth 14 into 5039 parts, of which this file evaluates the parts 2520 to 5038).  Reference:
`scratchP/pproto.c` visits 15,136,651,976 kept prefixes in the whole search and finds no violation.

This file imports `PSearch.lean` and the tables `PTables.lean` only.  No file of level 1 imports
it.
-/

namespace SuperpermLowerBounds
namespace PS

open T5899

/-- One of 2 ranges of parts. -/
theorem f1_1 : seqSearch 7 Ptabs 1 0 78 400 14 5039 2520 5039 = false := by
  native_decide

end PS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.PS.f1_1
