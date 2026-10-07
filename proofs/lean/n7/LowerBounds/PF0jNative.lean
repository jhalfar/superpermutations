import LowerBounds.PSearch
import LowerBounds.PTables

/-!
# F0: chains, parts 4536 to 5038 of 5039, evaluated as compiled code

**Trusted here.**  Every theorem of this file is proved by `native_decide`: Lean does not check
the computation in its kernel but runs it as compiled code and records the result as an axiom
(`SuperpermLowerBounds.PS.<name>._native.native_decide.ax_1_1`, listed by `#print axioms`).  So
this file trusts, in addition to the kernel: the Lean compiler (from `PSearch.lean` to C), the C
compiler of the Lean toolchain (`leanc`, clang), the Lean runtime (natural numbers, arrays, byte
arrays, tasks), and that the library loaded with `--load-dynlib` (`build/native/PSearch.dll`, made
by `p_native_build.sh`) was compiled from `PSearch.lean` as it is.  The search itself and the
proof that its answer `false` means what is claimed (`PSound.lean`, `PSeq.lean`, `PEnc.lean`,
`PLevels.lean`, `PRules.lean`) are checked by the kernel and do not depend on this file.

What is evaluated: `seqSearch 7 Ptabs 0 0 84 400 14 5039 4536 5039` (chains with at most 84 holes,
fuel 400, cut at depth 14 into 5039 parts, of which this file evaluates the parts 4536 to 5038).
Reference: `scratchP/pproto.c` visits 90,373,570,810 kept prefixes in the whole search and finds no violation.

This file imports `PSearch.lean` and the tables `PTables.lean` only.  No file of level 1 imports
it.
-/

namespace SuperpermLowerBounds
namespace PS

open T5899

/-- One of 10 ranges of parts. -/
theorem f0_9 : seqSearch 7 Ptabs 0 0 84 400 14 5039 4536 5039 = false := by
  native_decide

end PS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.PS.f0_9
