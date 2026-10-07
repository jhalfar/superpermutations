import LowerBounds.PSearch
import LowerBounds.PTables

/-!
# FF: the five profile searches, evaluated as compiled code

**Trusted here.**  Every theorem of this file is proved by `native_decide`: Lean does not check
the computation in its kernel but runs it as compiled code and records the result as an axiom
(`SuperpermLowerBounds.PS.<name>._native.native_decide.ax_1_1`, listed by `#print axioms`).  So
this file trusts, in addition to the kernel: the Lean compiler (from `PSearch.lean` to C), the C
compiler of the Lean toolchain (`leanc`, clang), the Lean runtime (natural numbers, arrays, byte
arrays, tasks), and that the library loaded with `--load-dynlib` (`build/native/PSearch.dll`, made
by `p_native_build.sh`) was compiled from `PSearch.lean` as it is.  The search itself and the
proof that its answer `false` means what is claimed (`PSound.lean`, `PSeq.lean`, `PEnc.lean`,
`PLevels.lean`, `PRules.lean`) are checked by the kernel and do not depend on this file.

What is evaluated: `profSearch 7 Mtab ts 400 0 1 0 1` for the five profiles `ts` (fuel 400, one part).
Reference: `scratchP/pproto.c` (mode `prof`) and the counting copy `PCount.lean` visit
108,741 / 27,110 / 54,979 / 103,034 / 405,173 kept prefixes and find no family.

This file imports `PSearch.lean` and the tables `PTables.lean` only.  No file of level 1 imports
it.
-/

namespace SuperpermLowerBounds
namespace PS

open T5899

/-- 108,741 kept prefixes. -/
theorem prof36 : profSearch 7 Mtab [(66, 36), (66, 36)] 400 0 1 0 1 = false := by
  native_decide

/-- 27,110 kept prefixes. -/
theorem prof26 : profSearch 7 Mtab [(50, 26), (50, 26)] 400 0 1 0 1 = false := by
  native_decide

/-- 54,979 kept prefixes. -/
theorem prof34 : profSearch 7 Mtab [(63, 34), (34, 16)] 400 0 1 0 1 = false := by
  native_decide

/-- 103,034 kept prefixes. -/
theorem prof14 : profSearch 7 Mtab [(66, 36), (31, 14)] 400 0 1 0 1 = false := by
  native_decide

/-- 405,173 kept prefixes. -/
theorem prof4 : profSearch 7 Mtab [(31, 14), (31, 14), (34, 16), (34, 16)] 400 0 1 0 1 = false := by
  native_decide

end PS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.PS.prof36
#print axioms SuperpermLowerBounds.PS.prof26
#print axioms SuperpermLowerBounds.PS.prof34
#print axioms SuperpermLowerBounds.PS.prof14
#print axioms SuperpermLowerBounds.PS.prof4
