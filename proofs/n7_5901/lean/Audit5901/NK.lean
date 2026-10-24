import LowerBounds.K16Search
import LowerBounds.K16Tables

/-!
# K10, K9, K8 of Table C of 5,901: the Lean search equations, evaluated as compiled code

Agent pub5901, 2026-10-20.  Not part of the build of the level-1 sources; compiled in this folder (`lean/`) with
`--load-dynlib` of `build/native/K16Search.dll` of the level-1 build (`K16Search.c` + `KSearch.c` + `PSearch.c`, made by
`k16_native_build.sh` from the sources whose SHA-256 is in `build/native/SHA256_K16Search.txt`).

**Trusted here.**  Every theorem of this file is proved by `native_decide`: Lean does not check the computation
in its kernel but runs it as compiled code and records the result as an axiom (listed by `#print axioms`).  So
this file trusts, besides the kernel, the Lean compiler, the C compiler of the toolchain, the Lean runtime and
that the loaded library was compiled from those sources, as the native modules of 5,900 do.

The equations are those of the fields `k10`, `k9`, `k8` of `K16.Evals` (`LowerBounds/K16Final.lean`):
`Ev Utab10 10 36 36 10 16 25 false`, `Ev Utab9 9 36 42 10 16 25 false`, `Ev Utab8 8 36 48 10 16 25 false`,
with fuel 400; K10 and K9 in one part, K8 in 8 parts by hash at depth 8.  `NEv.lean` turns them into the fields.
-/

namespace SuperpermLowerBounds
namespace K16
namespace Audit

open T5901

theorem k10_native : seqSearch 7 Utab10 10 36 36 10 16 25 false 400 0 1 0 1 = false := by native_decide
theorem k9_native : seqSearch 7 Utab9 9 36 42 10 16 25 false 400 0 1 0 1 = false := by native_decide
theorem k8_native : seqSearch 7 Utab8 8 36 48 10 16 25 false 400 8 8 0 8 = false := by native_decide

end Audit
end K16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K16.Audit.k10_native
#print axioms SuperpermLowerBounds.K16.Audit.k9_native
#print axioms SuperpermLowerBounds.K16.Audit.k8_native
