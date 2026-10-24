import LowerBounds.J16Search
import LowerBounds.J16Tables

/-!
# T9' and T8 of Table C of 5,901: the Lean search equations, evaluated as compiled code

Agent pub5901, 2026-10-20.  Not part of the build of the level-1 sources; compiled in this folder (`lean/`) with
`--load-dynlib` of `build/A16C.dll` (`build.sh`: the C code of `LowerBounds/J16Search.lean`, of
`J15Search`, `KSearch`, `PSearch`, `PCount` from the native build of the level-1 sources, and of `Audit5901/J16Count.lean`;
hashes in `build/SHA256.txt`).

**Trusted here.**  Every theorem of this file is proved by `native_decide` (see `NK.lean`): the compiler, the C
compiler, the runtime and the loaded library are trusted, the kernel does not check the computation.

The rules are written out as structure literals; they are `J16.rT9` and `J16.rT8` of `LowerBounds/J16Bridge.lean`
(`NEv.lean` checks this by unfolding).  T9' in one part, T8 in 35 parts (gates `(0, 3, 7)`, `(0, 5, 5)`); fuel 1000.
-/

namespace SuperpermLowerBounds
namespace J16
namespace Audit

open T5901J

theorem t9_native :
    jSearch 7 DJ DRj [(1, 0, 0), (0, 8, 68), (0, 8, 68), (0, 8, 68), (0, 8, 68)]
      ⟨[(J15.negInf, 1000000000), (0, 1000000000), (0, 1000000000), (0, 1000000000), (0, 1000000000)],
        true, 9, 10, 15, 25, 9⟩ 64 68 4 1000 [] 0 1 = false := by native_decide

theorem t8_native :
    jSearch 7 DJ DRj [(1, 0, 0), (1, 0, 0), (1, 0, 0), (0, 0, 65)]
      ⟨[(J15.negInf, 1000000000), (J15.negInf, 1000000000), (J15.negInf, 1000000000), (0, 1000000000)],
        true, 9, 10, 15, 25, 9⟩ 66 65 2 1000 [(0, 3, 7), (0, 5, 5)] 0 35 = false := by native_decide

end Audit
end J16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.J16.Audit.t9_native
#print axioms SuperpermLowerBounds.J16.Audit.t8_native
