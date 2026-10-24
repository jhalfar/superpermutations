import LowerBounds.J15Search
import LowerBounds.KTables

/-!
# A statement of part C of 5,900, evaluated as compiled code

**Trusted here.**  Every theorem of this file is proved by `native_decide`: Lean does not check
the computation in its kernel but runs it as compiled code and records the result as an axiom
(`SuperpermLowerBounds.J15.<name>._native.native_decide.ax_1_1`, listed by `#print axioms`).  So
this file trusts, in addition to the kernel: the Lean compiler (from `PSearch.lean`,
`KSearch.lean` and `J15Search.lean` to C), the C compiler of the Lean toolchain (`leanc`, clang),
the Lean runtime (natural numbers, integers, arrays, byte arrays, tasks), and that the library
loaded with `--load-dynlib` (the library `J15Search` that `build.sh` makes) was
compiled from these three files as they are.  The search and the proof that its answer `false`
means what is claimed (`J15Sound.lean`, `J15Rules.lean`, `J15Final.lean`) are checked by the
kernel and do not depend on this file.

What is evaluated (the reference runs of the first and the second program found no object, with
the numbers of kept prefixes and of start vertices tried given):

* `s1_5`: S1 = J(S4 S4; 55, 78; 1), parts 1400 to 1679 of 3360 (2,104,901,227,440 kept, 10,736,238,262,512 tried in all)

A piece is `(c, lo, hi)`: `c = 0` a ring with `lo` to `hi` holes, `c = s + 1` a sequence with at
most `s` links of weight 4.  The arguments after the pieces are `V W B`, the fuel, the gates
`(piece, rows, classes)` and the range of parts (the number of parts is the product of the
numbers of classes).

This file imports `J15Search.lean` and the tables `KTables.lean` only.  No file of level 1
imports it.
-/

namespace SuperpermLowerBounds
namespace J15

open T5900

theorem s1_5 :
    jSearch 7 Ttab TRtab [(5, 0, 0), (5, 0, 0)] 55 78 1 400 [(0, 16, 32), (0, 22, 5), (0, 28, 3), (0, 32, 7)] 1400 1680 = false := by
  native_decide

end J15
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.J15.s1_5
