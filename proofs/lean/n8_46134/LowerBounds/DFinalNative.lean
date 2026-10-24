import LowerBounds.DFinal
import LowerBounds.DLine1Native
import LowerBounds.DLine2Native
import LowerBounds.DZoneNative

/-!
# 46,134 for 8 symbols, with the three searches evaluated as compiled code

**Trusted here.**  Every theorem of this file depends on the three axioms recorded by
`native_decide` in `DLine1Native.lean`, `DLine2Native.lean` and `DZoneNative.lean`:

* `S.lineSearch_8_4_9_56._native.native_decide.ax_1_1`:
  `S.lineSearch 8 2097152 4 9 56 400 40 251 = false`;
* `S.lineSearch_8_17_38_264._native.native_decide.ax_1_1`:
  `S.lineSearch 8 2097152 17 38 264 400 40 251 = false`;
* `S.zoneSearch_8._native.native_decide.ax_1_1`:
  `S.zoneSearch 8 2097152 4 9 56 2 17 38 264 6 400 40 251 = false`.

These three equations were not checked by the kernel.  They were computed by the compiled search
of `DSearch.lean` (Lean compiler, the C compiler of the Lean toolchain, the Lean runtime, the
library `DSearch.dll` (`.so`, `.dylib`) that `build.sh` makes).  Everything else is checked by the kernel: this file only
applies `covers_boundD_8_of_search` (`DFinal.lean`, axioms `propext`, `Classical.choice`,
`Quot.sound`) to the three equations.

No file of level 1 imports this file.  The names of the theorems end in `_native`.
-/

namespace SuperpermLowerBounds

/-- (H1) for model chains, from the evaluated search. -/
theorem modelLine_8_4_9_56_native : ModelLine 8 4 9 56 :=
  modelLine_of_search (by norm_num) (by norm_num) (by norm_num) S.lineSearch_8_4_9_56

/-- (H2) for model chains, from the evaluated search. -/
theorem modelLine_8_17_38_264_native : ModelLine 8 17 38 264 :=
  modelLine_of_search (by norm_num) (by norm_num) (by norm_num) S.lineSearch_8_17_38_264

/-- (H3) for model chains, from the three evaluated searches. -/
theorem modelZone8_native : ModelZone8 :=
  modelZone8_of_search (by norm_num) (by norm_num) (by norm_num) S.lineSearch_8_4_9_56
    S.lineSearch_8_17_38_264 S.zoneSearch_8

/-- (H1) for the chains of strongly exitless paths. -/
theorem chainLine_8_4_9_56_native : ChainLine 8 4 9 56 :=
  chainLine_of_model (by norm_num) modelLine_8_4_9_56_native

/-- (H2) for the chains of strongly exitless paths. -/
theorem chainLine_8_17_38_264_native : ChainLine 8 17 38 264 :=
  chainLine_of_model (by norm_num) modelLine_8_17_38_264_native

/-- (H3) for the chains of strongly exitless paths. -/
theorem zone8_native : Zone8 :=
  zone8_of_model modelZone8_native

/-- **Every word over `Fin 8` that contains all permutations has at least 46,134 letters**
(with the three searches evaluated as compiled code). -/
theorem covers_lower_bound_8_native :
    ∀ w : List (Fin 8), SuperpermutationBounds.Covers w → 46134 ≤ w.length :=
  covers_boundD_8_of_search (by norm_num) (by norm_num) (by norm_num) S.lineSearch_8_4_9_56
    S.lineSearch_8_17_38_264 S.zoneSearch_8

/-- The same for `Hunter.Ssuper 8`. -/
theorem ssuper_lower_bound_8_native : 46134 ≤ Hunter.Ssuper 8 :=
  superperm_boundD_8 chainLine_8_4_9_56_native chainLine_8_17_38_264_native zone8_native

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.modelLine_8_4_9_56_native
#print axioms SuperpermLowerBounds.modelLine_8_17_38_264_native
#print axioms SuperpermLowerBounds.modelZone8_native
#print axioms SuperpermLowerBounds.covers_lower_bound_8_native
#print axioms SuperpermLowerBounds.ssuper_lower_bound_8_native
