import LowerBounds.F5900
import LowerBounds.KFinalNative
import LowerBounds.J15FinalNative

/-!
# 5,900 for 7 symbols, with the searches evaluated as compiled code

**Trusted here.**  The theorems of this file depend on the axioms recorded by `native_decide` in
the files `P*Native.lean` (the 22 equations of the proof of 5,899), `K*Native.lean` (the equations
for table T' and for Theorem K) and `J15*Native.lean` (the equations for the joint statements);
`#print axioms` lists them.  These equations were not checked by the kernel: they were computed by
the compiled searches (Lean compiler, the C compiler of the Lean toolchain, the Lean runtime, the
libraries of the search engines).  Everything else is checked by the kernel: this file only
applies `covers_5900_of_caps` (axioms `propext`, `Classical.choice`, `Quot.sound`) to the evaluated
statements `caps_native`, `profiles_native`, `KS.tableT_native`, `KS.theoremK_native` and
`J15.evals_native`.

No file of level 1 imports this file.  The names of the theorems end in `_native`.
-/

namespace SuperpermLowerBounds

/-- The joint statements S1 .. S5. -/
theorem joint_native : KS.Joint :=
  J15.joint_of_search KS.tableT_native KS.theoremK_native J15.evals_native

/-- **Every word over `Fin 7` that contains all permutations has at least 5,900 letters** (with
the searches evaluated as compiled code). -/
theorem covers_lower_bound_7_5900_native :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5900 ≤ w.length :=
  covers_5900_of_caps caps_native profiles_native KS.tableT_native KS.theoremK_native joint_native

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.joint_native
#print axioms SuperpermLowerBounds.covers_lower_bound_7_5900_native
