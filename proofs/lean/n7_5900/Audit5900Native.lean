import LowerBounds.F5900Native

/-!
# Audit of level 2 for 5,900: the final statement with the searches evaluated

**Trusted here.**  `covers_lower_bound_7_5900_native` depends on the three standard axioms and on
one axiom per evaluated search equation, recorded by `native_decide` in the files
`LowerBounds/P*Native.lean` (22 equations of the proof of 5,899), `LowerBounds/K*Native.lean` (the
equations for table T' and for Theorem K) and `LowerBounds/J15*Native.lean` (the equations for the
joint statements): the Lean compiler, the C compiler of the Lean toolchain, the Lean runtime and
the libraries of the search engines are trusted for these equations.  Everything else is checked
by the kernel (`Audit5900.lean`, `Audit5900Search.lean`).

The statement below uses no definition of this project.
-/

open SuperpermLowerBounds

/-- **Every word over 7 symbols that contains every permutation of the 7 symbols as a factor has
at least 5,900 letters.** -/
example : ∀ w : List (Fin 7),
    (∀ p : List (Fin 7), p.length = 7 → p.Nodup → ∃ u v : List (Fin 7), w = u ++ p ++ v) →
    5900 ≤ w.length :=
  covers_lower_bound_7_5900_native

/-- The finite statements, evaluated. -/
example : Caps ∧ Profiles ∧ KS.TableT ∧ KS.TheoremK ∧ KS.Joint :=
  ⟨caps_native, profiles_native, KS.tableT_native, KS.theoremK_native, joint_native⟩

/-! ### Axioms: level 1 and level 2 -/

#print axioms SuperpermLowerBounds.covers_5900_of_caps
#print axioms SuperpermLowerBounds.covers_5900_of_search
#print axioms SuperpermLowerBounds.caps_native
#print axioms SuperpermLowerBounds.profiles_native
#print axioms SuperpermLowerBounds.KS.tableT_native
#print axioms SuperpermLowerBounds.KS.theoremK_native
#print axioms SuperpermLowerBounds.joint_native
#print axioms SuperpermLowerBounds.covers_lower_bound_7_5900_native
