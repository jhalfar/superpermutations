import LowerBounds.PFinalNative

/-!
# Audit of level 2 for 5,899: the final statement with the searches evaluated

**Trusted here.**  `covers_lower_bound_7_native` depends on the three standard axioms and on one
axiom per evaluated search equation (22 of them, recorded by `native_decide` in the files
`LowerBounds/P*Native.lean`): the Lean compiler, the C compiler of the Lean toolchain, the Lean
runtime and the library `build/native/PSearch.dll` are trusted for these equations.  Everything
else is checked by the kernel (`Audit5899.lean`, `Audit5899Search.lean`).

The statement below uses no definition of this project.
-/

open SuperpermLowerBounds

/-- **Every word over 7 symbols that contains every permutation of the 7 symbols as a factor has
at least 5,899 letters.** -/
example : ∀ w : List (Fin 7),
    (∀ p : List (Fin 7), p.length = 7 → p.Nodup → ∃ u v : List (Fin 7), w = u ++ p ++ v) →
    5899 ≤ w.length :=
  covers_lower_bound_7_native

/-- The finite statements, evaluated. -/
example : ChainCap T5899.Mf 84 ∧ (∀ s, 1 ≤ s → s ≤ 5 → PathCap s (T5899.Pf s) (84 - 6 * s)) ∧
    RingCap T5899.PRf 77 :=
  ⟨caps_native.chain, caps_native.path, caps_native.ring⟩

example : NoProfile [(66, 36), (66, 36)] ∧ NoProfile [(50, 26), (50, 26)] ∧
    NoProfile [(63, 34), (34, 16)] ∧ NoProfile [(66, 36), (31, 14)] ∧
    NoProfile [(31, 14), (31, 14), (34, 16), (34, 16)] :=
  ⟨profiles_native.p36, profiles_native.p26, profiles_native.p34, profiles_native.p14,
    profiles_native.p4⟩

/-! ### Axioms: level 1 and level 2 -/

#print axioms SuperpermLowerBounds.covers_5899_of_caps
#print axioms SuperpermLowerBounds.covers_5899_of_search
#print axioms SuperpermLowerBounds.caps_native
#print axioms SuperpermLowerBounds.profiles_native
#print axioms SuperpermLowerBounds.covers_lower_bound_7_native
