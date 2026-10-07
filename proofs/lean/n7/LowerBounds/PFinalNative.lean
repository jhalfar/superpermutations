import LowerBounds.PFinal
import LowerBounds.PProfNative
import LowerBounds.PF45Native
import LowerBounds.PF3Native
import LowerBounds.PRingNative
import LowerBounds.PF2Native
import LowerBounds.PF1aNative
import LowerBounds.PF1bNative
import LowerBounds.PF0aNative
import LowerBounds.PF0bNative
import LowerBounds.PF0cNative
import LowerBounds.PF0dNative
import LowerBounds.PF0eNative
import LowerBounds.PF0fNative
import LowerBounds.PF0gNative
import LowerBounds.PF0hNative
import LowerBounds.PF0iNative
import LowerBounds.PF0jNative

/-!
# 5,899 for 7 symbols, with the searches evaluated as compiled code

**Trusted here.**  Every theorem of this file depends on the axioms recorded by `native_decide`
in the files `P*Native.lean` (one axiom per evaluated equation; `#print axioms` lists them):

* FF: `PS.prof36`, `PS.prof26`, `PS.prof34`, `PS.prof14`, `PS.prof4` (`PProfNative.lean`);
* F5, F4: `PS.f5`, `PS.f4` (`PF45Native.lean`); F3: `PS.f3`; F2: `PS.f2`; FR: `PS.ring`;
* F1: `PS.f1_0`, `PS.f1_1` (two ranges of the 5039 parts of one search);
* F0: `PS.f0_0`, …, `PS.f0_9` (ten ranges of the 5039 parts of one search).

These equations were not checked by the kernel.  They were computed by the compiled search of
`PSearch.lean` (Lean compiler, the C compiler of the Lean toolchain, the Lean runtime, the library
`build/native/PSearch.dll`).  Everything else is checked by the kernel: this file only applies
`covers_5899_of_search` (`PFinal.lean`, axioms `propext`, `Classical.choice`, `Quot.sound`) to the
equations.

No file of level 1 imports this file.  The names of the theorems end in `_native`.
-/

namespace SuperpermLowerBounds

open T5899

/-- F0, from the ten ranges of parts. -/
theorem f0_covered_native : PS.Covered 5039 (PS.seqSearch 7 Ptabs 0 0 84 400 14 5039) :=
  (fun tp htp => by
      by_cases h0 : tp < 504
      · exact ⟨0, 504, by omega, h0, PS.f0_0⟩
      by_cases h1 : tp < 1008
      · exact ⟨504, 1008, by omega, h1, PS.f0_1⟩
      by_cases h2 : tp < 1512
      · exact ⟨1008, 1512, by omega, h2, PS.f0_2⟩
      by_cases h3 : tp < 2016
      · exact ⟨1512, 2016, by omega, h3, PS.f0_3⟩
      by_cases h4 : tp < 2520
      · exact ⟨2016, 2520, by omega, h4, PS.f0_4⟩
      by_cases h5 : tp < 3024
      · exact ⟨2520, 3024, by omega, h5, PS.f0_5⟩
      by_cases h6 : tp < 3528
      · exact ⟨3024, 3528, by omega, h6, PS.f0_6⟩
      by_cases h7 : tp < 4032
      · exact ⟨3528, 4032, by omega, h7, PS.f0_7⟩
      by_cases h8 : tp < 4536
      · exact ⟨4032, 4536, by omega, h8, PS.f0_8⟩
      exact ⟨4536, 5039, by omega, htp, PS.f0_9⟩)

/-- F1, from the two ranges of parts. -/
theorem f1_covered_native : PS.Covered 5039 (PS.seqSearch 7 Ptabs 1 0 78 400 14 5039) :=
  (fun tp htp => by
      by_cases h0 : tp < 2520
      · exact ⟨0, 2520, by omega, h0, PS.f1_0⟩
      exact ⟨2520, 5039, by omega, htp, PS.f1_1⟩)

/-- The chain caps, the caps for sequences with 1 to 5 links of weight 4, and the ring caps. -/
theorem caps_native : Caps :=
  caps_of_search (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) f0_covered_native f1_covered_native (PS.covered_one PS.f2) (PS.covered_one PS.f3)
    (PS.covered_one PS.f4) (PS.covered_one PS.f5) (PS.covered_one PS.ring)

/-- The five profile statements. -/
theorem profiles_native : Profiles :=
  profiles_of_search (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) f0_covered_native (PS.covered_one PS.prof36) (PS.covered_one PS.prof26)
    (PS.covered_one PS.prof34) (PS.covered_one PS.prof14) (PS.covered_one PS.prof4)

/-- **Every word over `Fin 7` that contains all permutations has at least 5,899 letters** (with
the searches evaluated as compiled code). -/
theorem covers_lower_bound_7_native :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5899 ≤ w.length :=
  covers_5899_of_caps caps_native profiles_native

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.caps_native
#print axioms SuperpermLowerBounds.profiles_native
#print axioms SuperpermLowerBounds.covers_lower_bound_7_native
