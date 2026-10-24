import LowerBounds.KFinal
import LowerBounds.PFinalNative
import LowerBounds.KK87Native
import LowerBounds.KSmallNative
import LowerBounds.KK4Native
import LowerBounds.KK5Native
import LowerBounds.KK3Native
import LowerBounds.KK1_00Native
import LowerBounds.KK1_01Native
import LowerBounds.KK1_02Native
import LowerBounds.KK1_03Native
import LowerBounds.KK1_04Native
import LowerBounds.KK1_05Native
import LowerBounds.KK1_06Native
import LowerBounds.KK1_07Native
import LowerBounds.KK0_00Native
import LowerBounds.KK0_01Native
import LowerBounds.KK0_02Native
import LowerBounds.KK0_03Native
import LowerBounds.KK0_04Native
import LowerBounds.KK0_05Native
import LowerBounds.KK0_06Native
import LowerBounds.KK0_07Native
import LowerBounds.KK0_08Native
import LowerBounds.KK0_09Native
import LowerBounds.KK0_10Native
import LowerBounds.KK2_00Native
import LowerBounds.KK2_01Native
import LowerBounds.KK2_02Native
import LowerBounds.KK2_03Native
import LowerBounds.KK2_04Native
import LowerBounds.KK2_05Native
import LowerBounds.KK2_06Native
import LowerBounds.KK2_07Native
import LowerBounds.KK2_08Native
import LowerBounds.KK2_09Native
import LowerBounds.KK2_10Native
import LowerBounds.KK2_11Native

/-!
# Table T' and Theorem K, with the searches evaluated as compiled code

**Trusted here.**  The theorems of this file depend on the equations of the files `K*Native.lean`
and on the equations of the proof of 5,899 (`P*Native.lean`), each proved by `native_decide`: one
axiom per equation, listed by `#print axioms` below.  Everything else is checked by the kernel.
No file of level 1 imports this file.  The names of the theorems end in `_native`.
-/

namespace SuperpermLowerBounds
namespace KS

open T5899 T5900

/-- 8 links, all levels to 42 holes. -/
theorem k8_native : Ev Ttab 8 0 42 1 0 0 :=
  ⟨400, 0, 1, by norm_num, PS.covered_one k8⟩

/-- 7 links, all levels to 48 holes. -/
theorem k7_native : Ev Ttab 7 0 48 1 0 0 :=
  ⟨400, 0, 1, by norm_num, PS.covered_one k7⟩

/-- Chains, level 59. -/
theorem c59_native : Ev Ttab 0 59 59 2 3 5 :=
  ⟨400, 8, 61, by norm_num, PS.covered_one c59⟩

/-- Chains, levels 62 to 75. -/
theorem c62_native : Ev Ttab 0 62 75 2 3 5 :=
  ⟨400, 12, 499, by norm_num, PS.covered_one c62⟩

/-- Rings to 69 holes. -/
theorem ring_native : EvR (Ttab.getD 0 []) TRtab 69 :=
  ⟨400, 16, 1009, by norm_num, PS.covered_one ring⟩

/-- 6 links, all levels to 54 holes. -/
theorem k6_native : Ev Ttab 6 0 54 1 0 0 :=
  ⟨400, 10, 251, by norm_num, PS.covered_one k6⟩

/-- Chains, level 76. -/
theorem c76_native : Ev Ttab 0 76 76 2 3 5 :=
  ⟨400, 12, 499, by norm_num, PS.covered_one c76⟩

/-- 4 links, levels 48 to 66. -/
theorem k4_native : Ev Dtab 4 48 66 10 16 25 :=
  ⟨400, 12, 251, by norm_num, PS.covered_one k4⟩

/-- 5 links, all levels to 60 holes. -/
theorem k5_native : Ev Ttab 5 0 60 1 0 0 :=
  ⟨400, 12, 1021, by norm_num, PS.covered_one k5⟩

/-- 3 links, levels 55 to 72. -/
theorem k3_native : Ev Dtab 3 55 72 10 16 30 :=
  ⟨400, 13, 1021, by norm_num, PS.covered_one k3⟩

/-- 1 link, levels 62 to 84. -/
theorem k1_native : Ev Dtab 1 62 84 10 15 30 :=
  ⟨400, 17, 8191, by norm_num, fun tp htp => by
    by_cases h0 : tp < 1023
    · exact ⟨0, 1023, by omega, h0, k1_0⟩
    by_cases h1 : tp < 2047
    · exact ⟨1023, 2047, by omega, h1, k1_1⟩
    by_cases h2 : tp < 3071
    · exact ⟨2047, 3071, by omega, h2, k1_2⟩
    by_cases h3 : tp < 4095
    · exact ⟨3071, 4095, by omega, h3, k1_3⟩
    by_cases h4 : tp < 5119
    · exact ⟨4095, 5119, by omega, h4, k1_4⟩
    by_cases h5 : tp < 6143
    · exact ⟨5119, 6143, by omega, h5, k1_5⟩
    by_cases h6 : tp < 7167
    · exact ⟨6143, 7167, by omega, h6, k1_6⟩
    exact ⟨7167, 8191, by omega, htp, k1_7⟩⟩

/-- Chains, levels 77 to 90. -/
theorem k0_native : Ev Dtab 0 77 90 2 3 5 :=
  ⟨400, 18, 16381, by norm_num, fun tp htp => by
    by_cases h0 : tp < 1489
    · exact ⟨0, 1489, by omega, h0, k0_0⟩
    by_cases h1 : tp < 2978
    · exact ⟨1489, 2978, by omega, h1, k0_1⟩
    by_cases h2 : tp < 4467
    · exact ⟨2978, 4467, by omega, h2, k0_2⟩
    by_cases h3 : tp < 5956
    · exact ⟨4467, 5956, by omega, h3, k0_3⟩
    by_cases h4 : tp < 7445
    · exact ⟨5956, 7445, by omega, h4, k0_4⟩
    by_cases h5 : tp < 8935
    · exact ⟨7445, 8935, by omega, h5, k0_5⟩
    by_cases h6 : tp < 10424
    · exact ⟨8935, 10424, by omega, h6, k0_6⟩
    by_cases h7 : tp < 11913
    · exact ⟨10424, 11913, by omega, h7, k0_7⟩
    by_cases h8 : tp < 13402
    · exact ⟨11913, 13402, by omega, h8, k0_8⟩
    by_cases h9 : tp < 14891
    · exact ⟨13402, 14891, by omega, h9, k0_9⟩
    exact ⟨14891, 16381, by omega, htp, k0_10⟩⟩

/-- 2 links, levels 61 to 78. -/
theorem k2_native : Ev Dtab 2 61 78 10 16 25 :=
  ⟨400, 14, 4093, by norm_num, fun tp htp => by
    by_cases h0 : tp < 341
    · exact ⟨0, 341, by omega, h0, k2_0⟩
    by_cases h1 : tp < 682
    · exact ⟨341, 682, by omega, h1, k2_1⟩
    by_cases h2 : tp < 1023
    · exact ⟨682, 1023, by omega, h2, k2_2⟩
    by_cases h3 : tp < 1364
    · exact ⟨1023, 1364, by omega, h3, k2_3⟩
    by_cases h4 : tp < 1705
    · exact ⟨1364, 1705, by omega, h4, k2_4⟩
    by_cases h5 : tp < 2046
    · exact ⟨1705, 2046, by omega, h5, k2_5⟩
    by_cases h6 : tp < 2387
    · exact ⟨2046, 2387, by omega, h6, k2_6⟩
    by_cases h7 : tp < 2728
    · exact ⟨2387, 2728, by omega, h7, k2_7⟩
    by_cases h8 : tp < 3069
    · exact ⟨2728, 3069, by omega, h8, k2_8⟩
    by_cases h9 : tp < 3410
    · exact ⟨3069, 3410, by omega, h9, k2_9⟩
    by_cases h10 : tp < 3751
    · exact ⟨3410, 3751, by omega, h10, k2_10⟩
    exact ⟨3751, 4093, by omega, htp, k2_11⟩⟩

/-- The evaluated statements behind table T'. -/
theorem evalsT_native : EvalsT :=
  ⟨c59_native, c62_native, c76_native, ring_native, k5_native, k6_native, k7_native, k8_native⟩

/-- The evaluated statements for 0 to 4 links. -/
theorem evalsK_native : EvalsK := ⟨k0_native, k1_native, k2_native, k3_native, k4_native⟩

/-- Set B on words, from the evaluated equations of the proof of 5,899. -/
theorem setB_native : SetB :=
  setB_of_search (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) f0_covered_native f1_covered_native (PS.covered_one PS.f2)
    (PS.covered_one PS.f3) (PS.covered_one PS.f4) (PS.covered_one PS.f5) (PS.covered_one PS.ring)

/-- Table T' is valid. -/
theorem tableT_native : TableT := tableT_of_search setB_native evalsT_native

/-- Theorem K. -/
theorem theoremK_native : TheoremK := theoremK_of_search setB_native evalsT_native evalsK_native

end KS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.KS.tableT_native
#print axioms SuperpermLowerBounds.KS.theoremK_native
