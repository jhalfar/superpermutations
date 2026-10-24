import LowerBounds.J15Final
import LowerBounds.J15S5Native
import LowerBounds.J15S4Native
import LowerBounds.J15S3Native
import LowerBounds.J15S2A1_00Native
import LowerBounds.J15S2A1_01Native
import LowerBounds.J15S2A1_02Native
import LowerBounds.J15S1_00Native
import LowerBounds.J15S1_01Native
import LowerBounds.J15S1_02Native
import LowerBounds.J15S1_03Native
import LowerBounds.J15S1_04Native
import LowerBounds.J15S1_05Native
import LowerBounds.J15S1_06Native
import LowerBounds.J15S1_07Native
import LowerBounds.J15S1_08Native
import LowerBounds.J15S1_09Native
import LowerBounds.J15S1_10Native
import LowerBounds.J15S1_11Native
import LowerBounds.J15S2A2_00Native
import LowerBounds.J15S2A2_01Native
import LowerBounds.J15S2A2_02Native
import LowerBounds.J15S2A2_03Native
import LowerBounds.J15S2A2_04Native
import LowerBounds.J15S2A2_05Native
import LowerBounds.J15S2A2_06Native
import LowerBounds.J15S2A2_07Native
import LowerBounds.J15S2A2_08Native
import LowerBounds.J15S2A2_09Native
import LowerBounds.J15S2A2_10Native
import LowerBounds.J15S2A2_11Native
import LowerBounds.J15S2A2_12Native
import LowerBounds.J15S2A2_13Native
import LowerBounds.J15S2A2_14Native
import LowerBounds.J15S2A2_15Native
import LowerBounds.J15S2A2_16Native
import LowerBounds.J15S2A2_17Native

/-!
# The six evaluated statements of part C, with the searches evaluated as compiled code

**Trusted here.**  The theorems of this file depend on the equations of the files
`J15*Native.lean`, each proved by `native_decide`: one axiom per equation, listed by
`#print axioms` below.  Everything else is checked by the kernel.  No file of level 1 imports
this file.  The names of the theorems end in `_native`.
-/

namespace SuperpermLowerBounds
namespace J15

open T5900

/-- S5 = J(S0 S0 R; 62, 70; 2). -/
theorem s5_native : Ev [(1, 0, 0), (1, 0, 0), (0, 0, 70)] 62 70 2 :=
  ⟨400, [(0, 20, 5), (0, 28, 4), (0, 36, 3)], by decide, fun tp htp => by
    have htp' : tp < 60 := htp
    exact ⟨0, 60, Nat.zero_le _, htp', s5⟩⟩

/-- S4 = J(S1 S1 R; 61, 71; 1). -/
theorem s4_native : Ev [(2, 0, 0), (2, 0, 0), (0, 0, 71)] 61 71 1 :=
  ⟨400, [(0, 16, 5), (0, 24, 4), (0, 32, 3)], by decide, fun tp htp => by
    have htp' : tp < 60 := htp
    exact ⟨0, 60, Nat.zero_le _, htp', s4⟩⟩

/-- S3 = J(S2 R R; 57, 76; 2). -/
theorem s3_native : Ev [(3, 0, 0), (0, 0, 76), (0, 0, 76)] 57 76 2 :=
  ⟨400, [(0, 8, 11), (0, 12, 7), (0, 20, 5), (0, 30, 3), (0, 40, 2), (1, 6, 4)], by decide, fun tp htp => by
    have htp' : tp < 9240 := htp
    exact ⟨0, 9240, Nat.zero_le _, htp', s3⟩⟩

/-- S2a1 = J(R S5; 51, 83; 1), rings with at least 16 holes. -/
theorem s2a1_native : Ev [(0, 16, 83), (6, 0, 0)] 51 83 1 :=
  ⟨400, [(0, 20, 13), (0, 32, 5), (0, 44, 3), (0, 56, 7), (0, 60, 2)], by decide, fun tp htp => by
    have htp' : tp < 2730 := htp
    by_cases h0 : tp < 910
    · exact ⟨0, 910, by omega, h0, s2a1_0⟩
    by_cases h1 : tp < 1820
    · exact ⟨910, 1820, by omega, h1, s2a1_1⟩
    exact ⟨1820, 2730, by omega, htp', s2a1_2⟩⟩

/-- S1 = J(S4 S4; 55, 78; 1). -/
theorem s1_native : Ev [(5, 0, 0), (5, 0, 0)] 55 78 1 :=
  ⟨400, [(0, 16, 32), (0, 22, 5), (0, 28, 3), (0, 32, 7)], by decide, fun tp htp => by
    have htp' : tp < 3360 := htp
    by_cases h0 : tp < 280
    · exact ⟨0, 280, by omega, h0, s1_0⟩
    by_cases h1 : tp < 560
    · exact ⟨280, 560, by omega, h1, s1_1⟩
    by_cases h2 : tp < 840
    · exact ⟨560, 840, by omega, h2, s1_2⟩
    by_cases h3 : tp < 1120
    · exact ⟨840, 1120, by omega, h3, s1_3⟩
    by_cases h4 : tp < 1400
    · exact ⟨1120, 1400, by omega, h4, s1_4⟩
    by_cases h5 : tp < 1680
    · exact ⟨1400, 1680, by omega, h5, s1_5⟩
    by_cases h6 : tp < 1960
    · exact ⟨1680, 1960, by omega, h6, s1_6⟩
    by_cases h7 : tp < 2240
    · exact ⟨1960, 2240, by omega, h7, s1_7⟩
    by_cases h8 : tp < 2520
    · exact ⟨2240, 2520, by omega, h8, s1_8⟩
    by_cases h9 : tp < 2800
    · exact ⟨2520, 2800, by omega, h9, s1_9⟩
    by_cases h10 : tp < 3080
    · exact ⟨2800, 3080, by omega, h10, s1_10⟩
    exact ⟨3080, 3360, by omega, htp', s1_11⟩⟩

/-- S2a2 = J(R S5; 51, 83; 1), rings with 8 to 15 holes. -/
theorem s2a2_native : Ev [(0, 8, 15), (6, 0, 0)] 51 83 1 :=
  ⟨400, [(1, 2, 16), (1, 8, 8), (1, 14, 4), (1, 20, 4), (1, 26, 4), (1, 32, 2)], by decide, fun tp htp => by
    have htp' : tp < 16384 := htp
    by_cases h0 : tp < 910
    · exact ⟨0, 910, by omega, h0, s2a2_0⟩
    by_cases h1 : tp < 1820
    · exact ⟨910, 1820, by omega, h1, s2a2_1⟩
    by_cases h2 : tp < 2730
    · exact ⟨1820, 2730, by omega, h2, s2a2_2⟩
    by_cases h3 : tp < 3640
    · exact ⟨2730, 3640, by omega, h3, s2a2_3⟩
    by_cases h4 : tp < 4551
    · exact ⟨3640, 4551, by omega, h4, s2a2_4⟩
    by_cases h5 : tp < 5461
    · exact ⟨4551, 5461, by omega, h5, s2a2_5⟩
    by_cases h6 : tp < 6371
    · exact ⟨5461, 6371, by omega, h6, s2a2_6⟩
    by_cases h7 : tp < 7281
    · exact ⟨6371, 7281, by omega, h7, s2a2_7⟩
    by_cases h8 : tp < 8192
    · exact ⟨7281, 8192, by omega, h8, s2a2_8⟩
    by_cases h9 : tp < 9102
    · exact ⟨8192, 9102, by omega, h9, s2a2_9⟩
    by_cases h10 : tp < 10012
    · exact ⟨9102, 10012, by omega, h10, s2a2_10⟩
    by_cases h11 : tp < 10922
    · exact ⟨10012, 10922, by omega, h11, s2a2_11⟩
    by_cases h12 : tp < 11832
    · exact ⟨10922, 11832, by omega, h12, s2a2_12⟩
    by_cases h13 : tp < 12743
    · exact ⟨11832, 12743, by omega, h13, s2a2_13⟩
    by_cases h14 : tp < 13653
    · exact ⟨12743, 13653, by omega, h14, s2a2_14⟩
    by_cases h15 : tp < 14563
    · exact ⟨13653, 14563, by omega, h15, s2a2_15⟩
    by_cases h16 : tp < 15473
    · exact ⟨14563, 15473, by omega, h16, s2a2_16⟩
    exact ⟨15473, 16384, by omega, htp', s2a2_17⟩⟩

/-- The six evaluated statements. -/
theorem evals_native : Evals :=
  ⟨s1_native, s2a1_native, s2a2_native, s3_native, s4_native, s5_native⟩

end J15
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.J15.evals_native
