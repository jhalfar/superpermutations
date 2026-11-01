import Audit5901.NK6_00
import Audit5901.NK6_01
import Audit5901.NK6_02
import Audit5901.NK6_03
import Audit5901.NK6_04
import Audit5901.NK6_05
import Audit5901.NK6_06
import Audit5901.NK6_07
import Audit5901.NK6_08
import Audit5901.NK6_09
import Audit5901.NK6_10
import Audit5901.NK6_11
import Audit5901.NK6_12
import Audit5901.NK6_13
import Audit5901.NK6_14
import Audit5901.NK6_15
import LowerBounds.K16Final

/-!
# The field `k6` of `K16.Evals` from the sixteen compiled parts of K6 (2026-11-01)

`NK6_00` … `NK6_15` evaluate the parts `[16 i, 16 i + 16)`, `i < 16`, of
`seqSearch 7 Utab6 6 38 60 10 16 25 false 400 10 256`.  Every part `tp < 256` lies in one of these ranges, which is
the field `k6 : Ev Utab6 6 38 60 10 16 25 false` of `LowerBounds/K16Final.lean`.  The step from the sixteen
equations to the field is checked by the kernel; the equations rest on `native_decide` (`#print axioms` below).
-/

namespace SuperpermLowerBounds
namespace Audit5901

open T5901

theorem k6_ev : K16.Ev Utab6 6 38 60 10 16 25 false :=
  ⟨400, 10, 256, by decide, fun tp htp => by
    rcases Nat.lt_or_ge tp 16 with h1 | h1
    · exact ⟨0, 16, Nat.zero_le tp, h1, K16.Audit.k6_0_16⟩
    rcases Nat.lt_or_ge tp 32 with h2 | h2
    · exact ⟨16, 32, h1, h2, K16.Audit.k6_16_32⟩
    rcases Nat.lt_or_ge tp 48 with h3 | h3
    · exact ⟨32, 48, h2, h3, K16.Audit.k6_32_48⟩
    rcases Nat.lt_or_ge tp 64 with h4 | h4
    · exact ⟨48, 64, h3, h4, K16.Audit.k6_48_64⟩
    rcases Nat.lt_or_ge tp 80 with h5 | h5
    · exact ⟨64, 80, h4, h5, K16.Audit.k6_64_80⟩
    rcases Nat.lt_or_ge tp 96 with h6 | h6
    · exact ⟨80, 96, h5, h6, K16.Audit.k6_80_96⟩
    rcases Nat.lt_or_ge tp 112 with h7 | h7
    · exact ⟨96, 112, h6, h7, K16.Audit.k6_96_112⟩
    rcases Nat.lt_or_ge tp 128 with h8 | h8
    · exact ⟨112, 128, h7, h8, K16.Audit.k6_112_128⟩
    rcases Nat.lt_or_ge tp 144 with h9 | h9
    · exact ⟨128, 144, h8, h9, K16.Audit.k6_128_144⟩
    rcases Nat.lt_or_ge tp 160 with h10 | h10
    · exact ⟨144, 160, h9, h10, K16.Audit.k6_144_160⟩
    rcases Nat.lt_or_ge tp 176 with h11 | h11
    · exact ⟨160, 176, h10, h11, K16.Audit.k6_160_176⟩
    rcases Nat.lt_or_ge tp 192 with h12 | h12
    · exact ⟨176, 192, h11, h12, K16.Audit.k6_176_192⟩
    rcases Nat.lt_or_ge tp 208 with h13 | h13
    · exact ⟨192, 208, h12, h13, K16.Audit.k6_192_208⟩
    rcases Nat.lt_or_ge tp 224 with h14 | h14
    · exact ⟨208, 224, h13, h14, K16.Audit.k6_208_224⟩
    rcases Nat.lt_or_ge tp 240 with h15 | h15
    · exact ⟨224, 240, h14, h15, K16.Audit.k6_224_240⟩
    · exact ⟨240, 256, h15, htp, K16.Audit.k6_240_256⟩⟩

end Audit5901
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.Audit5901.k6_ev
