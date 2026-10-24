import Audit5901.NK7_0
import Audit5901.NK7_1
import Audit5901.NK7_2
import Audit5901.NK7_3
import LowerBounds.K16Final

/-!
# The field `k7` of `K16.Evals` from the four compiled parts of K7 (2026-10-24)

`NK7_0` … `NK7_3` evaluate the parts `[0, 16)`, `[16, 32)`, `[32, 48)` and `[48, 64)` of
`seqSearch 7 Utab7 7 36 54 10 16 25 false 400 8 64`.  Every part `tp < 64` lies in one of these ranges, which is
the field `k7 : Ev Utab7 7 36 54 10 16 25 false` of `LowerBounds/K16Final.lean`.  The step from the four
equations to the field is checked by the kernel; the equations rest on `native_decide` (`#print axioms` below).
-/

namespace SuperpermLowerBounds
namespace Audit5901

open T5901

theorem k7_ev : K16.Ev Utab7 7 36 54 10 16 25 false :=
  ⟨400, 8, 64, by decide, fun tp htp => by
    rcases Nat.lt_or_ge tp 16 with h1 | h1
    · exact ⟨0, 16, Nat.zero_le tp, h1, K16.Audit.k7_0_16⟩
    rcases Nat.lt_or_ge tp 32 with h2 | h2
    · exact ⟨16, 32, h1, h2, K16.Audit.k7_16_32⟩
    rcases Nat.lt_or_ge tp 48 with h3 | h3
    · exact ⟨32, 48, h2, h3, K16.Audit.k7_32_48⟩
    · exact ⟨48, 64, h3, htp, K16.Audit.k7_48_64⟩⟩

end Audit5901
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.Audit5901.k7_ev
