import Audit5901.NK
import Audit5901.NJ
import LowerBounds.K16Final
import LowerBounds.J16Bridge

/-!
# Five fields of `K16.Evals` and `J16.Evals` from the compiled evaluations (agent pub5901, 2026-10-20)

`k10`, `k9`, `k8` of `K16.Evals` and `t9`, `t8` of `J16.Evals`, stated with the definitions of
`LowerBounds/K16Final.lean` and `LowerBounds/J16Bridge.lean` (`K16.Ev`, `J16.Ev`, `J16.rT9`, `J16.rT8`), from the
`native_decide` theorems of `NK.lean` and `NJ.lean`.  The step from the equation to the field is checked by the
kernel; the equations themselves rest on `native_decide` (`#print axioms` below).
-/

namespace SuperpermLowerBounds
namespace Audit5901

open T5901 T5901J

theorem k10_ev : K16.Ev Utab10 10 36 36 10 16 25 false :=
  ⟨400, 0, 1, by decide, PS.covered_one K16.Audit.k10_native⟩
theorem k9_ev : K16.Ev Utab9 9 36 42 10 16 25 false :=
  ⟨400, 0, 1, by decide, PS.covered_one K16.Audit.k9_native⟩
theorem k8_ev : K16.Ev Utab8 8 36 48 10 16 25 false :=
  ⟨400, 8, 8, by decide, PS.covered_one K16.Audit.k8_native⟩

/-- The field `t9` of `J16.Evals`: T9' (T9r). -/
theorem t9_ev : J16.Ev DRj [(1, 0, 0), (0, 8, 68), (0, 8, 68), (0, 8, 68), (0, 8, 68)] J16.rT9 64 68 4 :=
  ⟨1000, [], by simp, fun tp htp => ⟨0, 1, Nat.zero_le tp, htp, J16.Audit.t9_native⟩⟩

/-- The field `t8` of `J16.Evals`. -/
theorem t8_ev : J16.Ev DRj [(1, 0, 0), (1, 0, 0), (1, 0, 0), (0, 0, 65)] J16.rT8 66 65 2 :=
  ⟨1000, [(0, 3, 7), (0, 5, 5)], by decide, fun tp htp => ⟨0, 35, Nat.zero_le tp, htp, J16.Audit.t8_native⟩⟩

end Audit5901
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.Audit5901.k10_ev
#print axioms SuperpermLowerBounds.Audit5901.k9_ev
#print axioms SuperpermLowerBounds.Audit5901.k8_ev
#print axioms SuperpermLowerBounds.Audit5901.t9_ev
#print axioms SuperpermLowerBounds.Audit5901.t8_ev
