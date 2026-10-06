import Superperm.BridgeCore
import Superperm.Upper

/-!
# The upper bounds for the Hunter–Raudvere quantity, without importing the library

`SuperpermBridge.HR.Ssuper` is `Hunter.Ssuper` restated (`Superperm/BridgeCore.lean`);
`Superperm/Bridge.lean` proves `@HR.Ssuper = @Hunter.Ssuper` by `rfl`.  This file imports
only small parts of Mathlib; `Superperm/UpperHunter.lean` states the same bounds for
`Hunter.Ssuper` itself.
-/

namespace SuperpermBridge

/-- L(7) ≤ 5,905. -/
theorem hr_ssuper_seven_le : HR.Ssuper 7 ≤ 5905 :=
  ssuper_le_of_hasWord LiteralSuperperm.hasWord_seven

/-- L(8) ≤ 46,181. -/
theorem hr_ssuper_eight_le : HR.Ssuper 8 ≤ 46181 :=
  ssuper_le_of_hasWord LiteralSuperperm.hasWord_eight

/-- L(9) ≤ 408,731. -/
theorem hr_ssuper_nine_le : HR.Ssuper 9 ≤ 408731 :=
  ssuper_le_of_hasWord LiteralSuperperm.hasWord_nine

end SuperpermBridge

#print axioms SuperpermBridge.hr_ssuper_seven_le
#print axioms SuperpermBridge.hr_ssuper_eight_le
#print axioms SuperpermBridge.hr_ssuper_nine_le
