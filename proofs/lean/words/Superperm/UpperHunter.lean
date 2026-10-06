import Superperm.Bridge
import Superperm.Upper

/-!
# The upper bounds for `Hunter.Ssuper`

`Hunter.Ssuper k` is the quantity for which the Hunter–Raudvere library and the
preimage-chain project prove lower bounds (5,892 / 46,118 / 408,418 for k = 7, 8, 9).
Here are the matching upper bounds, from the literal words of `Superperm/Upper.lean`.
-/

namespace SuperpermBridge

/-- L(7) ≤ 5,905. -/
theorem ssuper_seven_le : Hunter.Ssuper 7 ≤ 5905 :=
  hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_seven

/-- L(8) ≤ 46,181. -/
theorem ssuper_eight_le : Hunter.Ssuper 8 ≤ 46181 :=
  hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_eight

/-- L(9) ≤ 408,731. -/
theorem ssuper_nine_le : Hunter.Ssuper 9 ≤ 408731 :=
  hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_nine

end SuperpermBridge

#print axioms SuperpermBridge.ssuper_seven_le
#print axioms SuperpermBridge.ssuper_eight_le
#print axioms SuperpermBridge.ssuper_nine_le
