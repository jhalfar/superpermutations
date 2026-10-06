import Superperm.BridgeCore
import Superperm.Upper10

/-! The ten-symbol upper bound for the Hunter–Raudvere quantity (see `Superperm/UpperHR.lean`). -/

namespace SuperpermBridge

/-- L(10) ≤ 4,034,873. -/
theorem hr_ssuper_ten_le : HR.Ssuper 10 ≤ 4034873 :=
  ssuper_le_of_hasWord LiteralSuperperm.hasWord_ten

end SuperpermBridge

#print axioms SuperpermBridge.hr_ssuper_ten_le
