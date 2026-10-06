import Superperm.Bridge
import Superperm.Upper10

/-! The ten-symbol upper bound for `Hunter.Ssuper` (see `Superperm/UpperHunter.lean`). -/

namespace SuperpermBridge

/-- L(10) ≤ 4,034,873. -/
theorem ssuper_ten_le : Hunter.Ssuper 10 ≤ 4034873 :=
  hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_ten

end SuperpermBridge

#print axioms SuperpermBridge.ssuper_ten_le
