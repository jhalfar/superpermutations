import Superperm.Bridge
import Superperm.Upper10b

/-! The ten-symbol upper bound 4,034,855 for `Hunter.Ssuper` (see `Superperm/UpperHunter.lean`). -/

namespace SuperpermBridge

/-- L(10) ≤ 4,034,855. -/
theorem ssuper_ten_le_b : Hunter.Ssuper 10 ≤ 4034855 :=
  hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_ten_b

end SuperpermBridge

#print axioms SuperpermBridge.ssuper_ten_le_b
