import Superperm.Bridge
import Superperm.Upper12

/-! The twelve-symbol upper bound 522,737,175 for `Hunter.Ssuper` (the Hunter-Raudvere library, through
`Superperm/Bridge.lean`). -/

namespace SuperpermBridge

/-- L(12) ≤ 522,737,175. -/
theorem ssuper_twelve_le : Hunter.Ssuper 12 ≤ 522737175 :=
  hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_twelve

end SuperpermBridge

#print axioms SuperpermBridge.ssuper_twelve_le
