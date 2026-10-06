import Superperm.Bridge
import Superperm.Upper11

/-! The eleven-symbol upper bound 43,930,578 for `Hunter.Ssuper` (the Hunter-Raudvere library, through
`Superperm/Bridge.lean`). -/

namespace SuperpermBridge

/-- L(11) ≤ 43,930,578. -/
theorem ssuper_eleven_le : Hunter.Ssuper 11 ≤ 43930578 :=
  hunter_ssuper_le_of_hasWord LiteralSuperperm.hasWord_eleven

end SuperpermBridge

#print axioms SuperpermBridge.ssuper_eleven_le
