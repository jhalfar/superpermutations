import K6.Engine
import K6.CapTab
import LowerBounds.PSearch

/-!
# The rules of the chain search (F0 on 6 symbols)

`capRules caps lo hi TB TK`: one trail, counters `(rows, holes)`; continue with a seam when
`SuperpermLowerBounds.PS.seqKeepN caps 0 lo hi 0 r d`, found when `PS.seqBad caps 0 lo hi 0 r d`, never a jump.  The two
rules are read from the bit tables `TB`, `TK` for `r < 64`, `d < 32` and computed outside;
`CapRulesOK` (in `Cap.lean`) proves that the tables agree with the rules, so the search with tables
is the search with the rules of `PSearch.lean`.  This file imports no Mathlib: the evaluations load
only it.
-/

namespace K6

/-- A Boolean function of two numbers, read from the bits of `T` for `r < 64`, `d < 32`. -/
@[inline] def lk (T : Nat) (f : Nat → Nat → Bool) (r d : Nat) : Bool :=
  cond (r.blt 64 && d.blt 32) (T.testBit (32 * r + d)) (f r d)

/-- The rules of the chain search with caps `caps` on the levels `lo … hi`. -/
def capRules (caps : List (List Nat)) (lo hi TB TK : Nat) : Rules (Nat × Nat) where
  init n _ := (1, n)
  stN c n _ := (c.1 + 1, c.2 + n)
  stJ c _ _ := c
  keepN c := lk TK (SuperpermLowerBounds.PS.seqKeepN caps 0 lo hi 0) c.1 c.2
  keepJ _ := false
  bad c _ := lk TB (SuperpermLowerBounds.PS.seqBad caps 0 lo hi 0) c.1 c.2

end K6
