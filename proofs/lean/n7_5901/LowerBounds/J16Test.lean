import LowerBounds.J16Search

/-!
# Small runs of the engine of 5,901, evaluated by the kernel (5 symbols)

The statements of `J15SmallSearch.lean` (true caps on 5 symbols: chains `3 3 5 5 6`, one link `6`, rings
`3 - 2 - 6`) with the rules of 5,901 switched on.  A statement for which objects exist must still be found
(the rules keep a counterexample: Rule PREV keeps one of `O`, `O^inv`, Rule ORD the sorted one, the class
its rings); one above it must still answer `false`.  `decide +kernel`, no `native_decide`.
-/

namespace SuperpermLowerBounds
namespace J16
namespace Small

/-- Caps on 5 symbols. -/
def C5 : List (List Nat) := [[3, 3, 5, 5, 6], [6, 0, 0, 0, 0]]
def R5 : List Nat := [3, 0, 2, 0, 6]

def nc : Int × Int := (J15.negInf, 1000000000)

/-- No rule of 5,901. -/
def rPlain : Rules := ⟨[nc, nc], false, 9, 10, 15, 25, 9⟩
/-- PREV on piece 1 (potential 10,15,25; on 5 symbols XL = 4 * 5 + 3 * 10 - 50 = 0). -/
def rPrev0 : Rules := ⟨[nc, nc], false, 0, 10, 15, 25, 9⟩
/-- ORD on pieces 1, 2. -/
def rOrd : Rules := ⟨[nc, nc], false, 9, 10, 15, 25, 0⟩
/-- PREV on piece 1 and ORD on pieces 1, 2. -/
def rBoth : Rules := ⟨[nc, nc], false, 0, 10, 15, 25, 0⟩
/-- PREV on piece 2 (behind a ring). -/
def rPrev1 : Rules := ⟨[nc, nc], false, 1, 10, 15, 25, 9⟩
/-- Rings of value at least `a`, need clipped at 0. -/
def rRing (a : Int) : Rules := ⟨[(a, 1000000000), nc], true, 9, 10, 15, 25, 9⟩

/-! ### Two chains: J(S0 S0; 7, 2; 0) holds, value 6 is reached -/

theorem chains_plain : jSearchA 5 C5 R5 [(1, 0, 0), (1, 0, 0)] rPlain 7 2 0 40 [] 0 1 = false := by
  decide +kernel
theorem chains_plain_low : jSearchA 5 C5 R5 [(1, 0, 0), (1, 0, 0)] rPlain 6 2 0 40 [] 0 1 = true := by
  decide +kernel
theorem chains_prev : jSearchA 5 C5 R5 [(1, 0, 0), (1, 0, 0)] rPrev0 7 2 0 40 [] 0 1 = false := by
  decide +kernel
theorem chains_prev_low : jSearchA 5 C5 R5 [(1, 0, 0), (1, 0, 0)] rPrev0 6 2 0 40 [] 0 1 = true := by
  decide +kernel
theorem chains_ord_low : jSearchA 5 C5 R5 [(1, 0, 0), (1, 0, 0)] rOrd 6 2 0 40 [] 0 1 = true := by
  decide +kernel
theorem chains_both_low : jSearchA 5 C5 R5 [(1, 0, 0), (1, 0, 0)] rBoth 6 2 0 40 [] 0 1 = true := by
  decide +kernel
theorem chains_both_parts :
    jSearchA 5 C5 R5 [(1, 0, 0), (1, 0, 0)] rBoth 7 2 0 40 [(0, 2, 3)] 0 3 = false := by
  decide +kernel

/-! ### A ring and a chain: J(R S0; 7, 3; 1) holds, value 6 is reached -/

theorem ring_plain_low : jSearchA 5 C5 R5 [(0, 0, 3), (1, 0, 0)] rPlain 6 3 1 40 [] 0 1 = true := by
  decide +kernel
theorem ring_prev_low : jSearchA 5 C5 R5 [(0, 0, 3), (1, 0, 0)] rPrev1 6 3 1 40 [] 0 1 = true := by
  decide +kernel
theorem ring_prev : jSearchA 5 C5 R5 [(0, 0, 3), (1, 0, 0)] rPrev1 7 3 1 40 [] 0 1 = false := by
  decide +kernel
/-- The ring of the objects of value 6 has value 3: kept by the class "value at least 3" ... -/
theorem ring_cls3_low : jSearchA 5 C5 R5 [(0, 0, 3), (1, 0, 0)] (rRing 3) 6 3 1 40 [] 0 1 = true := by
  decide +kernel
/-- ... and no object of value 6 has a ring of value at least 4. -/
theorem ring_cls4 : jSearchA 5 C5 R5 [(0, 0, 3), (1, 0, 0)] (rRing 4) 6 3 1 40 [] 0 1 = false := by
  decide +kernel

/-! ### The compiled search with tables (`jSearch`, what `Evals` evaluates) on the same statements

Printed when the file is compiled: `[false, true, false, true, true, true, false, true, true, false, true, false]`
is expected (the answers of the twelve theorems above, in their order). -/

#eval [jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0)] rPlain 7 2 0 40 [] 0 1,
  jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0)] rPlain 6 2 0 40 [] 0 1,
  jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0)] rPrev0 7 2 0 40 [] 0 1,
  jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0)] rPrev0 6 2 0 40 [] 0 1,
  jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0)] rOrd 6 2 0 40 [] 0 1,
  jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0)] rBoth 6 2 0 40 [] 0 1,
  jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0)] rBoth 7 2 0 40 [(0, 2, 3)] 0 3,
  jSearch 5 C5 R5 [(0, 0, 3), (1, 0, 0)] rPlain 6 3 1 40 [] 0 1,
  jSearch 5 C5 R5 [(0, 0, 3), (1, 0, 0)] rPrev1 6 3 1 40 [] 0 1,
  jSearch 5 C5 R5 [(0, 0, 3), (1, 0, 0)] rPrev1 7 3 1 40 [] 0 1,
  jSearch 5 C5 R5 [(0, 0, 3), (1, 0, 0)] (rRing 3) 6 3 1 40 [] 0 1,
  jSearch 5 C5 R5 [(0, 0, 3), (1, 0, 0)] (rRing 4) 6 3 1 40 [] 0 1]

end Small
end J16
end SuperpermLowerBounds
