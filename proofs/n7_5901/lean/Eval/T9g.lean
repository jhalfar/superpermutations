import LowerBounds.J16Search
import LowerBounds.J16Tables
import Audit5901.J16Count
/-! Check of the parts mechanism on T9' (fast): the same search as Eval/T9.lean in 8 parts with the gate
`[(0, 4, 8)]`; the summed counts must be those of one part. -/
open SuperpermLowerBounds J16 T5901J
def noC : Int × Int := (J15.negInf, 1000000000)
def rT9 : Rules :=
  ⟨[noC, (0, 1000000000), (0, 1000000000), (0, 1000000000), (0, 1000000000)], true, 9, 10, 15, 25, 9⟩
def sp9 : List (Nat × Nat × Nat) := [(1, 0, 0), (0, 8, 68), (0, 8, 68), (0, 8, 68), (0, 8, 68)]
#eval jSearch 7 DJ DRj sp9 rT9 64 68 4 1000 [(0, 4, 8)] 0 8
#eval J16C.jCount 7 DJ DRj sp9 rT9 64 68 4 1000 [(0, 4, 8)] 0 8
#eval (J16C.jRunDigs 7 DJ DRj sp9 rT9 64 68 4 1000 ((List.range 8).map fun j => J15.digs [(0, 4, 8)] j))
