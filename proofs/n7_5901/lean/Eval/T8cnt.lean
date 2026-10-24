import LowerBounds.J16Search
import LowerBounds.J16Tables
import Audit5901.J16Count
/-! T8 of Table C: J(S0 S0 S0 R; 66, 65; 2).  `rT8` and the specs are copied literally from
`LowerBounds/J16Bridge.lean` (`rT8`, field `t8` of `J16.Evals`).
(1) the Lean equation: `jSearch 7 DJ DRj specs rT8 66 65 2 1000 gs 0 35` with the gates `gs = [(0, 3, 7), (0, 5, 5)]`
(piece 1 at 3 and 5 rows, keys modulo 7 and 5; `Cov (gprod gs)` with gprod gs = 35, every g.2.2 > 0);
(2) the tree of the same search counted by the counting copy, same parts.
Table C: kept 7,126,584,865, tried 36,384,111,126. -/
open SuperpermLowerBounds J16 T5901J
def noC : Int × Int := (J15.negInf, 1000000000)
def rT8 : Rules := ⟨[noC, noC, noC, (0, 1000000000)], true, 9, 10, 15, 25, 9⟩
def sp8 : List (Nat × Nat × Nat) := [(1, 0, 0), (1, 0, 0), (1, 0, 0), (0, 0, 65)]
def timedB (name : String) (f : Unit → Bool) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.println s!"{name}: answer {r}"
  let t1 ← IO.monoMsNow
  IO.println s!"  {t1 - t0} ms"
def timedC (name : String) (f : Unit → Nat × Nat × Nat × Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.println s!"{name}: kept {r.1} tried {r.2.1} found {r.2.2.1} visits {r.2.2.2}"
  let t1 ← IO.monoMsNow
  IO.println s!"  {t1 - t0} ms"
#eval timedC "T8 count, Lean rule, 35 parts" fun _ =>
  J16C.jCount 7 DJ DRj sp8 rT8 66 65 2 1000 [(0, 3, 7), (0, 5, 5)] 0 35
