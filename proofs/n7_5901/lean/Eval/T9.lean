import LowerBounds.J16Search
import LowerBounds.J16Tables
import Audit5901.J16Count
/-! T9' (tag T9r of Table C): J(S0 R R R R; 64, 68; 4), rings with 8..68 holes.
`rT9` and the specs are copied literally from `LowerBounds/J16Bridge.lean` (`rT9`, field `t9` of `J16.Evals`).
(1) the Lean equation itself: `jSearch 7 DJ DRj specs rT9 64 68 4 fuel [] 0 1` (one part, gprod [] = 1);
(2) its tree counted by the counting copy; (3) the same with the class cut off and the clip on (the rule of the
card program, PROOF_5901.md 4.2), to compare with Table C: kept 11,105,597, tried 59,706,146. -/
open SuperpermLowerBounds J16 T5901J
def noC : Int × Int := (J15.negInf, 1000000000)
def rT9 : Rules :=
  ⟨[noC, (0, 1000000000), (0, 1000000000), (0, 1000000000), (0, 1000000000)], true, 9, 10, 15, 25, 9⟩
def rT9prog : Rules := ⟨[noC, noC, noC, noC, noC], true, 9, 10, 15, 25, 9⟩
def rT9noclip : Rules := ⟨[noC, noC, noC, noC, noC], false, 9, 10, 15, 25, 9⟩
def sp9 : List (Nat × Nat × Nat) := [(1, 0, 0), (0, 8, 68), (0, 8, 68), (0, 8, 68), (0, 8, 68)]
def timedB (name : String) (f : Unit → Bool) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  let t1 ← IO.monoMsNow
  IO.println s!"{name}: answer {r}  ({t1 - t0} ms)"
def timedC (name : String) (f : Unit → Nat × Nat × Nat × Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  let t1 ← IO.monoMsNow
  IO.println s!"{name}: kept {r.1} tried {r.2.1} found {r.2.2.1} visits {r.2.2.2}  ({t1 - t0} ms)"
#eval timedB "T9' Lean equation jSearch (t9 of J16.Evals), fuel 1000" fun _ =>
  jSearch 7 DJ DRj sp9 rT9 64 68 4 1000 [] 0 1
#eval timedC "T9' count, Lean rule (class cut + clip)" fun _ =>
  J16C.jCount 7 DJ DRj sp9 rT9 64 68 4 1000 [] 0 1
#eval timedC "T9' count, program rule (clip, no class cut)" fun _ =>
  J16C.jCount 7 DJ DRj sp9 rT9prog 64 68 4 1000 [] 0 1
#eval timedC "T9' count, no clip, no class cut" fun _ =>
  J16C.jCount 7 DJ DRj sp9 rT9noclip 64 68 4 1000 [] 0 1
