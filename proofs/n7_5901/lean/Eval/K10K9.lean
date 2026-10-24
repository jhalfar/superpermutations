import LowerBounds.K16Count
import LowerBounds.K16Tables
/-! K10 and K9 of Table C: the Lean equations of `K16.Evals` (fields k10, k9:
`Ev Utab10 10 36 36 10 16 25 false`, `Ev Utab9 9 36 42 10 16 25 false`), evaluated with fuel 400, one part
(`seqSearch ... 400 0 1 0 1 = false` gives `PS.Covered 1`), and the K10 count by the counting copy.
Table C: K10 kept 172,577; K9 kept 384,081,983 (K9 counted by the counting copy on 2026-10-17, k16_K16Bench.log). -/
open SuperpermLowerBounds K16 T5901
def timedB (name : String) (f : Unit → Bool) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.println s!"{name}: answer {r}"
  let t1 ← IO.monoMsNow
  IO.println s!"  {t1 - t0} ms"
def timedC (name : String) (f : Unit → Nat × Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.println s!"{name}: kept {r.1} violations/fuel-out {r.2}"
  let t1 ← IO.monoMsNow
  IO.println s!"  {t1 - t0} ms"
#eval timedC "K10 count" fun _ => seqCount 7 Utab10 10 36 36 10 16 25 false 400 0 1 0 1
#eval timedB "K10 Lean equation (k10)" fun _ => seqSearch 7 Utab10 10 36 36 10 16 25 false 400 0 1 0 1
#eval timedB "K9 Lean equation (k9)" fun _ => seqSearch 7 Utab9 9 36 42 10 16 25 false 400 0 1 0 1
