import LowerBounds.K16Count
import LowerBounds.K16Tables
/-! K8 of Table C: the Lean equation of `K16.Evals` (field k8: `Ev Utab8 8 36 48 10 16 25 false`), evaluated with
fuel 400 in 8 parts by hash at depth 8 (`seqSearch ... 400 8 8 0 8 = false` gives `PS.Covered 8`), then the
count by the counting copy with the same parts.  Table C: kept 22,732,567,392. -/
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
#eval timedB "K8 Lean equation (k8), 8 parts" fun _ => seqSearch 7 Utab8 8 36 48 10 16 25 false 400 8 8 0 8
#eval timedC "K8 count, 8 parts" fun _ => seqCount 7 Utab8 8 36 48 10 16 25 false 400 8 8 0 8
