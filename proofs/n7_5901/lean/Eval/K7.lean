import LowerBounds.K16Count
import LowerBounds.K16Tables
/-! K7 of Table C: the Lean equation of `K16.Evals` (field k7: `Ev Utab7 7 36 54 10 16 25 false`), evaluated with
fuel 400 in 64 parts by hash at depth 8 (`seqSearch ... 400 8 64 0 64 = false` gives `PS.Covered 64`).
Table C: kept 320,243,136,927 (gk4; k2_s12 the same). -/
open SuperpermLowerBounds K16 T5901
def timedB (name : String) (f : Unit → Bool) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.println s!"{name}: answer {r}"
  let t1 ← IO.monoMsNow
  IO.println s!"  {t1 - t0} ms"
#eval timedB "K7 Lean equation (k7), 64 parts" fun _ => seqSearch 7 Utab7 7 36 54 10 16 25 false 400 8 64 0 64
