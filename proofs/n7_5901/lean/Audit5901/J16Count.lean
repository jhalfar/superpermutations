import LowerBounds.J16Search
import LowerBounds.PCount

/-!
# A counting copy of the engine of `J16Search.lean` (not part of any proof; agent pub5901, 2026-10-20)

`goC` is `J16.go` with the counters of `J15Count.lean` (`J15.goC`): it does not stop at an object, and
it counts, in 32 bytes behind the marks of the table,

* the kept prefixes: the prefixes that are continued with at least one kind of link (here: a link
  kind whose test `k3Ok`/`k4Ok` *and* hook `xr` pass, since the hooks are part of the J16 rule),
* the start vertices tried: the walks that are started, except at the successor that lies in the
  class of the last block (the unit of the reference programs),
* the objects found, plus the prefixes at which the fuel ran out,
* the visits (all calls that pass the gates).

Everything else (`compOk`, `xc`, the ring targets, `live`, the masks) is that of `J16.go` and
`J16.jSearch`, copied term for term.  With one part (`gs = []`) the counts are those of the whole
search.  Purpose: compare the tree of the Lean engine with the counts of Table C of PROOF_5901.md.
-/

namespace SuperpermLowerBounds
namespace J16C

open PS (all marks0 capF incr decode)
open KS (tabA tab2 look2 maxLe maxLeN par minLe)
open J15 (mkMask walkJ scanJ walkG vOf compOk k3Ok k4Ok live negInf sval pval bestF bestStep
  tmax kdF loF hiF gateD earlyD digs gprod bestT gT fT)
open J16 (Rules xrF xcF fG ringOk segF potF vloF)

def cntD : List (Nat × Nat × Nat × Nat) → Nat → Nat → Bool
  | [], _, _ => true
  | g :: ds, i, r =>
    (decide (g.1 < i) || (i == g.1 && decide (g.2.1 ≤ r)) || g.2.2.2 == 0) && cntD ds i r

@[specialize] def goC (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (jl : List Nat)
    (kb np bm : Nat) (kd lo hi : Nat → Nat) (bestLe : Nat → Nat → Int → Bool)
    (gLe : Nat → Nat → Nat → Int → Bool) (fLe : Nat → Nat → Nat → Nat → Int → Bool)
    (xr : Nat → Nat → Nat → Nat → Nat → Int → Nat → Int → Int → Bool)
    (xc : Nat → Nat → Nat → Nat → Int → Nat → Int → Int → Bool)
    (phi : Nat → Nat → Nat → Nat → Int) (sz : Nat) (ds : List (Nat × Nat × Nat × Nat)) :
    Nat → Nat → Nat → Nat → Nat → Int → Nat → Int → Int → Int → Nat → Nat → Nat → ByteArray →
      ByteArray
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, M => incr M 8 (sz + 16)
  | fuel + 1, i, t, r, d, a, b, m, pm, pM, z, q, du, M =>
    if gateD ds i r (q + 8192 * d) then
      let M := incr M 8 (sz + 24)
      let c := kd i
      let wt := d + kb * t
      let y := b - wt
      let v := vOf kb t r d
      let cn := cntD ds i r
      let M1 :=
        if compOk np bestLe (fun i' r' => earlyD ds i' r' (q + 8192 * d)) i r a y v &&
            (if c == 0 then
              decide (2 ≤ r) && decide (lo i ≤ d) && decide (d ≤ hi i) && (s3 q).contains z
            else decide (m < v)) && xc i t r d a b pm pM then
          if i + 1 == np then incr M 8 (sz + 16)
          else
            let mk := mkMask (fun n => decide (n ≤ y) &&
              live kb np kd bestLe gLe fLe (fun _ _ => true) (i + 1) 0 1 n (a - v) y (-(kb : Int))) kb
            all (fun D M' => walkG ci nxt
              (fun n e du' M'' =>
                goC ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe xr xc phi sz ds fuel
                  (i + 1) 0 1 n (a - v) y (-(kb : Int)) 0 0 D e du' M'')
              (UInt8.ofNat (i + 2)) bm kb mk du D
              (if cntD ds (i + 1) 0 then incr M' 8 (sz + 8) else M')) jl M
        else M
      let m' := max m v
      let k3 := k3Ok gLe fLe i c t r d a b y v && xr 0 i t r d a b pm pM
      let k4 := k4Ok gLe kb i c t a y v && xr 1 i t r d a b pm pM
      let M0 := if (k3 || k4) && cn then incr M1 8 sz else M1
      let M2 :=
        if k3 then
          let mk := mkMask (fun n => decide (wt + n ≤ b) &&
            live kb np kd bestLe gLe fLe (fun _ _ => true) i t (r + 1) (d + n) a b m') kb
          all (fun D M' => walkG ci nxt
            (fun n e du' M'' =>
              goC ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe xr xc phi sz ds fuel
                i t (r + 1) (d + n) a b m' (min pm (phi 0 t r d)) (max pM (phi 0 t r d)) z e
                du' M'')
            (UInt8.ofNat (i + 1)) bm kb mk du D
            (if cn && ci D != ci q then incr M' 8 (sz + 8) else M')) (s3 q) M0
        else M0
      if k4 then
        let mk := mkMask (fun n => decide (wt + kb + n ≤ b) &&
          live kb np kd bestLe gLe fLe (fun _ _ => true) i (t + 1) (r + 1) (d + n) a b m') kb
        all (fun D M' => walkG ci nxt
          (fun n e du' M'' =>
            goC ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe xr xc phi sz ds fuel
              i (t + 1) (r + 1) (d + n) a b m' (min pm (phi 1 t r d)) (max pM (phi 1 t r d)) z e
              du' M'')
          (UInt8.ofNat (i + 1)) bm kb mk du D
          (if cn && ci D != ci q then incr M' 8 (sz + 8) else M')) (s4 q) M2
      else M2
    else M

/-- (kept, tried, found, visits) of every part of the list `dss`; the tables are those of
`J16.jSearch`, built the same way. -/
def jRunDigs (k : Nat) (caps : List (List Nat)) (PRl : List Nat) (specs : List (Nat × Nat × Nat))
    (R : Rules) (V W bm fuel : Nat) (dss : List (List (Nat × Nat × Nat × Nat))) :
    List (Nat × Nat × Nat × Nat) :=
  let np := specs.length
  let S := maxLeN (kdF specs) np + 1
  let C := W + 1
  let tP := tab2 S C (capF caps)
  let P := look2 S C tP (capF caps)
  let tR := tab2 1 C (fun _ x => PRl.getD x 0)
  let PR := fun x => look2 1 C tR (fun _ x => PRl.getD x 0) 0 x
  let RR := maxLeN PR W + 1
  let kdA := (specs.map fun p => p.1).toArray
  let loA := (specs.map fun p => p.2.1).toArray
  let hiA := (specs.map fun p => p.2.2).toArray
  let tB := tab2 (np + 1) C (fun i y => bestF P PR (k - 1) (specs.drop (i + 1)) y)
  let B := look2 (np + 1) C tB (fun i y => bestF P PR (k - 1) (specs.drop (i + 1)) y)
  let tG := tabA np S C (fun i u y => bestStep P PR (k - 1) (u + 1, 0, 0) (B i) y)
  let tRB := tab2 S C (fun u y => bestF P PR (k - 1) [(u + 1, 0, 0)] y)
  let RB := look2 S C tRB (fun u y => bestF P PR (k - 1) [(u + 1, 0, 0)] y)
  let tS := tab2 S C (segF P (k - 1) R.pa R.pb R.ph)
  let SG := look2 S C tS (segF P (k - 1) R.pa R.pb R.ph)
  let tF := tabA (np * C) RR C (fun ib r d =>
    if kdA[ib / C]! == 0 then
      fG P PR (B (ib / C)) loA[ib / C]! hiA[ib / C]! (vloF R (ib / C)) (ib % C) r d
    else 0)
  let jl := PS.permCodes k k
  let ciT := PS.ciTab k jl
  let nxtT := PS.nxtTab k jl
  let s3T := PS.sdTab k 3 jl
  let s4T := PS.sdTab k 4 jl
  let sz := jl.length
  let st := jl.idxOf (PS.idcF k)
  let fLe := fun i b r d x => if i < np && b < C && r < RR && d < C then
        ringOk R.clip tF[((i * C + b) * RR + r) * C + d]! x else true
  let ts := dss.map fun ds => Task.spawn fun _ =>
    let M0 := marks0 (sz + 32)
    let M := walkG (fun i => ciT[i]!) (fun i => nxtT[i]!)
      (fun n e du M =>
        goC (fun i => ciT[i]!) (fun i => nxtT[i]!) (fun i => s3T[i]!) (fun i => s4T[i]!)
          (List.range jl.length) (k - 1) np bm (fun i => kdA[i]!) (fun i => loA[i]!)
          (fun i => hiA[i]!) (bestT np C tB) (gT np S C tG) fLe
          (xrF R (k - 1) np (fun i => kdA[i]!) B RB SG)
          (xcF R (k - 1) np (fun i => kdA[i]!) B)
          (fun c t r d => potF R.pa R.pb R.ph c t r d) sz ds
          fuel 0 0 1 n (V : Int) W (-((k - 1 : Nat) : Int)) 0 0 st e du M)
      (UInt8.ofNat 1) bm (k - 1)
      (mkMask (fun n => decide (n ≤ W) && live (k - 1) np (fun i => kdA[i]!) (bestT np C tB)
        (gT np S C tG) fLe (fun _ _ => true) 0 0 1 n (V : Int) W
        (-((k - 1 : Nat) : Int))) (k - 1))
      0 st (if cntD ds 0 0 then incr M0 8 (sz + 8) else M0)
    (decode M sz, decode M (sz + 8), decode M (sz + 16), decode M (sz + 24))
  ts.map Task.get

/-- (kept, tried, found, visits) summed over the parts `pa ≤ tp < pb` of the gates `gs`. -/
def jCount (k : Nat) (caps : List (List Nat)) (PRl : List Nat) (specs : List (Nat × Nat × Nat))
    (R : Rules) (V W bm fuel : Nat) (gs : List (Nat × Nat × Nat)) (pa pb : Nat) :
    Nat × Nat × Nat × Nat :=
  (jRunDigs k caps PRl specs R V W bm fuel ((List.range (pb - pa)).map fun j => digs gs (pa + j))).foldl
    (fun acc c => (acc.1 + c.1, acc.2.1 + c.2.1, acc.2.2.1 + c.2.2.1, acc.2.2.2 + c.2.2.2))
    (0, 0, 0, 0)

end J16C
end SuperpermLowerBounds
