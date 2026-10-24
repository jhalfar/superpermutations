import LowerBounds.K16Search
import LowerBounds.PCount

/-!
# A counting copy of the search of `K16Search.lean` (not part of any proof)

`goC` is `K16.go` (the search of 5,900 with Rule JS if `js`) with two changes: it does not stop at a violation, and it counts, in 16 bytes
behind the marks of the table,

* the *kept prefixes*: the sequences that are continued with at least one kind of link (the unit
  of the counts of the reference programs), and
* the violations, plus the sequences at which the fuel ran out.

With parts, a prefix above the depth of the gate is counted in part 0 only, so the sum over the
parts is the count of the whole search.  Nothing is proved about this file.
-/

namespace SuperpermLowerBounds
namespace K16

open PS (walk all marks0 capF incr decode)
open KS (walkG tab2 look2 maxLeN tabA codeF maskG codeT uF segF a1F a2F maskT potN potS cutT)

@[specialize] def goC (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (kb : Nat)
    (code mask : Nat → Nat → Nat → Nat) (fN fS : Nat → Nat → Nat → Int)
    (cut : Nat → Nat → Nat → Int → Int → Bool) (js : Bool) (sz fg nt tp : Nat) :
    Nat → Nat → Nat → Nat → Int → Int → Nat → ByteArray → ByteArray
  | 0, _, _, _, _, _, _, B => incr B 8 (sz + 8)
  | fuel + 1, t, r, d, m, M, q, B =>
    let c := code t r d
    if c == 0 then B
    else if c == 1 then incr B 8 (sz + 8)
    else if fuel != fg || (q + 8192 * d) % nt == tp then
      let cq := ci (nxt q)
      let f := fN t r d
      let mN := min m f
      let MN := max M f
      let g := fS t r d
      let mS := min m g
      let MS := max M g
      let kn := c != 3 && cut t r d mN MN
      let ks := c != 2 && cut t r d mS MS
      let B0 := if (kn || ks) && (fuel ≤ fg || tp == 0) then incr B 8 sz else B
      let B1 :=
        if kn then
          let mk := mask t (r + 1) d
          all (fun D B' => walkG ci nxt
            (fun n e B'' => goC ci nxt s3 s4 kb code mask fN fS cut js sz fg nt tp fuel
              t (r + 1) (d + n) mN MN e B'') kb (jsM js ci cq D mk) D B') (s3 q) B0
        else B0
      if ks then
        let mk := mask (t + 1) (r + 1) d
        all (fun D B' => walkG ci nxt
          (fun n e B'' => goC ci nxt s3 s4 kb code mask fN fS cut js sz fg nt tp fuel
            (t + 1) (r + 1) (d + n) mS MS e B'') kb (jsM js ci cq D mk) D B') (s4 q) B1
      else B1
    else B

/-- (kept prefixes, violations) of every part `pa ≤ tp < pb`. -/
def seqCountParts (k : Nat) (caps : List (List Nat)) (s lo hi a b h : Nat) (js : Bool)
    (fuel ds nt pa pb : Nat) : List (Nat × Nat) :=
  let A := s + 1
  let C := hi + 1
  let tP := tab2 A C (capF caps)
  let P := look2 A C tP (capF caps)
  let R := maxLeN (P s) hi + 1
  let tc := tabA A (R + 1) C (codeF P s lo hi)
  let tm := tabA A (R + 1) C (fun t r d => maskG (codeT A R C tc) t r d (k - 1))
  let tu := tab2 A C (uF P s a b h)
  let tg := tab2 A C (segF P s a b h)
  let t1 := tabA A (R + 1) C (a1F P s lo hi a b h)
  let t2 := tabA A (R + 1) C
    (a2F (look2 A C tu (uF P s a b h)) (look2 A C tg (segF P s a b h)) P s lo hi a b h)
  let full := maskG (fun _ _ _ => 1) 0 0 0 (k - 1)
  let jl := PS.permCodes k k
  let ciT := PS.ciTab k jl
  let nxtT := PS.nxtTab k jl
  let s3T := PS.sdTab k 3 jl
  let s4T := PS.sdTab k 4 jl
  let sz := jl.length
  let ts := (List.range (pb - pa)).map fun i => Task.spawn fun _ =>
    let M := walk (fun i => ciT[i]!) (fun i => nxtT[i]!)
      (fun n e M => goC (fun i => ciT[i]!) (fun i => nxtT[i]!) (fun i => s3T[i]!)
        (fun i => s4T[i]!) (k - 1) (codeT A R C tc) (maskT A (R + 1) C full tm) (potN a b h)
        (potS a b h) (cutT A (R + 1) C t1 t2) js sz (fuel - ds) nt (pa + i) fuel 0 1 n 0 0 e M)
      (k - 1) (jl.idxOf (PS.idcF k)) (marks0 (sz + 16))
    (decode M sz, decode M (sz + 8))
  ts.map Task.get

/-- (kept prefixes, violations) summed over the parts `pa ≤ tp < pb`. -/
def seqCount (k : Nat) (caps : List (List Nat)) (s lo hi a b h : Nat) (js : Bool)
    (fuel ds nt pa pb : Nat) : Nat × Nat :=
  (seqCountParts k caps s lo hi a b h js fuel ds nt pa pb).foldl
    (fun acc c => (acc.1 + c.1, acc.2 + c.2)) (0, 0)

end K16
end SuperpermLowerBounds
