import LowerBounds.PSearch

/-!
# A counting copy of the search of `PSearch.lean` (not part of any proof)

`goC` is `PS.go` with two changes: it does not stop when a sequence is found, and it counts, in
16 bytes behind the marks of the table,

* the *kept prefixes*: the sequences for which at least one `keep` holds (the unit of the node
  counts of the C programs), and
* the sequences found (`bad`, or `badR` with the closing link), plus the sequences at which the
  fuel ran out.

With parts, a prefix above the depth of the gate is counted in part 0 only, so the sum over the
parts is the count of the whole search.  Nothing is proved about this file; it is the cross-check
of the compiled search against a C program of mine.
-/

namespace SuperpermLowerBounds
namespace PS

/-- Add one to the little-endian counter at `off` (at most `n` bytes). -/
def incr (M : ByteArray) : Nat → Nat → ByteArray
  | 0, _ => M
  | n + 1, off =>
    let b := M.get! off
    if b == 255 then incr (M.set! off 0) n (off + 1) else M.set! off (b + 1)

/-- The little-endian counter of 8 bytes at `off`. -/
def decode (M : ByteArray) (off : Nat) : Nat :=
  (List.range 8).foldr (fun i acc => acc * 256 + (M.get! (off + i)).toNat) 0

@[specialize] def goC (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (jl : List Nat) (st kb : Nat)
    (rs : Bool) (bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool) (sz fg nt tp : Nat) :
    Nat → Nat → Nat → Nat → Nat → ByteArray → ByteArray
  | 0, _, _, _, _, M => incr M 8 (sz + 8)
  | fuel + 1, t, r, d, q, M =>
    if bad t r d || (badR t r d && (s3 q).contains st) then incr M 8 (sz + 8)
    else if fuel != fg || q % nt == tp then
      let kn := keepN t r d
      let ks := keepS t r d
      let kj := keepJ t r d
      let M0 := if (kn || ks || kj) && (fuel ≤ fg || tp == 0) then incr M 8 sz else M
      let M1 :=
        if kn then
          all (fun D M' => walk ci nxt
            (fun n e M'' => goC ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ sz fg nt tp
              fuel t (r + 1) (d + n) e M'') kb D M') (s3 q) M0
        else M0
      let M2 :=
        if ks then
          all (fun D M' => walk ci nxt
            (fun n e M'' => goC ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ sz fg nt tp
              fuel (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'') kb D
              M') (s4 q) M1
        else M1
      if kj then
        all (fun D M' => walk ci nxt
          (fun n e M'' => goC ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ sz fg nt tp
            fuel (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'') kb D M')
          jl M2
      else M2
    else M

@[specialize] def countPart (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (jl : List Nat)
    (st kb : Nat) (rs : Bool) (bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool)
    (sz fuel fg nt tp : Nat) : Nat × Nat :=
  let M := walk ci nxt
    (fun n e M => goC ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ sz fg nt tp fuel 0 1 n e
      M) kb st (marks0 (sz + 16))
  (decode M sz, decode M (sz + 8))

/-- (kept prefixes, found) summed over the parts `pa ≤ tp < pb`. -/
@[specialize] def countB (k : Nat) (rs : Bool)
    (bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool) (fuel ds nt pa pb : Nat) : Nat × Nat :=
  let jl := permCodes k k
  let ciT := ciTab k jl
  let nxtT := nxtTab k jl
  let s3T := sdTab k 3 jl
  let s4T := sdTab k 4 jl
  let ts := (List.range (pb - pa)).map fun i => Task.spawn fun _ =>
    countPart (fun i => ciT[i]!) (fun i => nxtT[i]!) (fun i => s3T[i]!) (fun i => s4T[i]!)
      (List.range jl.length) (jl.idxOf (idcF k)) (k - 1) rs bad badR keepN keepS keepJ jl.length
      fuel (fuel - ds) nt (pa + i)
  ts.foldl (fun acc t => (acc.1 + t.get.1, acc.2 + t.get.2)) (0, 0)

def seqCount (k : Nat) (caps : List (List Nat)) (s lo hi fuel ds nt pa pb : Nat) : Nat × Nat :=
  let B := capF caps s hi + 2
  let tb := tab3 (s + 1) B (hi + 1) (seqBad caps s lo hi)
  let tn := tab3 (s + 1) B (hi + 1) (seqKeepN caps s lo hi)
  let tS := tab3 (s + 1) B (hi + 1) (seqKeepS caps s lo hi)
  countB k false (look3 (s + 1) B (hi + 1) tb (seqBad caps s lo hi)) noRule
    (look3 (s + 1) B (hi + 1) tn (seqKeepN caps s lo hi))
    (look3 (s + 1) B (hi + 1) tS (seqKeepS caps s lo hi)) noRule fuel ds nt pa pb

def ringCount (k : Nat) (M PR : List Nat) (G fuel ds nt pa pb : Nat) : Nat × Nat :=
  let B := M.getD G 0 + 2
  let tb := tab3 1 B (G + 1) (ringBad PR G)
  let tn := tab3 1 B (G + 1) (ringKeep M PR G)
  countB k false noRule (look3 1 B (G + 1) tb (ringBad PR G))
    (look3 1 B (G + 1) tn (ringKeep M PR G)) noRule noRule fuel ds nt pa pb

def profCount (k : Nat) (M : List Nat) (ts : List (Nat × Nat)) (fuel ds nt pa pb : Nat) :
    Nat × Nat :=
  let B := (ts.map Prod.fst).foldl max 0 + 2
  let C := (ts.map Prod.snd).foldl max 0 + 2
  let tb := tab3 ts.length B C (profBad ts)
  let tn := tab3 ts.length B C (profKeepN M ts)
  let tj := tab3 ts.length B C (profKeepJ ts)
  countB k true (look3 ts.length B C tb (profBad ts)) noRule
    (look3 ts.length B C tn (profKeepN M ts)) noRule
    (look3 ts.length B C tj (profKeepJ ts)) fuel ds nt pa pb

end PS
end SuperpermLowerBounds
