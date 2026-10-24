import LowerBounds.KSearch

/-!
# The kernel-alone search of 5,901: the search of 5,900 with Rule JS (the written proof, section 3.3)

The engine is `KS.go` of `KSearch.lean` with one more argument `js`.  With `js = true` a row that begins
at a word `D` behind the last entry `q` of the row before it is placed with one block only if `D` lies in
the class of the next block of `q` (the word `nxt q`): that is, if `D` is `j3(q)` behind a link of weight
3 or `j4(q)` behind a link of weight 4 (Lemma JS1; `K16Word.lean` proves what is used).  In the engine
this is the mask `jsM`: only its bit `0` (the row with one block) is kept.  With `js = false` the search
is that of 5,900.

The rule tables (`KS.codeF`, `KS.cutF`, ...), the tables (`KS.tabA`, ...) and the cutting into parts are
those of `KSearch.lean`, unchanged.  This file imports `KSearch.lean` only.
-/

namespace SuperpermLowerBounds
namespace K16

open PS (walk all marks0 capF)
open KS (walkG)

/-- The mask of the rows that begin at `D` behind a row whose next block lies in the class `cq`: with
Rule JS on, a row that begins in that class has one block. -/
@[inline] def jsM (js : Bool) (ci : Nat → Nat) (cq D mk : Nat) : Nat :=
  if js && ci D == cq then mk % 2 else mk

/-- The search below a sequence (as `KS.go`), with Rule JS if `js`. -/
@[specialize] def go (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (kb : Nat)
    (code mask : Nat → Nat → Nat → Nat) (fN fS : Nat → Nat → Nat → Int)
    (cut : Nat → Nat → Nat → Int → Int → Bool) (js : Bool) (fg nt tp : Nat) :
    Nat → Nat → Nat → Nat → Int → Int → Nat → ByteArray → ByteArray
  | 0, _, _, _, _, _, _, _ => ByteArray.empty
  | fuel + 1, t, r, d, m, M, q, B =>
    let c := code t r d
    if c == 0 then B
    else if c == 1 then ByteArray.empty
    else if fuel != fg || (q + 8192 * d) % nt == tp then
      let cq := ci (nxt q)
      let B1 :=
        if c != 3 then
          let f := fN t r d
          let mN := min m f
          let MN := max M f
          if cut t r d mN MN then
            let mk := mask t (r + 1) d
            all (fun D B' => walkG ci nxt
              (fun n e B'' => go ci nxt s3 s4 kb code mask fN fS cut js fg nt tp fuel
                t (r + 1) (d + n) mN MN e B'') kb (jsM js ci cq D mk) D B') (s3 q) B
          else B
        else B
      if B1.size == 0 then B1
      else if c != 2 then
        let g := fS t r d
        let mS := min m g
        let MS := max M g
        if cut t r d mS MS then
          let mk := mask (t + 1) (r + 1) d
          all (fun D B' => walkG ci nxt
            (fun n e B'' => go ci nxt s3 s4 kb code mask fN fS cut js fg nt tp fuel
              (t + 1) (r + 1) (d + n) mS MS e B'') kb (jsM js ci cq D mk) D B') (s4 q) B1
        else B1
      else B1
    else B

/-- Part `tp` of `nt` of the search.  `false`: none of the visited sequences is found. -/
@[specialize] def searchPart (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (st kb : Nat)
    (code mask : Nat → Nat → Nat → Nat) (fN fS : Nat → Nat → Nat → Int)
    (cut : Nat → Nat → Nat → Int → Int → Bool) (js : Bool) (sz fuel fg nt tp : Nat) : Bool :=
  (walk ci nxt
    (fun n e B => go ci nxt s3 s4 kb code mask fN fS cut js fg nt tp fuel 0 1 n 0 0 e B)
    kb st (marks0 sz)).size == 0

/-- A part of F(s; lo - 1, hi) with the potential `(a, b, h)` and Rule JS if `js`, with words as
codes (for the kernel). -/
def seqPartA (k : Nat) (caps : List (List Nat)) (s lo hi a b h : Nat) (js : Bool)
    (fuel ds nt tp : Nat) : Bool :=
  searchPart (PS.cidxF k (4 * (k - 1)) (16 ^ (k - 1) - 1)) (PS.nxtF (4 * (k - 1)) (16 ^ (k - 1) - 1))
    (PS.sdA k 3 (PS.permCodes k k)) (PS.sdA k 4 (PS.permCodes k k)) (PS.idcF k) (k - 1)
    (KS.codeF (capF caps) s lo hi)
    (fun t r d => KS.maskG (KS.codeF (capF caps) s lo hi) t r d (k - 1))
    (KS.potN a b h) (KS.potS a b h)
    (KS.cutF (KS.a1F (capF caps) s lo hi a b h)
      (KS.a2F (KS.uF (capF caps) s a b h) (KS.segF (capF caps) s a b h) (capF caps) s lo hi a b h))
    js (k ^ (k - 1)) fuel (fuel - ds) nt tp

/-- F(s; lo - 1, hi) with words as codes (for the kernel). -/
def seqSearchA (k : Nat) (caps : List (List Nat)) (s lo hi a b h : Nat) (js : Bool)
    (fuel ds nt pa pb : Nat) : Bool :=
  KS.par (seqPartA k caps s lo hi a b h js fuel ds nt) pa pb

/-- F(s; lo - 1, hi) with the potential `(a, b, h)` and Rule JS if `js`, compiled (the tables of
`KS.seqSearch`). -/
def seqSearch (k : Nat) (caps : List (List Nat)) (s lo hi a b h : Nat) (js : Bool)
    (fuel ds nt pa pb : Nat) : Bool :=
  let A := s + 1
  let C := hi + 1
  let tP := KS.tab2 A C (capF caps)
  let P := KS.look2 A C tP (capF caps)
  let R := KS.maxLeN (P s) hi + 1
  let tc := KS.tabA A (R + 1) C (KS.codeF P s lo hi)
  let tm := KS.tabA A (R + 1) C (fun t r d => KS.maskG (KS.codeT A R C tc) t r d (k - 1))
  let tu := KS.tab2 A C (KS.uF P s a b h)
  let tg := KS.tab2 A C (KS.segF P s a b h)
  let t1 := KS.tabA A (R + 1) C (KS.a1F P s lo hi a b h)
  let t2 := KS.tabA A (R + 1) C
    (KS.a2F (KS.look2 A C tu (KS.uF P s a b h)) (KS.look2 A C tg (KS.segF P s a b h)) P s lo hi a b h)
  let full := KS.maskG (fun _ _ _ => 1) 0 0 0 (k - 1)
  let jl := PS.permCodes k k
  let ciT := PS.ciTab k jl
  let nxtT := PS.nxtTab k jl
  let s3T := PS.sdTab k 3 jl
  let s4T := PS.sdTab k 4 jl
  KS.par (fun tp => searchPart (fun i => ciT[i]!) (fun i => nxtT[i]!) (fun i => s3T[i]!)
    (fun i => s4T[i]!) (jl.idxOf (PS.idcF k)) (k - 1) (KS.codeT A R C tc)
    (KS.maskT A (R + 1) C full tm) (KS.potN a b h) (KS.potS a b h) (KS.cutT A (R + 1) C t1 t2) js
    jl.length fuel (fuel - ds) nt tp) pa pb

end K16
end SuperpermLowerBounds
