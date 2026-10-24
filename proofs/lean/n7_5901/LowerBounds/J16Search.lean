import LowerBounds.J15Search

/-!
# The search for the joint statements of 5,901 (the written proof, section 4)

The engine of 5,900 (`J15Search.lean`, section 5.4 of the proof of 5,900) with three additions, as
hooks that the search calls at every step:

* `xr c i t r d a b pm pM`: a prefix of piece `i` (counters `t`, `r`, `d`, needed value `a`, weight
  `b`) is continued with a link of weight 3 (`c = 0`) or 4 (`c = 1`) only if this is `true`;
* `xc i t r d a b pm pM`: the prefix is taken as the whole piece `i` only if this is `true`;
* the engine carries the least and the largest value `pm`, `pM` of `phi c t r d` over the cuts of
  the piece so far (`c` the kind of the link behind the cut; the cut before the first row has
  value 0).

The hooks of the runs (`xrF`, `xcF` below) are the rules of section 4: Rule PREV on one sequence
piece (section 4.3, with the potential `phi` of Lemma REV), Rule ORD on one pair of neighbouring
pieces of equal kind (section 4.4), and the class of the ring pieces (section 4.1: the value of a
ring lies in a range `vlo .. vhi`; this is the cut at negative need `RNN` of section 4.2, the two
halves of the split VS of section 4.6).  The ring rule may in addition clip the needed value at 0
(section 4.2) and take only targets with `T - H ≥ vlo` (VS (hi)).

`J16Sound.lean` proves that the answer `false` of all parts means that the rule holds along no
list of pieces; `J16Rules.lean` proves that a suitable counterexample with the fewest rows is
such a list.
-/

namespace SuperpermLowerBounds
namespace J16

open PS (all marks0 capF)
open KS (tabA tab2 look2 maxLe maxLeN par minLe)
open J15 (mkMask walkJ scanJ walkG vOf compOk k3Ok k4Ok live negInf sval pval bestF bestStep
  tmax kdF loF hiF gateD earlyD digs gprod bestT gT fT)

/-! ### The engine -/

/-- The search below a prefix of piece `i`.  A table of size zero stands for "found". -/
@[specialize] def go (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (jl : List Nat)
    (kb np bm : Nat) (kd lo hi : Nat → Nat) (bestLe : Nat → Nat → Int → Bool)
    (gLe : Nat → Nat → Nat → Int → Bool) (fLe : Nat → Nat → Nat → Nat → Int → Bool)
    (gate early : Nat → Nat → Nat → Bool)
    (xr : Nat → Nat → Nat → Nat → Nat → Int → Nat → Int → Int → Bool)
    (xc : Nat → Nat → Nat → Nat → Int → Nat → Int → Int → Bool)
    (phi : Nat → Nat → Nat → Nat → Int) :
    Nat → Nat → Nat → Nat → Nat → Int → Nat → Int → Int → Int → Nat → Nat → Nat → ByteArray →
      ByteArray
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _ => ByteArray.empty
  | fuel + 1, i, t, r, d, a, b, m, pm, pM, z, q, du, M =>
    if gate i r (q + 8192 * d) then
      let c := kd i
      let wt := d + kb * t
      let y := b - wt
      let v := vOf kb t r d
      -- the prefix as the whole piece
      let M1 :=
        if compOk np bestLe (fun i' r' => early i' r' (q + 8192 * d)) i r a y v &&
            (if c == 0 then
              decide (2 ≤ r) && decide (lo i ≤ d) && decide (d ≤ hi i) && (s3 q).contains z
            else decide (m < v)) && xc i t r d a b pm pM then
          if i + 1 == np then ByteArray.empty
          else
            let mk := mkMask (fun n => decide (n ≤ y) &&
              live kb np kd bestLe gLe fLe (fun _ _ => true) (i + 1) 0 1 n (a - v) y (-(kb : Int))) kb
            all (fun D M' => walkG ci nxt
              (fun n e du' M'' =>
                go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early xr xc phi fuel
                  (i + 1) 0 1 n (a - v) y (-(kb : Int)) 0 0 D e du' M'')
              (UInt8.ofNat (i + 2)) bm kb mk du D M') jl M
        else M
      if M1.size == 0 then M1
      else
        let m' := max m v
        let M2 :=
          if k3Ok gLe fLe i c t r d a b y v && xr 0 i t r d a b pm pM then
            let mk := mkMask (fun n => decide (wt + n ≤ b) &&
              live kb np kd bestLe gLe fLe (fun _ _ => true) i t (r + 1) (d + n) a b m') kb
            all (fun D M' => walkG ci nxt
              (fun n e du' M'' =>
                go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early xr xc phi fuel
                  i t (r + 1) (d + n) a b m' (min pm (phi 0 t r d)) (max pM (phi 0 t r d)) z e
                  du' M'')
              (UInt8.ofNat (i + 1)) bm kb mk du D M') (s3 q) M1
          else M1
        if M2.size == 0 then M2
        else if k4Ok gLe kb i c t a y v && xr 1 i t r d a b pm pM then
          let mk := mkMask (fun n => decide (wt + kb + n ≤ b) &&
            live kb np kd bestLe gLe fLe (fun _ _ => true) i (t + 1) (r + 1) (d + n) a b m') kb
          all (fun D M' => walkG ci nxt
            (fun n e du' M'' =>
              go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early xr xc phi fuel
                i (t + 1) (r + 1) (d + n) a b m' (min pm (phi 1 t r d)) (max pM (phi 1 t r d)) z e
                du' M'')
            (UInt8.ofNat (i + 1)) bm kb mk du D M') (s4 q) M2
        else M2
    else M

/-- A part of the search for J(…; V, W; bm), given by the two tests of its gates.  `false`: no
object is found (and the fuel was enough to see that). -/
@[specialize] def searchPart (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (jl : List Nat)
    (st kb np bm : Nat) (kd lo hi : Nat → Nat) (bestLe : Nat → Nat → Int → Bool)
    (gLe : Nat → Nat → Nat → Int → Bool) (fLe : Nat → Nat → Nat → Nat → Int → Bool)
    (xr : Nat → Nat → Nat → Nat → Nat → Int → Nat → Int → Int → Bool)
    (xc : Nat → Nat → Nat → Nat → Int → Nat → Int → Int → Bool)
    (phi : Nat → Nat → Nat → Nat → Int)
    (V : Int) (W sz fuel : Nat) (gate early : Nat → Nat → Nat → Bool) : Bool :=
  (walkG ci nxt
    (fun n e du M =>
      go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early xr xc phi fuel 0 0 1 n V W
        (-(kb : Int)) 0 0 st e du M)
    (UInt8.ofNat 1) bm kb
    (mkMask (fun n => decide (n ≤ W) &&
      live kb np kd bestLe gLe fLe (fun _ _ => true) 0 0 1 n V W (-(kb : Int))) kb)
    0 st (marks0 sz)).size == 0

/-! ### The rules of the runs

The potential of Lemma REV with the numbers `pa`, `pb`, `ph` (section 4.3): at a cut behind `r`
rows with `d` holes and `t` links of weight 4, followed by a link of kind `c`,
`phi = pa r - pb d - 2 ph t - ph c`. -/

/-- The potential at a cut. -/
def potF (pa pb ph : Nat) (c t r d : Nat) : Int :=
  (pa : Int) * r - (pb : Int) * d - 2 * (ph : Int) * t - (ph : Int) * c

/-- `SEG(tl, w)`: the largest `pa D_u(e) - pb e - 2 ph u` with `u ≤ tl`, `e + c6 u ≤ w`. -/
def segF (P : Nat → Nat → Nat) (c6 pa pb ph : Nat) (tl w : Nat) : Int :=
  maxLe (fun u => maxLe (fun e =>
    if e + c6 * u ≤ w then (pa : Int) * (P u e : Nat) - (pb : Int) * e - 2 * (ph : Int) * u
    else negInf) w) tl

/-- `c(need, om; w) = pa (need - Best(om - w)) - (pb - pa) w`, with `Best = nx`. -/
def cF (nx : Nat → Int) (pa pb : Nat) (need : Int) (om w : Nat) : Int :=
  (pa : Int) * (need - nx (om - w)) - ((pb : Int) - pa) * w

/-- The least of `f w` for `w ≤ n`. -/
def minUp (f : Nat → Int) (n : Nat) : Int := minLe (fun _ => true) f 1000000000 n

/-- `CN1(need, om)`. -/
def cn1F (nx : Nat → Int) (pa pb : Nat) (need : Int) (om : Nat) : Int :=
  minUp (fun w => cF nx pa pb need om w) om

/-- `A2P(tl, need, om)`. -/
def a2pF (seg : Nat → Nat → Int) (nx : Nat → Int) (pa pb : Nat) (tl : Nat) (need : Int)
    (om : Nat) : Int :=
  minUp (fun w => cF nx pa pb need om w - seg tl w) om

/-- Rule PREV at a cut of the piece, followed by a link of kind `c` (rules (L) and (H) of section
4.3): `f` the potential `potF 0` of the prefix, `pm`, `pM` the extremes over the earlier cuts,
`tl` the links that the piece may still take, `need`, `om` the value needed and the weight left
for the rest of the piece and the later pieces. -/
def prevOk (seg : Nat → Nat → Int) (nx : Nat → Int) (c6 pa pb ph : Nat) (c : Nat) (f pm pM : Int)
    (tl : Nat) (need : Int) (om : Nat) : Bool :=
  if c = 0 then
    decide (0 ≤ min pm f) || decide (cn1F nx pa pb need om ≤ max pM f + min pm f - f) ||
      decide (a2pF seg nx pa pb tl need om ≤ min pm f)
  else
    decide (0 ≤ min pm (f - ph)) ||
      decide (cn1F nx pa pb (need + ((c6 - 1 : Nat) : Int)) (om - c6) - 2 * (ph : Int) ≤
        max pM (f - ph) + min pm (f - ph) - f) ||
      decide (a2pF seg nx pa pb (tl - 1) (need + ((c6 - 1 : Nat) : Int)) (om - c6) ≤
        min pm (f - ph))

/-- Rule (T1) of section 4.3: the complete piece has `m + M - phi_T ≥ 0`. -/
def prevEnd (f pm pM : Int) : Bool := decide (0 ≤ min pm f + max pM f - f)

/-- The parameters of a run that are not those of the engine of 5,900. -/
structure Rules where
  /-- the value range of the ring piece `i` (`(vlo, vhi)`; ignored for sequence pieces) -/
  vcl : List (Int × Int)
  /-- the ring rule clips the value needed at 0 (section 4.2) -/
  clip : Bool
  /-- the piece of Rule PREV (none if it is not a sequence piece of the run) -/
  rp : Nat
  /-- the potential of Rule PREV -/
  pa : Nat
  pb : Nat
  ph : Nat
  /-- Rule ORD on the pieces `oi`, `oi + 1` (none if `oi + 1` is not a piece) -/
  oi : Nat

/-- The value range of ring piece `i`. -/
def vloF (R : Rules) (i : Nat) : Int := (R.vcl.getD i (negInf, 1000000000)).1
def vhiF (R : Rules) (i : Nat) : Int := (R.vcl.getD i (negInf, 1000000000)).2

/-- Rule PREV is on at piece `i`. -/
def prevOn (R : Rules) (kd : Nat → Nat) (i : Nat) : Bool := i == R.rp && kd i != 0

/-- Rule ORD is on at piece `i` (the pair `i`, `i + 1`). -/
def ordOn (R : Rules) (np : Nat) (i : Nat) : Bool := i == R.oi && decide (i + 1 < np)

/-- The hook at a continuation (kind `c` of the link): Rule PREV and the prefix rule of ORD.
`B i y` is `Best` of the pieces after `i`, `RB u y` the table bound of a rest of a sequence piece
with at most `u` links alone, `seg` the table `SEG` of the run. -/
def xrF (R : Rules) (kb np : Nat) (kd : Nat → Nat) (B : Nat → Nat → Int) (RB : Nat → Nat → Int)
    (seg : Nat → Nat → Int) (c i t r d : Nat) (a : Int) (b : Nat) (pm pM : Int) : Bool :=
  (!prevOn R kd i ||
    prevOk seg (B i) kb R.pa R.pb R.ph c (potF R.pa R.pb R.ph 0 t r d) pm pM (kd i - 1 - t)
      (a - vOf kb t r d) (b - (d + kb * t))) &&
  (!ordOn R np i ||
    (if c = 0 then
      decide (a ≤ 2 * (vOf kb t r d + RB (kd i - 1 - t) (b - (d + kb * t))) + B (i + 1) b)
    else
      decide (a ≤ 2 * (vOf kb t r d - ((kb - 1 : Nat) : Int) +
        RB (kd i - 2 - t) (b - (d + kb * t) - kb)) + B (i + 1) b)))

/-- The hook at a complete piece: the class of a ring, Rule (T1) of PREV, the jump rule of ORD. -/
def xcF (R : Rules) (kb np : Nat) (kd : Nat → Nat) (B : Nat → Nat → Int) (i t r d : Nat) (a : Int)
    (b : Nat) (pm pM : Int) : Bool :=
  (kd i != 0 || (decide (vloF R i ≤ (r : Int) - d) && decide ((r : Int) - d ≤ vhiF R i))) &&
  (!prevOn R kd i || prevEnd (potF R.pa R.pb R.ph 0 t r d) pm pM) &&
  (!ordOn R np i || decide (a ≤ 2 * vOf kb t r d + B (i + 1) (b - (d + kb * t))))

/-- The targets of a ring prefix (step 5 of the proof of 5,900), only targets `(T, H)` with
`T - H ≥ amin` (VS (hi), section 4.6). -/
def fG (P : Nat → Nat → Nat) (PR : Nat → Nat) (nx : Nat → Int) (lo hi : Nat) (amin : Int)
    (b r d : Nat) : Int :=
  maxLe (fun H =>
    if lo ≤ H ∧ H ≤ hi ∧ d ≤ H ∧ r + 1 ≤ tmax P PR r d H ∧
        amin ≤ ((tmax P PR r d H : Nat) : Int) - (H : Int) then
      ((tmax P PR r d H : Nat) : Int) - (H : Int) + nx (b - H)
    else negInf) b

/-- The ring test with the value needed `x`, clipped at 0 if the run says so. -/
@[inline] def ringOk (clip : Bool) (F x : Int) : Bool :=
  decide (x ≤ F) && (!clip || decide (0 ≤ F))

/-! ### The searches -/

/-- A part of a run with words as codes and the rule evaluated (for the kernel). -/
def jPartA (k : Nat) (caps : List (List Nat)) (PRl : List Nat) (specs : List (Nat × Nat × Nat))
    (R : Rules) (V W bm fuel : Nat) (gs : List (Nat × Nat × Nat)) (tp : Nat) : Bool :=
  let P := capF caps
  let PR := fun x => PRl.getD x 0
  let B := fun i y => bestF P PR (k - 1) (specs.drop (i + 1)) y
  searchPart (PS.cidxF k (4 * (k - 1)) (16 ^ (k - 1) - 1)) (PS.nxtF (4 * (k - 1)) (16 ^ (k - 1) - 1))
    (PS.sdA k 3 (PS.permCodes k k)) (PS.sdA k 4 (PS.permCodes k k)) (PS.permCodes k k) (PS.idcF k)
    (k - 1) specs.length bm (kdF specs) (loF specs) (hiF specs)
    (fun i y x => decide (x ≤ B i y))
    (fun i u y x => decide (x ≤ bestStep P PR (k - 1) (u + 1, 0, 0) (B i) y))
    (fun i b r d x => ringOk R.clip (fG P PR (B i) (loF specs i) (hiF specs i) (vloF R i) b r d) x)
    (xrF R (k - 1) specs.length (kdF specs) B (fun u y => bestF P PR (k - 1) [(u + 1, 0, 0)] y)
      (segF P (k - 1) R.pa R.pb R.ph))
    (xcF R (k - 1) specs.length (kdF specs) B)
    (fun c t r d => potF R.pa R.pb R.ph c t r d)
    (V : Int) W (k ^ (k - 1)) fuel (gateD (digs gs tp)) (earlyD (digs gs tp))

/-- A run with words as codes (for the kernel). -/
def jSearchA (k : Nat) (caps : List (List Nat)) (PRl : List Nat) (specs : List (Nat × Nat × Nat))
    (R : Rules) (V W bm fuel : Nat) (gs : List (Nat × Nat × Nat)) (pa pb : Nat) : Bool :=
  par (jPartA k caps PRl specs R V W bm fuel gs) pa pb

/-- A run, compiled: words are indices into the list of permutation codes and the rule is read
from tables (`Best`, the rest of a sequence piece with the later pieces, the rest alone, the ring
targets, `SEG`).  All tables are built once, before the parts start; the parts are `pa ≤ tp < pb`
of the `gprod gs` parts of the gates `gs`. -/
def jSearch (k : Nat) (caps : List (List Nat)) (PRl : List Nat) (specs : List (Nat × Nat × Nat))
    (R : Rules) (V W bm fuel : Nat) (gs : List (Nat × Nat × Nat)) (pa pb : Nat) : Bool :=
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
  par (fun tp => searchPart (fun i => ciT[i]!) (fun i => nxtT[i]!) (fun i => s3T[i]!)
    (fun i => s4T[i]!) (List.range jl.length) (jl.idxOf (PS.idcF k)) (k - 1) np bm
    (fun i => kdA[i]!) (fun i => loA[i]!) (fun i => hiA[i]!) (bestT np C tB) (gT np S C tG)
    (fun i b r d x => if i < np && b < C && r < RR && d < C then
        ringOk R.clip tF[((i * C + b) * RR + r) * C + d]! x else true)
    (xrF R (k - 1) np (fun i => kdA[i]!) B RB SG)
    (xcF R (k - 1) np (fun i => kdA[i]!) B)
    (fun c t r d => potF R.pa R.pb R.ph c t r d)
    (V : Int) W jl.length fuel (gateD (digs gs tp)) (earlyD (digs gs tp))) pa pb

end J16
end SuperpermLowerBounds
