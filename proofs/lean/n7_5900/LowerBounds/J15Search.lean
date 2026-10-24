import LowerBounds.KSearch

/-!
# The search for the joint statements of 5,900 (the written proof, section 5.4)

The statement J(p_1 … p_n; V, W; B): there are no pieces `p_1, …, p_n` of the given kinds (a
sequence with at most `s` links of weight 4, or a ring) with total value at least `V`, total
weight at most `W` and at most `B` shared classes.  The search is depth-first over the pieces in
order.  Piece 1 starts at the word `1 2 … k`, every later piece at every word.  A piece has
pairwise different classes; a block of a piece may lie in a class of an earlier piece while the
number of such blocks stays at most `B`.

A piece is described by three numbers `(c, lo, hi)`: `c = 0` is a ring whose number of holes lies
in the window `lo … hi`, and `c = s + 1` is a sequence with at most `s` links of weight 4.

The engine `go` carries, for the piece `i` that is being built: the counters `t` (links of
weight 4), `r` (rows), `d` (holes), the value `a` that the pieces from `i` on still need, the
weight `b` that is left for them, the largest value `m` of a shorter prefix of the piece, the
first entry `z` and the last entry `q` of the piece, and the number `du` of shared blocks so far.
With `kb = k - 1`, the value of the prefix is `v = r - d - (kb - 1) t` and its weight is
`d + kb t`.  The engine is given

* `kd`, `lo`, `hi`: the three numbers of piece `i`;
* `bestLe i y x`: `x` is at most the largest total of table values of the pieces after `i` within
  weight `y`;
* `gLe i u y x`: the same for a rest of the sequence piece `i` with at most `u` links followed by
  the pieces after `i`;
* `fLe i b r d x`: the same for a ring piece `i` that continues a prefix with `r` rows and `d`
  holes, followed by the pieces after `i`, within weight `b` (the target of step 5).

A mark in the table of bytes is the number of the last piece (counted from 1) that has a block in
the class, so that no mark is cleared when a new piece starts.

To cut a search into parts, gates are put into the tree.  A gate `(gi, gr, n)` stands at the
prefixes with `gr` rows of piece `gi`: such a prefix is continued only if
`(last entry + 8192 · holes) mod n` (its key) is the digit of the part at this gate, and a piece
`gi` that is complete with fewer than `gr` rows is followed only if the key of its end is that
digit.  With the gates
`g_1, …, g_m` there are `n_1 ⋯ n_m` parts, and the digits of part `tp` are its digits in the
mixed radix `n_1, n_2, …` (`tp mod n_1` first).  The engine is given the two tests as functions:
`gate i r key` (the prefix with `r` rows of piece `i` and the key `key` is continued) and
`early i r key` (a piece `i` that is complete with `r` rows and the key `key` is followed).

`J15Sound.lean` proves that the answer `false` of all parts means that the rule holds along no
list of pieces; `J15Rules.lean` proves that a counterexample with the fewest rows is such a list.

This file imports `KSearch.lean` only; it is compiled to C and loaded by the files that evaluate
the search.
-/

namespace SuperpermLowerBounds
namespace J15

open PS (all marks0 capF)
open KS (tabA tab2 look2 maxLe maxLeN par)

/-! ### The engine -/

/-- The mask of the rows that are visited: bit `j` of `mkMask p n` is `p (n - 1 - j)`.  With `n`
the largest number of blocks of a row, bit `j` belongs to the row with `j + 1` blocks, which has
`n - 1 - j` holes. -/
@[specialize] def mkMask (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 * mkMask p n + (if p n then 1 else 0)

/-- The rows that begin with the block of entry `D`, for the piece with mark `pm`.  A block whose
class has the mark `pm` ends the walk (the class is in the piece); a block whose class has
another mark is a shared block and is allowed while `du < bm`.  Bit `j` of `mk` says whether the
row with `j + 1` blocks is visited; when no bit is left the walk stops.  `visit n e du M` is the
search below the piece extended by the row with `n` holes that ends with the block of entry
`e`. -/
@[specialize] def walkJ (ci nxt : Nat → Nat) (visit : Nat → Nat → Nat → ByteArray → ByteArray)
    (pm : UInt8) (bm : Nat) : Nat → Nat → Nat → Nat → ByteArray → ByteArray
  | 0, _, _, _, M => M
  | n + 1, mk, du, D, M =>
    if mk == 0 then M
    else
      let o := M.get! (ci D)
      if o == pm then M
      else if o != 0 && decide (bm ≤ du) then M
      else
        let du' := if o != 0 then du + 1 else du
        let M1 := if mk % 2 == 1 then visit n D du' (M.set! (ci D) pm) else M.set! (ci D) pm
        if M1.size == 0 then M1
        else (walkJ ci nxt visit pm bm n (mk / 2) du' (nxt D) M1).set! (ci D) o

/-- Does the walk with the mask `mk` that begins at the entry `D` visit a row?  It does if the
blocks up to a block whose bit is set are all allowed.  (This reads the marks only.) -/
@[specialize] def scanJ (ci nxt : Nat → Nat) (M : ByteArray) (pm : UInt8) (bm : Nat) :
    Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => false
  | n + 1, mk, du, D =>
    if mk == 0 then false
    else
      let o := M.get! (ci D)
      if o == pm then false
      else if o != 0 && decide (bm ≤ du) then false
      else if mk % 2 == 1 then true
      else scanJ ci nxt M pm bm n (mk / 2) (if o != 0 then du + 1 else du) (nxt D)

/-- The walk, entered only if it visits a row. -/
@[inline] def walkG (ci nxt : Nat → Nat) (visit : Nat → Nat → Nat → ByteArray → ByteArray)
    (pm : UInt8) (bm n mk du D : Nat) (M : ByteArray) : ByteArray :=
  if scanJ ci nxt M pm bm n mk du D then walkJ ci nxt visit pm bm n mk du D M else M

/-- The value of a prefix with `t` links, `r` rows and `d` holes. -/
@[inline] def vOf (kb t r d : Nat) : Int := (r : Int) - (d : Int) - (((kb - 1) * t : Nat) : Int)

/-- The prefix with value `v` may be the whole piece `i`, as far as the values go: it is the last
piece and has the value `a`, or the later pieces can bring the rest within the weight `y` (and
the test `early` of the gates lets a piece that is complete with `r` rows pass). -/
@[inline] def compOk (np : Nat) (bestLe : Nat → Nat → Int → Bool) (early : Nat → Nat → Bool)
    (i r : Nat) (a : Int) (y : Nat) (v : Int) : Bool :=
  if i + 1 == np then decide (a ≤ v)
  else bestLe i y (a - v) && early i r

/-- The prefix is continued with links of weight 3. -/
@[inline] def k3Ok (gLe : Nat → Nat → Nat → Int → Bool) (fLe : Nat → Nat → Nat → Nat → Int → Bool)
    (i c t r d : Nat) (a : Int) (b y : Nat) (v : Int) : Bool :=
  if c == 0 then fLe i b r d a else decide (1 ≤ v) && gLe i (c - 1 - t) y (a - v)

/-- The prefix is continued with links of weight 4. -/
@[inline] def k4Ok (gLe : Nat → Nat → Nat → Int → Bool) (kb i c t : Nat) (a : Int) (y : Nat)
    (v : Int) : Bool :=
  decide (t + 1 < c) && decide ((kb : Int) ≤ v) && decide (kb ≤ y) &&
    gLe i (c - 2 - t) (y - kb) (a - v + (((kb - 1 : Nat)) : Int))

/-- Something is done at the prefix: it may be the whole piece or it is continued.  (The search
is entered only at such prefixes.  It asks this with `early` always `true`: the gates are not
looked at before a row is walked.) -/
@[inline] def live (kb np : Nat) (kd : Nat → Nat) (bestLe : Nat → Nat → Int → Bool)
    (gLe : Nat → Nat → Nat → Int → Bool) (fLe : Nat → Nat → Nat → Nat → Int → Bool)
    (early : Nat → Nat → Bool) (i t r d : Nat) (a : Int) (b : Nat) (m : Int) : Bool :=
  k3Ok gLe fLe i (kd i) t r d a b (b - (d + kb * t)) (vOf kb t r d) ||
    k4Ok gLe kb i (kd i) t a (b - (d + kb * t)) (vOf kb t r d) ||
    ((if kd i == 0 then decide (2 ≤ r) else decide (m < vOf kb t r d)) &&
      compOk np bestLe early i r a (b - (d + kb * t)) (vOf kb t r d))

/-- The search below a prefix of piece `i`.  A table of size zero stands for "found". -/
@[specialize] def go (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (jl : List Nat)
    (kb np bm : Nat) (kd lo hi : Nat → Nat) (bestLe : Nat → Nat → Int → Bool)
    (gLe : Nat → Nat → Nat → Int → Bool) (fLe : Nat → Nat → Nat → Nat → Int → Bool)
    (gate early : Nat → Nat → Nat → Bool) :
    Nat → Nat → Nat → Nat → Nat → Int → Nat → Int → Nat → Nat → Nat → ByteArray → ByteArray
  | 0, _, _, _, _, _, _, _, _, _, _, _ => ByteArray.empty
  | fuel + 1, i, t, r, d, a, b, m, z, q, du, M =>
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
            else decide (m < v)) then
          if i + 1 == np then ByteArray.empty
          else
            let mk := mkMask (fun n => decide (n ≤ y) &&
              live kb np kd bestLe gLe fLe (fun _ _ => true) (i + 1) 0 1 n (a - v) y (-(kb : Int))) kb
            all (fun D M' => walkG ci nxt
              (fun n e du' M'' =>
                go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early fuel
                  (i + 1) 0 1 n (a - v) y (-(kb : Int)) D e du' M'')
              (UInt8.ofNat (i + 2)) bm kb mk du D M') jl M
        else M
      if M1.size == 0 then M1
      else
        let m' := max m v
        let M2 :=
          if k3Ok gLe fLe i c t r d a b y v then
            let mk := mkMask (fun n => decide (wt + n ≤ b) &&
              live kb np kd bestLe gLe fLe (fun _ _ => true) i t (r + 1) (d + n) a b m') kb
            all (fun D M' => walkG ci nxt
              (fun n e du' M'' =>
                go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early fuel
                  i t (r + 1) (d + n) a b m' z e du' M'')
              (UInt8.ofNat (i + 1)) bm kb mk du D M') (s3 q) M1
          else M1
        if M2.size == 0 then M2
        else if k4Ok gLe kb i c t a y v then
          let mk := mkMask (fun n => decide (wt + kb + n ≤ b) &&
            live kb np kd bestLe gLe fLe (fun _ _ => true) i (t + 1) (r + 1) (d + n) a b m') kb
          all (fun D M' => walkG ci nxt
            (fun n e du' M'' =>
              go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early fuel
                i (t + 1) (r + 1) (d + n) a b m' z e du' M'')
            (UInt8.ofNat (i + 1)) bm kb mk du D M') (s4 q) M2
        else M2
    else M

/-- A part of the search for J(…; V, W; bm), given by the two tests of its gates.  `false`: no
object is found (and the fuel was enough to see that). -/
@[specialize] def searchPart (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (jl : List Nat)
    (st kb np bm : Nat) (kd lo hi : Nat → Nat) (bestLe : Nat → Nat → Int → Bool)
    (gLe : Nat → Nat → Nat → Int → Bool) (fLe : Nat → Nat → Nat → Nat → Int → Bool)
    (V : Int) (W sz fuel : Nat) (gate early : Nat → Nat → Nat → Bool) : Bool :=
  (walkG ci nxt
    (fun n e du M =>
      go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early fuel 0 0 1 n V W
        (-(kb : Int)) st e du M)
    (UInt8.ofNat 1) bm kb
    (mkMask (fun n => decide (n ≤ W) &&
      live kb np kd bestLe gLe fLe (fun _ _ => true) 0 0 1 n V W (-(kb : Int))) kb)
    0 st (marks0 sz)).size == 0

/-! ### The gates

A gate is `(gi, gr, n)`; with the digit `t` of a part it is `(gi, gr, n, t)`. -/

/-- The digits of part `tp` at the gates `gs` (mixed radix, the first gate is the lowest digit). -/
def digs : List (Nat × Nat × Nat) → Nat → List (Nat × Nat × Nat × Nat)
  | [], _ => []
  | g :: gs, tp => (g.1, g.2.1, g.2.2, tp % g.2.2) :: digs gs (tp / g.2.2)

/-- The number of parts. -/
def gprod : List (Nat × Nat × Nat) → Nat
  | [] => 1
  | g :: gs => g.2.2 * gprod gs

/-- The prefix with `r` rows of piece `i` and the key `key` passes all gates. -/
def gateD : List (Nat × Nat × Nat × Nat) → Nat → Nat → Nat → Bool
  | [], _, _, _ => true
  | g :: ds, i, r, key =>
    (i != g.1 || r != g.2.1 || key % g.2.2.1 == g.2.2.2) && gateD ds i r key

/-- A piece `i` that is complete with `r` rows and the key `key` is followed: at every gate of
piece `i` that it has not reached, the digit is its key. -/
def earlyD : List (Nat × Nat × Nat × Nat) → Nat → Nat → Nat → Bool
  | [], _, _, _ => true
  | g :: ds, i, r, key =>
    (i != g.1 || decide (g.2.1 ≤ r) || key % g.2.2.1 == g.2.2.2) && earlyD ds i r key

/-! ### The rule

`P u x` is the cap for sequences with `u` links of weight 4 and `x` holes, `PR x` the cap for
rings with `x` holes, `c6 = k - 1`. -/

/-- Below every value. -/
def negInf : Int := -1000000

/-- The table value of a sequence with `t` links and `e` holes. -/
def sval (P : Nat → Nat → Nat) (c6 t e : Nat) : Int :=
  ((P t e : Nat) : Int) - (e : Int) - (((c6 - 1) * t : Nat) : Int)

/-- The table value of a piece `p = (c, lo, hi)` at weight `w`. -/
def pval (P : Nat → Nat → Nat) (PR : Nat → Nat) (c6 : Nat) (p : Nat × Nat × Nat) (w : Nat) : Int :=
  if p.1 = 0 then (if p.2.1 ≤ w ∧ w ≤ p.2.2 then ((PR w : Nat) : Int) - (w : Int) else negInf)
  else maxLe (fun t => if c6 * t ≤ w then sval P c6 t (w - c6 * t) else negInf) (p.1 - 1)

/-- `Best`: the largest total of table values of pieces of the kinds `ps` within weight `b`. -/
def bestF (P : Nat → Nat → Nat) (PR : Nat → Nat) (c6 : Nat) : List (Nat × Nat × Nat) → Nat → Int
  | [], _ => 0
  | p :: ps, b => maxLe (fun w => pval P PR c6 p w + bestF P PR c6 ps (b - w)) b

/-- The same for one piece followed by pieces whose `Best` is `nx`. -/
def bestStep (P : Nat → Nat → Nat) (PR : Nat → Nat) (c6 : Nat) (p : Nat × Nat × Nat)
    (nx : Nat → Int) (b : Nat) : Int :=
  maxLe (fun w => pval P PR c6 p w + nx (b - w)) b

/-- The largest number of rows of a ring with `H` holes of which a prefix with `r` rows and `d`
holes is given: at most the ring cap, at most `r` plus the chain cap of the rest, and at most
`r H / d` (the cycle lemma). -/
def tmax (P : Nat → Nat → Nat) (PR : Nat → Nat) (r d H : Nat) : Nat :=
  if d = 0 then min (PR H) (r + P 0 (H - d))
  else min (min (PR H) (r + P 0 (H - d))) (r * H / d)

/-- The largest value of a target of step 5 for a prefix with `r` rows and `d` holes of a ring
with holes in `lo … hi`, plus `nx` of the weight that the ring leaves of `b`. -/
def fF (P : Nat → Nat → Nat) (PR : Nat → Nat) (nx : Nat → Int) (lo hi b r d : Nat) : Int :=
  maxLe (fun H =>
    if lo ≤ H ∧ H ≤ hi ∧ d ≤ H ∧ r + 1 ≤ tmax P PR r d H then
      ((tmax P PR r d H : Nat) : Int) - (H : Int) + nx (b - H)
    else negInf) b

/-- The three numbers of the pieces. -/
def kdF (specs : List (Nat × Nat × Nat)) (i : Nat) : Nat := (specs.getD i (0, 0, 0)).1
def loF (specs : List (Nat × Nat × Nat)) (i : Nat) : Nat := (specs.getD i (0, 0, 0)).2.1
def hiF (specs : List (Nat × Nat × Nat)) (i : Nat) : Nat := (specs.getD i (0, 0, 0)).2.2

/-! ### Tables -/

/-- `x ≤ T i y`, read from the table of `Best`; outside the table the answer is `true`. -/
@[inline] def bestT (A C : Nat) (T : Array Int) (i y : Nat) (x : Int) : Bool :=
  if i < A && y < C then decide (x ≤ T[i * C + y]!) else true

/-- `x ≤ T i u y`, read from the table for the rest of a sequence piece. -/
@[inline] def gT (A S C : Nat) (T : Array Int) (i u y : Nat) (x : Int) : Bool :=
  if i < A && u < S && y < C then decide (x ≤ T[(i * S + u) * C + y]!) else true

/-- `x ≤ T i b r d`, read from the table for ring pieces. -/
@[inline] def fT (A C R : Nat) (T : Array Int) (i b r d : Nat) (x : Int) : Bool :=
  if i < A && b < C && r < R && d < C then decide (x ≤ T[((i * C + b) * R + r) * C + d]!)
  else true

/-! ### The searches -/

/-- A part of J(specs; V, W; bm) with words as codes and the rule evaluated (for the kernel). -/
def jPartA (k : Nat) (caps : List (List Nat)) (PRl : List Nat) (specs : List (Nat × Nat × Nat))
    (V W bm fuel : Nat) (gs : List (Nat × Nat × Nat)) (tp : Nat) : Bool :=
  searchPart (PS.cidxF k (4 * (k - 1)) (16 ^ (k - 1) - 1)) (PS.nxtF (4 * (k - 1)) (16 ^ (k - 1) - 1))
    (PS.sdA k 3 (PS.permCodes k k)) (PS.sdA k 4 (PS.permCodes k k)) (PS.permCodes k k) (PS.idcF k)
    (k - 1) specs.length bm (kdF specs) (loF specs) (hiF specs)
    (fun i y x => decide (x ≤ bestF (capF caps) (fun x => PRl.getD x 0) (k - 1) (specs.drop (i + 1)) y))
    (fun i u y x => decide (x ≤ bestF (capF caps) (fun x => PRl.getD x 0) (k - 1)
      ((u + 1, 0, 0) :: specs.drop (i + 1)) y))
    (fun i b r d x => decide (x ≤ fF (capF caps) (fun x => PRl.getD x 0)
      (bestF (capF caps) (fun x => PRl.getD x 0) (k - 1) (specs.drop (i + 1)))
      (loF specs i) (hiF specs i) b r d))
    (V : Int) W (k ^ (k - 1)) fuel (gateD (digs gs tp)) (earlyD (digs gs tp))

/-- J(specs; V, W; bm) with words as codes (for the kernel). -/
def jSearchA (k : Nat) (caps : List (List Nat)) (PRl : List Nat) (specs : List (Nat × Nat × Nat))
    (V W bm fuel : Nat) (gs : List (Nat × Nat × Nat)) (pa pb : Nat) : Bool :=
  par (jPartA k caps PRl specs V W bm fuel gs) pa pb

/-- J(specs; V, W; bm), compiled: words are indices into the list of permutation codes and the
rule is read from tables.  All tables are built once, before the parts start; the parts are
`pa ≤ tp < pb` of the `gprod gs` parts of the gates `gs`. -/
def jSearch (k : Nat) (caps : List (List Nat)) (PRl : List Nat) (specs : List (Nat × Nat × Nat))
    (V W bm fuel : Nat) (gs : List (Nat × Nat × Nat)) (pa pb : Nat) : Bool :=
  let np := specs.length
  let S := maxLeN (kdF specs) np + 1
  let C := W + 1
  let tP := tab2 S C (capF caps)
  let P := look2 S C tP (capF caps)
  let tR := tab2 1 C (fun _ x => PRl.getD x 0)
  let PR := fun x => look2 1 C tR (fun _ x => PRl.getD x 0) 0 x
  let R := maxLeN PR W + 1
  let kdA := (specs.map fun p => p.1).toArray
  let loA := (specs.map fun p => p.2.1).toArray
  let hiA := (specs.map fun p => p.2.2).toArray
  let tB := tab2 np C (fun i y => bestF P PR (k - 1) (specs.drop (i + 1)) y)
  let B := look2 np C tB (fun i y => bestF P PR (k - 1) (specs.drop (i + 1)) y)
  let tG := tabA np S C (fun i u y => bestStep P PR (k - 1) (u + 1, 0, 0) (B i) y)
  let tF := tabA (np * C) R C (fun ib r d =>
    if kdA[ib / C]! == 0 then fF P PR (B (ib / C)) loA[ib / C]! hiA[ib / C]! (ib % C) r d else 0)
  let jl := PS.permCodes k k
  let ciT := PS.ciTab k jl
  let nxtT := PS.nxtTab k jl
  let s3T := PS.sdTab k 3 jl
  let s4T := PS.sdTab k 4 jl
  par (fun tp => searchPart (fun i => ciT[i]!) (fun i => nxtT[i]!) (fun i => s3T[i]!)
    (fun i => s4T[i]!) (List.range jl.length) (jl.idxOf (PS.idcF k)) (k - 1) np bm
    (fun i => kdA[i]!) (fun i => loA[i]!) (fun i => hiA[i]!) (bestT np C tB) (gT np S C tG)
    (fT np C R tF) (V : Int) W jl.length fuel (gateD (digs gs tp)) (earlyD (digs gs tp))) pa pb

end J15
end SuperpermLowerBounds
