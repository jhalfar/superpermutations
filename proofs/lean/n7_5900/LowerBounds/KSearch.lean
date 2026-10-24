import LowerBounds.PSearch

/-!
# The search for the kernel-alone statements of 5,900 (the written proof, section 4)

The statement F(s; lo - 1, hi): every sequence with exactly `s` links of weight 4 and `x` holes,
`lo ≤ x ≤ hi`, has at most `P_s(x)` rows.  The search is the depth-first search of `PSearch.lean`
over sequences of rows that start at the word `1 2 … k`, with two kinds of links (weight 3 and
weight 4) and with the rule of section 4.4: besides the counters `t` (links of weight 4), `r`
(rows) and `d` (holes) a sequence carries the least and the largest potential `m ≤ 0 ≤ M` of its
cuts, and it is continued only if the plain rule continues it and the reversal cut does not
remove it.

The engine `go` is given

* `code t r d`: `0` nothing to do, `1` found (a violation), `2` continue with links of weight 3,
  `3` with links of weight 4, `4` with both (the plain rule);
* `mask t r d`: bit `j` is set if the code of `t`, `r`, `d + (kb - 1 - j)` is not `0`, where `kb`
  is the largest number of blocks of a row: a row whose bit is not set is not visited, and a
  successor none of whose rows would be visited is skipped after a look at the marks;
* `fN t r d`, `fS t r d`: the potential of the cut behind the sequence if a link of weight 3, of
  weight 4 follows;
* `cut t r d m M`: the reversal cut allows the continuation, where `m` and `M` include the
  potential of the cut behind the sequence.

`KSound.lean` proves that the answer `false` of all parts means that there is no sequence along
which this rule holds; `KPot.lean` proves that a counterexample with the fewest rows, or its
reversal, is such a sequence.

A search is cut into `nt` parts at the sequences with a fixed number of rows: such a sequence is
continued in the part `(last entry + 8192 · holes) mod nt` only.

This file imports `PSearch.lean` only; it is compiled to C and loaded by the files that evaluate
the search.
-/

namespace SuperpermLowerBounds
namespace KS

open PS (walk all marks0 capF)

/-! ### The engine -/

/-- The rows that begin with the block of entry `D`, as `PS.walk`, with a mask: bit `j` of `mk`
says whether the row with `j + 1` blocks is visited.  When no bit is left the walk stops. -/
@[specialize] def walkM (ci nxt : Nat → Nat) (visit : Nat → Nat → ByteArray → ByteArray) :
    Nat → Nat → Nat → ByteArray → ByteArray
  | 0, _, _, B => B
  | n + 1, mk, D, B =>
    if mk == 0 then B
    else if B.get! (ci D) != 0 then B
    else
      let B1 := if mk % 2 == 1 then visit n D (B.set! (ci D) 1) else B.set! (ci D) 1
      if B1.size == 0 then B1
      else (walkM ci nxt visit n (mk / 2) (nxt D) B1).set! (ci D) 0

/-- Does the walk with the mask `mk` that begins at the entry `D` visit a row?  It does if the
blocks up to a block whose bit is set are all unmarked.  (This reads the marks only.) -/
@[specialize] def scanLive (ci nxt : Nat → Nat) (B : ByteArray) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | n + 1, mk, D =>
    if mk == 0 then false
    else if B.get! (ci D) != 0 then false
    else if mk % 2 == 1 then true
    else scanLive ci nxt B n (mk / 2) (nxt D)

/-- The walk with a mask, entered only if it visits a row. -/
@[inline] def walkG (ci nxt : Nat → Nat) (visit : Nat → Nat → ByteArray → ByteArray)
    (n mk D : Nat) (B : ByteArray) : ByteArray :=
  if scanLive ci nxt B n mk D then walkM ci nxt visit n mk D B else B

/-- The search below a sequence with counters `t`, `r`, `d`, potentials `m`, `M` of its earlier
cuts and last entry `q`.  A table of size zero stands for "found". -/
@[specialize] def go (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (kb : Nat)
    (code mask : Nat → Nat → Nat → Nat) (fN fS : Nat → Nat → Nat → Int)
    (cut : Nat → Nat → Nat → Int → Int → Bool) (fg nt tp : Nat) :
    Nat → Nat → Nat → Nat → Int → Int → Nat → ByteArray → ByteArray
  | 0, _, _, _, _, _, _, _ => ByteArray.empty
  | fuel + 1, t, r, d, m, M, q, B =>
    let c := code t r d
    if c == 0 then B
    else if c == 1 then ByteArray.empty
    else if fuel != fg || (q + 8192 * d) % nt == tp then
      let B1 :=
        if c != 3 then
          let f := fN t r d
          let mN := min m f
          let MN := max M f
          if cut t r d mN MN then
            let mk := mask t (r + 1) d
            all (fun D B' => walkG ci nxt
              (fun n e B'' => go ci nxt s3 s4 kb code mask fN fS cut fg nt tp fuel
                t (r + 1) (d + n) mN MN e B'') kb mk D B') (s3 q) B
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
            (fun n e B'' => go ci nxt s3 s4 kb code mask fN fS cut fg nt tp fuel
              (t + 1) (r + 1) (d + n) mS MS e B'') kb mk D B') (s4 q) B1
        else B1
      else B1
    else B

/-- Part `tp` of `nt` of the search.  `false`: none of the visited sequences is found (and the
fuel was enough to see that). -/
@[specialize] def searchPart (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (st kb : Nat)
    (code mask : Nat → Nat → Nat → Nat) (fN fS : Nat → Nat → Nat → Int)
    (cut : Nat → Nat → Nat → Int → Int → Bool) (sz fuel fg nt tp : Nat) : Bool :=
  (walk ci nxt
    (fun n e B => go ci nxt s3 s4 kb code mask fN fS cut fg nt tp fuel 0 1 n 0 0 e B)
    kb st (marks0 sz)).size == 0

/-- The parts `pa ≤ tp < pb`, evaluated as tasks. -/
@[inline] def par (part : Nat → Bool) (pa pb : Nat) : Bool :=
  ((List.range (pb - pa)).map fun i => Task.spawn fun _ => part (pa + i)).any Task.get

/-! ### Tables -/

/-- A function of three numbers, tabulated for `t < A`, `r < B`, `d < C`. -/
def tabA {α : Type} (A B C : Nat) (f : Nat → Nat → Nat → α) : Array α :=
  Array.ofFn (n := A * B * C) fun i => f (i.val / C / B) (i.val / C % B) (i.val % C)

/-- A function of two numbers, tabulated for `t < A`, `y < C`. -/
def tab2 {α : Type} (A C : Nat) (f : Nat → Nat → α) : Array α :=
  Array.ofFn (n := A * C) fun i => f (i.val / C) (i.val % C)

/-- The function read from its table; outside the table it is evaluated. -/
@[inline] def look2 {α : Type} [Inhabited α] (A C : Nat) (T : Array α) (f : Nat → Nat → α)
    (t y : Nat) : α :=
  if t < A && y < C then T[t * C + y]! else f t y

/-- `p x` holds for some `x ≤ n`. -/
def anyLe (p : Nat → Bool) : Nat → Bool
  | 0 => p 0
  | n + 1 => p (n + 1) || anyLe p n

/-- The least of `init` and of the `f x` with `x ≤ n` and `p x`. -/
def minLe (p : Nat → Bool) (f : Nat → Int) (init : Int) : Nat → Int
  | 0 => if p 0 then min init (f 0) else init
  | n + 1 => if p (n + 1) then min (minLe p f init n) (f (n + 1)) else minLe p f init n

/-- The largest of the `f x` with `x ≤ n`. -/
def maxLe (f : Nat → Int) : Nat → Int
  | 0 => f 0
  | n + 1 => max (maxLe f n) (f (n + 1))

/-- The largest of the `f x` with `x ≤ n`, for natural numbers. -/
def maxLeN (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n + 1 => max (maxLeN f n) (f (n + 1))

/-! ### The rule

`P u x` is the cap for sequences with `u` links of weight 4 and `x` holes. -/

/-- A violation: `s` links, `lo ≤ d ≤ hi` holes, more rows than the cap. -/
def kBad (P : Nat → Nat → Nat) (s lo hi : Nat) (t r d : Nat) : Bool :=
  t == s && lo ≤ d && d ≤ hi && P s d < r

/-- Level `x` is allowed for the continuation with a link of weight 3: with a rest of `s - t`
links and `x - d` holes at its cap the sequence would be above the cap at `x`. -/
def kLevN (P : Nat → Nat → Nat) (s lo : Nat) (t r d x : Nat) : Bool :=
  t ≤ s && lo ≤ x && d ≤ x && P s x < r + P (s - t) (x - d)

/-- Level `x` is allowed for the continuation with a link of weight 4 (the rest has `s - t - 1`
links). -/
def kLevS (P : Nat → Nat → Nat) (s lo : Nat) (t r d x : Nat) : Bool :=
  t < s && lo ≤ x && d ≤ x && P s x < r + P (s - t - 1) (x - d)

/-- The plain rule as a code: `1` a violation, `4`, `2`, `3` continue with both kinds of links,
with weight 3 only, with weight 4 only, `0` nothing. -/
def codeF (P : Nat → Nat → Nat) (s lo hi : Nat) (t r d : Nat) : Nat :=
  if kBad P s lo hi t r d then 1
  else if anyLe (kLevN P s lo t r d) hi then (if anyLe (kLevS P s lo t r d) hi then 4 else 2)
  else if anyLe (kLevS P s lo t r d) hi then 3 else 0

/-- The potential `a · rows - b · holes - 2 h · links` of the cut behind a sequence that is
followed by a link of weight 3. -/
@[inline] def potN (a b h : Nat) (t r d : Nat) : Int :=
  ((a * r : Nat) : Int) - ((b * d : Nat) : Int) - ((2 * h * t : Nat) : Int)

/-- The same for a link of weight 4. -/
@[inline] def potS (a b h : Nat) (t r d : Nat) : Int := potN a b h t r d - (h : Int)

/-- `a P_u(e) - b e - 2 h u`: the largest potential of a part with `u` links and `e` holes. -/
def lin (P : Nat → Nat → Nat) (a b h u e : Nat) : Int := potN a b h u (P u e) e

/-- `seg(e)`: the most that a later part with `e` holes and at most `s - t` links adds. -/
def segF (P : Nat → Nat → Nat) (s a b h : Nat) (t e : Nat) : Int :=
  maxLe (fun u => lin P a b h u e) (s - t)

/-- `U(y)`: the largest potential of a prefix with `y` holes and at least `t` links. -/
def uF (P : Nat → Nat → Nat) (s a b h : Nat) (t y : Nat) : Int :=
  maxLe (fun i => lin P a b h (t + i) y) (s - t)

/-- The largest value that the peak can have at level `x`: the maximum over `0 ≤ e ≤ x - d` of
`min (U (d + e)) (f + seg e)`. -/
def pkF (U sg : Nat → Nat → Int) (f : Int) (t d x : Nat) : Int :=
  maxLe (fun e => min (U t (d + e)) (f + sg t e)) (x - d)

/-- `c(x)`: the least potential of a counterexample at level `x`. -/
def cF (P : Nat → Nat → Nat) (s a b h x : Nat) : Int := potN a b h s (P s x + 1) x

/-- Level `x` is allowed for a prefix with counters `t`, `r`, `d`. -/
def allowedF (P : Nat → Nat → Nat) (s lo : Nat) (t r d x : Nat) : Bool :=
  kLevN P s lo t r d x || kLevS P s lo t r d x

/-- A value above every potential. -/
def big : Int := 1000000000

/-- `A1`: the least `c(x)` over the allowed levels. -/
def a1F (P : Nat → Nat → Nat) (s lo hi a b h : Nat) (t r d : Nat) : Int :=
  minLe (allowedF P s lo t r d) (cF P s a b h) big hi

/-- `A2`: the least `c(x)` less the largest peak, over the allowed levels. -/
def a2F (U sg : Nat → Nat → Int) (P : Nat → Nat → Nat) (s lo hi a b h : Nat) (t r d : Nat) :
    Int :=
  minLe (allowedF P s lo t r d)
    (fun x => cF P s a b h x - pkF U sg (potN a b h t r d) t d x) big hi

/-- The reversal cut in table form: the continuation is allowed if `m = 0`, or `M + m ≥ A1`, or
`m ≥ A2`. -/
def cutF (A1 A2 : Nat → Nat → Nat → Int) (t r d : Nat) (m M : Int) : Bool :=
  decide (0 ≤ m) || decide (A1 t r d ≤ M + m) || decide (A2 t r d ≤ m)

/-- The mask of the rows that can follow: bit `j` of `maskG code t r d n` is set if the code of
the counters `t`, `r`, `d + (n - 1 - j)` is not `0`. -/
def maskG (code : Nat → Nat → Nat → Nat) (t r d : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 * maskG code t r d n + (if code t r (d + n) != 0 then 1 else 0)

/-- The code read from its table.  Rows above `R` are read at `R` (which is above every cap, so
that the code is the same); for other `t` or `d` outside the table the code is `0`. -/
@[inline] def codeT (A R C : Nat) (T : Array Nat) (t r d : Nat) : Nat :=
  if t < A && d < C then T[(t * (R + 1) + min r R) * C + d]! else 0

/-- The mask read from its table; outside the table it is `full`. -/
@[inline] def maskT (A B C full : Nat) (T : Array Nat) (t r d : Nat) : Nat :=
  if t < A && r < B && d < C then T[(t * B + r) * C + d]! else full

/-- The cut read from its tables; outside the tables the continuation is allowed. -/
@[inline] def cutT (A B C : Nat) (T1 T2 : Array Int) (t r d : Nat) (m M : Int) : Bool :=
  decide (0 ≤ m) || !(decide (t < A) && decide (r < B) && decide (d < C)) ||
    decide (T1[(t * B + r) * C + d]! ≤ M + m) || decide (T2[(t * B + r) * C + d]! ≤ m)

/-! ### The searches -/

/-- A part of F(s; lo - 1, hi) with the potential `(a, b, h)`, with words as codes (set A of
`PSearch.lean`, for the kernel). -/
def seqPartA (k : Nat) (caps : List (List Nat)) (s lo hi a b h fuel ds nt tp : Nat) : Bool :=
  searchPart (PS.cidxF k (4 * (k - 1)) (16 ^ (k - 1) - 1)) (PS.nxtF (4 * (k - 1)) (16 ^ (k - 1) - 1))
    (PS.sdA k 3 (PS.permCodes k k)) (PS.sdA k 4 (PS.permCodes k k)) (PS.idcF k) (k - 1)
    (codeF (capF caps) s lo hi) (fun t r d => maskG (codeF (capF caps) s lo hi) t r d (k - 1))
    (potN a b h) (potS a b h)
    (cutF (a1F (capF caps) s lo hi a b h)
      (a2F (uF (capF caps) s a b h) (segF (capF caps) s a b h) (capF caps) s lo hi a b h))
    (k ^ (k - 1)) fuel (fuel - ds) nt tp

/-- F(s; lo - 1, hi) with words as codes (for the kernel). -/
def seqSearchA (k : Nat) (caps : List (List Nat)) (s lo hi a b h fuel ds nt pa pb : Nat) : Bool :=
  par (seqPartA k caps s lo hi a b h fuel ds nt) pa pb

/-- F(s; lo - 1, hi) with the potential `(a, b, h)`, compiled: words are indices into the list of
permutation codes (set B of `PSearch.lean`), and the rule is read from tables.  All tables are
built once, before the parts start; the parts only read them. -/
def seqSearch (k : Nat) (caps : List (List Nat)) (s lo hi a b h fuel ds nt pa pb : Nat) : Bool :=
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
  par (fun tp => searchPart (fun i => ciT[i]!) (fun i => nxtT[i]!) (fun i => s3T[i]!)
    (fun i => s4T[i]!) (jl.idxOf (PS.idcF k)) (k - 1) (codeT A R C tc)
    (maskT A (R + 1) C full tm) (potN a b h) (potS a b h) (cutT A (R + 1) C t1 t2) jl.length
    fuel (fuel - ds) nt tp) pa pb

end KS
end SuperpermLowerBounds
