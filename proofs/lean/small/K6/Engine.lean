import K6.Tab

/-!
# A search on 6 symbols for the Lean kernel

One depth-first search over sequences of rows on 6 symbols whose blocks lie in pairwise different
rotation classes.  A word is its index `0 … 719` in the table `TP` (index 0 is `1 2 3 4 5 6`).  The
tables are natural numbers read with shifts (`fld`), and the set of used classes is a natural number
read as a set of bits, so that every step of the search is a few operations on numbers, which the
kernel does with GMP.

A row is a walk from block to block (`nx`, the door) as long as the classes are new.  After a row the
search continues with a row whose entry is one of the five words that the exit of the last block
overlaps in 3 letters (`s3`; a seam of weight 3, kind `0`), or with a row that starts at any word of
a new class (a jump, any other kind).  What the search counts and when it stops is given by `Rules`:
counters of type `Cn`, updated at every row (`stN` after a seam, `stJ` after a jump, `init` for the
first row, with the number of holes of the new row and the index of its last entry), two rules that
say whether a sequence is continued with a seam (`keepN`) or with a jump (`keepJ`), and `bad`, which
also sees the set of used classes: the sequence is found.  A search is cut into parts by giving each
part its own rules (the counters can remember entries, and the rules can refuse all but a share of
them).

`part R fuel`: the answer `false` means: nothing found, and the fuel was enough to see that (fuel `0`
counts as found).  `Sound.lean` proves what it means.
-/

namespace K6

/-- The field of `w` bits number `i` of the number `T`. -/
@[inline] def fld (T w i : Nat) : Nat := (T >>> (w * i)) % 2 ^ w

/-- The word with index `i`. -/
def pw (i : Nat) : List Nat :=
  let X := fld TP 18 i
  [X / 32768 % 8, X / 4096 % 8, X / 512 % 8, X / 64 % 8, X / 8 % 8, X % 8]

/-- The class index of the word with index `i` (`0 … 119`). -/
def ci (i : Nat) : Nat := fld TCI 7 i

/-- The entry of the next block of a row. -/
def nx (i : Nat) : Nat := fld TNX 10 i

/-- The `j`-th (`j < 5`) word of another class that the exit overlaps in 3 letters. -/
def s3 (i j : Nat) : Nat := fld TS3 10 (5 * i + j)

/-- The representative of class `c`. -/
def rep (c : Nat) : Nat := fld TREP 10 c

/-- The rotation that turns the word `i` into the representative of its class. -/
def rot (i : Nat) : Nat := fld TROT 3 i

/-- The set `{c}` as a number. -/
@[inline] def bit (c : Nat) : Nat := 1 <<< c

/-- What the search counts and when it stops. -/
structure Rules (Cn : Type) where
  init : Nat → Nat → Cn
  stN : Cn → Nat → Nat → Cn
  stJ : Cn → Nat → Nat → Cn
  keepN : Cn → Bool
  keepJ : Cn → Bool
  bad : Cn → Nat → Bool

/-- The rows that begin with the block of entry `D`, given the used classes `U`.  The last
argument is the number of blocks that may still be added; when it is `n + 1`, the row that ends
with the current block has `n` holes.  `g U' e n` is the search below the sequence extended by the
row with `n` holes that ends with the block of entry `e`, with the used classes `U'`. -/
def walk (g : Nat → Nat → Nat → Bool) : Nat → Nat → Nat → Bool
  | _, _, 0 => false
  | U, D, n + 1 =>
    cond (U.testBit (ci D)) false
      (g (U ||| bit (ci D)) D n || walk g (U ||| bit (ci D)) (nx D) n)

/-- The rows after a seam: the five successors `s3 q j`, `j < 5`. -/
def succ3 (g : Nat → Nat → Nat → Bool) (U q : Nat) : Nat → Bool
  | 0 => false
  | j + 1 => walk g U (s3 q j) 5 || succ3 g U q j

/-- The rows after a jump: every word `i < 720`. -/
def jumps (g : Nat → Nat → Nat → Bool) (U : Nat) : Nat → Bool
  | 0 => false
  | i + 1 => walk g U i 5 || jumps g U i

/-- The search below a sequence with used classes `U`, last entry `q` and counters `c`. -/
def go {Cn : Type} (R : Rules Cn) : Nat → Nat → Nat → Cn → Bool
  | 0, _, _, _ => true
  | f + 1, U, q, c =>
    R.bad c U || (R.keepN c && succ3 (fun U' e n => go R f U' e (R.stN c n e)) U q 5) ||
      (R.keepJ c && jumps (fun U' e n => go R f U' e (R.stJ c n e)) U 720)

/-- The search: the first row starts at the word `1 2 3 4 5 6`. -/
def part {Cn : Type} (R : Rules Cn) (fuel : Nat) : Bool :=
  walk (fun U e n => go R fuel U e (R.init n e)) 0 0 5

end K6
