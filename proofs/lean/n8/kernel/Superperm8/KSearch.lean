/-
The positive-prefix search of `AffineSearch.lean`, written so that the Lean kernel can evaluate it.
New file (not in williamechols/superperm8-ge-46130).  Apache-2.0, as the project.
-/

/-!
# A search on numbers

The search of `AffineSearch.lean` asks for a trail of marked rows whose score
`A * rows - Cc * charge` stays positive along the trail and ends above `Bd`.  Here the same search
works on natural numbers only:

* a state `St` holds the code `uc` of the last state of the last row, the set `B` of used blocks
  and the set `C` of used rotation classes (both as bit sets, indexed by `bidx` and `cidx`), and
  the score `s`;
* `children` lists the states after one more row: six possible starts (`sixCodes`), and for each
  start the rows found by `rowAcc`, which walks along the block and decides at each position
  whether the row ends there, goes on with the position visible, or goes on with the position
  omitted;
* `fsearchK leaf fuel st key` explores `fuel` rows below `st` and calls `leaf` on what is left.
  With `leaf = fun _ _ => true` it is the search itself: `false` means that no trail was found
  and that the fuel was not exhausted.  The argument `key` records the path (the index of each
  child taken, last first); other leaves use it to cut the search into parts (`KSound.lean`).

`fsearch A Cc Bd fuel` is the whole search: the first row starts at the identity.

This file imports nothing, so that the generated files which evaluate parts of the search in the
kernel load quickly.  `KCode.lean` relates the numbers to permutations, `KSound.lean` proves that the
search is complete.
-/

namespace Superperm8
namespace K

/-! ### Arithmetic on codes

A code is the word of a permutation of eight symbols read as eight octal digits, first symbol first
(`K.code` in `KCode.lean`, where the facts about these functions are proved). -/

/-- `F` on codes: rotate the first seven digits, keep the last. -/
def rotF (c : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.mod (Nat.div c 8) 262144) 8) (Nat.div c 2097152)) 8)
    (Nat.mod c 8)

/-- `R` on codes: rotate all eight digits. -/
def rotR (c : Nat) : Nat := Nat.add (Nat.mul (Nat.mod c 2097152) 8) (Nat.div c 2097152)

/-- `2 ^ (3 j)`, where the digit `7` of `c` is the `j`-th from the right. -/
def cmask (c : Nat) : Nat :=
  Nat.land (Nat.land (Nat.land c (Nat.shiftRight c 1)) (Nat.shiftRight c 2)) 2396745

def ccanonM (c m : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.mul c (Nat.div 2097152 m)) 16777216) (Nat.div c (Nat.mul 8 m))

/-- The rotation of `c` that begins with the digit `7`. -/
def ccanon (c : Nat) : Nat := ccanonM c (cmask c)

def cidxV (v : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.mod (Nat.div v 64) 32768) 2)
    (bif Nat.blt (Nat.mod (Nat.div v 8) 8) (Nat.mod v 8) then 1 else 0)

/-- The index of the rotation class of `c`: digits 2 to 6 of the rotation that begins with `7`,
and one bit for the order of its last two digits. -/
def cidx (c : Nat) : Nat := cidxV (ccanon c)

def bmask (nx : Nat) : Nat :=
  Nat.land (Nat.land (Nat.land nx (Nat.shiftRight nx 1)) (Nat.shiftRight nx 2)) 299593

def bcanonM (top last m : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.add (Nat.mod (Nat.mul top (Nat.div 262144 m)) 2097152)
    (Nat.div top (Nat.mul 8 m))) 8) last

/-- The symbol put first: `7`, or `6` when the last symbol is `7`. -/
def btarget (last : Nat) : Nat := bif Nat.beq last 7 then 6 else 7

/-- `2 ^ (3 j)`, where the digit `btarget` of the first seven digits of `c` is the `j`-th from
the right among them. -/
def bm (c : Nat) : Nat :=
  bmask (Nat.xor (Nat.xor (Nat.div c 8) (Nat.mul (btarget (Nat.mod c 8)) 299593)) 2097151)

/-- The `F`-rotation of `c` that begins with `btarget` of its last digit. -/
def bcanon (c : Nat) : Nat := bcanonM (Nat.div c 8) (Nat.mod c 8) (bm c)

def bidxV (v : Nat) : Nat :=
  Nat.add (Nat.add (Nat.mul (Nat.mod (Nat.div v 512) 4096) 16)
    (bif Nat.blt (Nat.mod (Nat.div v 64) 8) (Nat.mod (Nat.div v 8) 8) then 8 else 0)) (Nat.mod v 8)

/-- The index of the insertion block of `c`: digits 2 to 5 of the `F`-rotation that begins with
`btarget`, one bit for the order of digits 6 and 7, and the last digit. -/
def bidx (c : Nat) : Nat := bidxV (bcanon c)

def six (base x y z : Nat) : List Nat :=
  [Nat.add base (Nat.add (Nat.add (Nat.mul x 64) (Nat.mul y 8)) z),
   Nat.add base (Nat.add (Nat.add (Nat.mul x 64) (Nat.mul z 8)) y),
   Nat.add base (Nat.add (Nat.add (Nat.mul y 64) (Nat.mul x 8)) z),
   Nat.add base (Nat.add (Nat.add (Nat.mul y 64) (Nat.mul z 8)) x),
   Nat.add base (Nat.add (Nat.add (Nat.mul z 64) (Nat.mul x 8)) y),
   Nat.add base (Nat.add (Nat.add (Nat.mul z 64) (Nat.mul y 8)) x)]

/-- The codes of the six permutations that begin with symbols 3 to 7 of `c`. -/
def sixCodes (c : Nat) : List Nat :=
  six (Nat.mul (Nat.mod (Nat.div c 8) 32768) 512) (Nat.div c 2097152)
    (Nat.mod (Nat.div c 262144) 8) (Nat.mod c 8)

/-! ### The search -/

/-- A state of the search. -/
structure St where
  /-- code of the last state of the last row -/
  uc : Nat
  /-- used blocks: bit `bidx` -/
  B : Nat
  /-- used rotation classes: bit `cidx` -/
  C : Nat
  /-- score so far -/
  s : Nat

/-- Bit `i` of `S`. -/
def bit (S i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight S i) 1) 1

/-- `S` with bit `i` set. -/
def setBit (S i : Nat) : Nat := Nat.lor S (Nat.shiftLeft 1 i)

/-- The rows that start at the state with code `sc` (position `i` of its block, `n` positions
left), with `k` positions omitted so far and `Cacc` the classes of this row added to the used
ones.  `C0` is the set of classes used before this row, `kmax` the largest charge that keeps the
score positive.  A row that ends at position `i` has charge `6 - i + k`; `mk charge code classes`
builds the state after it. -/
def rowAcc (mk : Nat → Nat → Nat → St) (kmax C0 : Nat) :
    Nat → Nat → Nat → Nat → Nat → List St → List St
  | 0, _, _, _, _, acc => acc
  | n + 1, i, k, sc, Cacc, acc =>
    bif bit C0 (cidx sc) then
      bif and (Nat.ble 1 i) (Nat.ble (Nat.succ k) kmax) then
        rowAcc mk kmax C0 n (Nat.succ i) (Nat.succ k) (rotF sc) Cacc acc
      else acc
    else
      bif Nat.ble (Nat.add (Nat.sub 6 i) k) kmax then
        mk (Nat.add (Nat.sub 6 i) k) sc (setBit Cacc (cidx sc)) ::
          rowAcc mk kmax C0 n (Nat.succ i) k (rotF sc) (setBit Cacc (cidx sc))
            (bif and (Nat.ble 1 i) (Nat.ble (Nat.succ k) kmax) then
              rowAcc mk kmax C0 n (Nat.succ i) (Nat.succ k) (rotF sc) Cacc acc
            else acc)
      else
        rowAcc mk kmax C0 n (Nat.succ i) k (rotF sc) (setBit Cacc (cidx sc))
          (bif and (Nat.ble 1 i) (Nat.ble (Nat.succ k) kmax) then
            rowAcc mk kmax C0 n (Nat.succ i) (Nat.succ k) (rotF sc) Cacc acc
          else acc)

/-- The states after one row that starts at the code `qc`, put in front of `acc`. -/
def childrenAt (A Cc : Nat) (st : St) (qc : Nat) (acc : List St) : List St :=
  rowAcc (fun ch sc C' => ⟨sc, setBit st.B (bidx qc), C', Nat.sub (Nat.add st.s A) (Nat.mul Cc ch)⟩)
    (Nat.div (Nat.sub (Nat.add st.s A) 1) Cc) st.C 7 0 0 qc st.C acc

/-- The states after one more row. -/
def children (A Cc : Nat) (st : St) : List St :=
  (sixCodes st.uc).foldr
    (fun qc acc => bif bit st.B (bidx qc) then acc else childrenAt A Cc st qc acc) []

/-- `f c i` for some element `c` of the list, `i` being its index plus `j`. -/
def anyIdx (f : St → Nat → Bool) : List St → Nat → Bool
  | [], _ => false
  | c :: t, j => f c j || anyIdx f t (Nat.succ j)

/-- The search below `st`: `fuel` rows deep, then `leaf`. -/
def fsearchK (A Cc Bd : Nat) (leaf : St → List Nat → Bool) : Nat → St → List Nat → Bool
  | 0, st, key => leaf st key
  | fuel + 1, st, key =>
    bif Nat.blt Bd st.s then true
    else anyIdx (fun c i => fsearchK A Cc Bd leaf fuel c (i :: key)) (children A Cc st) 0

/-- The code of the identity. -/
def idc : Nat := 342391

/-- The states after the first row, which starts at the identity. -/
def rootChildren (A Cc : Nat) : List St := childrenAt A Cc ⟨0, 0, 0, 0⟩ idc []

/-- The whole search.  `false`: there is no trail of marked rows whose score stays positive and
ends above `Bd` (and the fuel was enough to see that). -/
def fsearch (A Cc Bd fuel : Nat) : Bool :=
  anyIdx (fun c i => fsearchK A Cc Bd (fun _ _ => true) fuel c [i]) (rootChildren A Cc) 0

/-! ### Cutting a search into parts

Used by the generated files; the lemmas are in `KSound.lean`. -/

/-- Element `i` of a list of states, or `d`. -/
def nthD : List St → Nat → St → St
  | [], _, d => d
  | c :: _, 0, _ => c
  | _ :: t, i + 1, d => nthD t i d

/-- The state reached from `st` by taking child `i` at each step of the path. -/
def stepPath (A Cc : Nat) : St → List Nat → St
  | st, [] => st
  | st, i :: t => stepPath A Cc (nthD (children A Cc st) i st) t

def beqKey : List Nat → List Nat → Bool
  | [], [] => true
  | a :: s, b :: t => Nat.beq a b && beqKey s t
  | _, _ => false

def memKey (key : List Nat) : List (List Nat) → Bool
  | [] => false
  | k :: t => beqKey key k || memKey key t

/-- The leaf that accepts (returns `false` for) exactly the paths of `cover`.  Paths are stored
last step first, as the search records them. -/
def leafCover (cover : List (List Nat)) : St → List Nat → Bool := fun _ key => !(memKey key cover)

/-- `Ref b st`: the search `b` rows deep finds nothing below `st`. -/
def Ref (A Cc Bd b : Nat) (st : St) : Prop := fsearchK A Cc Bd (fun _ _ => true) b st [] = false

/-- The state after the first row, when there is only one. -/
def rootSt (A Cc : Nat) : St := nthD (rootChildren A Cc) 0 ⟨0, 0, 0, 0⟩

end K
end Superperm8
