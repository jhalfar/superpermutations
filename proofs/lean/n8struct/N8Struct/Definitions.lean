import SuperpermutationUpperBound.RowSpelling
import SuperpermutationUpperBound.Completion.Local

/-!
# The objects of the n = 8 completion, as computable data

Route: Pantone's definitions are reused where they specialise to 8 symbols without hypotheses,
and the rest is defined here, mirroring the tool `words/n8/tools/n8lib/model.py` of this repository
(abbreviated `model.py` below) function by function.

* Letters are `Nat`; 0..5 are the ordinary letters, 6 is Pantone's distinguished letter `s`, 7 the
  completion letter `z` (model.py: `S_LETTER = 6`, `Z_LETTER = 7`).
* A *state* is an ordering of 0..5 (model.py: `STATES`), a list of length 6.
* The *loop* of a state is its cyclic class, represented by the rotation that starts with 0
  (model.py: `canon`).  Two states are in the same loop iff they have the same `canon`.
* A *row* of length `v` at the state `x` is Pantone's `Row` `⟨x, 6, v⟩` (Rows.lean): base `x`,
  satellite 6, `v` visible classes; its cost is Pantone's `Row.charge = 6 - v`
  (model.py: a row (x, v) costs `K - v`).  The next state is `gstep x v` (model.py: `gstep`).
  Pantone's level-7 compatibility `Row.Compatible` (tail = head, 4 letters) holds between consecutive
  rows of a walk (checked for the 27-walk in Walk27.lean); `gstep` is the tool's choice of the next
  state, which fixes also the order of the last two letters.
* The *slices* of a row are Pantone's completion rows `Completion.completeRows ⟨x, 6, v⟩ 7`
  (Completion/Local.lean): the lift rows `⟨insert 7 at j into x, 6, v + [j < v]⟩`, j = 0..5, and the
  repair rows `⟨rot x j ++ [6], 7, 7⟩`, j = v..5.  This is exactly model.py `option_slices (x, v)`:
  `i_j` = lift row j and `r_j` = repair row j; Pantone's `Row.word` is model.py `spell`
  (`rowSpellingAux b d (m-1)` = `spell(b, d, m)`).
* Two slices overlap by 5 letters iff Pantone's `Row.Compatible` holds (`tail = head`, 5 letters at
  level 8; RowSpelling.lean proves that the word starts with `head` and ends with `tail`).
  A *closed trail* is Pantone's `ClosedTrail` (Rows.lean): a nonempty cyclically compatible list.
  model.py `trail_cycles` takes the overlap-5 successor of every slice; when the heads of the slices
  are pairwise different, the successor is unique and a cyclically compatible ordering of all slices
  is one cycle of it.  That is our `SingleClosedTrail`.
* The *port map* (model.py `port`, `port_trails`) is the tool's fast rule for the number of trails of
  a closed walk: compose the port permutations of the rows on the 5 strands, count cycles, add one
  closed 2-slice trail for every row of length 5.
-/

namespace N8Struct

open SuperpermutationUpperBound

/-- An ordering of the letters 0..5 (model.py: an element of `STATES`). -/
abbrev State := List Nat

/-- `x` is an ordering of 0..5. -/
def IsState (x : State) : Prop := x.length = 6 ∧ x.Nodup ∧ ∀ a ∈ x, a < 6

instance (x : State) : Decidable (IsState x) := by
  unfold IsState
  infer_instance

/-- The identity ordering `012345`. -/
def id6 : State := [0, 1, 2, 3, 4, 5]

/-- The loop of a state: its rotation that starts with 0 (model.py: `canon`). -/
def canon (x : State) : State := x.rotateLeft (x.idxOf 0)

/-- The state at which the row after the row `(x, v)` starts (model.py: `gstep`):
`x[1:5] + (x[0], x[5])` for `v = 6`, else `x[v+1:] + x[:v-1] + (x[v], x[v-1])`. -/
def gstep (x : State) (v : Nat) : State :=
  if v = 6 then (x.drop 1).take 4 ++ x.take 1 ++ x.drop 5
  else x.drop (v + 1) ++ x.take (v - 1) ++ (x.drop v).take 1 ++ (x.drop (v - 1)).take 1

/-- The row of length `v` at the state `x`, as Pantone's row: base `x`, satellite 6. -/
def nrow (x : State) (v : Nat) : Row Nat := ⟨x, 6, v⟩

/-- The rows of the walk that starts at `x` with the row lengths `vs`
(model.py `walks.placements`: `rows.append((x, v)); x = gstep(x, v)`). -/
def walkRows : State → List Nat → List (Row Nat)
  | _, [] => []
  | x, v :: vs => nrow x v :: walkRows (gstep x v) vs

/-- The state reached after the rows. -/
def walkEnd : State → List Nat → State
  | x, [] => x
  | x, v :: vs => walkEnd (gstep x v) vs

/-- The loops visited by a list of rows. -/
def loopsOf (rs : List (Row Nat)) : List State := rs.map (fun r => canon r.base)

/-- A closed walk (model.py `walks.placements`, the test `x != g or len(set(loops)) != len(rows)`):
the walk from the state `g` returns to `g`, every row length is 1..6, and the loops are distinct. -/
def ClosedWalk (g : State) (vs : List Nat) : Prop :=
  IsState g ∧ walkEnd g vs = g ∧ (loopsOf (walkRows g vs)).Nodup ∧ ∀ v ∈ vs, 1 ≤ v ∧ v ≤ 6

instance (g : State) (vs : List Nat) : Decidable (ClosedWalk g vs) := by
  unfold ClosedWalk
  infer_instance

/-- The cost of the rows (model.py `q_of`): the sum of `6 - v`. -/
def Q (rs : List (Row Nat)) : Nat := (rs.map Row.charge).sum

/-! ## Ports (model.py `port`, `port_trails`) -/

/-- How a row of length `v` permutes the 5 strands of a walk (model.py `port`). -/
def port (v j : Nat) : Nat :=
  if v = 6 then (j + 4) % 5
  else if j < v then j + 6 - v - 1 else if j = v then 6 - v - 2 else j - v - 1

/-- The product of the port maps along the walk.  model.py starts with `p = identity` and replaces
`p` by `[PORT[v][j] for j in p]` for each `v`, so strand `j` goes to `port vL (... (port v1 j))`. -/
def portMap (vs : List Nat) (j : Nat) : Nat := vs.foldl (fun p v => port v p) j

/-- `f` applied `n` times. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, j => j
  | n + 1, j => iter f n (f j)

/-- The orbit of `j` under `portMap vs`: the images after 1..5 steps. -/
def portOrbit (vs : List Nat) (j : Nat) : List Nat :=
  (List.range 5).map (fun k => iter (portMap vs) (k + 1) j)

/-- The port map is a permutation of the strands 0..4. -/
def PortPerm (vs : List Nat) : Prop :=
  ((List.range 5).map (portMap vs)).Perm (List.range 5)

instance (vs : List Nat) : Decidable (PortPerm vs) := by
  unfold PortPerm
  infer_instance

/-- The number of cycles of the port map: the strands that are the least element of their orbit. -/
def portCycles (vs : List Nat) : Nat :=
  ((List.range 5).filter (fun j => (portOrbit vs j).all (fun i => j ≤ i))).length

/-- model.py `port_trails`: cycles of the port map plus one closed 2-slice trail per row of length 5. -/
def portTrails (vs : List Nat) : Nat := portCycles vs + vs.count 5

/-! ## Slices and trails (Pantone's definitions) -/

/-- The slices of a list of rows: Pantone's completion rows with the completion letter 7
(the same as `Completion.packingRows rs 7`, Completion/Counts.lean; model.py `option_slices`). -/
def slices (rs : List (Row Nat)) : List (Row Nat) :=
  rs.flatMap (fun r => Completion.completeRows r 7)

/-- The slices of the rows form a single closed trail: some ordering of all of them is a closed trail
in Pantone's sense (consecutive slices overlap by 5 letters, cyclically), and the heads of the slices
are pairwise different, so the overlap-5 successor of each slice is unique and this ordering is the
only cycle of model.py `trail_cycles`. -/
def SingleClosedTrail (rs : List (Row Nat)) : Prop :=
  ∃ ord : List (Row Nat), ord.Perm (slices rs) ∧ ClosedTrail ord ∧ (ord.map Row.head).Nodup

/-! ## Symmetries -/

/-- A state `σ` as a renaming of the letters: `a ↦ σ[a]` for `a < 6`, the identity beyond
(model.py `pack.relabel`: `c -> g[c]`). -/
def app (σ : State) (a : Nat) : Nat := σ.getD a a

/-- Rename the letters of a state. -/
def relabel (σ x : State) : State := x.map (app σ)

/-- Rename the letters of the base of a row (the satellite 6 is fixed by every renaming of 0..5). -/
def relabelRow (σ : State) (r : Row Nat) : Row Nat := ⟨relabel σ r.base, r.satellite, r.visible⟩

/-- Reading backwards: the row `(x, v)` becomes the row `(rot (reverse x) ((7 - v) mod 6), v)`.
Packing.lean checks on the rows of the packing that the slices of the new row are exactly the
reversed slices of the old one (as words), so this is the reversal of the word at selection level. -/
def revRow (r : Row Nat) : Row Nat :=
  ⟨r.base.reverse.rotateLeft ((7 - r.visible) % 6), 6, r.visible⟩

/-- The loops of two lists of rows are disjoint. -/
def Disj (P R : List (Row Nat)) : Prop := ∀ r ∈ P, ∀ s ∈ R, canon r.base ≠ canon s.base

instance (P R : List (Row Nat)) : Decidable (Disj P R) := by
  unfold Disj
  infer_instance

end N8Struct
