import N8Struct.PackBase

/-!
# The packing of the published selection and its Klein symmetry

`Pstar` (the start states of the four walks of `selection-46174.txt`) is the image of `K1` under the
renaming `[0,2,1,5,4,3]`; its rows are exactly the 108 rows of the selection; it covers 108 loops, and
the 12 loops without a row are all the other loops.  The Klein group
V4 = {id, (25)(34), (01)(34), (01)(25)} maps `Pstar` to itself, every non-trivial element swaps the
four walks in pairs, and V4 maps the 12 rowless loops onto themselves (three orbits of four); no
non-identity element fixes any single one of them.  Kernel `decide` only.
-/

namespace N8Struct

open SuperpermutationUpperBound

theorem Pstar_class : (K1.map (relabel [0,2,1,5,4,3])).Perm Pstar := by decide +kernel

theorem Pstar_walks : ∀ g ∈ Pstar, ClosedWalk g vs27 := by
  intro g hg
  have hs : ∀ g ∈ Pstar, IsState g := by decide +kernel
  exact placement_closed_all (hs g hg)

/-- The rows of the four walks of `Pstar` are exactly the 108 rows of `selection-46174.txt`. -/
theorem Pstar_rows :
    ((Pstar.flatMap placement).map (fun r => (r.base, r.visible))).Perm selectionRows := by
  decide +kernel

theorem selectionRows_length : selectionRows.length = 108 := by decide

/-- The four walks visit 108 different loops. -/
theorem Pstar_loops : (loopsOf (Pstar.flatMap placement)).Nodup ∧
    (loopsOf (Pstar.flatMap placement)).length = 108 := by
  rw [coveredLoops_eq]
  decide +kernel

/-- The 12 left-over loops are loops (canonical rotations of states), different, and not covered. -/
theorem leftover_spec : leftover.length = 12 ∧ leftover.Nodup ∧
    (∀ L ∈ leftover, IsState L ∧ canon L = L ∧ L ∉ loopsOf (Pstar.flatMap placement)) := by
  rw [coveredLoops_eq]
  decide +kernel

/-- Every loop is covered or left over: 108 + 12 = all 120 loops. -/
theorem all_loops_covered : ∀ x, IsState x →
    canon x ∈ leftover ∨ canon x ∈ loopsOf (Pstar.flatMap placement) := by
  rw [coveredLoops_eq]
  exact forall_stateP (by decide +kernel)

theorem V4_states : ∀ σ ∈ V4, IsState σ := by decide +kernel

theorem V4_stabilises : ∀ σ ∈ V4, (Pstar.map (relabel σ)).Perm Pstar := by decide +kernel

/-- Each non-trivial element of V4 swaps the four walks in pairs: (25)(34) swaps walks 0,1 and 2,3;
(01)(34) swaps 0,2 and 1,3; (01)(25) swaps 0,3 and 1,2 (walk i = the placement at `Pstar[i]`). -/
theorem V4_swaps :
    Pstar.map (relabel [0,1,5,4,3,2]) = [1,0,3,2].map (fun i => Pstar.getD i []) ∧
    Pstar.map (relabel [1,0,2,4,3,5]) = [2,3,0,1].map (fun i => Pstar.getD i []) ∧
    Pstar.map (relabel [1,0,5,3,4,2]) = [3,2,1,0].map (fun i => Pstar.getD i []) := by
  decide +kernel

/-- The same at the level of rows: the renamed walk is the other walk. -/
theorem V4_swaps_rows (i j : Nat) (σ : State)
    (h : relabel σ (Pstar.getD i []) = Pstar.getD j []) :
    (placement (Pstar.getD i [])).map (relabelRow σ) = placement (Pstar.getD j []) := by
  rw [← placement_relabel, h]

/-- V4 maps the set of the 12 rowless loops onto itself. -/
theorem V4_leftover : ∀ σ ∈ V4, (leftover.map (fun L => canon (relabel σ L))).Perm leftover := by
  decide +kernel

/-- No non-identity element of V4 fixes a single rowless loop. -/
theorem V4_leftover_no_fixed : ∀ σ ∈ V4.tail, ∀ L ∈ leftover, canon (relabel σ L) ≠ L := by
  decide +kernel

/-- Three orbits of four: the orbits of V4 on the rowless loops, as lists. -/
theorem V4_leftover_orbits : ∀ L ∈ leftover, ((V4.map (fun σ => canon (relabel σ L)))).Nodup := by
  decide +kernel

end N8Struct

#print axioms N8Struct.Pstar_class
#print axioms N8Struct.Pstar_walks
#print axioms N8Struct.Pstar_rows
#print axioms N8Struct.Pstar_loops
#print axioms N8Struct.leftover_spec
#print axioms N8Struct.all_loops_covered
#print axioms N8Struct.V4_stabilises
#print axioms N8Struct.V4_swaps
#print axioms N8Struct.V4_leftover
#print axioms N8Struct.V4_leftover_no_fixed
#print axioms N8Struct.V4_leftover_orbits
