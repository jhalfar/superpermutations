import N8Struct.PackBase

/-!
# Reading backwards

`revRow` turns the row `(x, v)` into `(rot (reverse x) ((7 - v) mod 6), v)`.  At word level, for
every row of the published packing `Pstar` the slices (Pantone's completion rows, as words) of the
reversed row are exactly the reversed slices, and the same holds for the 12 rowless loops with
`L ↦ canon (reverse L)`.  So the reversed word is a word of the selection `revRow(Pstar)`, whose rows
are the rows of the packing `PstarRev`, the image of `K0` under the renaming `[0,3,4,5,1,2]`;
`Pstar` itself is in the class of `K1`.  Reversal therefore joins the two renaming classes.
Kernel `decide`, split into one lemma per walk.
-/

namespace N8Struct

open SuperpermutationUpperBound

/-- The slices of a loop without a row (model.py `option_slices` with v = 0): Pantone's repair rows
`⟨rot L j ++ [6], 7, 7⟩`, j = 0..5. -/
def rowlessSlices (L : State) : List (Row Nat) :=
  (List.range 6).map (fun j => Completion.repairRow ⟨L, 6, 0⟩ 7 j)

/-- The slices of the reversed row are the reversed slices of the row. -/
def RevOK (r : Row Nat) : Prop :=
  ((Completion.completeRows (revRow r) 7).map Row.word).Perm
    ((Completion.completeRows r 7).map (fun t => t.word.reverse))

instance (r : Row Nat) : Decidable (RevOK r) := by
  unfold RevOK
  infer_instance

theorem rev_walk0 : ∀ r ∈ placement (Pstar.getD 0 []), RevOK r := by decide +kernel
theorem rev_walk1 : ∀ r ∈ placement (Pstar.getD 1 []), RevOK r := by decide +kernel
theorem rev_walk2 : ∀ r ∈ placement (Pstar.getD 2 []), RevOK r := by decide +kernel
theorem rev_walk3 : ∀ r ∈ placement (Pstar.getD 3 []), RevOK r := by decide +kernel

/-- Word level: for every row of `Pstar`, the slices of the reversed row are the reversed slices. -/
theorem rev_slices : ∀ r ∈ Pstar.flatMap placement, RevOK r := by
  intro r hr
  obtain ⟨g, hg, hr⟩ := List.mem_flatMap.mp hr
  have hP : Pstar = [Pstar.getD 0 [], Pstar.getD 1 [], Pstar.getD 2 [], Pstar.getD 3 []] := rfl
  rw [hP] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact rev_walk0 r hr
  · exact rev_walk1 r hr
  · exact rev_walk2 r hr
  · exact rev_walk3 r hr
/-- Word level, loops without a row: the loop `L` becomes the loop of `reverse L`. -/
theorem rev_rowless : ∀ L ∈ leftover,
    ((rowlessSlices (canon L.reverse)).map Row.word).Perm
      ((rowlessSlices L).map (fun t => t.word.reverse)) := by
  decide +kernel

/-- The reversed rows of `Pstar` are the rows of the packing `PstarRev`. -/
theorem rev_packing :
    ((Pstar.flatMap placement).map revRow).Perm (PstarRev.flatMap placement) := by
  decide +kernel

/-- `PstarRev` is in the class of `K0` (`Pstar` is in the class of `K1`, Published.lean). -/
theorem PstarRev_class : (K0.map (relabel [0,3,4,5,1,2])).Perm PstarRev := by decide +kernel

end N8Struct

#print axioms N8Struct.rev_slices
#print axioms N8Struct.rev_rowless
#print axioms N8Struct.rev_packing
#print axioms N8Struct.PstarRev_class
