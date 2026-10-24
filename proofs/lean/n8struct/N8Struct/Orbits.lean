import N8Struct.PackBase

/-!
# The two classes up to renaming and their stabilisers

`K0` and `K1` are not renamings of each other, and each is fixed by exactly 4 renamings.  With
`packing_classification` this gives 2 classes of 720 / 4 = 180 packings each (360 in all; the counting
step itself, orbit-stabiliser, is not formalised).  Kernel `decide` over the 720 renamings.
-/

namespace N8Struct

open SuperpermutationUpperBound

/-- `K0` and `K1` are not renamings of each other: two classes up to renaming. -/
theorem K0_not_K1 : ∀ σ, IsState σ → ¬ (K0.map (relabel σ)).Perm K1 :=
  forall_stateP (by decide +kernel)

theorem stab_K0 : ∀ σ, IsState σ → ((K0.map (relabel σ)).Perm K0 ↔ σ ∈ stabK0) :=
  forall_stateP (by decide +kernel)

theorem stab_K1 : ∀ σ, IsState σ → ((K1.map (relabel σ)).Perm K1 ↔ σ ∈ stabK1) :=
  forall_stateP (by decide +kernel)

theorem stab_length : stabK0.length = 4 ∧ stabK1.length = 4 := by decide

end N8Struct

#print axioms N8Struct.K0_not_K1
#print axioms N8Struct.stab_K0
#print axioms N8Struct.stab_K1
