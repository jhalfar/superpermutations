/-
This file is a modified copy of SuperpermutationUpperBound/Assembly/SupportedStates.lean of Jay Pantone's
repository github.com/jaypantone/superperm-upper-43-80 (commit c8fb7ffdd69be1375580710ae11b47a295b1f0f6),
which is under the Apache License, Version 2.0.

Two changes: the import of SuperpermutationUpperBound.Partition.SprintFamily is replaced by an import of
SuperpermutationUpperBound.Foundation.SupportedWords, and the section Partition.SprintFamily at the end
(stateAlphabet, stateAlphabet_card, stateAlphabet_mem) is removed.  Everything else is his text, unchanged.
The file SupportedStates.diff in the directory patches shows the change.
-/
import SuperpermutationUpperBound.Assembly.OverlapStates
import SuperpermutationUpperBound.Foundation.SupportedWords

namespace SuperpermutationUpperBound
variable {α : Type}

/-- Literal injective states supported on an arbitrary finite alphabet. -/
def supportedOverlapState (A : Finset α) (ell : Nat) :=
  {v : List α // v.length = ell ∧ v.Nodup ∧ ∀ a ∈ v, a ∈ A}

def embeddingSupportedState (A : Finset α) (ell : Nat) (f : Fin ell ↪ A) :
    supportedOverlapState A ell := by
  refine ⟨List.ofFn (fun i => (f i).val), List.length_ofFn, ?_, ?_⟩
  · apply List.nodup_ofFn_ofInjective
    intro i j hij
    exact f.injective (Subtype.ext hij)
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact (f i).property

theorem embeddingSupportedState_bijective (A : Finset α) (ell : Nat) :
    Function.Bijective (embeddingSupportedState A ell) := by
  constructor
  · intro f g he
    have hval := List.ofFn_injective (congrArg Subtype.val he)
    apply DFunLike.ext
    intro i
    exact Subtype.ext (congrFun hval i)
  · rintro ⟨v, hv, hn, hs⟩
    subst ell
    let f : Fin v.length ↪ A :=
      ⟨fun i => ⟨v.get i, hs _ (List.get_mem v i)⟩,
        fun i j hij => hn.get_inj_iff.mp (congrArg Subtype.val hij)⟩
    refine ⟨f, Subtype.ext ?_⟩
    exact List.ofFn_get v

noncomputable def supportedStateEquivEmbedding (A : Finset α) (ell : Nat) :
    supportedOverlapState A ell ≃ (Fin ell ↪ A) :=
  (Equiv.ofBijective (embeddingSupportedState A ell) (embeddingSupportedState_bijective A ell)).symm

noncomputable instance (A : Finset α) (ell : Nat) : Fintype (supportedOverlapState A ell) :=
  Fintype.ofEquiv (Fin ell ↪ A) (supportedStateEquivEmbedding A ell).symm

instance [DecidableEq α] (A : Finset α) (ell : Nat) : DecidableEq (supportedOverlapState A ell) :=
  inferInstanceAs (DecidableEq {v : List α // v.length = ell ∧ v.Nodup ∧ ∀ a ∈ v, a ∈ A})

theorem supportedOverlapState_card (A : Finset α) (ell : Nat) :
    Fintype.card (supportedOverlapState A ell) = A.card.descFactorial ell := by
  rw [Fintype.card_congr (supportedStateEquivEmbedding A ell)]
  simp only [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]

theorem supportedOverlapState_card_factorial (A : Finset α) (ell : Nat) (hl : ell ≤ A.card) :
    (A.card - ell).factorial * Fintype.card (supportedOverlapState A ell) = A.card.factorial := by
  rw [supportedOverlapState_card]
  exact Nat.factorial_mul_descFactorial hl

end SuperpermutationUpperBound
