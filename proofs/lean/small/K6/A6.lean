import K6.Final872
import Superperm6.Witness

/-!
# a(6) = 872, checked by the kernel alone

Two standard statements of "superpermutation" on 6 symbols, shown to agree:

* Grayzel's (`Superperm6.IsSuperpermutation`, his `Basic.lean`): every permutation `p` of `Fin 6`
  occurs, as the word `List.ofFn p`, as a contiguous part (`<:+:`) of the word;
* Pantone's (`SuperpermutationBounds.Covers`, his `Challenge.lean`): every list of 6 different
  letters of `Fin 6` is `w = u ++ p ++ v` for some `u`, `v`.

`isSuperpermutation_iff_covers` proves them equivalent.  The upper bound is Grayzel's witness
(`Superperm6.verified_upper_bound`, a word of 872 letters, checked by the kernel in the kernel-only
version of his `Witness.lean` in `../superperm6/`); the lower bound is `covers_872`.  Together:
`a6_eq_872 : Superperm6.IsMinimumLength 872`, Grayzel's own formulation of `s(6) = 872`, and
`a6_eq_872_covers`, the same with `Covers`.
-/

namespace K6

open Superperm6

/-- The permutation of `Fin 6` whose word is a list of 6 different letters. -/
noncomputable def permOfList (p : List (Fin 6)) (hl : p.length = 6) (hn : p.Nodup) : Perm6 :=
  Equiv.ofBijective (fun i => p.get ⟨i.val, by rw [hl]; exact i.isLt⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun i j h => by
        have := (List.Nodup.get_inj_iff hn).mp h
        exact Fin.ext (by simpa using this), rfl⟩)

theorem permWord_permOfList (p : List (Fin 6)) (hl : p.length = 6) (hn : p.Nodup) :
    permWord (permOfList p hl hn) = p := by
  apply List.ext_getElem
  · simp [permWord, hl]
  · intro n h1 h2
    simp only [permWord, List.getElem_ofFn]
    rfl

/-- **Grayzel's and Pantone's definitions agree.** -/
theorem isSuperpermutation_iff_covers (w : Word) :
    IsSuperpermutation w ↔ SuperpermutationBounds.Covers w := by
  constructor
  · intro h p hl hn
    have hocc := h (permOfList p hl hn)
    unfold Occurs at hocc
    rw [permWord_permOfList] at hocc
    obtain ⟨u, v, huv⟩ := hocc
    exact ⟨u, v, huv.symm⟩
  · intro h p
    obtain ⟨u, v, huv⟩ := h (permWord p) (permWord_length p) (permWord_nodup p)
    exact ⟨u, v, huv.symm⟩

/-- **Every superpermutation on 6 symbols has at least 872 letters** (Grayzel's statement). -/
theorem a6_lower : ∀ w : Word, IsSuperpermutation w → 872 ≤ w.length :=
  fun w hw => covers_872 w ((isSuperpermutation_iff_covers w).mp hw)

/-- **a(6) = 872**, in Grayzel's formulation `IsMinimumLength 872`. -/
theorem a6_eq_872 : IsMinimumLength 872 := ⟨verified_upper_bound, a6_lower⟩

/-- **a(6) = 872**, with Pantone's `Covers`. -/
theorem a6_eq_872_covers :
    (∃ w : List (Fin 6), SuperpermutationBounds.Covers w ∧ w.length = 872) ∧
      ∀ w : List (Fin 6), SuperpermutationBounds.Covers w → 872 ≤ w.length := by
  obtain ⟨w, hw, hl⟩ := verified_upper_bound
  exact ⟨⟨w, (isSuperpermutation_iff_covers w).mp hw, hl⟩, covers_872⟩

end K6

#print axioms K6.isSuperpermutation_iff_covers
#print axioms K6.a6_lower
#print axioms K6.a6_eq_872
#print axioms K6.a6_eq_872_covers
