import Superperm.Upper
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange

/-!
# The same statements with permutations as bijections

Two further Lean projects state lower bounds for words over `Fin n` with permutations as
`Equiv.Perm (Fin n)`, written out by `List.ofFn`:

* `jlebar/superperm7-ge-5898` (Lean 4.30): `∀ w, IsSuperpermutation w → 5898 ≤ w.length`, where
  `IsSuperpermutation w` is `∀ p : Equiv.Perm (Fin 7), List.ofFn p <:+: w`; it also proves
  `∃ w, IsSuperpermutation w ∧ w.length = 5906`.
* `williamechols/superperm8-ge-46130` (Lean 4.30): `∀ w, ContainsAllEightPermutations w →
  46130 ≤ w.length`, where `ContainsAllEightPermutations w` is
  `∀ p : Equiv.Perm (Fin 8), ∃ before after, w = before ++ List.ofFn p ++ after`.

Both notions are Pantone's `Covers` (`covers_iff_forall_perm`, `covers_iff_forall_perm_infix`),
so the literal words give upper bounds in those vocabularies too, and those lower bounds are
lower bounds for covering words.  The two projects use another Lean and Mathlib version and
are not imported here; the statements below use only Mathlib's own notions.
-/

namespace LiteralSuperperm

open SuperpermutationBounds

/-- A duplicate-free list of all `K` letters is a permutation written out. -/
theorem exists_perm_ofFn {K : ℕ} (l : List (Fin K)) (hlen : l.length = K) (hnd : l.Nodup) :
    ∃ p : Equiv.Perm (Fin K), List.ofFn p = l := by
  let f : Fin K → Fin K := fun i => l[i.val]'(by rw [hlen]; exact i.isLt)
  have hinj : Function.Injective f := by
    intro i j hij
    have h := (hnd.getElem_inj_iff (hi := by rw [hlen]; exact i.isLt)
      (hj := by rw [hlen]; exact j.isLt)).mp hij
    exact Fin.ext h
  refine ⟨Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩, ?_⟩
  apply List.ext_getElem
  · rw [List.length_ofFn, hlen]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    rfl

/-- Pantone's `Covers`, with the permutations as bijections of `Fin K`. -/
theorem covers_iff_forall_perm {K : ℕ} (w : List (Fin K)) :
    Covers w ↔ ∀ p : Equiv.Perm (Fin K), ∃ before after : List (Fin K),
      w = before ++ List.ofFn p ++ after := by
  constructor
  · intro h p
    exact h (List.ofFn p) (List.length_ofFn) (List.nodup_ofFn.mpr p.injective)
  · intro h l hlen hnd
    obtain ⟨p, rfl⟩ := exists_perm_ofFn l hlen hnd
    exact h p

/-- The same with the factor relation `<:+:`. -/
theorem covers_iff_forall_perm_infix {K : ℕ} (w : List (Fin K)) :
    Covers w ↔ ∀ p : Equiv.Perm (Fin K), List.ofFn p <:+: w := by
  rw [covers_iff_forall_perm]
  constructor
  · intro h p
    obtain ⟨u, v, huv⟩ := h p
    exact ⟨u, v, huv.symm⟩
  · intro h p
    obtain ⟨u, v, huv⟩ := h p
    exact ⟨u, v, huv.symm⟩

/-- Seven symbols, 5,905 letters, in the form of `jlebar/superperm7-ge-5898` (whose own upper
statement has 5,906). -/
theorem exists_word_seven_perm :
    ∃ w : List (Fin 7), (∀ p : Equiv.Perm (Fin 7), List.ofFn p <:+: w) ∧ w.length = 5905 :=
  ⟨N7.word, (covers_iff_forall_perm_infix _).mp N7.word_covers, N7.word_length⟩

/-- Eight symbols, 46,181 letters, in the form of `williamechols/superperm8-ge-46130`. -/
theorem exists_word_eight_perm :
    ∃ w : List (Fin 8), (∀ p : Equiv.Perm (Fin 8), ∃ before after : List (Fin 8),
      w = before ++ List.ofFn p ++ after) ∧ w.length = 46181 :=
  ⟨N8.word, (covers_iff_forall_perm _).mp N8.word_covers, N8.word_length⟩

/-- Nine symbols, 408,731 letters. -/
theorem exists_word_nine_perm :
    ∃ w : List (Fin 9), (∀ p : Equiv.Perm (Fin 9), List.ofFn p <:+: w) ∧ w.length = 408731 :=
  ⟨N9.word, (covers_iff_forall_perm_infix _).mp N9.word_covers, N9.word_length⟩

/-- A lower bound stated for permutations as bijections is a lower bound for covering words. -/
theorem lower_of_perm_form {K L : ℕ}
    (h : ∀ w : List (Fin K), (∀ p : Equiv.Perm (Fin K), ∃ before after : List (Fin K),
      w = before ++ List.ofFn p ++ after) → L ≤ w.length) :
    ∀ w : List (Fin K), Covers w → L ≤ w.length :=
  fun w hw => h w ((covers_iff_forall_perm w).mp hw)

end LiteralSuperperm

#print axioms LiteralSuperperm.covers_iff_forall_perm
#print axioms LiteralSuperperm.exists_word_seven_perm
#print axioms LiteralSuperperm.exists_word_eight_perm
#print axioms LiteralSuperperm.exists_word_nine_perm
