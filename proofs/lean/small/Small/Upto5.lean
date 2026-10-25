import Small.Words
import LowerBounds.TheoremAWords
import Hunter.Paper

/-!
# The shortest superpermutations on 1 to 5 symbols

For n = 1, ..., 5 the shortest word over `Fin n` that contains every arrangement of the n letters as a contiguous
part has 1, 3, 9, 33 and 153 letters. Each `exact_` theorem states both halves with Pantone's `Covers`: a word of
that length exists, and no word with `Covers` is shorter. `ssuper_upto5` says the same with `Hunter.Ssuper`, the
least length as the Hunter-Raudvere library defines it.

Where each half comes from:

* upper bounds: the words of `Small/Words.lean`, checked by the kernel;
* n = 1, 2: `lower_one`, `lower_two` of `Small/Words.lean`, a few lines each;
* n = 3, 4: `Hunter.Paper.pointwise_3`, `pointwise_4` of the Hunter-Raudvere library (Corollary 28 of their
  paper), turned into statements about `Covers` by `SuperpermBridge.hunter_le_ssuper_iff` of `../words`;
* n = 5: Theorem A of `../lower` at k = 5 (`SuperpermLowerBounds.covers_kisic_numerical_bounds`).
-/

namespace SmallSuperperm

open SuperpermutationBounds

theorem lower_three : ∀ w : List (Fin 3), Covers w → 9 ≤ w.length :=
  (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp Hunter.Paper.pointwise_3

theorem lower_four : ∀ w : List (Fin 4), Covers w → 33 ≤ w.length :=
  (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp Hunter.Paper.pointwise_4

theorem lower_five : ∀ w : List (Fin 5), Covers w → 153 ≤ w.length :=
  SuperpermLowerBounds.covers_kisic_numerical_bounds.1

theorem exact_one :
    (∃ w : List (Fin 1), Covers w ∧ w.length = 1) ∧ ∀ w : List (Fin 1), Covers w → 1 ≤ w.length :=
  ⟨upper_one, lower_one⟩

theorem exact_two :
    (∃ w : List (Fin 2), Covers w ∧ w.length = 3) ∧ ∀ w : List (Fin 2), Covers w → 3 ≤ w.length :=
  ⟨upper_two, lower_two⟩

theorem exact_three :
    (∃ w : List (Fin 3), Covers w ∧ w.length = 9) ∧ ∀ w : List (Fin 3), Covers w → 9 ≤ w.length :=
  ⟨upper_three, lower_three⟩

theorem exact_four :
    (∃ w : List (Fin 4), Covers w ∧ w.length = 33) ∧ ∀ w : List (Fin 4), Covers w → 33 ≤ w.length :=
  ⟨upper_four, lower_four⟩

theorem exact_five :
    (∃ w : List (Fin 5), Covers w ∧ w.length = 153) ∧ ∀ w : List (Fin 5), Covers w → 153 ≤ w.length :=
  ⟨upper_five, lower_five⟩

/-- From the two halves to the value of `Hunter.Ssuper`. -/
theorem ssuper_eq_of_exact {k L : ℕ} (hk : 0 < k)
    (h : (∃ w : List (Fin k), Covers w ∧ w.length = L) ∧ ∀ w : List (Fin k), Covers w → L ≤ w.length) :
    Hunter.Ssuper k = L := by
  obtain ⟨⟨w, hw, hl⟩, hlow⟩ := h
  apply le_antisymm
  · exact (SuperpermBridge.hunter_hasWord_iff hk).mp ⟨w, hw, hl.le⟩
  · exact (SuperpermBridge.hunter_le_ssuper_iff hk).mpr hlow

theorem ssuper_upto5 :
    Hunter.Ssuper 1 = 1 ∧ Hunter.Ssuper 2 = 3 ∧ Hunter.Ssuper 3 = 9 ∧ Hunter.Ssuper 4 = 33 ∧
      Hunter.Ssuper 5 = 153 :=
  ⟨ssuper_eq_of_exact (by norm_num) exact_one, ssuper_eq_of_exact (by norm_num) exact_two,
    ssuper_eq_of_exact (by norm_num) exact_three, ssuper_eq_of_exact (by norm_num) exact_four,
    ssuper_eq_of_exact (by norm_num) exact_five⟩

end SmallSuperperm

#print axioms SmallSuperperm.exact_one
#print axioms SmallSuperperm.exact_two
#print axioms SmallSuperperm.exact_three
#print axioms SmallSuperperm.exact_four
#print axioms SmallSuperperm.exact_five
#print axioms SmallSuperperm.ssuper_upto5
