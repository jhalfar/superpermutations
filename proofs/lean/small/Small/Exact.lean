import Small.Upto5
import K6.A6

/-!
# The shortest superpermutations on 1 to 6 symbols

`exact_six`: the shortest word over `Fin 6` that contains every arrangement of the 6 letters as a contiguous part
has 872 letters. The upper bound is Grayzel's word (Robin Houston's word of 872 letters), checked by the kernel in
`superperm6/Superperm6/Witness.lean`; the lower bound is `K6.covers_872` of `K6/`, on top of the model of standard
configurations and Theorems W and N of the proof of 5,899 (`../n7`). `grayzel_six` is the same in Grayzel's own
formulation, and `ssuper_values` collects n = 1 to 6 for `Hunter.Ssuper`.
-/

namespace SmallSuperperm

open SuperpermutationBounds

theorem lower_six : ∀ w : List (Fin 6), Covers w → 872 ≤ w.length :=
  K6.covers_872

theorem exact_six :
    (∃ w : List (Fin 6), Covers w ∧ w.length = 872) ∧ ∀ w : List (Fin 6), Covers w → 872 ≤ w.length :=
  K6.a6_eq_872_covers

/-- Grayzel's formulation of s(6) = 872 (`Superperm6.IsMinimumLength`, with his `IsSuperpermutation`). -/
theorem grayzel_six : Superperm6.IsMinimumLength 872 :=
  K6.a6_eq_872

theorem ssuper_values :
    Hunter.Ssuper 1 = 1 ∧ Hunter.Ssuper 2 = 3 ∧ Hunter.Ssuper 3 = 9 ∧ Hunter.Ssuper 4 = 33 ∧
      Hunter.Ssuper 5 = 153 ∧ Hunter.Ssuper 6 = 872 :=
  ⟨ssuper_upto5.1, ssuper_upto5.2.1, ssuper_upto5.2.2.1, ssuper_upto5.2.2.2.1, ssuper_upto5.2.2.2.2,
    ssuper_eq_of_exact (by norm_num) exact_six⟩

end SmallSuperperm

#print axioms SmallSuperperm.lower_six
#print axioms SmallSuperperm.exact_six
#print axioms SmallSuperperm.grayzel_six
#print axioms SmallSuperperm.ssuper_values
