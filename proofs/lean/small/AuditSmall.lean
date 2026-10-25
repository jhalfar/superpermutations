import Small.Exact

/-!
# The six statements with nothing of this repository in them

The theorems of `Small/Upto5.lean` and `Small/Exact.lean` once more, with Pantone's `Covers` written out: every
list of n different letters of `Fin n` is a contiguous part `w = u ++ p ++ v` of the word `w`. Each proof is the
theorem of `Small/` itself; Lean accepts it because the two statements are the same after unfolding `Covers`. So
to know what is proven, it is enough to read this file and the Lean core definitions of `List`, `Fin`, `Nodup`.
-/

theorem audit_one :
    (∃ w : List (Fin 1), (∀ p : List (Fin 1), p.length = 1 → p.Nodup → ∃ u v, w = u ++ p ++ v) ∧
      w.length = 1) ∧
    ∀ w : List (Fin 1), (∀ p : List (Fin 1), p.length = 1 → p.Nodup → ∃ u v, w = u ++ p ++ v) →
      1 ≤ w.length :=
  SmallSuperperm.exact_one

theorem audit_two :
    (∃ w : List (Fin 2), (∀ p : List (Fin 2), p.length = 2 → p.Nodup → ∃ u v, w = u ++ p ++ v) ∧
      w.length = 3) ∧
    ∀ w : List (Fin 2), (∀ p : List (Fin 2), p.length = 2 → p.Nodup → ∃ u v, w = u ++ p ++ v) →
      3 ≤ w.length :=
  SmallSuperperm.exact_two

theorem audit_three :
    (∃ w : List (Fin 3), (∀ p : List (Fin 3), p.length = 3 → p.Nodup → ∃ u v, w = u ++ p ++ v) ∧
      w.length = 9) ∧
    ∀ w : List (Fin 3), (∀ p : List (Fin 3), p.length = 3 → p.Nodup → ∃ u v, w = u ++ p ++ v) →
      9 ≤ w.length :=
  SmallSuperperm.exact_three

theorem audit_four :
    (∃ w : List (Fin 4), (∀ p : List (Fin 4), p.length = 4 → p.Nodup → ∃ u v, w = u ++ p ++ v) ∧
      w.length = 33) ∧
    ∀ w : List (Fin 4), (∀ p : List (Fin 4), p.length = 4 → p.Nodup → ∃ u v, w = u ++ p ++ v) →
      33 ≤ w.length :=
  SmallSuperperm.exact_four

theorem audit_five :
    (∃ w : List (Fin 5), (∀ p : List (Fin 5), p.length = 5 → p.Nodup → ∃ u v, w = u ++ p ++ v) ∧
      w.length = 153) ∧
    ∀ w : List (Fin 5), (∀ p : List (Fin 5), p.length = 5 → p.Nodup → ∃ u v, w = u ++ p ++ v) →
      153 ≤ w.length :=
  SmallSuperperm.exact_five

theorem audit_six :
    (∃ w : List (Fin 6), (∀ p : List (Fin 6), p.length = 6 → p.Nodup → ∃ u v, w = u ++ p ++ v) ∧
      w.length = 872) ∧
    ∀ w : List (Fin 6), (∀ p : List (Fin 6), p.length = 6 → p.Nodup → ∃ u v, w = u ++ p ++ v) →
      872 ≤ w.length :=
  SmallSuperperm.exact_six

#print axioms audit_one
#print axioms audit_two
#print axioms audit_three
#print axioms audit_four
#print axioms audit_five
#print axioms audit_six
