import LowerBounds.SFinal
import Challenge

/-!
# Audit file for the lower bounds of Theorem C without a hypothesis

`LowerBounds/SFinal.lean` is a generated file: Theorem C applied to the certificates of the finite search.
Here its seven best bounds are written out by hand, without any definition of this project: a list over `Fin k`
in which every list of `k` different letters occurs as a contiguous part has at least so many letters.  Lean is
asked to accept the theorems of the generated file as proofs of exactly these statements, so a generator that
wrote other numbers would not get past this file.  Nothing here is a new proof.
-/

open SuperpermutationBounds

example {K : ℕ} (w : List (Fin K)) :
    Covers w = ∀ p : List (Fin K), p.length = K → p.Nodup → ∃ u v : List (Fin K), w = u ++ p ++ v := rfl

/-- The seven values, written out in full. -/
example :
    (∀ w : List (Fin 8), (∀ p : List (Fin 8), p.length = 8 → p.Nodup → ∃ u v : List (Fin 8), w = u ++ p ++ v) →
      46133 ≤ w.length) ∧
    (∀ w : List (Fin 9), (∀ p : List (Fin 9), p.length = 9 → p.Nodup → ∃ u v : List (Fin 9), w = u ++ p ++ v) →
      408469 ≤ w.length) ∧
    (∀ w : List (Fin 10), (∀ p : List (Fin 10), p.length = 10 → p.Nodup → ∃ u v : List (Fin 10), w = u ++ p ++ v) →
      4033378 ≤ w.length) ∧
    (∀ w : List (Fin 11), (∀ p : List (Fin 11), p.length = 11 → p.Nodup → ∃ u v : List (Fin 11), w = u ++ p ++ v) →
      43917903 ≤ w.length) ∧
    (∀ w : List (Fin 12), (∀ p : List (Fin 12), p.length = 12 → p.Nodup → ∃ u v : List (Fin 12), w = u ++ p ++ v) →
      522622378 ≤ w.length) ∧
    (∀ w : List (Fin 13), (∀ p : List (Fin 13), p.length = 13 → p.Nodup → ∃ u v : List (Fin 13), w = u ++ p ++ v) →
      6746626957 ≤ w.length) ∧
    (∀ w : List (Fin 14), (∀ p : List (Fin 14), p.length = 14 → p.Nodup → ∃ u v : List (Fin 14), w = u ++ p ++ v) →
      93891141008 ≤ w.length) :=
  ⟨SuperpermLowerBounds.covers_lower_bound_8, SuperpermLowerBounds.covers_lower_bound_9,
    SuperpermLowerBounds.covers_lower_bound_10, SuperpermLowerBounds.covers_lower_bound_11,
    SuperpermLowerBounds.covers_lower_bound_12, SuperpermLowerBounds.covers_lower_bound_13,
    SuperpermLowerBounds.covers_lower_bound_14⟩

/-- The same seven values for the length of the shortest superpermutation as the Hunter-Raudvere library
defines it. -/
example :
    46133 ≤ Hunter.Ssuper 8 ∧ 408469 ≤ Hunter.Ssuper 9 ∧ 4033378 ≤ Hunter.Ssuper 10 ∧
    43917903 ≤ Hunter.Ssuper 11 ∧ 522622378 ≤ Hunter.Ssuper 12 ∧ 6746626957 ≤ Hunter.Ssuper 13 ∧
    93891141008 ≤ Hunter.Ssuper 14 :=
  ⟨SuperpermLowerBounds.ssuper_lower_bound_8, SuperpermLowerBounds.ssuper_lower_bound_9,
    SuperpermLowerBounds.ssuper_lower_bound_10, SuperpermLowerBounds.ssuper_lower_bound_11,
    SuperpermLowerBounds.ssuper_lower_bound_12, SuperpermLowerBounds.ssuper_lower_bound_13,
    SuperpermLowerBounds.ssuper_lower_bound_14⟩

#print axioms SuperpermLowerBounds.covers_lower_bound_8
#print axioms SuperpermLowerBounds.covers_lower_bound_9
#print axioms SuperpermLowerBounds.covers_lower_bound_10
#print axioms SuperpermLowerBounds.covers_lower_bound_11
#print axioms SuperpermLowerBounds.covers_lower_bound_12
#print axioms SuperpermLowerBounds.covers_lower_bound_13
#print axioms SuperpermLowerBounds.covers_lower_bound_14
#print axioms SuperpermLowerBounds.ssuper_lower_bound_8
#print axioms SuperpermLowerBounds.ssuper_lower_bound_9
#print axioms SuperpermLowerBounds.ssuper_lower_bound_10
#print axioms SuperpermLowerBounds.ssuper_lower_bound_11
#print axioms SuperpermLowerBounds.ssuper_lower_bound_12
#print axioms SuperpermLowerBounds.ssuper_lower_bound_13
#print axioms SuperpermLowerBounds.ssuper_lower_bound_14
