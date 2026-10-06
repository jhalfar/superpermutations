import LowerBounds.SFinalSmall
import Challenge

/-!
# Audit file for the lower bounds of Theorem C from the small certificates

`LowerBounds/SFinalSmall.lean` is a generated file: Theorem C applied to the small certificates of the
finite search, which the default level of `build.sh` checks.  Here its seven best bounds are written out by
hand, without any definition of this project: a list over `Fin k` in which every list of `k` different letters
occurs as a contiguous part has at least so many letters.  Lean is asked to accept the theorems of the
generated file as proofs of exactly these statements, so a generator that wrote other numbers would not get
past this file.  Nothing here is a new proof.  `AuditCFinal.lean` does the same for all 27 certificates, which
give larger values for 8, 11, 13 and 14 symbols.
-/

open SuperpermutationBounds

example {K : ℕ} (w : List (Fin K)) :
    Covers w = ∀ p : List (Fin K), p.length = K → p.Nodup → ∃ u v : List (Fin K), w = u ++ p ++ v := rfl

/-- The seven values, written out in full. -/
example :
    (∀ w : List (Fin 8), (∀ p : List (Fin 8), p.length = 8 → p.Nodup → ∃ u v : List (Fin 8), w = u ++ p ++ v) →
      46132 ≤ w.length) ∧
    (∀ w : List (Fin 9), (∀ p : List (Fin 9), p.length = 9 → p.Nodup → ∃ u v : List (Fin 9), w = u ++ p ++ v) →
      408469 ≤ w.length) ∧
    (∀ w : List (Fin 10), (∀ p : List (Fin 10), p.length = 10 → p.Nodup → ∃ u v : List (Fin 10), w = u ++ p ++ v) →
      4033378 ≤ w.length) ∧
    (∀ w : List (Fin 11), (∀ p : List (Fin 11), p.length = 11 → p.Nodup → ∃ u v : List (Fin 11), w = u ++ p ++ v) →
      43917901 ≤ w.length) ∧
    (∀ w : List (Fin 12), (∀ p : List (Fin 12), p.length = 12 → p.Nodup → ∃ u v : List (Fin 12), w = u ++ p ++ v) →
      522622378 ≤ w.length) ∧
    (∀ w : List (Fin 13), (∀ p : List (Fin 13), p.length = 13 → p.Nodup → ∃ u v : List (Fin 13), w = u ++ p ++ v) →
      6746626601 ≤ w.length) ∧
    (∀ w : List (Fin 14), (∀ p : List (Fin 14), p.length = 14 → p.Nodup → ∃ u v : List (Fin 14), w = u ++ p ++ v) →
      93891140217 ≤ w.length) :=
  ⟨SuperpermLowerBounds.covers_lower_bound_8_small, SuperpermLowerBounds.covers_lower_bound_9_small,
    SuperpermLowerBounds.covers_lower_bound_10_small, SuperpermLowerBounds.covers_lower_bound_11_small,
    SuperpermLowerBounds.covers_lower_bound_12_small, SuperpermLowerBounds.covers_lower_bound_13_small,
    SuperpermLowerBounds.covers_lower_bound_14_small⟩

/-- The same seven values for the length of the shortest superpermutation as the Hunter-Raudvere library
defines it. -/
example :
    46132 ≤ Hunter.Ssuper 8 ∧ 408469 ≤ Hunter.Ssuper 9 ∧ 4033378 ≤ Hunter.Ssuper 10 ∧
    43917901 ≤ Hunter.Ssuper 11 ∧ 522622378 ≤ Hunter.Ssuper 12 ∧ 6746626601 ≤ Hunter.Ssuper 13 ∧
    93891140217 ≤ Hunter.Ssuper 14 :=
  ⟨SuperpermLowerBounds.ssuper_lower_bound_8_small, SuperpermLowerBounds.ssuper_lower_bound_9_small,
    SuperpermLowerBounds.ssuper_lower_bound_10_small, SuperpermLowerBounds.ssuper_lower_bound_11_small,
    SuperpermLowerBounds.ssuper_lower_bound_12_small, SuperpermLowerBounds.ssuper_lower_bound_13_small,
    SuperpermLowerBounds.ssuper_lower_bound_14_small⟩

#print axioms SuperpermLowerBounds.covers_lower_bound_8_small
#print axioms SuperpermLowerBounds.covers_lower_bound_9_small
#print axioms SuperpermLowerBounds.covers_lower_bound_10_small
#print axioms SuperpermLowerBounds.covers_lower_bound_11_small
#print axioms SuperpermLowerBounds.covers_lower_bound_12_small
#print axioms SuperpermLowerBounds.covers_lower_bound_13_small
#print axioms SuperpermLowerBounds.covers_lower_bound_14_small
#print axioms SuperpermLowerBounds.ssuper_lower_bound_8_small
#print axioms SuperpermLowerBounds.ssuper_lower_bound_9_small
#print axioms SuperpermLowerBounds.ssuper_lower_bound_10_small
#print axioms SuperpermLowerBounds.ssuper_lower_bound_11_small
#print axioms SuperpermLowerBounds.ssuper_lower_bound_12_small
#print axioms SuperpermLowerBounds.ssuper_lower_bound_13_small
#print axioms SuperpermLowerBounds.ssuper_lower_bound_14_small
