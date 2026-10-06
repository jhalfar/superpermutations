import Superperm.TwoSided12
import Challenge

/-!
# Audit file for the word on 12 symbols

The statement is written out without any definition of this project: a list over `Fin 12` of 522,737,175
letters in which every list of 12 different letters occurs as a contiguous part.  Lean is asked to accept the
theorem of `Superperm/Upper12.lean` as a proof of exactly this, and of the same statement in the words of
Pantone's `Challenge.lean`; the lower side of `Superperm/TwoSided12.lean` is restated in the same way.
Nothing here is a new proof.
-/

open SuperpermutationBounds

example {K : ℕ} (w : List (Fin K)) :
    Covers w = ∀ p : List (Fin K), p.length = K → p.Nodup → ∃ u v : List (Fin K), w = u ++ p ++ v := rfl

example (K bound : ℕ) :
    HasWord K bound = ∃ w : List (Fin K), Covers w ∧ w.length ≤ bound := rfl

/-- Written out in full. -/
example : ∃ w : List (Fin 12),
    (∀ p : List (Fin 12), p.length = 12 → p.Nodup → ∃ u v : List (Fin 12), w = u ++ p ++ v) ∧
      w.length = 522737175 :=
  LiteralSuperperm.exists_word_twelve

/-- In the words of `Challenge.lean`. -/
example : HasWord 12 522737175 := LiteralSuperperm.hasWord_twelve

/-- Both sides about one definition: the word, and Liu's lower bound for every covering word. -/
example : (∃ w : List (Fin 12),
      (∀ p : List (Fin 12), p.length = 12 → p.Nodup → ∃ u v : List (Fin 12), w = u ++ p ++ v) ∧
        w.length = 522737175) ∧
    ∀ w : List (Fin 12),
      (∀ p : List (Fin 12), p.length = 12 → p.Nodup → ∃ u v : List (Fin 12), w = u ++ p ++ v) →
        522610764 ≤ w.length :=
  SuperpermBridge.words_twelve

#print axioms LiteralSuperperm.hasWord_twelve
#print axioms LiteralSuperperm.exists_word_twelve
#print axioms SuperpermBridge.words_twelve
