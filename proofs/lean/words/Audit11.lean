import Superperm.Upper11
import Challenge

/-!
# Audit file for the word on 11 symbols

The statement is written out without any definition of this project: a list over `Fin 11` of 43,930,578
letters in which every list of 11 different letters occurs as a contiguous part.  Lean is asked to accept the
theorem of `Superperm/Upper11.lean` as a proof of exactly this, and of the same statement in the words of
Pantone's `Challenge.lean`.  Nothing here is a new proof.
-/

open SuperpermutationBounds

example {K : ℕ} (w : List (Fin K)) :
    Covers w = ∀ p : List (Fin K), p.length = K → p.Nodup → ∃ u v : List (Fin K), w = u ++ p ++ v := rfl

example (K bound : ℕ) :
    HasWord K bound = ∃ w : List (Fin K), Covers w ∧ w.length ≤ bound := rfl

/-- Written out in full. -/
example : ∃ w : List (Fin 11),
    (∀ p : List (Fin 11), p.length = 11 → p.Nodup → ∃ u v : List (Fin 11), w = u ++ p ++ v) ∧
      w.length = 43930578 :=
  LiteralSuperperm.exists_word_eleven

/-- In the words of `Challenge.lean`. -/
example : HasWord 11 43930578 := LiteralSuperperm.hasWord_eleven

#print axioms LiteralSuperperm.hasWord_eleven
#print axioms LiteralSuperperm.exists_word_eleven
