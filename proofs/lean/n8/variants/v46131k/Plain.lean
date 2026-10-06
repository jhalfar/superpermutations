import Solution

/-!
The bound for covering words in plain form: a word over eight symbols in which every list of eight
distinct symbols occurs as a factor has at least 46131 letters.  New file (not in
williamechols/superperm8-ge-46130); a bridge from `solution : Statement.Challenge`.
Written @ATTRIBUTION@.  Apache-2.0, as the project.
-/

theorem covering_word_length_ge_46131 :
    ∀ w : List (Fin 8),
      (∀ p : List (Fin 8), p.length = 8 → p.Nodup → ∃ u v, w = u ++ p ++ v) → 46131 ≤ w.length := by
  intro w hw
  apply solution w
  intro p
  exact hw (List.ofFn p) (by simp) (List.nodup_ofFn.mpr p.injective)

#print axioms covering_word_length_ge_46131
