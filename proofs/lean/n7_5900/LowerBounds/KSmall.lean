import LowerBounds.KRules
import LowerBounds.KSmallSearch

/-!
# The chain of proofs of part B on 5 symbols, with the searches evaluated by the kernel

From the equations of `KSmallSearch.lean` (proved by `decide +kernel`) and the theorems of
`KRules.lean`: the chain caps on 5 symbols to 3 holes, once from one search for all levels and
once level by level, and the cap for sequences with one link of weight 4.  No `native_decide`.
-/

namespace SuperpermLowerBounds
namespace KS
namespace Small

open PS (SeqCapLt capF)

/-- Chains on 5 symbols with at most 3 holes have at most 3, 3, 5, 5 rows (one search, three
parts). -/
theorem chainCap5 : SeqCapLt 5 0 (capF [M5] 0) (3 + 1) :=
  seqCap_of_ksearchA (by norm_num) (by norm_num) (show 0 < 3 by norm_num)
    (fun j hj => absurd hj (Nat.not_lt_zero j)) (fun _ _ _ _ h => absurd h (Nat.not_lt_zero _))
    (fun tp htp => ⟨0, 3, Nat.zero_le tp, htp, chain5_parts⟩)

/-- The same, from the levels 0 to 2 and then the level 3 above them. -/
theorem chainCap5_levels : SeqCapLt 5 0 (capF [M5] 0) (3 + 1) := by
  have c2 : SeqCapLt 5 0 (capF [M5] 0) (2 + 1) :=
    seqCap_of_ksearchA (by norm_num) (by norm_num) (show 0 < 1 by norm_num)
      (fun j hj => absurd hj (Nat.not_lt_zero j)) (fun _ _ _ _ h => absurd h (Nat.not_lt_zero _))
      (fun tp htp => ⟨0, 1, Nat.zero_le tp, htp, chain5⟩)
  exact seqCap_of_ksearchA (by norm_num) (by norm_num) (show 0 < 1 by norm_num)
    (fun j hj => absurd hj (Nat.not_lt_zero j)) c2
    (fun tp htp => ⟨0, 1, Nat.zero_le tp, htp, chain5_level⟩)

/-- Sequences on 5 symbols with one link of weight 4 and at most 1 hole have at most 6 rows. -/
theorem pathCap5 : SeqCapLt 5 1 (capF [M5, P5] 1) (1 + 1) :=
  seqCap_of_ksearchA (by norm_num) (by norm_num) (show 0 < 1 by norm_num)
    (fun j hj => by
      have hj0 : j = 0 := by omega
      subst hj0
      exact fun L h1 h2 h3 h4 => chainCap5 L h1 h2 h3 (by omega))
    (fun _ _ _ _ h => absurd h (Nat.not_lt_zero _))
    (fun tp htp => ⟨0, 1, Nat.zero_le tp, htp, path5⟩)

end Small
end KS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.KS.Small.chainCap5
#print axioms SuperpermLowerBounds.KS.Small.chainCap5_levels
#print axioms SuperpermLowerBounds.KS.Small.pathCap5
