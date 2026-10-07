import LowerBounds.PFinal
import LowerBounds.PSmallSearch

/-!
# The finite statements on 5 symbols, with the searches evaluated by the kernel

A test of the whole chain of proofs of the search side with no `native_decide`: the searches of
`PSmallSearch.lean` are evaluated by the kernel (`decide +kernel`), and `PRules.lean` turns the
equations into statements about chains, paths, rings and families of vertices on 5 symbols.  The
theorems used are those that `PFinal.lean` uses for 7 symbols, with the arithmetic tables
(`…SearchA`) in place of the compiled tables.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace SuperpermLowerBounds

open PS PS.Small

/-- Chains of words on 5 symbols with at most 3 holes obey `3 3 5 5`. -/
theorem seqCap5 : PS.SeqCapLt 5 0 (PS.capF [M5] 0) 4 :=
  PS.seqCap_of_searchA (by norm_num) (by norm_num) (by norm_num)
    (fun j hj => absurd hj (Nat.not_lt_zero j)) (PS.seqCapLt_zero _ _ _)
    (PS.covered_one chain5_parts)

/-- F0 on 5 symbols: a chain with `x ≤ 3` holes has at most `3 3 5 5` rows. -/
theorem chainCap5 : PS.ChainCapK 5 (fun x => M5.getD x 0) 3 :=
  PS.chainCapK_of_wcap (PS.wcap_of_seqCap seqCap5)

/-- F1 on 5 symbols: a sequence with one link of weight 4 and `x ≤ 1` holes has at most `6 6`
rows. -/
theorem pathCap5 : PS.PathCapK 5 1 (fun x => P5.getD x 0) 1 :=
  PS.pathCapK_of_seqCap (PS.seqCap_of_searchA (caps := [M5, P5]) (by norm_num) (by norm_num)
    (by norm_num)
    (fun j hj => by
      interval_cases j
      exact seqCap5.mono (by norm_num))
    (PS.seqCapLt_zero _ _ _) (PS.covered_one path5))

/-- FR on 5 symbols: a ring with `x ≤ 3` holes has at most `3 1 2 1` rows. -/
theorem ringCap5 : PS.RingCapK 5 (fun x => R5.getD x 0) 3 :=
  PS.ringCapK_of_ringCapT (PS.ringCapT_of_searchA (by norm_num) (by norm_num) (by norm_num)
    seqCap5 (PS.covered_one ring5))

/-- FF on 5 symbols: no chain with 5 rows and at most 2 holes beside a chain with 2 rows and no
hole. -/
theorem noProfile5 : PS.NoProfileK 5 [(5, 2), (2, 0)] :=
  PS.noProfileK_of_searchA (G := 2) (by norm_num) (by norm_num) (by norm_num)
    (PS.wcap_of_seqCap (seqCap5.mono (by norm_num))) (by decide) (by decide)
    (PS.covered_one prof5)

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.chainCap5
#print axioms SuperpermLowerBounds.pathCap5
#print axioms SuperpermLowerBounds.ringCap5
#print axioms SuperpermLowerBounds.noProfile5
