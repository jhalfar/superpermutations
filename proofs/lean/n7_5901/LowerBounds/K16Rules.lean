import LowerBounds.K16Pot
import LowerBounds.KRules

/-!
# From search equations with Rule JS to the statements F(s; lo - 1, hi)

As `KRules.lean` of 5,900, for the search of `K16Search.lean`: the tables are the functions they
tabulate (`KS.codeT_eq`, `KS.maskG_bit`, `KS.cutT_of_cutF`, reused), so a search all of whose parts answer
`false` proves `KStmt16` (`kstmt16_of_search`, compiled; `kstmt16_of_searchA`, arithmetic tables), and then
F(s; lo - 1, hi) holds (`seqCap_of_k16search`, `seqCap_of_k16searchA`), with or without Rule JS.
-/

namespace SuperpermLowerBounds
namespace K16

open PS (TRow IsSeq holesT linksT SeqCapLt capF)
open KS (codeF potN potS cutF a1F a2F uF segF codeT maskT cutT tabA maskG rowsR)

section Search

variable {k : ℕ} {caps : List (List ℕ)} {s lo hi a b h : ℕ} {js : Bool} {fuel ds nt : ℕ}

/-- The compiled search, with its tables written out. -/
theorem seqSearch_eq (k : ℕ) (caps : List (List ℕ)) (s lo hi a b h : ℕ) (js : Bool)
    (fuel ds nt pa pb : ℕ) :
    seqSearch k caps s lo hi a b h js fuel ds nt pa pb =
      KS.par (fun tp => searchPart (fun i => (PS.ciTab k (PS.permCodes k k))[i]!)
        (fun i => (PS.nxtTab k (PS.permCodes k k))[i]!)
        (fun i => (PS.sdTab k 3 (PS.permCodes k k))[i]!)
        (fun i => (PS.sdTab k 4 (PS.permCodes k k))[i]!)
        ((PS.permCodes k k).idxOf (PS.idcF k)) (k - 1)
        (codeT (s + 1) (rowsR caps s hi) (hi + 1)
          (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (codeF (capF caps) s lo hi)))
        (maskT (s + 1) (rowsR caps s hi + 1) (hi + 1) (maskG (fun _ _ _ => 1) 0 0 0 (k - 1))
          (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (fun t r d =>
            maskG (codeT (s + 1) (rowsR caps s hi) (hi + 1)
              (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (codeF (capF caps) s lo hi)))
              t r d (k - 1))))
        (potN a b h) (potS a b h)
        (cutT (s + 1) (rowsR caps s hi + 1) (hi + 1)
          (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (a1F (capF caps) s lo hi a b h))
          (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1)
            (a2F (uF (capF caps) s a b h) (segF (capF caps) s a b h) (capF caps) s lo hi a b h)))
        js (PS.permCodes k k).length fuel (fuel - ds) nt tp) pa pb := by
  simp only [seqSearch, KS.look2_tab2, rowsR]

/-- **The compiled search with Rule JS proves `KStmt16`** (`4 ≤ k ≤ 15`). -/
theorem kstmt16_of_search (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      seqSearch k caps s lo hi a b h js fuel ds nt pa pb = false) :
    KStmt16 k js (codeF (capF caps) s lo hi) (potN a b h) (potS a b h)
      (cutF (a1F (capF caps) s lo hi a b h)
        (a2F (uF (capF caps) s a b h) (segF (capF caps) s a b h) (capF caps) s lo hi a b h)) := by
  have hcode := KS.codeT_eq (lo := lo) (KS.rowsR_spec caps s hi)
  have hstmt : KStmt16 k js (codeT (s + 1) (rowsR caps s hi) (hi + 1)
      (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (codeF (capF caps) s lo hi)))
      (potN a b h) (potS a b h)
      (cutT (s + 1) (rowsR caps s hi + 1) (hi + 1)
        (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (a1F (capF caps) s lo hi a b h))
        (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1)
          (a2F (uF (capF caps) s a b h) (segF (capF caps) s a b h) (capF caps) s lo hi a b
            h))) := by
    refine kstmt16_of_parts (PS.encB_enc k hk hk15) (by omega) hnt
      (mask := maskT (s + 1) (rowsR caps s hi + 1) (hi + 1) (maskG (fun _ _ _ => 1) 0 0 0 (k - 1))
        (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (fun t r d =>
          maskG (codeT (s + 1) (rowsR caps s hi) (hi + 1)
            (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (codeF (capF caps) s lo hi)))
            t r d (k - 1))))
      (sz := (PS.permCodes k k).length) (fuel := fuel) (fg := fuel - ds) ?_ ?_
    · intro t r d j hj hne
      unfold maskT
      by_cases hin : (decide (t < s + 1) && decide (r < rowsR caps s hi + 1)
          && decide (d < hi + 1)) = true
      · rw [if_pos hin]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
        rw [KS.tabA_get _ _ _ _ hin.1.1 hin.1.2 hin.2]
        exact KS.maskG_bit _ t r d (k - 1) j hj (by
          rw [show k - 1 - 1 - j = k - 2 - j from by omega]
          exact hne)
      · rw [if_neg hin]
        exact KS.maskG_bit (fun _ _ _ => 1) 0 0 0 (k - 1) j hj (by simp)
    · intro tp htp
      obtain ⟨pa, pb, h1, h2, hsr⟩ := hs tp htp
      rw [seqSearch_eq] at hsr
      exact KS.par_false hsr tp h1 h2
  intro x rest hL hjs hrule
  exact hstmt x rest hL hjs (KS.ruleK_mono (fun t r d => by rw [hcode])
    (fun t r d m M hc => KS.cutT_of_cutF t r d m M hc) rest _ _ _ _ _ hrule)

/-- **The search with arithmetic tables and Rule JS proves `KStmt16`.** -/
theorem kstmt16_of_searchA (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      seqSearchA k caps s lo hi a b h js fuel ds nt pa pb = false) :
    KStmt16 k js (codeF (capF caps) s lo hi) (potN a b h) (potS a b h)
      (cutF (a1F (capF caps) s lo hi a b h)
        (a2F (uF (capF caps) s a b h) (segF (capF caps) s a b h) (capF caps) s lo hi a b h)) :=
  kstmt16_of_parts (PS.encA k hk hk15) (by omega) hnt
    (mask := fun t r d => maskG (codeF (capF caps) s lo hi) t r d (k - 1))
    (sz := k ^ (k - 1)) (fuel := fuel) (fg := fuel - ds)
    (fun t r d j hj hne => KS.maskG_bit _ t r d (k - 1) j hj (by
      rw [show k - 1 - 1 - j = k - 2 - j from by omega]
      exact hne))
    (fun tp htp => by
      obtain ⟨pa, pb, h1, h2, hsr⟩ := hs tp htp
      exact KS.par_false hsr tp h1 h2)

/-- **F(s; lo - 1, hi) from the compiled search with Rule JS** (`5 ≤ k ≤ 15`). -/
theorem seqCap_of_k16search (hk : 5 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hlow : ∀ j, j < s → SeqCapLt k j (capF caps j) (hi + 1))
    (hprev : SeqCapLt k s (capF caps s) lo)
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      seqSearch k caps s lo hi a b h js fuel ds nt pa pb = false) :
    SeqCapLt k s (capF caps s) (hi + 1) :=
  seqCap_levelK16 hk hlow hprev (kstmt16_of_search (by omega) hk15 hnt hs)

/-- **F(s; lo - 1, hi) from the search with arithmetic tables and Rule JS.** -/
theorem seqCap_of_k16searchA (hk : 5 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hlow : ∀ j, j < s → SeqCapLt k j (capF caps j) (hi + 1))
    (hprev : SeqCapLt k s (capF caps s) lo)
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      seqSearchA k caps s lo hi a b h js fuel ds nt pa pb = false) :
    SeqCapLt k s (capF caps s) (hi + 1) :=
  seqCap_levelK16 hk hlow hprev (kstmt16_of_searchA (by omega) hk15 hnt hs)

end Search

end K16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K16.seqCap_of_k16search
#print axioms SuperpermLowerBounds.K16.seqCap_of_k16searchA
