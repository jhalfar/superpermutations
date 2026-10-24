import LowerBounds.A15Final
import LowerBounds.KFinal

/-!
# 5,900 for 7 symbols, from the finite statements and from the searches of the parts that
do not involve the joint statements (the written proof, section 6)

* `covers_5900_of_caps`: every word over `Fin 7` that contains all permutations has at least
  5,900 letters, given the finite statements: the caps and profile statements of the proof of
  5,899 (`Caps`, `Profiles`), table T' (`KS.TableT`), Theorem K (`KS.TheoremK`) and the joint
  statements S1 .. S5 (`KS.Joint`).
* `covers_5900_of_joint`: the same from the twelve searches of the proof of 5,899, the searches
  for table T' (`KS.EvalsT`) and for Theorem K (`KS.EvalsK`), and the joint statements as an
  implication from table T' and Theorem K.

No `native_decide`.
-/

namespace SuperpermLowerBounds

open T5899

/-- **Every word over `Fin 7` that contains all permutations has at least 5,900 letters**, from
the finite statements. -/
theorem covers_5900_of_caps (hC : Caps) (hF : Profiles) (hT : KS.TableT) (hK : KS.TheoremK)
    (hJ : KS.Joint) :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5900 ≤ w.length := by
  have e1 : (7 - 2).factorial + 15 = 135 := by decide
  have e2 : hpv 7 + 15 + 1 = 5900 := by decide
  have h := covers_length_gt_of_no_stdConfig (k := 7) (by norm_num) 15
    (by rw [e1]; exact A15.no_config_135 hC hF hT hK hJ)
  rw [e2] at h
  exact h

section

variable {f₀ d₀ n₀ f₁ d₁ n₁ f₂ d₂ n₂ f₃ d₃ n₃ f₄ d₄ n₄ f₅ d₅ n₅ fR dR nR : ℕ}
  {fa da na fb db nb fc dc nc fd dd nd fe de ne : ℕ}

/-- **5,900 from the searches of 5,899, of table T' and of Theorem K**, with the joint statements
as an implication from table T' and Theorem K. -/
theorem covers_5900_of_joint (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
    (hn₄ : 0 < n₄) (hn₅ : 0 < n₅) (hnR : 0 < nR) (hna : 0 < na) (hnb : 0 < nb) (hnc : 0 < nc)
    (hnd : 0 < nd) (hne : 0 < ne)
    (h0 : PS.Covered n₀ (PS.seqSearch 7 Ptabs 0 0 84 f₀ d₀ n₀))
    (h1 : PS.Covered n₁ (PS.seqSearch 7 Ptabs 1 0 78 f₁ d₁ n₁))
    (h2 : PS.Covered n₂ (PS.seqSearch 7 Ptabs 2 0 72 f₂ d₂ n₂))
    (h3 : PS.Covered n₃ (PS.seqSearch 7 Ptabs 3 0 66 f₃ d₃ n₃))
    (h4 : PS.Covered n₄ (PS.seqSearch 7 Ptabs 4 0 60 f₄ d₄ n₄))
    (h5 : PS.Covered n₅ (PS.seqSearch 7 Ptabs 5 0 54 f₅ d₅ n₅))
    (hR : PS.Covered nR (PS.ringSearch 7 Mtab PRtab 77 fR dR nR))
    (ha : PS.Covered na (PS.profSearch 7 Mtab [(66, 36), (66, 36)] fa da na))
    (hb : PS.Covered nb (PS.profSearch 7 Mtab [(50, 26), (50, 26)] fb db nb))
    (hc : PS.Covered nc (PS.profSearch 7 Mtab [(63, 34), (34, 16)] fc dc nc))
    (hd : PS.Covered nd (PS.profSearch 7 Mtab [(66, 36), (31, 14)] fd dd nd))
    (he : PS.Covered ne (PS.profSearch 7 Mtab [(31, 14), (31, 14), (34, 16), (34, 16)] fe de ne))
    (hT : KS.EvalsT) (hK : KS.EvalsK) (hJ : KS.TableT → KS.TheoremK → KS.Joint) :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5900 ≤ w.length := by
  have hC := caps_of_search hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ hnR h0 h1 h2 h3 h4 h5 hR
  have hF := profiles_of_search hn₀ hna hnb hnc hnd hne h0 ha hb hc hd he
  have hB := KS.setB_of_search hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ hnR h0 h1 h2 h3 h4 h5 hR
  have hTT := KS.tableT_of_search hB hT
  have hKK := KS.theoremK_of_search hB hT hK
  exact covers_5900_of_caps hC hF hTT hKK (hJ hTT hKK)

end

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_5900_of_caps
#print axioms SuperpermLowerBounds.covers_5900_of_joint
