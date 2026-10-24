import LowerBounds.F5901
import LowerBounds.F5900Joint
import LowerBounds.K16Final
import LowerBounds.J16Final

/-!
# 5,901 for 7 symbols, from the searches (part D16 of my plan of the Lean proof)

`covers_5901_of_search`: every word over `Fin 7` that contains all permutations has at least 5,901
letters, if the searches answer `false`: the twelve searches of the proof of 5,899, the searches for
table T' (`KS.EvalsT`) and for Theorem K (`KS.EvalsK`) of 5,900, the eleven kernel searches of defect 16
(`K16.Evals`: K0 .. K10) and the joint searches of Table C (`J16.Evals`: T1, the ten T2 runs, T3', T4',
T5, T6', T7, T8, T9' and the ring search for RX).

The parts: `caps_of_search`, `profiles_of_search` (5,899), `KS.setB_of_search`, `KS.tableT_of_search`,
`KS.theoremK_of_search` (5,900), `K16.theoremK16_of_search` (B16, with Lemma CL from Theorem K),
`J16.joint_of_search` (C16) and `covers_5901_of_statements` (A16).  No `native_decide`.
-/

namespace SuperpermLowerBounds

open T5899

section

variable {f₀ d₀ n₀ f₁ d₁ n₁ f₂ d₂ n₂ f₃ d₃ n₃ f₄ d₄ n₄ f₅ d₅ n₅ fR dR nR : ℕ}
  {fa da na fb db nb fc dc nc fd dd nd fe de ne : ℕ}

/-- **Every word over `Fin 7` that contains all permutations has at least 5,901 letters**, if the
searches answer `false`. -/
theorem covers_5901_of_search (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
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
    (hT : KS.EvalsT) (hK : KS.EvalsK) (hK16 : K16.Evals) (hJ16 : J16.Evals) :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5901 ≤ w.length := by
  have hC := caps_of_search hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ hnR h0 h1 h2 h3 h4 h5 hR
  have hF := profiles_of_search hn₀ hna hnb hnc hnd hne h0 ha hb hc hd he
  have hB := KS.setB_of_search hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ hnR h0 h1 h2 h3 h4 h5 hR
  have hTT := KS.tableT_of_search hB hT
  have hKK := KS.theoremK_of_search hB hT hK
  have hK16' := K16.theoremK16_of_search hKK hK16
  exact covers_5901_of_statements hC hF hTT hK16' (J16.joint_of_search hTT hK16' hJ16)

end

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_5901_of_search
