import LowerBounds.F5900Joint
import LowerBounds.J15Final

/-!
# 5,900 for 7 symbols, from the searches (the written proof, section 6)

`covers_5900_of_search`: every word over `Fin 7` that contains all permutations has at least 5,900
letters, if the searches answer `false`: the twelve searches of the proof of 5,899, the searches
for table T' (`KS.EvalsT`: I1, I2, C76, I4, K5 .. K8), the searches for Theorem K (`KS.EvalsK`:
K0 .. K4) and the six searches for the joint statements (`J15.Evals`: S1, S2a1, S2a2, S3, S4, S5).

The parts: `caps_of_search`, `profiles_of_search` (the proof of 5,899), `KS.setB_of_search`,
`KS.tableT_of_search`, `KS.theoremK_of_search` (the kernel alone), `J15.joint_of_search` (the joint
statements), `A15.no_config_135` (the accounting at defect 15) and
`covers_length_gt_of_no_stdConfig` (the model).  No `native_decide`.
-/

namespace SuperpermLowerBounds

open T5899

section

variable {f₀ d₀ n₀ f₁ d₁ n₁ f₂ d₂ n₂ f₃ d₃ n₃ f₄ d₄ n₄ f₅ d₅ n₅ fR dR nR : ℕ}
  {fa da na fb db nb fc dc nc fd dd nd fe de ne : ℕ}

/-- **Every word over `Fin 7` that contains all permutations has at least 5,900 letters**, if the
searches answer `false`. -/
theorem covers_5900_of_search (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
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
    (hT : KS.EvalsT) (hK : KS.EvalsK) (hE : J15.Evals) :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5900 ≤ w.length :=
  covers_5900_of_joint hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ hnR hna hnb hnc hnd hne h0 h1 h2 h3 h4 h5 hR ha hb hc hd he
    hT hK (fun hTT hKK => J15.joint_of_search hTT hKK hE)

end

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_5900_of_search
