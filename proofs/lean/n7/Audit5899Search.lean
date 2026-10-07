import LowerBounds.PFinal

/-!
# Audit of level 1 for 5,899 with the finite statements replaced by search equations

`Audit5899.lean` states level 1 with the finite statements F0–F5, FR, FF as hypotheses.  Here the
hypotheses are twelve equations about the search function of `LowerBounds/PSearch.lean` (a file
with no imports): each says that a search answers `false`.  No `native_decide` is used; the
equations are hypotheses.  `Audit5899Native.lean` is the same with the equations evaluated.

The proof that a search which answers `false` gives the finite statement is in `PSound.lean`
(the engine is complete), `PSeq.lean`, `PEnc.lean` (the tables), `PLevels.lean` (the three kinds
of rules) and `PRules.lean`; `PFinal.lean` puts them together.
-/

open SuperpermLowerBounds

section

/-- A search may be evaluated in ranges of its parts: every part `tp < nt` lies in a range
`pa ≤ tp < pb` whose evaluation answered `false`. -/
example (nt : ℕ) (f : ℕ → ℕ → Bool) :
    PS.Covered nt f ↔ ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧ f pa pb = false :=
  Iff.rfl

/-- **Level 1, from search equations.**  Every search is evaluated in one range here (`0 ≤ tp <
n`); fuel `f`, depth of the gate `d` and number of parts `n > 0` of every search are arbitrary.
The conclusion is written without any definition of this project. -/
example (f₀ d₀ n₀ f₁ d₁ n₁ f₂ d₂ n₂ f₃ d₃ n₃ f₄ d₄ n₄ f₅ d₅ n₅ fR dR nR : ℕ)
    (fa da na fb db nb fc dc nc fd dd nd fe de ne : ℕ)
    (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃) (hn₄ : 0 < n₄) (hn₅ : 0 < n₅)
    (hnR : 0 < nR) (hna : 0 < na) (hnb : 0 < nb) (hnc : 0 < nc) (hnd : 0 < nd) (hne : 0 < ne)
    (hF0 : PS.seqSearch 7 T5899.Ptabs 0 0 84 f₀ d₀ n₀ 0 n₀ = false)
    (hF1 : PS.seqSearch 7 T5899.Ptabs 1 0 78 f₁ d₁ n₁ 0 n₁ = false)
    (hF2 : PS.seqSearch 7 T5899.Ptabs 2 0 72 f₂ d₂ n₂ 0 n₂ = false)
    (hF3 : PS.seqSearch 7 T5899.Ptabs 3 0 66 f₃ d₃ n₃ 0 n₃ = false)
    (hF4 : PS.seqSearch 7 T5899.Ptabs 4 0 60 f₄ d₄ n₄ 0 n₄ = false)
    (hF5 : PS.seqSearch 7 T5899.Ptabs 5 0 54 f₅ d₅ n₅ 0 n₅ = false)
    (hFR : PS.ringSearch 7 T5899.Mtab T5899.PRtab 77 fR dR nR 0 nR = false)
    (hP1 : PS.profSearch 7 T5899.Mtab [(66, 36), (66, 36)] fa da na 0 na = false)
    (hP2 : PS.profSearch 7 T5899.Mtab [(50, 26), (50, 26)] fb db nb 0 nb = false)
    (hP3 : PS.profSearch 7 T5899.Mtab [(63, 34), (34, 16)] fc dc nc 0 nc = false)
    (hP4 : PS.profSearch 7 T5899.Mtab [(66, 36), (31, 14)] fd dd nd 0 nd = false)
    (hP5 : PS.profSearch 7 T5899.Mtab [(31, 14), (31, 14), (34, 16), (34, 16)] fe de ne 0 ne
      = false) :
    ∀ w : List (Fin 7),
      (∀ p : List (Fin 7), p.length = 7 → p.Nodup → ∃ u v : List (Fin 7), w = u ++ p ++ v) →
      5899 ≤ w.length :=
  covers_5899_of_search hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ hnR hna hnb hnc hnd hne
    (PS.covered_one hF0) (PS.covered_one hF1) (PS.covered_one hF2) (PS.covered_one hF3)
    (PS.covered_one hF4) (PS.covered_one hF5) (PS.covered_one hFR) (PS.covered_one hP1)
    (PS.covered_one hP2) (PS.covered_one hP3) (PS.covered_one hP4) (PS.covered_one hP5)

/-- The finite statements themselves, from the searches: `Caps` (F0–F5, FR) and `Profiles` (FF)
are the hypotheses of `Audit5899.lean`. -/
example (f₀ d₀ n₀ f₁ d₁ n₁ f₂ d₂ n₂ f₃ d₃ n₃ f₄ d₄ n₄ f₅ d₅ n₅ fR dR nR : ℕ)
    (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃) (hn₄ : 0 < n₄) (hn₅ : 0 < n₅)
    (hnR : 0 < nR)
    (h0 : PS.Covered n₀ (PS.seqSearch 7 T5899.Ptabs 0 0 84 f₀ d₀ n₀))
    (h1 : PS.Covered n₁ (PS.seqSearch 7 T5899.Ptabs 1 0 78 f₁ d₁ n₁))
    (h2 : PS.Covered n₂ (PS.seqSearch 7 T5899.Ptabs 2 0 72 f₂ d₂ n₂))
    (h3 : PS.Covered n₃ (PS.seqSearch 7 T5899.Ptabs 3 0 66 f₃ d₃ n₃))
    (h4 : PS.Covered n₄ (PS.seqSearch 7 T5899.Ptabs 4 0 60 f₄ d₄ n₄))
    (h5 : PS.Covered n₅ (PS.seqSearch 7 T5899.Ptabs 5 0 54 f₅ d₅ n₅))
    (hR : PS.Covered nR (PS.ringSearch 7 T5899.Mtab T5899.PRtab 77 fR dR nR)) :
    ChainCap T5899.Mf 84 ∧ (∀ s, 1 ≤ s → s ≤ 5 → PathCap s (T5899.Pf s) (84 - 6 * s)) ∧
      RingCap T5899.PRf 77 :=
  have hC := caps_of_search hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ hnR h0 h1 h2 h3 h4 h5 hR
  ⟨hC.chain, hC.path, hC.ring⟩

end

/-! ### Axioms -/

#print axioms SuperpermLowerBounds.covers_5899_of_search
#print axioms SuperpermLowerBounds.caps_of_search
#print axioms SuperpermLowerBounds.profiles_of_search
#print axioms SuperpermLowerBounds.PS.not_ruleAlong_of_search
#print axioms SuperpermLowerBounds.PS.stmt_of_searchB
#print axioms SuperpermLowerBounds.PS.seqCap_level
#print axioms SuperpermLowerBounds.PS.ringCap_of_stmt
#print axioms SuperpermLowerBounds.PS.noProfileK_of_stmt
