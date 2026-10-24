import LowerBounds.F5900

/-!
# Audit of level 1 for 5,900 with the finite statements replaced by search equations

`Audit5900.lean` states level 1 with the finite statements as hypotheses.  Here the hypotheses are
search equations: each says that a search answers `false` on every range of its parts.  No
`native_decide` is used; the equations are hypotheses.  `Audit5900Native.lean` is the same with
the equations evaluated.

* the twelve searches of the proof of 5,899 (`Audit5899Search.lean`), engine `PSearch.lean`;
* `KS.EvalsT`: the eight searches behind table T' (chains at 59, at 62 to 75 and at 76 holes, rings
  to 69 holes, sequences with 5, 6, 7, 8 links), and `KS.EvalsK`: the five searches for Theorem K
  on table D (0 to 4 links), engine `KSearch.lean` (`AuditK.lean`);
* `J15.Evals`: the six searches for the joint statements S1, S2a1, S2a2, S3, S4, S5.
-/

open SuperpermLowerBounds

section

/-- A search may be evaluated in ranges of its parts. -/
example (nt : ℕ) (f : ℕ → ℕ → Bool) :
    PS.Covered nt f ↔ ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧ f pa pb = false :=
  Iff.rfl

/-- An evaluated statement of the kernel alone: some fuel, depth of the gate and number of parts
for which every part of the search answers `false`. -/
example (tab : List (List ℕ)) (s lo hi a b h : ℕ) :
    KS.Ev tab s lo hi a b h ↔
      ∃ fuel ds nt, 0 < nt ∧ PS.Covered nt (KS.seqSearch 7 tab s lo hi a b h fuel ds nt) :=
  Iff.rfl

example (M PR : List ℕ) (G : ℕ) :
    KS.EvR M PR G ↔ ∃ fuel ds nt, 0 < nt ∧ PS.Covered nt (PS.ringSearch 7 M PR G fuel ds nt) :=
  Iff.rfl

/-- The searches behind table T'. -/
example :
    KS.EvalsT ↔
      KS.Ev T5900.Ttab 0 59 59 2 3 5 ∧ KS.Ev T5900.Ttab 0 62 75 2 3 5 ∧
        KS.Ev T5900.Ttab 0 76 76 2 3 5 ∧ KS.EvR (T5900.Ttab.getD 0 []) T5900.TRtab 69 ∧
        KS.Ev T5900.Ttab 5 0 60 1 0 0 ∧ KS.Ev T5900.Ttab 6 0 54 1 0 0 ∧
        KS.Ev T5900.Ttab 7 0 48 1 0 0 ∧ KS.Ev T5900.Ttab 8 0 42 1 0 0 :=
  ⟨fun h => ⟨h.c59, h.c62, h.c76, h.ring, h.k5, h.k6, h.k7, h.k8⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2⟩⟩

/-- The searches for Theorem K. -/
example :
    KS.EvalsK ↔
      KS.Ev T5900.Dtab 0 77 90 2 3 5 ∧ KS.Ev T5900.Dtab 1 62 84 10 15 30 ∧
        KS.Ev T5900.Dtab 2 61 78 10 16 25 ∧ KS.Ev T5900.Dtab 3 55 72 10 16 30 ∧
        KS.Ev T5900.Dtab 4 48 66 10 16 25 :=
  ⟨fun h => ⟨h.k0, h.k1, h.k2, h.k3, h.k4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

/-- **Level 1, from search equations.**  The twelve searches of the proof of 5,899 are evaluated
in one range each here; fuel, depth of the gate and number of parts of every search are
arbitrary.  The conclusion is written without any definition of this project. -/
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
      = false)
    (hT : KS.EvalsT) (hK : KS.EvalsK) (hE : J15.Evals) :
    ∀ w : List (Fin 7),
      (∀ p : List (Fin 7), p.length = 7 → p.Nodup → ∃ u v : List (Fin 7), w = u ++ p ++ v) →
      5900 ≤ w.length :=
  covers_5900_of_search hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ hnR hna hnb hnc hnd hne
    (PS.covered_one hF0) (PS.covered_one hF1) (PS.covered_one hF2) (PS.covered_one hF3)
    (PS.covered_one hF4) (PS.covered_one hF5) (PS.covered_one hFR) (PS.covered_one hP1)
    (PS.covered_one hP2) (PS.covered_one hP3) (PS.covered_one hP4) (PS.covered_one hP5) hT hK hE

/-- The finite statements of `Audit5900.lean`, from the searches. -/
example (hB : KS.SetB) (hT : KS.EvalsT) (hK : KS.EvalsK) (hE : J15.Evals) :
    KS.TableT ∧ KS.TheoremK ∧ KS.Joint :=
  have h1 := KS.tableT_of_search hB hT
  have h2 := KS.theoremK_of_search hB hT hK
  ⟨h1, h2, J15.joint_of_search h1 h2 hE⟩

end

/-! ### Axioms -/

#print axioms SuperpermLowerBounds.covers_5900_of_search
#print axioms SuperpermLowerBounds.covers_5900_of_joint
#print axioms SuperpermLowerBounds.covers_5900_of_caps
#print axioms SuperpermLowerBounds.A15.no_config_135
#print axioms SuperpermLowerBounds.KS.setB_of_search
#print axioms SuperpermLowerBounds.KS.tableT_of_search
#print axioms SuperpermLowerBounds.KS.theoremK_of_search
#print axioms SuperpermLowerBounds.J15.joint_of_search
#print axioms SuperpermLowerBounds.caps_of_search
#print axioms SuperpermLowerBounds.profiles_of_search
