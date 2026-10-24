import LowerBounds.KRules
import LowerBounds.KDefs
import LowerBounds.PFinal

/-!
# Table T' and Theorem K from search equations (the written proof, sections 2.2, 2.3, 4.6)

`Ev tab s lo hi a b h`: the statement F(s; lo - 1, hi) on the table `tab` was searched with the
potential `(a, b, h)`: every part of the search lies in a range of parts that answered `false`
(`1, 0, 0` is the plain rule).  `EvR` is the same for the ring search of `PSearch.lean`.

* `EvalsT`: the chain caps at 59, at 62 to 75 and at 76 holes, the ring table to 69 holes, and
  the statements for 5, 6, 7, 8 links, all on table T'.
* `EvalsK`: the statements for 0 to 4 links on table D.
* `tableT_of_search`: set B and `EvalsT` give that T' is valid.
* `theoremK_of_search`: set B, `EvalsT` and `EvalsK` give Theorem K.

The statements for 6, 7 and 8 links read the rows for 5, 6 and 7 links that the statements before
them prove (the written proof reads the closure rows there, which are larger); so they are proved
in the order 5, 6, 7, 8.  The statements for 0 to 4 links are proved in this order, as in section
4.6.
-/

namespace SuperpermLowerBounds

namespace PS

theorem SeqCapLt.congr {k s b : ℕ} {P Q : ℕ → ℕ} (h : SeqCapLt k s P b)
    (hPQ : ∀ x, x < b → P x = Q x) : SeqCapLt k s Q b :=
  fun L h1 h2 h3 h4 => by
    rw [← hPQ _ h4]
    exact h L h1 h2 h3 h4

/-- Two tables for the same sequences, glued at `b`. -/
theorem SeqCapLt.glue {k s b b' : ℕ} {P Q : ℕ → ℕ} (h : SeqCapLt k s P b)
    (h' : SeqCapLt k s Q b') (hQP : ∀ x, b ≤ x → x < b' → Q x ≤ P x) : SeqCapLt k s P b' :=
  fun L h1 h2 h3 h4 => by
    by_cases hb : holesT k L < b
    · exact h L h1 h2 h3 hb
    · exact le_trans (h' L h1 h2 h3 h4) (hQP _ (by omega) h4)

end PS

namespace KS

open T5899 T5900
open PS (SeqCapLt RingCapT capF holesT linksT)

/-- F(s; lo - 1, hi) on `tab` was searched with the potential `(a, b, h)`. -/
def Ev (tab : List (List ℕ)) (s lo hi a b h : ℕ) : Prop :=
  ∃ fuel ds nt, 0 < nt ∧ PS.Covered nt (seqSearch 7 tab s lo hi a b h fuel ds nt)

/-- The ring table `PR` to `G` holes was searched with the chain row `M`. -/
def EvR (M PR : List ℕ) (G : ℕ) : Prop :=
  ∃ fuel ds nt, 0 < nt ∧ PS.Covered nt (PS.ringSearch 7 M PR G fuel ds nt)

/-- The evaluated statements behind table T'. -/
structure EvalsT : Prop where
  c59 : Ev Ttab 0 59 59 2 3 5
  c62 : Ev Ttab 0 62 75 2 3 5
  c76 : Ev Ttab 0 76 76 2 3 5
  ring : EvR (Ttab.getD 0 []) TRtab 69
  k5 : Ev Ttab 5 0 60 1 0 0
  k6 : Ev Ttab 6 0 54 1 0 0
  k7 : Ev Ttab 7 0 48 1 0 0
  k8 : Ev Ttab 8 0 42 1 0 0

/-- The evaluated statements for 0 to 4 links on table D. -/
structure EvalsK : Prop where
  k0 : Ev Dtab 0 77 90 2 3 5
  k1 : Ev Dtab 1 62 84 10 15 30
  k2 : Ev Dtab 2 61 78 10 16 25
  k3 : Ev Dtab 3 55 72 10 16 30
  k4 : Ev Dtab 4 48 66 10 16 25

/-! ### Small lemmas about caps -/

theorem capF_row {A B : List (List ℕ)} {i j : ℕ} (h : A.getD i [] = B.getD j []) :
    capF A i = capF B j := by
  funext x
  simp only [capF, h]

/-- F(s; lo - 1, hi) from its evaluated search. -/
theorem seqCap_of_ev {tab : List (List ℕ)} {s lo hi a b h : ℕ}
    (hlow : ∀ j, j < s → SeqCapLt 7 j (capF tab j) (hi + 1))
    (hprev : SeqCapLt 7 s (capF tab s) lo) (hE : Ev tab s lo hi a b h) :
    SeqCapLt 7 s (capF tab s) (hi + 1) := by
  obtain ⟨fuel, ds, nt, hnt, hc⟩ := hE
  exact seqCap_of_ksearch (by norm_num) (by norm_num) hnt hlow hprev hc

/-! ### Set B from the equations of 5,899 -/

section

variable {f₀ d₀ n₀ f₁ d₁ n₁ f₂ d₂ n₂ f₃ d₃ n₃ f₄ d₄ n₄ f₅ d₅ n₅ fR dR nR : ℕ}

/-- Set B on words, from the searches F0 … F5 and FR of the proof of 5,899. -/
theorem setB_of_search (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
    (hn₄ : 0 < n₄) (hn₅ : 0 < n₅) (hnR : 0 < nR)
    (h0 : PS.Covered n₀ (PS.seqSearch 7 Ptabs 0 0 84 f₀ d₀ n₀))
    (h1 : PS.Covered n₁ (PS.seqSearch 7 Ptabs 1 0 78 f₁ d₁ n₁))
    (h2 : PS.Covered n₂ (PS.seqSearch 7 Ptabs 2 0 72 f₂ d₂ n₂))
    (h3 : PS.Covered n₃ (PS.seqSearch 7 Ptabs 3 0 66 f₃ d₃ n₃))
    (h4 : PS.Covered n₄ (PS.seqSearch 7 Ptabs 4 0 60 f₄ d₄ n₄))
    (h5 : PS.Covered n₅ (PS.seqSearch 7 Ptabs 5 0 54 f₅ d₅ n₅))
    (hR : PS.Covered nR (PS.ringSearch 7 Mtab PRtab 77 fR dR nR)) : SetB := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := seqCaps_of_search hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ h0 h1 h2 h3 h4 h5
  refine ⟨c0, c1, c2, c3, c4, c5, ?_⟩
  have hM : SeqCapLt 7 0 (fun x => Mtab.getD x 0) (77 + 1) := by
    rw [← capF_zero]
    exact c0.mono (by norm_num)
  exact PS.ringCapT_of_search (by norm_num) (by norm_num) hnR hM hR

end

/-! ### Table T' -/

/-- The chain row of T' to 84 holes: set B, the chain caps at 59, at 62 to 75 and at 76 holes. -/
theorem chainT (hB : SetB) (hT : EvalsT) : SeqCapLt 7 0 (capF Ttab 0) 85 := by
  obtain ⟨b0, -⟩ := hB
  have none : ∀ j, j < 0 → SeqCapLt 7 j (capF Ttab j) (59 + 1) :=
    fun j hj => absurd hj (Nat.not_lt_zero j)
  have t59 : SeqCapLt 7 0 (capF Ttab 0) (59 + 1) :=
    seqCap_of_ev none ((b0.mono (b := 59) (by norm_num)).congr (by decide +kernel)) hT.c59
  have t61 : SeqCapLt 7 0 (capF Ttab 0) 62 :=
    t59.glue (b0.mono (b := 62) (by norm_num)) (by decide +kernel)
  have t75 : SeqCapLt 7 0 (capF Ttab 0) (75 + 1) :=
    seqCap_of_ev (fun j hj => absurd hj (Nat.not_lt_zero j)) t61 hT.c62
  have t76 : SeqCapLt 7 0 (capF Ttab 0) (76 + 1) :=
    seqCap_of_ev (fun j hj => absurd hj (Nat.not_lt_zero j)) t75 hT.c76
  exact t76.glue b0 (by decide +kernel)

/-- **Table T' is valid**, given set B and the evaluated statements. -/
theorem tableT_of_search (hB : SetB) (hT : EvalsT) : TableT := by
  have t0 := chainT hB hT
  obtain ⟨-, b1, b2, b3, b4, -, bR⟩ := hB
  have t1 : SeqCapLt 7 1 (capF Ttab 1) 79 := by
    rw [capF_row (show Ttab.getD 1 [] = Ptabs.getD 1 [] from by decide +kernel)]
    exact b1
  have t2 : SeqCapLt 7 2 (capF Ttab 2) 73 := by
    rw [capF_row (show Ttab.getD 2 [] = Ptabs.getD 2 [] from by decide +kernel)]
    exact b2
  have t3 : SeqCapLt 7 3 (capF Ttab 3) 67 := by
    rw [capF_row (show Ttab.getD 3 [] = Ptabs.getD 3 [] from by decide +kernel)]
    exact b3
  have t4 : SeqCapLt 7 4 (capF Ttab 4) 61 := by
    rw [capF_row (show Ttab.getD 4 [] = Ptabs.getD 4 [] from by decide +kernel)]
    exact b4
  have t5 : SeqCapLt 7 5 (capF Ttab 5) (60 + 1) :=
    seqCap_of_ev (fun j hj => by
      interval_cases j
      · exact t0.mono (by norm_num)
      · exact t1.mono (by norm_num)
      · exact t2.mono (by norm_num)
      · exact t3.mono (by norm_num)
      · exact t4) (PS.seqCapLt_zero _ _ _) hT.k5
  have t6 : SeqCapLt 7 6 (capF Ttab 6) (54 + 1) :=
    seqCap_of_ev (fun j hj => by
      interval_cases j
      · exact t0.mono (by norm_num)
      · exact t1.mono (by norm_num)
      · exact t2.mono (by norm_num)
      · exact t3.mono (by norm_num)
      · exact t4.mono (by norm_num)
      · exact t5.mono (by norm_num)) (PS.seqCapLt_zero _ _ _) hT.k6
  have t7 : SeqCapLt 7 7 (capF Ttab 7) (48 + 1) :=
    seqCap_of_ev (fun j hj => by
      interval_cases j
      · exact t0.mono (by norm_num)
      · exact t1.mono (by norm_num)
      · exact t2.mono (by norm_num)
      · exact t3.mono (by norm_num)
      · exact t4.mono (by norm_num)
      · exact t5.mono (by norm_num)
      · exact t6.mono (by norm_num)) (PS.seqCapLt_zero _ _ _) hT.k7
  have t8 : SeqCapLt 7 8 (capF Ttab 8) (42 + 1) :=
    seqCap_of_ev (fun j hj => by
      interval_cases j
      · exact t0.mono (by norm_num)
      · exact t1.mono (by norm_num)
      · exact t2.mono (by norm_num)
      · exact t3.mono (by norm_num)
      · exact t4.mono (by norm_num)
      · exact t5.mono (by norm_num)
      · exact t6.mono (by norm_num)
      · exact t7.mono (by norm_num)) (PS.seqCapLt_zero _ _ _) hT.k8
  refine ⟨fun s hs => ?_, ?_⟩
  · interval_cases s
    · exact t0
    · exact t1
    · exact t2
    · exact t3
    · exact t4
    · exact t5
    · exact t6
    · exact t7
    · exact t8
  · -- the ring row: the ring search to 69 holes, set B and "a ring is a chain" above
    obtain ⟨fuel, ds, nt, hnt, hc⟩ := hT.ring
    have r69 : RingCapT 7 (fun x => TRtab.getD x 0) 69 :=
      PS.ringCapT_of_search (by norm_num) (by norm_num) hnt (t0.mono (by norm_num)) hc
    intro L hL h0 h2 hcl hG
    by_cases h69 : holesT 7 L ≤ 69
    · exact r69 L hL h0 h2 hcl h69
    have hchain : L.length ≤ capF Ttab 0 (holesT 7 L) :=
      t0 L hL (fun x hx => by rw [h0 x hx]; exact Nat.zero_le 1) (PS.linksT_zero h0) (by omega)
    by_cases h77 : holesT 7 L ≤ 77
    · have hring := bR L hL h0 h2 hcl h77
      have e : ∀ x, 70 ≤ x → x ≤ 77 →
          TRtab.getD x 0 = min (PRtab.getD x 0) (capF Ttab 0 x) := by decide +kernel
      show L.length ≤ TRtab.getD (holesT 7 L) 0
      rw [e _ (by omega) h77]
      exact le_min hring hchain
    · have e : ∀ x, 78 ≤ x → x ≤ 84 → TRtab.getD x 0 = capF Ttab 0 x := by decide +kernel
      show L.length ≤ TRtab.getD (holesT 7 L) 0
      rw [e _ (by omega) hG]
      exact hchain

/-! ### Theorem K -/

/-- **Theorem K**, given set B and the evaluated statements. -/
theorem theoremK_of_search (hB : SetB) (hT : EvalsT) (hK : EvalsK) : TheoremK := by
  obtain ⟨hrows, -⟩ := tableT_of_search hB hT
  have t0 : SeqCapLt 7 0 (capF Ttab 0) 85 := hrows 0 (by norm_num)
  have t1 : SeqCapLt 7 1 (capF Ttab 1) 79 := hrows 1 (by norm_num)
  have t2 : SeqCapLt 7 2 (capF Ttab 2) 73 := hrows 2 (by norm_num)
  have t3 : SeqCapLt 7 3 (capF Ttab 3) 67 := hrows 3 (by norm_num)
  have t4 : SeqCapLt 7 4 (capF Ttab 4) 61 := hrows 4 (by norm_num)
  have t5 : SeqCapLt 7 5 (capF Ttab 5) 61 := hrows 5 (by norm_num)
  have t6 : SeqCapLt 7 6 (capF Ttab 6) 55 := hrows 6 (by norm_num)
  have t7 : SeqCapLt 7 7 (capF Ttab 7) 49 := hrows 7 (by norm_num)
  have t8 : SeqCapLt 7 8 (capF Ttab 8) 43 := hrows 8 (by norm_num)
  -- chains: T' to 76 holes, then the levels 77 to 90
  have d0 : SeqCapLt 7 0 (capF Dtab 0) (90 + 1) :=
    seqCap_of_ev (fun j hj => absurd hj (Nat.not_lt_zero j))
      ((t0.mono (b := 77) (by norm_num)).congr (by decide +kernel)) hK.k0
  -- 1 to 4 links: set B below the first level where D is below it, then the levels above
  have d1 : SeqCapLt 7 1 (capF Dtab 1) (84 + 1) :=
    seqCap_of_ev (fun j hj => by
      interval_cases j
      exact d0.mono (by norm_num))
      ((t1.mono (b := 62) (by norm_num)).congr (by decide +kernel)) hK.k1
  have d2 : SeqCapLt 7 2 (capF Dtab 2) (78 + 1) :=
    seqCap_of_ev (fun j hj => by
      interval_cases j
      · exact d0.mono (by norm_num)
      · exact d1.mono (by norm_num))
      ((t2.mono (b := 61) (by norm_num)).congr (by decide +kernel)) hK.k2
  have d3 : SeqCapLt 7 3 (capF Dtab 3) (72 + 1) :=
    seqCap_of_ev (fun j hj => by
      interval_cases j
      · exact d0.mono (by norm_num)
      · exact d1.mono (by norm_num)
      · exact d2.mono (by norm_num))
      ((t3.mono (b := 55) (by norm_num)).congr (by decide +kernel)) hK.k3
  have d4 : SeqCapLt 7 4 (capF Dtab 4) (66 + 1) :=
    seqCap_of_ev (fun j hj => by
      interval_cases j
      · exact d0.mono (by norm_num)
      · exact d1.mono (by norm_num)
      · exact d2.mono (by norm_num)
      · exact d3.mono (by norm_num))
      ((t4.mono (b := 48) (by norm_num)).congr (by decide +kernel)) hK.k4
  intro s hs
  interval_cases s
  · exact d0
  · exact d1
  · exact d2
  · exact d3
  · exact d4
  · rw [capF_row (show Dtab.getD 5 [] = Ttab.getD 5 [] from by decide +kernel)]
    exact t5
  · rw [capF_row (show Dtab.getD 6 [] = Ttab.getD 6 [] from by decide +kernel)]
    exact t6
  · rw [capF_row (show Dtab.getD 7 [] = Ttab.getD 7 [] from by decide +kernel)]
    exact t7
  · rw [capF_row (show Dtab.getD 8 [] = Ttab.getD 8 [] from by decide +kernel)]
    exact t8

end KS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.KS.setB_of_search
#print axioms SuperpermLowerBounds.KS.tableT_of_search
#print axioms SuperpermLowerBounds.KS.theoremK_of_search
