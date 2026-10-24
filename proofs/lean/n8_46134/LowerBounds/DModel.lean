import LowerBounds.SModel
import LowerBounds.SBridge
import LowerBounds.DSound
import LowerBounds.DCapacity

/-!
# The three hypotheses for 8 symbols, from the prefix search

`DSound.lean` gives, from a search that answers `false`, the prefix statement
`S.PStatement k keep bad`: no chain of words all of whose non-empty proper prefixes satisfy `keep`
is `bad`.  This file turns prefix statements into statements about all chains.

* **Line rule** (`S.wline_of_pstatement`): the prefix statement for `S.lineKeep a b c`,
  `S.lineBad a b c` gives `a r ≤ b δ + c` for every chain of words.  Proof: in a chain above the
  line with the fewest pieces, every proper part is a shorter chain and satisfies the line; so a
  proper prefix has `a r - b δ ≤ c`, and `> 0` because the rest of the chain has `a r - b δ ≤ c`.
* **Zone rule** (`S.wzone_of_pstatement`): given the two lines, the prefix statement for
  `S.zoneKeep`, `S.zoneBad` gives the zone statement.  Proof: for a chain in the zone, the rest
  after a proper prefix is a chain, so it satisfies both lines, and the prefix is within the
  widths of the zone.

Both use only that a contiguous part of a chain is a chain (`S.IsWChain.infix`).  Then:

* `ModelLine k a b c`, `ModelZone8`: the statements for the model chains of `SModelDef.lean`
  (`modelLine_of_wline`, `modelZone8_of_wzone`);
* `chainLine_of_model`, `zone8_of_model`: the statements for the exact weight-three chains of
  strongly exitless paths, through `chain_isModelChain` (`SBridge.lean`);
* `modelLine_of_search`, `modelZone8_of_search`: all of it from search equations.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

namespace S

/-- The line `a r ≤ b δ + c` for every chain of words. -/
def WLine (k a b c : ℕ) : Prop :=
  ∀ L : List (List (List ℕ)), IsWChain k L → a * (wdef k L).length ≤ b * (wdef k L).sum + c

/-- **The line rule is complete.** -/
theorem wline_of_pstatement {k a b c : ℕ}
    (h : PStatement k (lineKeep a b c) (lineBad a b c)) : WLine k a b c := by
  suffices hmain : ∀ n : ℕ, ∀ L : List (List (List ℕ)), L.length = n → IsWChain k L →
      a * (wdef k L).length ≤ b * (wdef k L).sum + c from fun L => hmain L.length L rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L hlen hL
    by_cases hne : L = []
    · subst hne
      simp [wdef]
    · by_contra hnb
      have hkeep : ∀ u w, wdef k L = u ++ w → u ≠ [] → w ≠ [] →
          lineKeep a b c u.length u.sum = true := by
        intro u w hds hu hw
        have hds' : List.map (fun P : List (List ℕ) => k - 1 - P.length) L = u ++ w := hds
        obtain ⟨Lu, Lw, rfl, hLu, hLw⟩ := List.map_eq_append_iff.mp hds'
        have hlu : Lu.length = u.length := by rw [← hLu, List.length_map]
        have hlw : Lw.length = w.length := by rw [← hLw, List.length_map]
        have hupos : 0 < u.length := List.length_pos_iff.mpr hu
        have hwpos : 0 < w.length := List.length_pos_iff.mpr hw
        have hn : Lu.length + Lw.length = n := by rw [← hlen, List.length_append]
        have h1 := ih Lu.length (by omega) Lu rfl (hL.infix ⟨[], Lw, by simp⟩)
        have h2 := ih Lw.length (by omega) Lw rfl (hL.infix ⟨Lu, [], by simp⟩)
        have e1 : wdef k Lu = u := hLu
        have e2 : wdef k Lw = w := hLw
        rw [e1] at h1
        rw [e2] at h2
        rw [hds, List.length_append, List.sum_append, Nat.mul_add, Nat.mul_add] at hnb
        simp only [lineKeep, Bool.and_eq_true, decide_eq_true_eq]
        constructor <;> omega
      have hbad := h L hL hne hkeep
      simp only [lineBad, decide_eq_false_iff_not] at hbad
      omega

/-- The zone statement for chains of words: a chain within `u₁` of the first line and within
`u₂` of the second line is on the first line. -/
def WZone (k a₁ b₁ c₁ u₁ a₂ b₂ c₂ u₂ : ℕ) : Prop :=
  ∀ L : List (List (List ℕ)), IsWChain k L →
    b₁ * (wdef k L).sum + c₁ ≤ a₁ * (wdef k L).length + u₁ →
    b₂ * (wdef k L).sum + c₂ ≤ a₂ * (wdef k L).length + u₂ →
    a₁ * (wdef k L).length = b₁ * (wdef k L).sum + c₁

/-- **The zone rule is complete**, given the two lines. -/
theorem wzone_of_pstatement {k a₁ b₁ c₁ u₁ a₂ b₂ c₂ u₂ : ℕ} (hu : u₁ < c₁)
    (h1 : WLine k a₁ b₁ c₁) (h2 : WLine k a₂ b₂ c₂)
    (h : PStatement k (zoneKeep a₁ b₁ u₁ a₂ b₂ u₂) (zoneBad a₁ b₁ c₁ u₁ a₂ b₂ c₂ u₂)) :
    WZone k a₁ b₁ c₁ u₁ a₂ b₂ c₂ u₂ := by
  intro L hL hz1 hz2
  have hne : L ≠ [] := by
    rintro rfl
    simp [wdef] at hz1
    omega
  have hkeep : ∀ u w, wdef k L = u ++ w → u ≠ [] → w ≠ [] →
      zoneKeep a₁ b₁ u₁ a₂ b₂ u₂ u.length u.sum = true := by
    intro u w hds _ _
    have hds' : List.map (fun P : List (List ℕ) => k - 1 - P.length) L = u ++ w := hds
    obtain ⟨Lu, Lw, rfl, hLu, hLw⟩ := List.map_eq_append_iff.mp hds'
    have hw1 := h1 Lw (hL.infix ⟨Lu, [], by simp⟩)
    have hw2 := h2 Lw (hL.infix ⟨Lu, [], by simp⟩)
    have e2 : wdef k Lw = w := hLw
    rw [e2] at hw1 hw2
    rw [hds, List.length_append, List.sum_append, Nat.mul_add, Nat.mul_add] at hz1 hz2
    simp only [zoneKeep, Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega
  have hbad := h L hL hne hkeep
  by_contra hneq
  have htrue : zoneBad a₁ b₁ c₁ u₁ a₂ b₂ c₂ u₂ (wdef k L).length (wdef k L).sum = true := by
    simp only [zoneBad, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    exact ⟨⟨hz1, hz2⟩, hneq⟩
  rw [hbad] at htrue
  cases htrue

end S

/-! ### Model chains -/

/-- The line `a r ≤ b δ + c` for every model chain on `k` symbols. -/
def ModelLine (k a b c : ℕ) : Prop :=
  ∀ L : List (List (Vtx k)), IsModelChain k L → a * L.length ≤ b * (modelDeficits k L).sum + c

/-- (H3) for the model chains on 8 symbols: `4 r - 9 δ ≥ 54` and `17 r - 38 δ ≥ 258` imply
`4 r - 9 δ = 56`. -/
def ModelZone8 : Prop :=
  ∀ L : List (List (Vtx 8)), IsModelChain 8 L →
    9 * (modelDeficits 8 L).sum + 54 ≤ 4 * L.length →
    38 * (modelDeficits 8 L).sum + 258 ≤ 17 * L.length →
    4 * L.length = 9 * (modelDeficits 8 L).sum + 56

theorem modelDeficits_length {k : ℕ} (L : List (List (Vtx k))) :
    (modelDeficits k L).length = L.length := by
  simp [modelDeficits]

theorem modelLine_of_wline {k a b c : ℕ} (h : S.WLine k a b c) : ModelLine k a b c := by
  intro L hL
  have h1 := h _ (isWChain_of_modelChain hL)
  rw [← modelDeficits_eq, modelDeficits_length] at h1
  exact h1

theorem modelZone8_of_wzone (h : S.WZone 8 4 9 56 2 17 38 264 6) : ModelZone8 := by
  intro L hL hz1 hz2
  have h1 := h _ (isWChain_of_modelChain hL)
  rw [← modelDeficits_eq, modelDeficits_length] at h1
  exact h1 (by omega) (by omega)

/-! ### Chains of strongly exitless paths -/

/-- A line for model chains is a chain line. -/
theorem chainLine_of_model {k a b c : ℕ} (hk : 4 ≤ k) (h : ModelLine k a b c) :
    ChainLine k a b c := by
  intro p hp chain
  have h1 := h _ (chain_isModelChain hk hp chain)
  rw [chain_modelDeficits, List.length_map] at h1
  exact h1

/-- (H3) for model chains gives (H3). -/
theorem zone8_of_model (h : ModelZone8) : Zone8 := by
  intro p hp chain hz1 hz2
  have h1 := h _ (chain_isModelChain (by norm_num) hp chain)
  rw [chain_modelDeficits, List.length_map] at h1
  exact h1 hz1 hz2

/-! ### From search equations -/

/-- A line search that answers `false` proves the line for model chains (`3 ≤ k ≤ 15`). -/
theorem modelLine_of_search {k sz a b c fuel ds nt : ℕ} (hk : 3 ≤ k) (hk15 : k ≤ 15)
    (hnt : 0 < nt) (hs : S.lineSearch k sz a b c fuel ds nt = false) : ModelLine k a b c :=
  modelLine_of_wline (S.wline_of_pstatement (S.pstatement_of_search hk hk15 hnt hs))

/-- The two line searches and the zone search prove (H3) for model chains. -/
theorem modelZone8_of_search {sz₁ f₁ d₁ n₁ sz₂ f₂ d₂ n₂ sz₃ f₃ d₃ n₃ : ℕ} (hn₁ : 0 < n₁)
    (hn₂ : 0 < n₂) (hn₃ : 0 < n₃) (h1 : S.lineSearch 8 sz₁ 4 9 56 f₁ d₁ n₁ = false)
    (h2 : S.lineSearch 8 sz₂ 17 38 264 f₂ d₂ n₂ = false)
    (h3 : S.zoneSearch 8 sz₃ 4 9 56 2 17 38 264 6 f₃ d₃ n₃ = false) : ModelZone8 :=
  modelZone8_of_wzone (S.wzone_of_pstatement (by norm_num)
    (S.wline_of_pstatement (S.pstatement_of_search (by norm_num) (by norm_num) hn₁ h1))
    (S.wline_of_pstatement (S.pstatement_of_search (by norm_num) (by norm_num) hn₂ h2))
    (S.pstatement_of_search (by norm_num) (by norm_num) hn₃ h3))

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.S.wline_of_pstatement
#print axioms SuperpermLowerBounds.S.wzone_of_pstatement
#print axioms SuperpermLowerBounds.chainLine_of_model
#print axioms SuperpermLowerBounds.zone8_of_model
#print axioms SuperpermLowerBounds.modelLine_of_search
#print axioms SuperpermLowerBounds.modelZone8_of_search
