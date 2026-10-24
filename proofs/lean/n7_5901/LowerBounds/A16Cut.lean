import LowerBounds.A15Cut

/-!
# The accounting at defect 16: Lemma ACC16, the excess, the number of chains, the cut at the dear seams
(the written proof `proofs/n7_5901/PROOF_5901.md`, sections 2.1 to 2.3)

* `acc_value`, `acc_weight` (Lemma ACC16): for a valid configuration of cost at most 136 the values of the
  components add up to at least 40 and the weights to at most 96.
* `eps_le_two` (Lemma EPS16): the excess of the link costs is at most 2.
* `famC_length_le` (not in the written proof, which does not need it): the family of the configuration has
  at most 11 chains, so every piece has at most 10 links.
* `cutG` (the cut of Lemma CUT16): the trails of a list of rows are groups, each joined by links of weight
  4, and the number of groups is at most one more than the excess (the groups are separated by the dear
  seams, the seams of weight at least 5).
-/

namespace SuperpermLowerBounds
namespace A16

open Hunter PreimageChain T5899

variable {c : NConfig 7}

/-! ### Lemma ACC16 -/

/-- **Lemma ACC16, values.** -/
theorem acc_value (hv : c.Valid) (hc : c.cost ≤ 136) :
    40 ≤ valR c.kernel (rX c.kernel) + (c.hanging.map vH).sum := by
  have hlen := hv.len_le (by norm_num : 2 ≤ 7)
  have hE := entries_length_ge hv
  have hEl : c.entries.length =
      (rowsEntries c.kernel).length + (c.hanging.flatMap fun H => rowsEntries H.rows).length := by
    unfold NConfig.entries
    rw [List.length_append]
  have hC : c.cost = (c.kernel.length + rX c.kernel) + (c.hanging.map NHanging.cost).sum := rfl
  rw [valR_eq hlen.1, sum_vH c.hanging hlen.2]
  have h1 : (720 : ℤ) ≤ ((rowsEntries c.kernel).length : ℤ) +
      ((c.hanging.flatMap fun H => rowsEntries H.rows).length : ℤ) := by
    exact_mod_cast (hEl ▸ hE)
  have h2 : ((c.kernel.length + rX c.kernel : ℕ) : ℤ) +
      (((c.hanging.map NHanging.cost).sum : ℕ) : ℤ) ≤ 136 := by
    exact_mod_cast (hC ▸ hc)
  linarith

/-- **Lemma ACC16, weights.** -/
theorem acc_weight (hv : c.Valid) (hc : c.cost ≤ 136) :
    wtR c.kernel (rX c.kernel) + (c.hanging.map wH).sum ≤ 96 := by
  have hlen := hv.len_le (by norm_num : 2 ≤ 7)
  have hE := entries_length_ge hv
  have hEl : c.entries.length =
      (rowsEntries c.kernel).length + (c.hanging.flatMap fun H => rowsEntries H.rows).length := by
    unfold NConfig.entries
    rw [List.length_append]
  have hC : c.cost = (c.kernel.length + rX c.kernel) + (c.hanging.map NHanging.cost).sum := rfl
  have h0 := wtR_eq hlen.1 (rX c.kernel)
  have h3 := sum_wH c.hanging hlen.2
  have h1 : (720 : ℤ) ≤ ((rowsEntries c.kernel).length : ℤ) +
      ((c.hanging.flatMap fun H => rowsEntries H.rows).length : ℤ) := by
    exact_mod_cast (hEl ▸ hE)
  have h2 : ((c.kernel.length + rX c.kernel : ℕ) : ℤ) +
      (((c.hanging.map NHanging.cost).sum : ℕ) : ℤ) ≤ 136 := by
    exact_mod_cast (hC ▸ hc)
  have : ((wtR c.kernel (rX c.kernel) + (c.hanging.map wH).sum : ℕ) : ℤ) ≤ 96 := by
    rw [Nat.cast_add]
    linarith
  exact_mod_cast this

/-! ### Lemma EPS16 and the number of chains -/

/-- **Lemma EPS16.**  The excess of the link costs is at most 2. -/
theorem eps_le_two (hC : Caps) (hF : Profiles) (hv : c.Valid) (hc : c.cost ≤ 136) :
    epsC c ≤ 2 := by
  have hav := acc_value hv hc
  have haw := acc_weight hv hc
  obtain ⟨n1, n2⟩ := famC_num hv
  have hfam := famC_trailFam hv
  by_contra hne
  have h3 : 3 ≤ epsC c := by omega
  have hW : lW (prs (famC c)) ≤ 84 := by omega
  have hE := family_le_49 hC.chain hF hfam hW
  have h3' : (3 : ℤ) ≤ (epsC c : ℤ) := by exact_mod_cast h3
  linarith

/-- A family of at least 12 trails of weight at most 102 has value at most 30. -/
theorem family_le_30 (h0 : ChainCap Mf 84) {S : List (List (NRow 7))} (h : TrailFam 7 S)
    (hW : lW (prs S) ≤ 102) (h12 : 12 ≤ S.length) : lE (prs S) ≤ 30 := by
  have hlen : (prs S).length = S.length := by
    unfold prs
    rw [List.length_map]
  have hx : ∀ p ∈ prs S, p.1 ≤ 84 := by
    intro p hp
    have h1 := lW_erase hp
    have h2 := lW_ge ((prs S).erase p)
    have h3 := List.length_erase_of_mem hp
    omega
  have hok : ∀ p ∈ prs S, p.2 ≤ 2 * p.1 + 5 := by
    intro p hp
    have hp84 := hx p hp
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hp
    have h1 : A.length ≤ Mf (rowsHoles 7 A) :=
      chain_cap_rows h0 (h.trails A hA) (h.classes.sublist (rowsEntries_sublist_flatten hA)) hp84
    have h2 : Mf (rowsHoles 7 A) ≤ 2 * rowsHoles 7 A + 5 := A15.M_lin _ hp84
    exact le_trans h1 h2
  have h1 := A15.lE_lin (prs S) hok
  have h2 : (12 : ℤ) ≤ ((prs S).length : ℤ) := by
    rw [hlen]
    exact_mod_cast h12
  have h3 : (lW (prs S) : ℤ) ≤ 102 := by exact_mod_cast hW
  linarith

/-- The family of a valid configuration of cost at most 136 has at most 11 chains. -/
theorem famC_length_le (hC : Caps) (hv : c.Valid) (hc : c.cost ≤ 136) : (famC c).length ≤ 11 := by
  have hav := acc_value hv hc
  have haw := acc_weight hv hc
  obtain ⟨n1, n2⟩ := famC_num hv
  have hfam := famC_trailFam hv
  by_contra hne
  have hE := family_le_30 hC.chain hfam (by omega) (by omega)
  have h0 : (0 : ℤ) ≤ (epsC c : ℤ) := Int.natCast_nonneg _
  linarith

/-! ### The cut at the dear seams -/

variable {k : ℕ}

/-- **The cut at the dear seams.**  The trails of a list of rows are the groups `G`, each a list of trails
joined by links of weight 4; the number of groups is at most `rX R + 2 - (cutRows R).length`, that is, one
more than the excess. -/
theorem cutG : ∀ R : List (NRow k), (∀ w ∈ seamWeights R, 3 ≤ w) → R ≠ [] →
    ∃ G : List (List (List (NRow k))), cutRows R = G.flatten ∧
      (∀ g ∈ G, g ≠ [] ∧ g.IsChain (RowLink k 4)) ∧ 1 ≤ G.length ∧
      G.length + (cutRows R).length ≤ rX R + 2
  | [], _, hne => absurd rfl hne
  | [r], _, _ => ⟨[[[r]]], by simp [cutRows], by
      intro g hg
      rw [List.mem_singleton.mp hg]
      exact ⟨by simp, List.isChain_singleton _⟩, by simp, by simp [cutRows, rX, seamWeights]⟩
  | r :: r' :: rest, hs, _ => by
      have hw : 3 ≤ ew k r.exit r'.entry := hs _ (by simp [seamWeights])
      have hs' : ∀ w ∈ seamWeights (r' :: rest), 3 ≤ w :=
        fun w hw' => hs w (by simp only [seamWeights, List.mem_cons]; exact Or.inr hw')
      have ih := cutRows_spec (r' :: rest) hs'
      obtain ⟨G, hG, hGc, hG1, hGl⟩ := cutG (r' :: rest) hs' (List.cons_ne_nil _ _)
      obtain ⟨S', hS'⟩ : ∃ S', S' = cutRows (r' :: rest) := ⟨_, rfl⟩
      rw [← hS'] at ih hG hGl
      obtain ⟨ihF, ihN, ihI, ihH, ihC, ihS, ihE⟩ := ih
      have hX := rX_cons_cons r r' rest
      -- the first group and its first trail
      obtain ⟨g0, G', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hG1)
      have hg0 := hGc g0 List.mem_cons_self
      obtain ⟨A, g0', rfl⟩ := List.exists_cons_of_ne_nil hg0.1
      rw [List.flatten_cons, List.cons_append] at hG
      have hA : A ≠ [] := ihN A (by rw [hG]; exact List.mem_cons_self)
      have hAh : A.head? = some r' := by
        have := ihH
        rw [hG] at this
        simpa using this
      obtain ⟨A', rfl⟩ : ∃ A', A = r' :: A' := by
        cases A with
        | nil => exact absurd rfl hA
        | cons a A' =>
            simp only [List.head?_cons, Option.some.injEq] at hAh
            exact ⟨A', by rw [hAh]⟩
      by_cases h3 : ew k r.exit r'.entry = 3
      · have hc : cutRows (r :: r' :: rest) = (r :: r' :: A') :: (g0' ++ G'.flatten) := by
          show (if ew k r.exit r'.entry = 3 then
              (match cutRows (r' :: rest) with
              | [] => [[r]]
              | A :: S => (r :: A) :: S)
            else [r] :: cutRows (r' :: rest)) = _
          rw [if_pos h3, ← hS', hG]
        refine ⟨((r :: r' :: A') :: g0') :: G', by rw [hc]; simp, ?_, by simp, ?_⟩
        · intro g hg
          rcases List.mem_cons.mp hg with rfl | hg
          · refine ⟨by simp, ?_⟩
            have hc0 := hg0.2
            rw [List.isChain_cons] at hc0 ⊢
            exact ⟨fun B hB => (hc0.1 B hB).append_left (List.cons_ne_nil _ _) [r], hc0.2⟩
          · exact hGc g (List.mem_cons_of_mem _ hg)
        · rw [hc, hX, h3]
          rw [hG] at hGl
          simp only [List.length_cons, List.length_append] at hGl ⊢
          omega
      · have hc : cutRows (r :: r' :: rest) = [r] :: (r' :: A') :: (g0' ++ G'.flatten) := by
          show (if ew k r.exit r'.entry = 3 then
              (match cutRows (r' :: rest) with
              | [] => [[r]]
              | A :: S => (r :: A) :: S)
            else [r] :: cutRows (r' :: rest)) = _
          rw [if_neg h3, ← hS', hG]
        rw [hG] at hGl
        by_cases h4 : ew k r.exit r'.entry = 4
        · refine ⟨([r] :: (r' :: A') :: g0') :: G', by rw [hc]; simp, ?_, by simp, ?_⟩
          · intro g hg
            rcases List.mem_cons.mp hg with rfl | hg
            · refine ⟨by simp, ?_⟩
              rw [List.isChain_cons_cons]
              refine ⟨?_, hg0.2⟩
              rw [rowLink_iff]
              intro a ha b hb
              simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at ha
              simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
              subst ha
              subst hb
              exact sLink_of_ew (x := sigmaInv r.lastEntry) rfl (by omega) h4
            · exact hGc g (List.mem_cons_of_mem _ hg)
          · rw [hc, hX, h4]
            simp only [List.length_cons, List.length_append] at hGl ⊢
            omega
        · refine ⟨[[r]] :: ((r' :: A') :: g0') :: G', by rw [hc]; simp, ?_, by simp, ?_⟩
          · intro g hg
            rcases List.mem_cons.mp hg with rfl | hg
            · exact ⟨by simp, List.isChain_singleton _⟩
            · exact hGc g hg
          · rw [hc, hX]
            simp only [List.length_cons, List.length_append] at hGl ⊢
            omega

end A16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.A16.acc_value
#print axioms SuperpermLowerBounds.A16.acc_weight
#print axioms SuperpermLowerBounds.A16.eps_le_two
#print axioms SuperpermLowerBounds.A16.famC_length_le
#print axioms SuperpermLowerBounds.A16.cutG
