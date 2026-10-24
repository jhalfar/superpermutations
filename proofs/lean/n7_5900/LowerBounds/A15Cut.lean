import LowerBounds.PTheorem
import LowerBounds.A15Arith

/-!
# The accounting at defect 15: Lemma ACC15, the excess, the number of chains, the cuts
(the written proof, sections 3.1 to 3.3 and 3.5)

* `acc_value`, `acc_weight` (Lemma ACC15): for a valid configuration of cost at most 135 the
  values of the components add up to at least 45 and the weights to at most 90.
* `eps_le_one` (Lemma EPS): the excess of the link costs is at most 1.
* `famC_length_le` (Lemma NCH): the family of the configuration has at most 9 chains.
* `cut5`: a list of rows with excess 1 is two lists of trails, each joined by links of weight 4
  (the cut at the dear place).
* `glue_split`: the trails of a component read cyclically from the cut, the last trail glued to
  the first one through a junction.
* `glue_ring'`: `glue_ring` with the blocks of the glued trail.
-/

namespace SuperpermLowerBounds
namespace A15

open Hunter PreimageChain T5899

variable {c : NConfig 7}

/-! ### Lemma ACC15 -/

/-- **Lemma ACC15, values.** -/
theorem acc_value (hv : c.Valid) (hc : c.cost ≤ 135) :
    45 ≤ valR c.kernel (rX c.kernel) + (c.hanging.map vH).sum := by
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
      (((c.hanging.map NHanging.cost).sum : ℕ) : ℤ) ≤ 135 := by
    exact_mod_cast (hC ▸ hc)
  linarith

/-- **Lemma ACC15, weights.** -/
theorem acc_weight (hv : c.Valid) (hc : c.cost ≤ 135) :
    wtR c.kernel (rX c.kernel) + (c.hanging.map wH).sum ≤ 90 := by
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
      (((c.hanging.map NHanging.cost).sum : ℕ) : ℤ) ≤ 135 := by
    exact_mod_cast (hC ▸ hc)
  have : ((wtR c.kernel (rX c.kernel) + (c.hanging.map wH).sum : ℕ) : ℤ) ≤ 90 := by
    rw [Nat.cast_add]
    linarith
  exact_mod_cast this

/-! ### Lemma EPS and Lemma NCH -/

/-- **Lemma EPS.**  The excess of the link costs is at most 1. -/
theorem eps_le_one (hC : Caps) (hF : Profiles) (hv : c.Valid) (hc : c.cost ≤ 135) :
    epsC c ≤ 1 := by
  have hav := acc_value hv hc
  have haw := acc_weight hv hc
  obtain ⟨n1, n2⟩ := famC_num hv
  have hfam := famC_trailFam hv
  by_contra hne
  have h2 : 2 ≤ epsC c := by omega
  have hW : lW (prs (famC c)) ≤ 84 := by omega
  have hE := family_le_49 hC.chain hF hfam hW
  have h2' : (2 : ℤ) ≤ (epsC c : ℤ) := by exact_mod_cast h2
  linarith

theorem lE_lin : ∀ l : List (ℕ × ℕ), (∀ p ∈ l, p.2 ≤ 2 * p.1 + 5) →
    lE l + 6 * (l.length : ℤ) ≤ (lW l : ℤ)
  | [], _ => by simp [lE, lW]
  | p :: l, h => by
      have ih := lE_lin l (fun q hq => h q (List.mem_cons_of_mem _ hq))
      have hp := h p List.mem_cons_self
      rw [lE_cons, lW_cons, List.length_cons]
      push_cast
      have hp' : (p.2 : ℤ) ≤ 2 * (p.1 : ℤ) + 5 := by exact_mod_cast hp
      linarith

/-- A family of at least 10 trails of weight at most 96 has value at most 36. -/
theorem family_le_36 (h0 : ChainCap Mf 84) {S : List (List (NRow 7))} (h : TrailFam 7 S)
    (hW : lW (prs S) ≤ 96) (h10 : 10 ≤ S.length) : lE (prs S) ≤ 36 := by
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
    have h2 : Mf (rowsHoles 7 A) ≤ 2 * rowsHoles 7 A + 5 := M_lin _ hp84
    exact le_trans h1 h2
  have h1 := lE_lin (prs S) hok
  have h2 : (10 : ℤ) ≤ ((prs S).length : ℤ) := by
    rw [hlen]
    exact_mod_cast h10
  have h3 : (lW (prs S) : ℤ) ≤ 96 := by exact_mod_cast hW
  linarith

/-- **Lemma NCH.**  The family of a valid configuration of cost at most 135 has at most 9
chains. -/
theorem famC_length_le (hC : Caps) (hv : c.Valid) (hc : c.cost ≤ 135) : (famC c).length ≤ 9 := by
  have hav := acc_value hv hc
  have haw := acc_weight hv hc
  obtain ⟨n1, n2⟩ := famC_num hv
  have hfam := famC_trailFam hv
  by_contra hne
  have hE := family_le_36 hC.chain hfam (by omega) (by omega)
  have h0 : (0 : ℤ) ≤ (epsC c : ℤ) := Int.natCast_nonneg _
  linarith

/-! ### The cut at the dear place -/

variable {k : ℕ}

/-- A list of rows whose seam excess is the number of its trails: the trails are two lists, each
joined by links of weight 4. -/
theorem cut5 : ∀ R : List (NRow k), (∀ w ∈ seamWeights R, 3 ≤ w) → R ≠ [] →
    rX R = (cutRows R).length →
    ∃ S₁ S₂ : List (List (NRow k)), cutRows R = S₁ ++ S₂ ∧ S₁ ≠ [] ∧ S₂ ≠ [] ∧
      S₁.IsChain (RowLink k 4) ∧ S₂.IsChain (RowLink k 4)
  | [], _, hne, _ => absurd rfl hne
  | [r], _, _, h => by
      simp [rX, seamWeights, cutRows] at h
  | r :: r' :: rest, hs, _, h => by
      have hw : 3 ≤ ew k r.exit r'.entry := hs _ (by simp [seamWeights])
      have hs' : ∀ w ∈ seamWeights (r' :: rest), 3 ≤ w :=
        fun w hw' => hs w (by simp only [seamWeights, List.mem_cons]; exact Or.inr hw')
      have ih := cutRows_spec (r' :: rest) hs'
      have ih5 := cut5 (r' :: rest) hs' (List.cons_ne_nil _ _)
      obtain ⟨S', hS'⟩ : ∃ S', S' = cutRows (r' :: rest) := ⟨_, rfl⟩
      rw [← hS'] at ih ih5
      obtain ⟨ihF, ihN, ihI, ihH, ihC, ihS, ihE⟩ := ih
      rcases S' with _ | ⟨A, S₀⟩
      · simp at ihF
      have hAne : A ≠ [] := ihN A List.mem_cons_self
      have hAh : A.head? = some r' := by
        simpa using ihH
      obtain ⟨A', rfl⟩ : ∃ A', A = r' :: A' := by
        cases A with
        | nil => exact absurd rfl hAne
        | cons a A' =>
            simp only [List.head?_cons, Option.some.injEq] at hAh
            exact ⟨A', by rw [hAh]⟩
      have ihC' := ihC (List.cons_ne_nil _ _)
      have hX := rX_cons_cons r r' rest
      by_cases h3 : ew k r.exit r'.entry = 3
      · have hc : cutRows (r :: r' :: rest) = (r :: r' :: A') :: S₀ := by
          show (if ew k r.exit r'.entry = 3 then
              (match cutRows (r' :: rest) with
              | [] => [[r]]
              | A :: S => (r :: A) :: S)
            else [r] :: cutRows (r' :: rest)) = _
          rw [if_pos h3, ← hS']
        rw [hc] at h ⊢
        have hXe : rX (r :: r' :: rest) = rX (r' :: rest) := by
          rw [hX, h3]
          omega
        rw [hXe] at h
        obtain ⟨S₁, S₂, e, n1, n2, c1, c2⟩ := ih5 (by simpa using h)
        obtain ⟨X, S₁', rfl⟩ := List.exists_cons_of_ne_nil n1
        rw [List.cons_append] at e
        injection e with e1 e2
        subst e1
        subst e2
        refine ⟨(r :: r' :: A') :: S₁', S₂, by simp, by simp, n2, ?_, c2⟩
        rw [List.isChain_cons] at c1 ⊢
        exact ⟨fun B hB => (c1.1 B hB).append_left (List.cons_ne_nil _ _) [r], c1.2⟩
      · have hc : cutRows (r :: r' :: rest) = [r] :: (r' :: A') :: S₀ := by
          show (if ew k r.exit r'.entry = 3 then
              (match cutRows (r' :: rest) with
              | [] => [[r]]
              | A :: S => (r :: A) :: S)
            else [r] :: cutRows (r' :: rest)) = _
          rw [if_neg h3, ← hS']
        rw [hc] at h ⊢
        rw [hX] at h
        simp only [List.length_cons] at ihC' h
        by_cases hfull : rX (r' :: rest) + 1 = ((r' :: A') :: S₀).length
        · exact ⟨[[r]], (r' :: A') :: S₀, rfl, by simp, by simp, List.isChain_singleton _,
            ihE hfull⟩
        · simp only [List.length_cons] at hfull
          have h4 : ew k r.exit r'.entry = 4 := by omega
          obtain ⟨S₁, S₂, e, n1, n2, c1, c2⟩ := ih5 (by simp only [List.length_cons]; omega)
          obtain ⟨X, S₁', rfl⟩ := List.exists_cons_of_ne_nil n1
          rw [List.cons_append] at e
          injection e with e1 e2
          subst e1
          subst e2
          refine ⟨[r] :: (r' :: A') :: S₁', S₂, by simp, by simp, n2, ?_, c2⟩
          rw [List.isChain_cons_cons]
          refine ⟨?_, c1⟩
          rw [rowLink_iff]
          intro a ha b hb
          simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at ha
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
          subst ha
          subst hb
          exact sLink_of_ew (x := sigmaInv r.lastEntry) rfl (by omega) h4

/-! ### Gluing -/

section glue

variable {first last A B J : List (NRow 7)} {S₁ S₂ : List (List (NRow 7))} {r r₁ : NRow 7}
  {x : Vtx 7}

theorem split_eq (first last : List (NRow 7)) (S₁ S₂ : List (List (NRow 7))) :
    (first :: S₁) ++ (S₂ ++ [last]) = first :: ((S₁ ++ S₂) ++ [last]) := by
  simp

theorem split_perm (g : List (NRow 7)) (S₁ S₂ : List (List (NRow 7))) :
    (S₂ ++ g :: S₁).Perm ((S₁ ++ S₂) ++ [g]) := by
  have h1 : (S₂ ++ g :: S₁).Perm (g :: S₁ ++ S₂) := List.perm_append_comm
  have h2 : ((S₁ ++ S₂) ++ [g]).Perm (g :: (S₁ ++ S₂)) := List.perm_append_singleton _ _
  exact h1.trans h2.symm

/-- **The trails of a component read cyclically from a cut**: the trails `first, S₁…` and
`S₂…, last` are each joined by links of weight 4, and the last trail is glued to the first one
through a junction.  The result `S₂…, glue, S₁…` is a list of trails joined by links of weight 4,
with the rows and holes of the junction in place of the two rows it replaces and with one more
block, of the class of the junction. -/
theorem glue_split (h : TrailFam 7 ((first :: S₁) ++ (S₂ ++ [last])))
    (hc₁ : (first :: S₁).IsChain (RowLink 7 4)) (hc₂ : (S₂ ++ [last]).IsChain (RowLink 7 4))
    (hf : first = r₁ :: B) (hl : last = A ++ [r]) (hJ : Junction 7 r r₁ x J)
    (hx : ∀ e ∈ rowsEntries ((first :: S₁) ++ (S₂ ++ [last])).flatten, NotRot x e) :
    TrailFam 7 (S₂ ++ glue A J B :: S₁) ∧ (S₂ ++ glue A J B :: S₁).IsChain (RowLink 7 4) ∧
      (S₂ ++ glue A J B :: S₁).flatten.length + 2 =
        ((first :: S₁) ++ (S₂ ++ [last])).flatten.length + J.length ∧
      rowsHoles 7 (S₂ ++ glue A J B :: S₁).flatten + rowsHoles 7 [r, r₁] =
        rowsHoles 7 ((first :: S₁) ++ (S₂ ++ [last])).flatten + rowsHoles 7 J ∧
      (rowsEntries (S₂ ++ glue A J B :: S₁).flatten).Perm
        (x :: rowsEntries ((first :: S₁) ++ (S₂ ++ [last])).flatten) := by
  rw [split_eq] at h hx ⊢
  have hp := split_perm (glue A J B) S₁ S₂
  have G0 := path_glue h hf hl hJ hx
  have hlen := path_glue_length (J := J) (mid := S₁ ++ S₂) hf hl
  have hhol := path_glue_holes (J := J) (mid := S₁ ++ S₂) hf hl
  have hent := path_glue_entries (mid := S₁ ++ S₂) hf hl hJ
  have hpl : (S₂ ++ glue A J B :: S₁).flatten.length = ((S₁ ++ S₂) ++ [glue A J B]).flatten.length :=
    hp.flatten.length_eq
  have hph : rowsHoles 7 (S₂ ++ glue A J B :: S₁).flatten =
      rowsHoles 7 ((S₁ ++ S₂) ++ [glue A J B]).flatten := by
    unfold rowsHoles
    exact (hp.flatten.map _).sum_eq
  refine ⟨G0.of_subperm hp.subperm, ?_, by omega, by omega, (rowsEntries_perm hp.flatten).trans hent⟩
  have h1 := List.isChain_append.mp hc₂
  have h2 := List.isChain_cons.mp hc₁
  rw [List.isChain_append]
  refine ⟨h1.1, ?_, ?_⟩
  · rw [List.isChain_cons]
    refine ⟨fun Y hY => ?_, h2.2⟩
    have h3 := h2.1 Y hY
    unfold RowLink at h3 ⊢
    rw [hJ.rowsLast_glue, ← hf]
    exact h3
  · intro X hX Y hY
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hY
    subst hY
    have h3 := h1.2.2 X hX last rfl
    unfold RowLink at h3 ⊢
    rw [hJ.rowsFirst_glue, ← hl]
    exact h3

/-- `glue_ring` with the blocks of the glued trail: those of the rows and the class of the
junction. -/
theorem glue_ring' {R : List (NRow 7)} (hok : RowsOK R) (h1 : (cutRows R).length = 1)
    (hm : 2 ≤ R.length) (hr : R.getLast? = some r) (hr₁ : R.head? = some r₁)
    (hJ : Junction 7 r r₁ x J) (hx : ∀ e ∈ rowsEntries R, NotRot x e) :
    ∃ T : List (NRow 7), Trail 7 T ∧ (rowsEntries T).Pairwise (NotRot (k := 7)) ∧
      RowLink 7 3 T T ∧ T.length + 2 = R.length + J.length ∧ (∀ j ∈ J, j ∈ T) ∧
      rowsHoles 7 T + rowsHoles 7 [r, r₁] = rowsHoles 7 R + rowsHoles 7 J ∧
      (rowsEntries T).Perm (x :: rowsEntries R) := by
  obtain ⟨_, hT, _⟩ := hok.single h1
  obtain ⟨r₁', A, r', hR⟩ := exists_first_mid_last hm
  have hh : R.head? = some r₁' := by rw [hR]; rfl
  have hg : R.getLast? = some r' := by
    rw [hR, ← List.cons_append, List.getLast?_concat]
  rw [hr₁] at hh
  rw [hr] at hg
  obtain rfl := Option.some.inj hh
  obtain rfl := Option.some.inj hg
  rw [hR] at hT hx
  have hcl := hok.classes
  rw [hR] at hcl
  obtain ⟨g1, g2, g3⟩ := ring_glue hT hcl hJ hx
  refine ⟨glue A J [], g1, g2, g3, ?_, ?_, ?_, ?_⟩
  · rw [ring_glue_length, hR]
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  · intro j hj
    unfold glue
    exact List.mem_append_right _ (List.mem_append_left _ hj)
  · rw [hR]
    exact ring_glue_holes A J r r₁
  · rw [hR]
    exact ring_glue_entries hJ

end glue

end A15
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.A15.acc_value
#print axioms SuperpermLowerBounds.A15.acc_weight
#print axioms SuperpermLowerBounds.A15.eps_le_one
#print axioms SuperpermLowerBounds.A15.famC_length_le
#print axioms SuperpermLowerBounds.A15.cut5
#print axioms SuperpermLowerBounds.A15.glue_split
#print axioms SuperpermLowerBounds.A15.glue_ring'
