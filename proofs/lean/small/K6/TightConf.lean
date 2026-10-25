import K6.TightFinal
import K6.Final871

/-!
# The family of a configuration of defect 4 as chains of words

`fam_words`: a valid configuration on 6 symbols of cost at most 28 has no closed trail and 1 to 3
open trails (`fam_tables`, `chk4`); written as chains of words, with the trail of the largest
`rows - holes` first, they have the numbers that `tight_contra` asks for, and every class outside
them lies in one of the loops of the configuration, a row of 4 blocks that avoids them
(`NoDeadW`).

`no_config_28_of_parts`: if every part of the search answers `false`, no valid configuration on 6
symbols has cost at most 28.
-/

namespace K6

open SuperpermLowerBounds SuperpermLowerBounds.S SuperpermLowerBounds.PS Hunter PreimageChain

variable {c : NConfig 6}

/-- An open trail as a chain of words. -/
noncomputable def trailW (A : List (NRow 6)) : List (List (List ℕ)) := toW (A.map NRow.entries)

theorem trailW_length (A : List (NRow 6)) : (trailW A).length = A.length := by
  simp [trailW, toW]

theorem trailW_hW (A : List (NRow 6)) : hW (trailW A) = rowsHoles 6 A := by
  unfold trailW hW
  rw [← holesL_toW, holesL_rows]

theorem flatten_trailW (L : List (List (NRow 6))) :
    (L.map trailW).flatten.flatten = (rowsEntries L.flatten).map Subtype.val := by
  induction L with
  | nil => rfl
  | cons A L ih =>
    simp only [List.map_cons, List.flatten_cons, List.flatten_append, ih, rowsEntries_append,
      List.map_append]
    congr 1
    unfold trailW toW
    rw [← rowsEntries_eq, List.map_flatten, List.map_map]

theorem isPermWord_of_permW {v : List ℕ} (hv : PermW 6 v) : IsPermWord 6 v := by
  refine ⟨hv.1, ?_⟩
  ext a
  rw [List.mem_toFinset, hv.2.2 a, Finset.mem_Icc]

/-- A largest element first. -/
theorem exists_max_first {α : Type*} (f : α → ℤ) : ∀ (l : List α), l ≠ [] →
    ∃ a l', l.Perm (a :: l') ∧ ∀ b ∈ l', f b ≤ f a
  | [], h => absurd rfl h
  | [a], _ => ⟨a, [], List.Perm.refl _, by simp⟩
  | a :: b :: l, _ => by
    obtain ⟨m, l', hp, hm⟩ := exists_max_first f (b :: l) (List.cons_ne_nil _ _)
    by_cases h : f a ≤ f m
    · refine ⟨m, a :: l', ?_, ?_⟩
      · exact (hp.cons a).trans (List.Perm.swap m a l')
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h
        · exact hm x hx
    · refine ⟨a, m :: l', hp.cons a, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact (hm x hx).trans (by omega)

/-- **The family of a configuration of defect 4.** -/
theorem fam_words (hv : c.Valid) (hc : c.cost ≤ 24 + 4) :
    ∃ (C0 : List (List (List ℕ))) (Cs : List (List (List (List ℕ)))) (T : ℕ),
      1 ≤ T ∧ T ≤ 3 ∧ Cs.length + 1 = T ∧ (∀ C ∈ C0 :: Cs, IsWChain 6 C ∧ C ≠ []) ∧
      List.Pairwise (fun u v : List ℕ => ¬ u ~r v) (C0 :: Cs).flatten.flatten ∧
      hW C0 + (Cs.map hW).sum + 5 * (T - 1) ≤ 20 ∧
      8 + 4 * (T - 1) + hW C0 + (Cs.map hW).sum ≤ C0.length + (Cs.map List.length).sum ∧
      (∀ C ∈ Cs, C.length + hW C0 ≤ C0.length + hW C) ∧ NoDeadW (C0 :: Cs).flatten.flatten := by
  obtain ⟨ht, hH, h6, hE, hK⟩ := fam_tables hv hc
  obtain ⟨hne, htr, hp, _, hloop, _⟩ := fam_spec hv
  -- no closed trail and at most 3 open trails
  have hshape : (closeds c).length = 0 ∧ (opens c).length ≤ 3 := by
    by_contra hcon
    have hK' := hK (by omega)
    have h1 := all4 chk4 (i := (opens c).length) (by omega)
    have ht0 : ((opens c).length == 0) = false := by
      simp only [beq_eq_false_iff_ne]
      omega
    rw [ht0, Bool.false_or] at h1
    have h2 := all4 h1 (i := (closeds c).length) (by omega)
    have hc0 : ((closeds c).length == 0 && decide ((opens c).length ≤ 3)) = false := by
      by_contra h'
      simp only [Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
      exact hcon h'
    rw [hc0, Bool.false_or] at h2
    have h3 := all4 h2 (i := rowsHoles 6 (opens c).flatten) (by omega)
    have h4 := all4 h3 (i := rowsHoles 6 (closeds c).flatten) (by omega)
    simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      decide_eq_true_eq] at h4
    rcases h4 with h4 | h4
    · omega
    · push_cast at hE
      linarith
  have hcl0 : closeds c = [] := List.length_eq_zero_iff.mp hshape.1
  rw [hcl0] at hE hH hp
  simp only [List.flatten_nil, rowsHoles_nil, List.length_nil, List.append_nil, Nat.cast_zero,
    sub_zero, add_zero] at hE hH hp
  -- the chains of words
  have hcls := fam_classes hv
  rw [hcl0] at hcls
  simp only [List.flatten_nil, List.append_nil, rowsEntries_append] at hcls
  have hclO : (rowsEntries (opens c).flatten).Pairwise (NotRot (k := 6)) :=
    (List.pairwise_append.mp hcls).1
  have htw : ∀ A ∈ opens c, IsWChain 6 (trailW A) ∧ trailW A ≠ [] := by
    intro A hA
    have hAcl : (rowsEntries A).Pairwise (NotRot (k := 6)) :=
      hclO.sublist (rowsEntries_sublist_flatten hA)
    refine ⟨isWChain_of_modelChain ((htr A hA).isModelChain (by norm_num) hAcl), ?_⟩
    intro h
    have := congrArg List.length h
    rw [trailW_length] at this
    exact (htr A hA).ne (List.length_eq_zero_iff.mp this)
  set Fw0 := (opens c).map trailW with hFw0
  have hFne : Fw0 ≠ [] := by
    rw [hFw0]
    exact fun h => hne (List.map_eq_nil_iff.mp h)
  obtain ⟨C0, Cs, hperm, hmax⟩ := exists_max_first (fun C => (C.length : ℤ) - hW C) Fw0 hFne
  have hT : Cs.length + 1 = (opens c).length := by
    have := hperm.length_eq
    rw [hFw0, List.length_map, List.length_cons] at this
    omega
  have hsumW : hW C0 + (Cs.map hW).sum = rowsHoles 6 (opens c).flatten := by
    have h1 := (hperm.map hW).sum_eq
    rw [List.map_cons, List.sum_cons] at h1
    rw [← h1, hFw0, List.map_map]
    rw [show hW ∘ trailW = rowsHoles 6 from funext trailW_hW, sum_holes_flatten]
  have hsumL : C0.length + (Cs.map List.length).sum = (opens c).flatten.length := by
    have h1 := (hperm.map List.length).sum_eq
    rw [List.map_cons, List.sum_cons] at h1
    rw [← h1, hFw0, List.map_map]
    rw [show List.length ∘ trailW = List.length from funext trailW_length, List.length_flatten]
  have hflat : ∀ u, u ∈ (C0 :: Cs).flatten.flatten ↔ u ∈ (rowsEntries (opens c).flatten).map
      Subtype.val := by
    intro u
    rw [← flatten_trailW, ← hFw0]
    exact (hperm.flatten.flatten.mem_iff).symm
  refine ⟨C0, Cs, (opens c).length, ht, hshape.2, hT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C hC
    have hC' : C ∈ Fw0 := hperm.symm.subset hC
    rw [hFw0] at hC'
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hC'
    exact htw A hA
  · have h1 : List.Pairwise (fun u v : List ℕ => ¬ u ~r v) Fw0.flatten.flatten := by
      rw [hFw0, flatten_trailW, List.pairwise_map]
      exact hclO
    exact (hperm.flatten.flatten.pairwise_iff (fun h h' => h h'.symm)).mp h1
  · rw [hsumW]
    omega
  · have : (8 : ℤ) + 4 * (((opens c).length : ℤ) - 1) ≤
        ((opens c).flatten.length : ℤ) - (rowsHoles 6 (opens c).flatten : ℤ) := by
      push_cast at hE
      linarith
    omega
  · intro C hC
    have := hmax C hC
    omega
  · -- no dead class: the loops cover the rest
    refine noDeadW_congr (fun u => (hflat u).symm) ?_
    intro v hvp hnew
    obtain ⟨e, he, hve⟩ := hv.cover ⟨v, isPermWord_of_permW hvp⟩
    have he' : e ∈ rowsEntries ((opens c).flatten ++ loops c) := by
      have hperm2 : (rowsEntries ((opens c).flatten ++ loops c)).Perm c.entries := by
        rw [← rowsEntries_allRows]
        unfold rowsEntries
        exact List.Perm.flatMap_right NRow.entries hp
      exact hperm2.mem_iff.mpr he
    rw [rowsEntries_append] at he'
    rcases List.mem_append.mp he' with hO | hL
    · exact absurd hve.symm (hnew e.1 (List.mem_map.mpr ⟨e, hO, rfl⟩))
    · obtain ⟨r, hr, her⟩ := List.mem_flatMap.mp hL
      have hr4 := hloop r hr
      have hrcl : (rowsEntries [r]).Pairwise (NotRot (k := 6)) := by
        refine (List.pairwise_append.mp hcls).2.1.sublist ?_
        rw [rowsEntries_cons, rowsEntries_nil, List.append_nil]
        unfold rowsEntries
        rw [List.flatMap_def]
        exact List.sublist_flatten_of_mem (List.mem_map_of_mem hr)
      have hTr : Trail 6 [r] := ⟨by simp, fun x hx => by
        rw [List.mem_singleton.mp hx, hr4]; norm_num, List.isChain_singleton _⟩
      have hWc := isWChain_of_modelChain (hTr.isModelChain (by norm_num) hrcl)
      simp only [List.map_cons, List.map_nil] at hWc
      refine ⟨r.entries.map Subtype.val, by rw [List.length_map, NRow.entries_length, hr4], ?_,
        hWc.doors _ List.mem_cons_self, ?_, ⟨e.1, List.mem_map.mpr ⟨e, her, rfl⟩, hve.symm⟩, ?_⟩
      · intro x hx
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
        exact permW_of_vtx y
      · have := hWc.classes
        simpa using this
      · intro x hx u hu
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hu
        have hyL : y ∈ rowsEntries (loops c) := List.mem_flatMap.mpr ⟨r, hr, hy⟩
        exact (List.pairwise_append.mp hcls).2.2 z hz y hyL

/-- **No valid configuration of defect 4**, given the parts of the search. -/
theorem no_config_28_of_parts {fuel : ℕ}
    (h1 : ∀ p0, p0 < 8 → ∀ p1, p1 < 1 → part (famRules 1 6 8 p0 1 p1) fuel = false)
    (h2 : ∀ p0, p0 < 4 → ∀ p1, p1 < 8 → part (famRules 2 4 4 p0 8 p1) fuel = false)
    (h3 : ∀ p0, p0 < 1 → ∀ p1, p1 < 32 → part (famRules 3 30 1 p0 32 p1) fuel = false)
    (c : NConfig 6) (hv : c.Valid) : ¬ c.cost ≤ (6 - 2).factorial + 4 := by
  intro hc
  have hf : (6 - 2).factorial = 24 := by decide
  obtain ⟨C0, Cs, T, hT1, hT3, hlen, hch, hcl, hG, hval, hord, hdead⟩ :=
    fam_words hv (by omega)
  interval_cases T
  · exact tight_contra (by norm_num) (by norm_num) h1 (by norm_num) (by norm_num) C0 Cs hlen hch
      hcl hG hval hord hdead
  · exact tight_contra (by norm_num) (by norm_num) h2 (by norm_num) (by norm_num) C0 Cs hlen hch
      hcl hG hval hord hdead
  · exact tight_contra (by norm_num) (by norm_num) h3 (by norm_num) (by norm_num) C0 Cs hlen hch
      hcl hG hval hord hdead

end K6

#print axioms K6.fam_words
#print axioms K6.no_config_28_of_parts
