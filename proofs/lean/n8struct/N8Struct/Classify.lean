import N8Struct.Partners

/-!
# Classification of the packings by four placed 27-walks

Every packing is the image of `K0` or `K1` under a renaming of 0..5, and every such image is a packing.
Kernel `decide` only on literal tables (`partnerTable`), the rest by ordinary proofs.
-/

namespace N8Struct

open SuperpermutationUpperBound

theorem disj_of_disjL' {P R : List (Row Nat)} (h : disjL (loopsOf P) (loopsOf R) = true) :
    Disj P R := by
  rw [disj_iff_loops]
  simp only [disjL, List.all_eq_true] at h
  intro L hL hL'
  have := h L hL
  simp_all

theorem mem_partnerTable {a : State} (ha : a ∈ partners) :
    (a, loopsOf (placement a)) ∈ partnerTable := by
  rw [← partnerTable_eq]
  exact List.mem_map_of_mem ha

/-- Two partners `a`, `b` with disjoint placements, read off the table. -/
theorem disj_partners {a b : State} (ha : a ∈ partners) (hb : b ∈ partners)
    (h : ∀ p ∈ partnerTable, ∀ q ∈ partnerTable, p.1 = a → q.1 = b → disjL p.2 q.2 = true) :
    Disj (placement a) (placement b) :=
  disj_of_disjL' (h _ (mem_partnerTable ha) _ (mem_partnerTable hb) rfl rfl)

theorem triples_table : ∀ p ∈ partnerTable, ∀ q ∈ partnerTable, disjL p.2 q.2 = true →
    ∀ r ∈ partnerTable, disjL p.2 r.2 = true → disjL q.2 r.2 = true →
    [p.1, q.1, r.1] ∈ completingTriples := by decide +kernel

theorem triples_complete : ∀ a ∈ partners, ∀ b ∈ partners, Disj (placement a) (placement b) →
    ∀ c ∈ partners, Disj (placement a) (placement c) → Disj (placement b) (placement c) →
    [a, b, c] ∈ completingTriples := by
  intro a ha b hb dab c hc dac dbc
  exact triples_table _ (mem_partnerTable ha) _ (mem_partnerTable hb) (disj_of_disjL dab)
    _ (mem_partnerTable hc) (disj_of_disjL dac) (disj_of_disjL dbc)

theorem completing_K : ∀ t ∈ completingTriples, (id6 :: t).Perm K0 ∨ (id6 :: t).Perm K1 := by
  decide +kernel

/-- Fact (4), completeness: every packing of four placed 27-walks is the image of `K0` or `K1`
under a renaming of the letters 0..5 (as a set of start states, equivalently of placements). -/
theorem packing_classification {g1 g2 g3 g4 : State} (hp : IsPacking g1 g2 g3 g4) :
    ∃ σ, IsState σ ∧ ([g1, g2, g3, g4].Perm (K0.map (relabel σ)) ∨
      [g1, g2, g3, g4].Perm (K1.map (relabel σ))) := by
  obtain ⟨s1, s2, s3, s4, d12, d13, d14, d23, d24, d34⟩ := hp
  have si := (inv_all g1 s1).1
  have t2 := relabel_state si s2
  have t3 := relabel_state si s3
  have t4 := relabel_state si s4
  have e1 : relabel (inv g1) g1 = id6 := relabel_inv_self_all g1 s1
  have back : ∀ {g}, IsState g →
      placement g = (placement (relabel (inv g1) g)).map (relabelRow g1) := by
    intro g hg
    rw [← placement_relabel, relabel_relabel_inv s1 hg]
  have tr : ∀ {g h}, IsState g → IsState h → Disj (placement g) (placement h) →
      Disj (placement (relabel (inv g1) g)) (placement (relabel (inv g1) h)) := by
    intro g h hg hh d
    apply disj_of_relabel s1 (placement_states (relabel_state si hg))
      (placement_states (relabel_state si hh))
    rw [← back hg, ← back hh]
    exact d
  have p2 := partners_complete _ t2 (by rw [← e1]; exact tr s1 s2 d12)
  have p3 := partners_complete _ t3 (by rw [← e1]; exact tr s1 s3 d13)
  have p4 := partners_complete _ t4 (by rw [← e1]; exact tr s1 s4 d14)
  have ht := triples_complete _ p2 _ p3 (tr s2 s3 d23) _ p4 (tr s2 s4 d24) (tr s3 s4 d34)
  have hK := completing_K _ ht
  have hmap : [g1, g2, g3, g4] = (id6 :: [relabel (inv g1) g2, relabel (inv g1) g3,
      relabel (inv g1) g4]).map (relabel g1) := by
    simp only [List.map_cons, List.map_nil, relabel_id6 s1, relabel_relabel_inv s1 s2,
      relabel_relabel_inv s1 s3, relabel_relabel_inv s1 s4]
  refine ⟨g1, s1, ?_⟩
  rw [hmap]
  rcases hK with h | h
  · exact Or.inl (h.map _)
  · exact Or.inr (h.map _)

/-- Conversely every renaming of a packing is a packing. -/
theorem relabel_packing {σ g1 g2 g3 g4 : State} (hσ : IsState σ) (hp : IsPacking g1 g2 g3 g4) :
    IsPacking (relabel σ g1) (relabel σ g2) (relabel σ g3) (relabel σ g4) := by
  obtain ⟨s1, s2, s3, s4, d12, d13, d14, d23, d24, d34⟩ := hp
  have r : ∀ {g h}, IsState g → IsState h → Disj (placement g) (placement h) →
      Disj (placement (relabel σ g)) (placement (relabel σ h)) := by
    intro g h hg hh d
    rw [placement_relabel, placement_relabel]
    exact relabel_disj hσ (placement_states hg) (placement_states hh) d
  exact ⟨relabel_state hσ s1, relabel_state hσ s2, relabel_state hσ s3, relabel_state hσ s4,
    r s1 s2 d12, r s1 s3 d13, r s1 s4 d14, r s2 s3 d23, r s2 s4 d24, r s3 s4 d34⟩

/-- `K0` and `K1` are packings (both contain the identity placement). -/
theorem K0_packing : IsPacking [0,1,2,3,4,5] [0,2,1,5,4,3] [4,1,2,5,0,3] [4,2,1,3,0,5] := by
  have hm : ∀ a ∈ [[0,2,1,5,4,3], [4,1,2,5,0,3], [4,2,1,3,0,5]], a ∈ partners := by decide +kernel
  refine ⟨by decide, by decide, by decide, by decide,
    partners_disj _ (hm _ (by simp)), partners_disj _ (hm _ (by simp)),
    partners_disj _ (hm _ (by simp)), ?_, ?_, ?_⟩ <;>
  exact disj_partners (hm _ (by simp)) (hm _ (by simp)) (by decide +kernel)

theorem K1_packing : IsPacking [0,1,2,3,4,5] [0,3,2,1,5,4] [2,1,0,3,5,4] [2,3,0,1,4,5] := by
  have hm : ∀ a ∈ [[0,3,2,1,5,4], [2,1,0,3,5,4], [2,3,0,1,4,5]], a ∈ partners := by decide +kernel
  refine ⟨by decide, by decide, by decide, by decide,
    partners_disj _ (hm _ (by simp)), partners_disj _ (hm _ (by simp)),
    partners_disj _ (hm _ (by simp)), ?_, ?_, ?_⟩ <;>
  exact disj_partners (hm _ (by simp)) (hm _ (by simp)) (by decide +kernel)

end N8Struct

#print axioms N8Struct.triples_complete
#print axioms N8Struct.packing_classification
#print axioms N8Struct.relabel_packing
#print axioms N8Struct.K0_packing
#print axioms N8Struct.K1_packing
