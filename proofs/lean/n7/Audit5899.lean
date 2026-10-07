import LowerBounds.PTheorem

/-!
# Audit of level 1 for 5,899 (no `native_decide`)

What is proved in the files `LowerBounds/P*.lean` up to `PTheorem.lean`, with the statement about
words written out and the hypotheses (the finite statements F0–F5, FR, FF of
`opt/lb/lean/PROOF_5899.md`) unfolded to the objects they speak about.

Level 2 (the evaluation of the finite statements) is not part of this file yet.
-/

open SuperpermLowerBounds Hunter

section

/-! ### The objects of the finite statements -/

/-- A family: model chains (`IsModelChain`, `SModelDef.lean`), none empty, whose blocks lie in
pairwise different rotation classes. -/
example (k : ℕ) (F : List (List (List (Vtx k)))) :
    IsFamily k F ↔
      (∀ C ∈ F, IsModelChain k C) ∧ (∀ C ∈ F, C ≠ []) ∧
        F.flatten.flatten.Pairwise (fun a b : Vtx k => ¬ ((a : List ℕ) ~r (b : List ℕ))) :=
  ⟨fun h => ⟨h.chains, h.ne, h.classes⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- A link between two chains: the exit of the last block of the first chain (its entry rotated
by `k - 1`) without its first `d` symbols is the beginning of the first block entry of the
second chain. -/
example (k d : ℕ) (A B : List (List (Vtx k))) :
    ChainLink k d A B ↔
      ∀ u ∈ A.getLast?.bind List.getLast?, ∀ v ∈ B.head?.bind List.head?,
        ((u : List ℕ).rotate (k - 1)).drop d = (v : List ℕ).take (k - d) :=
  Iff.rfl

/-- A sequence with links of weight 4: a family whose consecutive chains are linked with
`d = 4`. -/
example (k : ℕ) (F : List (List (List (Vtx k)))) :
    IsPath k F ↔ IsFamily k F ∧ F.IsChain (ChainLink k 4) :=
  ⟨fun h => ⟨h.toIsFamily, h.links⟩, fun h => ⟨h.1, h.2⟩⟩

/-- A ring: a model chain with at least two rows that is linked to itself with `d = 3`. -/
example (k : ℕ) (C : List (List (Vtx k))) :
    IsRing k C ↔ IsModelChain k C ∧ 2 ≤ C.length ∧ ChainLink k 3 C C :=
  ⟨fun h => ⟨h.chain, h.two, h.closes⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- The number of holes of a chain: 6 minus the number of blocks, summed over its rows. -/
example (C : List (List (Vtx 7))) : holesL 7 C = (C.map fun P => 7 - 1 - P.length).sum := rfl

/-! ### The finite statements -/

/-- F0. -/
example (M : ℕ → ℕ) (G : ℕ) :
    ChainCap M G ↔
      ∀ C : List (List (Vtx 7)), IsModelChain 7 C → holesL 7 C ≤ G → C.length ≤ M (holesL 7 C) :=
  Iff.rfl

/-- F1–F5. -/
example (s : ℕ) (P : ℕ → ℕ) (G : ℕ) :
    PathCap s P G ↔
      ∀ F : List (List (List (Vtx 7))), IsPath 7 F → F.length = s + 1 →
        (F.map (holesL 7)).sum ≤ G → (F.map List.length).sum ≤ P ((F.map (holesL 7)).sum) :=
  Iff.rfl

/-- FR. -/
example (PR : ℕ → ℕ) (G : ℕ) :
    RingCap PR G ↔
      ∀ C : List (List (Vtx 7)), IsRing 7 C → holesL 7 C ≤ G → C.length ≤ PR (holesL 7 C) :=
  Iff.rfl

/-- FF. -/
example (ts : List (ℕ × ℕ)) :
    NoProfile ts ↔
      ¬ ∃ F : List (List (List (Vtx 7))), IsFamily 7 F ∧
        List.Forall₂ (fun C t => t.1 ≤ C.length ∧ holesL 7 C ≤ t.2) F ts :=
  Iff.rfl

/-- The tables: entries of the lists of `PTables.lean`. -/
example (x : ℕ) : T5899.Mf x = T5899.Mtab.getD x 0 := rfl

example (s x : ℕ) : T5899.Pf s x = (T5899.Ptabs.getD s []).getD x 0 := rfl

example (x : ℕ) : T5899.PRf x = T5899.PRtab.getD x 0 := rfl

/-! ### Level 1: the theorem from the finite statements -/

/-- **Level 1.**  If the chain caps (F0), the caps for sequences with 1 to 5 links of weight 4
(F1–F5), the ring caps (FR) and the five profile statements (FF) hold, then every word over 7
symbols that contains every permutation of the 7 symbols as a factor has at least 5,899
letters. -/
example
    (hF0 : ChainCap T5899.Mf 84)
    (hF1 : PathCap 1 (T5899.Pf 1) 78) (hF2 : PathCap 2 (T5899.Pf 2) 72)
    (hF3 : PathCap 3 (T5899.Pf 3) 66) (hF4 : PathCap 4 (T5899.Pf 4) 60)
    (hF5 : PathCap 5 (T5899.Pf 5) 54)
    (hFR : RingCap T5899.PRf 77)
    (hP1 : NoProfile [(66, 36), (66, 36)]) (hP2 : NoProfile [(50, 26), (50, 26)])
    (hP3 : NoProfile [(63, 34), (34, 16)]) (hP4 : NoProfile [(66, 36), (31, 14)])
    (hP5 : NoProfile [(31, 14), (31, 14), (34, 16), (34, 16)]) :
    ∀ w : List (Fin 7),
      (∀ p : List (Fin 7), p.length = 7 → p.Nodup → ∃ u v : List (Fin 7), w = u ++ p ++ v) →
      5899 ≤ w.length := by
  refine covers_5899_of_caps ⟨hF0, ?_, hFR⟩ ⟨hP1, hP2, hP3, hP4, hP5⟩
  intro s h1 h5
  have hs : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact hF1
  · exact hF2
  · exact hF3
  · exact hF4
  · exact hF5

/-- The same step without words: no valid standard configuration (`NConfig.Valid`, audited in
`AuditN.lean`) on 7 symbols has cost at most 134. -/
example (hC : Caps) (hF : Profiles) (c : NConfig 7) (hv : c.Valid) : ¬ c.cost ≤ 134 :=
  no_config_134 hC hF c hv

end

/-! ### Axioms -/

#print axioms SuperpermLowerBounds.covers_5899_of_caps
#print axioms SuperpermLowerBounds.no_config_134
#print axioms SuperpermLowerBounds.family_le_49
#print axioms SuperpermLowerBounds.family_le_44
#print axioms SuperpermLowerBounds.hanging_item
#print axioms SuperpermLowerBounds.famH_spec
#print axioms SuperpermLowerBounds.acc_value
#print axioms SuperpermLowerBounds.acc_weight
#print axioms SuperpermLowerBounds.T5899.profile_of_family
#print axioms SuperpermLowerBounds.T5899.many_chains
#print axioms SuperpermLowerBounds.T5899.kern
