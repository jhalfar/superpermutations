import LowerBounds.SBridge
import LowerBounds.SBridgeRelabel

/-!
# Facts about model chains

Not needed for `hStatement_of_model`; written for the side that proves `ModelStatement` by a
search, and to record that the model is not weaker than the description of a chain by doors and
edges of weight 3.

* Symmetry: a relabelling of the symbols maps a model chain to a model chain with the same
  deficits (`IsModelChain.relabel`, `modelDeficits_relabel`), and every non-empty model chain
  has the deficits of one whose first entry is the word `1 2 … k`
  (`IsModelChain.exists_normalised`).
* Links as words: an overlap of `k - 2` symbols leaves `tau2V a` or `sigma a`
  (`sLink_two_cases`); an overlap of `k - 3` symbols leaves six words (`sLink_three_cases`, and
  `sLink_three_cases_entry` in terms of the entry `a b Y c` of the block that is left).
* In a model chain the links inside a piece are doors (`IsModelChain.doors_eq`) and, for
  `4 ≤ k`, the links between pieces are edges of weight exactly 3 (`IsModelChain.seams_ew`).
  Hence `IsModelChain k L ∧ L ≠ [] ↔ EntriesChain k L` (`isModelChain_iff_entriesChain`).
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ}

/-! ### Symmetry -/

/-- A relabelling keeps the overlaps. -/
theorem sLink_relabelV (f : Relabelling k) {d : ℕ} {u v : Vtx k} (h : SLink k d u v) :
    SLink k d (relabelV f u) (relabelV f v) := by
  unfold SLink at h ⊢
  rw [relabelV_val, relabelV_val, ← List.map_rotate, ← List.map_drop, ← List.map_take, h]

/-- A relabelling maps a model chain to a model chain. -/
theorem IsModelChain.relabel (f : Relabelling k) {L : List (List (Vtx k))}
    (h : IsModelChain k L) : IsModelChain k (L.map (List.map (relabelV f))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hP
    intro hnil
    exact h.pieces_ne Q hQ (List.map_eq_nil_iff.mp hnil)
  · intro P hP
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hP
    rw [List.length_map]
    exact h.size_le Q hQ
  · intro P hP
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hP
    rw [List.isChain_map]
    exact List.IsChain.imp (fun _ _ hab => sLink_relabelV f hab) (h.doors Q hQ)
  · rw [List.isChain_map]
    refine List.IsChain.imp ?_ h.seams
    intro P Q hPQ hP hQ
    have hP' : P ≠ [] := fun hnil => hP (by rw [hnil]; rfl)
    have hQ' : Q ≠ [] := fun hnil => hQ (by rw [hnil]; rfl)
    rw [List.getLast_map, List.head_map]
    exact sLink_relabelV f (hPQ hP' hQ')
  · rw [← List.map_flatten, List.pairwise_map]
    refine List.Pairwise.imp ?_ h.classes
    intro u v huv hrot
    exact huv ((relabelV_isRotated_iff f u v).mp hrot)

/-- A relabelling keeps the deficits. -/
theorem modelDeficits_relabel (f : Relabelling k) (L : List (List (Vtx k))) :
    modelDeficits k (L.map (List.map (relabelV f))) = modelDeficits k L := by
  unfold modelDeficits
  rw [List.map_map]
  apply List.map_congr_left
  intro P _
  simp

/-- Every non-empty model chain has the deficits of a model chain whose first entry is the word
`1 2 … k`. -/
theorem IsModelChain.exists_normalised {L : List (List (Vtx k))} (h : IsModelChain k L)
    (hne : L ≠ []) :
    ∃ L' : List (List (Vtx k)), IsModelChain k L' ∧ modelDeficits k L' = modelDeficits k L ∧
      ∃ tail rest, L' = (idVtx k :: tail) :: rest := by
  obtain ⟨P, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨a, tail, rfl⟩ := List.exists_cons_of_ne_nil (h.pieces_ne P List.mem_cons_self)
  refine ⟨((a :: tail) :: rest).map (List.map (relabelV (normRelabelling a))),
    h.relabel _, modelDeficits_relabel _ _, ?_⟩
  refine ⟨tail.map (relabelV (normRelabelling a)),
    rest.map (List.map (relabelV (normRelabelling a))), ?_⟩
  rw [List.map_cons, List.map_cons, relabelV_normRelabelling]

/-! ### The links as words -/

/-- An overlap of `k - 2` symbols leaves two vertices: the door of the exit, or `σ` of the
entry. -/
theorem sLink_two_cases (hk : 2 ≤ k) {a b : Vtx k} (h : SLink k 2 a b) :
    b = tau2V a ∨ b = sigma a := by
  have hover : (sigmaInv a : List ℕ).drop 2 = (b : List ℕ).take (k - 2) := h
  rcases Hunter.ProofsConfinement.wt_two_word_cases hk (sigmaInv a).2 b.2 hover with hrot | hdoor
  · right
    apply Subtype.ext
    rw [hrot]
    change ((a : List ℕ).rotate (k - 1)).rotate 2 = (a : List ℕ).rotate 1
    have hmod : (k - 1 + 2) % k = 1 := by
      rw [show k - 1 + 2 = 1 + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [List.rotate_rotate, ← List.rotate_mod (a : List ℕ) (k - 1 + 2), a.2.length, hmod]
  · left
    apply Subtype.ext
    rw [hdoor, tau2V_val hk]
    rfl

/-- An overlap of `k - 3` symbols with `y₁ y₂ y₃ Y` leaves `Y` followed by an arrangement of
`y₁, y₂, y₃`. -/
theorem overlap_three_cases (hk : 3 ≤ k) {x v : Vtx k}
    (h : (x : List ℕ).drop 3 = (v : List ℕ).take (k - 3)) :
    ∃ y₁ y₂ y₃ Y, (x : List ℕ) = y₁ :: y₂ :: y₃ :: Y ∧
      ((v : List ℕ) = Y ++ [y₁, y₂, y₃] ∨ (v : List ℕ) = Y ++ [y₁, y₃, y₂] ∨
        (v : List ℕ) = Y ++ [y₂, y₁, y₃] ∨ (v : List ℕ) = Y ++ [y₂, y₃, y₁] ∨
        (v : List ℕ) = Y ++ [y₃, y₁, y₂] ∨ (v : List ℕ) = Y ++ [y₃, y₂, y₁]) := by
  have hxlen : (x : List ℕ).length = k := x.2.length
  obtain ⟨y₁, y₂, y₃, Y, hx⟩ : ∃ y₁ y₂ y₃ Y, (x : List ℕ) = y₁ :: y₂ :: y₃ :: Y := by
    rcases hx : (x : List ℕ) with _ | ⟨a, _ | ⟨b, _ | ⟨c, Y⟩⟩⟩
    · rw [hx] at hxlen; simp at hxlen; omega
    · rw [hx] at hxlen; simp at hxlen; omega
    · rw [hx] at hxlen; simp at hxlen; omega
    · exact ⟨a, b, c, Y, rfl⟩
  have hY : Y.length + 3 = k := by
    rw [hx] at hxlen
    simpa using hxlen
  refine ⟨y₁, y₂, y₃, Y, hx, ?_⟩
  have hxp : IsPermWord (Y.length + 3) (Hunter.ProofsClosure3.finalExit Y y₃ y₂ y₁) := by
    rw [hY]
    have := x.2
    rw [hx] at this
    exact this
  have hvp : IsPermWord (Y.length + 3) (v : List ℕ) := by
    rw [hY]
    exact v.2
  have hover : (Hunter.ProofsClosure3.finalExit Y y₃ y₂ y₁).drop 3 =
      (v : List ℕ).take (Y.length + 3 - 3) := by
    rw [hY]
    rw [hx] at h
    exact h
  rcases Hunter.ProofsClosure3.w3_six_cases Y y₃ y₂ y₁ hxp hvp hover with
    h1 | h1 | h1 | h1 | h1 | h1
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inl h1)
  · exact Or.inl h1

/-- An overlap of `k - 3` symbols, in terms of the exit `y₁ y₂ y₃ Y` of the block that is
left. -/
theorem sLink_three_cases (hk : 3 ≤ k) {u v : Vtx k} (h : SLink k 3 u v) :
    ∃ y₁ y₂ y₃ Y, (sigmaInv u : List ℕ) = y₁ :: y₂ :: y₃ :: Y ∧
      ((v : List ℕ) = Y ++ [y₁, y₂, y₃] ∨ (v : List ℕ) = Y ++ [y₁, y₃, y₂] ∨
        (v : List ℕ) = Y ++ [y₂, y₁, y₃] ∨ (v : List ℕ) = Y ++ [y₂, y₃, y₁] ∨
        (v : List ℕ) = Y ++ [y₃, y₁, y₂] ∨ (v : List ℕ) = Y ++ [y₃, y₂, y₁]) :=
  overlap_three_cases hk (x := sigmaInv u) h

/-- An overlap of `k - 3` symbols, in terms of the entry `a b Y c` of the block that is left:
the next entry is `Y` followed by an arrangement of `c, a, b`.  The first of the six,
`Y c a b`, is `σ²` of the entry. -/
theorem sLink_three_cases_entry (hk : 3 ≤ k) {u v : Vtx k} (h : SLink k 3 u v) :
    ∃ a b Y c, (u : List ℕ) = a :: b :: (Y ++ [c]) ∧
      ((v : List ℕ) = Y ++ [c, a, b] ∨ (v : List ℕ) = Y ++ [c, b, a] ∨
        (v : List ℕ) = Y ++ [a, c, b] ∨ (v : List ℕ) = Y ++ [a, b, c] ∨
        (v : List ℕ) = Y ++ [b, c, a] ∨ (v : List ℕ) = Y ++ [b, a, c]) := by
  obtain ⟨y₁, y₂, y₃, Y, hexit, hcases⟩ := sLink_three_cases hk h
  refine ⟨y₂, y₃, Y, y₁, ?_, hcases⟩
  -- the entry is the exit rotated by one
  have hlen : (u : List ℕ).length = k := u.2.length
  have hrot : (u : List ℕ) = ((u : List ℕ).rotate (k - 1)).rotate 1 := by
    rw [List.rotate_rotate, show k - 1 + 1 = (u : List ℕ).length by rw [hlen]; omega,
      List.rotate_length]
  have hexit' : (u : List ℕ).rotate (k - 1) = y₁ :: y₂ :: y₃ :: Y := hexit
  rw [hrot, hexit']
  simp [List.rotate_cons_succ]

/-! ### Model chains are chains of doors and edges of weight 3 -/

/-- A relation that holds between all pairs holds between neighbours. -/
theorem isChain_and_of_pairwise {α : Type} {R S : α → α → Prop} :
    ∀ {l : List α}, List.IsChain R l → List.Pairwise S l →
      List.IsChain (fun a b => R a b ∧ S a b) l
  | [], _, _ => List.IsChain.nil
  | [_], _, _ => List.IsChain.singleton _
  | a :: b :: l, hR, hS => by
      rw [List.isChain_cons_cons] at hR ⊢
      rw [List.pairwise_cons] at hS
      exact ⟨⟨hR.1, hS.1 b List.mem_cons_self⟩, isChain_and_of_pairwise hR.2 hS.2⟩

/-- In a model chain the entries of a piece are joined by doors. -/
theorem IsModelChain.doors_eq (hk : 2 ≤ k) {L : List (List (Vtx k))} (h : IsModelChain k L) :
    ∀ P ∈ L, List.IsChain (fun a b => b = tau2V a) P := by
  intro P hP
  have hpw : List.Pairwise (fun u v : Vtx k => ¬ ((u : List ℕ) ~r (v : List ℕ))) P :=
    (List.pairwise_flatten.mp h.classes).1 P hP
  refine List.IsChain.imp ?_ (isChain_and_of_pairwise (h.doors P hP) hpw)
  rintro a b ⟨hlink, hnot⟩
  rcases sLink_two_cases hk hlink with h1 | h1
  · exact h1
  · exfalso
    apply hnot
    rw [h1]
    exact ⟨1, rfl⟩

/-- An overlap of `k - 3` symbols between entries of different rotation classes is an edge of
weight exactly 3 from the exit (`4 ≤ k`). -/
theorem ew_three_of_sLink (hk : 4 ≤ k) {u v : Vtx k} (h : SLink k 3 u v)
    (hnot : ¬ ((u : List ℕ) ~r (v : List ℕ))) : ew k (sigmaInv u) v = 3 := by
  have hov : (sigmaInv u : List ℕ).drop 3 = (v : List ℕ).take (k - 3) := h
  have hle : ew k (sigmaInv u) v ≤ 3 := wt_le (by omega) (by omega) hov
  have hge := Hunter.ProofsExitless.ew_ge_one (by omega : 1 ≤ k) (sigmaInv u) v
  have h1 : ew k (sigmaInv u) v ≠ 1 := by
    intro h1
    have hv : v = sigma (sigmaInv u) :=
      (Hunter.ProofsExitless.ew_eq_one_iff (by omega)).mp h1
    apply hnot
    rw [hv]
    refine ⟨k - 1 + 1, ?_⟩
    change _ = ((u : List ℕ).rotate (k - 1)).rotate 1
    rw [List.rotate_rotate]
  have h2 : ew k (sigmaInv u) v ≠ 2 := by
    intro h2
    rcases weight_two_successors (by omega) h2 with hs | ht
    · apply hnot
      rw [hs]
      refine ⟨k - 1 + 1 + 1, ?_⟩
      change _ = (((u : List ℕ).rotate (k - 1)).rotate 1).rotate 1
      rw [List.rotate_rotate, List.rotate_rotate]
    · have hperm := (sigmaInv u).2
      have hlen : (sigmaInv u : List ℕ).length = k := hperm.length
      obtain ⟨e0, e1, e2, e3, E, he⟩ :
          ∃ e0 e1 e2 e3 E, (sigmaInv u : List ℕ) = e0 :: e1 :: e2 :: e3 :: E := by
        rcases hx : (sigmaInv u : List ℕ) with _ | ⟨e0, _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, E⟩⟩⟩⟩
        · rw [hx] at hlen; simp at hlen; omega
        · rw [hx] at hlen; simp at hlen; omega
        · rw [hx] at hlen; simp at hlen; omega
        · rw [hx] at hlen; simp at hlen; omega
        · exact ⟨e0, e1, e2, e3, E, rfl⟩
      have hvval : (v : List ℕ) = e2 :: e3 :: (E ++ [e1, e0]) := by
        rw [ht, Hunter.tau_val_of_door (Hunter.door_isPermWord (by omega) hperm), he]
        rfl
      have hk3 : k - 3 = E.length + 1 := by
        rw [he] at hlen
        simp at hlen
        omega
      rw [he, hvval, hk3] at hov
      simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons] at hov
      have h23 : e3 = e2 := (List.cons.inj hov).1
      have hnd := hperm.nodup
      rw [he] at hnd
      subst h23
      simp at hnd
  omega

/-- In a model chain consecutive pieces are joined by edges of weight exactly 3 (`4 ≤ k`). -/
theorem IsModelChain.seams_ew (hk : 4 ≤ k) {L : List (List (Vtx k))} (h : IsModelChain k L) :
    List.IsChain
      (fun P Q => ∀ (hP : P ≠ []) (hQ : Q ≠ []), ew k (sigmaInv (P.getLast hP)) (Q.head hQ) = 3)
      L := by
  have hpw : List.Pairwise (fun P Q : List (Vtx k) =>
      ∀ x ∈ P, ∀ y ∈ Q, ¬ ((x : List ℕ) ~r (y : List ℕ))) L :=
    (List.pairwise_flatten.mp h.classes).2
  refine List.IsChain.imp ?_ (isChain_and_of_pairwise h.seams hpw)
  rintro P Q ⟨hlink, hnot⟩ hP hQ
  exact ew_three_of_sLink hk (hlink hP hQ)
    (hnot _ (List.getLast_mem hP) _ (List.head_mem hQ))

/-- A non-empty model chain is an `EntriesChain` (`4 ≤ k`). -/
theorem IsModelChain.entriesChain (hk : 4 ≤ k) {L : List (List (Vtx k))}
    (h : IsModelChain k L) (hne : L ≠ []) : EntriesChain k L :=
  ⟨hne, h.pieces_ne, h.size_le, h.doors_eq (by omega), h.seams_ew hk, h.classes⟩

/-- The model chains are exactly the chains of doors and edges of weight 3 (`4 ≤ k`). -/
theorem isModelChain_iff_entriesChain (hk : 4 ≤ k) {L : List (List (Vtx k))} :
    IsModelChain k L ∧ L ≠ [] ↔ EntriesChain k L :=
  ⟨fun h => h.1.entriesChain hk h.2, fun h => ⟨h.isModelChain (by omega), h.ne⟩⟩

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.IsModelChain.relabel
#print axioms SuperpermLowerBounds.IsModelChain.exists_normalised
#print axioms SuperpermLowerBounds.sLink_two_cases
#print axioms SuperpermLowerBounds.sLink_three_cases
#print axioms SuperpermLowerBounds.sLink_three_cases_entry
#print axioms SuperpermLowerBounds.IsModelChain.doors_eq
#print axioms SuperpermLowerBounds.ew_three_of_sLink
#print axioms SuperpermLowerBounds.IsModelChain.seams_ew
#print axioms SuperpermLowerBounds.isModelChain_iff_entriesChain
