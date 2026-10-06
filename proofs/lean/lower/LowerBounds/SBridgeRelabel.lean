import LowerBounds.SBridgeChain

/-!
# Relabelling the symbols

A relabelling of the symbols `1, …, k` acts on vertices letter by letter.  It commutes with
`sigma`, `sigmaInv` and `tau2V`, keeps the weight of every edge and keeps the relation "is a
rotation of".  Hence it maps an `EntriesChain` to an `EntriesChain` with the same piece sizes,
and every `EntriesChain` is the image of one whose first vertex is the word `1 2 … k`
(`EntriesChain.exists_normalised`).
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ}

/-- A relabelling of the symbols `1, …, k`: an injective map of `ℕ` that sends `{1, …, k}` into
itself. -/
structure Relabelling (k : ℕ) where
  toFun : ℕ → ℕ
  inj : Function.Injective toFun
  maps : ∀ x, x ∈ Finset.Icc 1 k → toFun x ∈ Finset.Icc 1 k

theorem isPermWord_map (f : Relabelling k) {w : List ℕ} (hw : IsPermWord k w) :
    IsPermWord k (w.map f.toFun) := by
  refine ⟨hw.1.map f.inj, ?_⟩
  have himg : (w.map f.toFun).toFinset = w.toFinset.image f.toFun := by
    ext y
    simp
  rw [himg, hw.2]
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact f.maps x hx
  · rw [Finset.card_image_of_injective _ f.inj]

/-- The action of a relabelling on a vertex. -/
def relabelV (f : Relabelling k) (v : Vtx k) : Vtx k :=
  ⟨(v : List ℕ).map f.toFun, isPermWord_map f v.2⟩

theorem relabelV_val (f : Relabelling k) (v : Vtx k) :
    (relabelV f v : List ℕ) = (v : List ℕ).map f.toFun := rfl

theorem relabelV_sigma (f : Relabelling k) (v : Vtx k) :
    relabelV f (sigma v) = sigma (relabelV f v) := by
  apply Subtype.ext
  change ((v : List ℕ).rotate 1).map f.toFun = ((v : List ℕ).map f.toFun).rotate 1
  rw [List.map_rotate]

theorem relabelV_sigmaInv (f : Relabelling k) (v : Vtx k) :
    relabelV f (sigmaInv v) = sigmaInv (relabelV f v) := by
  apply Subtype.ext
  change ((v : List ℕ).rotate (k - 1)).map f.toFun = ((v : List ℕ).map f.toFun).rotate (k - 1)
  rw [List.map_rotate]

theorem relabelV_tau2V (hk : 2 ≤ k) (f : Relabelling k) (v : Vtx k) :
    relabelV f (tau2V v) = tau2V (relabelV f v) := by
  apply Subtype.ext
  obtain ⟨x, M, m, hv, -⟩ := vtx_cons_append hk v
  rw [relabelV_val, tau2V_cons_append hk v x M m hv,
    tau2V_cons_append hk (relabelV f v) (f.toFun x) (M.map f.toFun) (f.toFun m)
      (by rw [relabelV_val, hv]; simp)]
  simp

/-- An injective map of the letters keeps the overlap weight. -/
theorem wt_map {f : ℕ → ℕ} (hf : Function.Injective f) (u v : List ℕ) :
    wt k (u.map f) (v.map f) = wt k u v := by
  unfold wt
  congr 1
  ext d
  simp only [Set.mem_setOf_eq]
  rw [← List.map_drop, ← List.map_take, (List.map_injective_iff.mpr hf).eq_iff]

theorem ew_relabelV (f : Relabelling k) (u v : Vtx k) :
    ew k (relabelV f u) (relabelV f v) = ew k u v :=
  wt_map f.inj _ _

theorem isRotated_of_map {f : ℕ → ℕ} (hf : Function.Injective f) {u v : List ℕ}
    (h : u.map f ~r v.map f) : u ~r v := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [← List.map_rotate] at hn
  exact List.map_injective_iff.mpr hf hn

theorem relabelV_isRotated_iff (f : Relabelling k) (u v : Vtx k) :
    ((relabelV f u : List ℕ) ~r (relabelV f v : List ℕ)) ↔ ((u : List ℕ) ~r (v : List ℕ)) :=
  ⟨isRotated_of_map f.inj, fun h => h.map f.toFun⟩

/-- A relabelling maps an `EntriesChain` to an `EntriesChain`. -/
theorem EntriesChain.relabel (hk : 2 ≤ k) (f : Relabelling k) {L : List (List (Vtx k))}
    (h : EntriesChain k L) : EntriesChain k (L.map (List.map (relabelV f))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hnil
    exact h.ne (List.map_eq_nil_iff.mp hnil)
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
    refine List.IsChain.imp ?_ (h.doors Q hQ)
    intro a b hab
    rw [hab, relabelV_tau2V hk]
  · rw [List.isChain_map]
    refine List.IsChain.imp ?_ h.seams
    intro P Q hPQ hP hQ
    have hP' : P ≠ [] := fun hnil => hP (by rw [hnil]; rfl)
    have hQ' : Q ≠ [] := fun hnil => hQ (by rw [hnil]; rfl)
    rw [List.getLast_map, List.head_map, ← relabelV_sigmaInv, ew_relabelV]
    exact hPQ hP' hQ'
  · rw [← List.map_flatten, List.pairwise_map]
    refine List.Pairwise.imp ?_ h.classes
    intro u v huv hrot
    exact huv ((relabelV_isRotated_iff f u v).mp hrot)

/-! ### The relabelling that sends a given vertex to `1 2 … k` -/

/-- The position of a letter in `a`, counted from 1; letters outside `a` are sent far away. -/
def normLabel (a : List ℕ) (x : ℕ) : ℕ :=
  if x ∈ a then a.idxOf x + 1 else x + a.length + 1

theorem normLabel_injective (a : List ℕ) : Function.Injective (normLabel a) := by
  intro x y hxy
  unfold normLabel at hxy
  by_cases hx : x ∈ a <;> by_cases hy : y ∈ a
  · rw [if_pos hx, if_pos hy] at hxy
    exact (List.idxOf_inj hx).mp (by omega)
  · rw [if_pos hx, if_neg hy] at hxy
    have := List.idxOf_lt_length_of_mem hx
    omega
  · rw [if_neg hx, if_pos hy] at hxy
    have := List.idxOf_lt_length_of_mem hy
    omega
  · rw [if_neg hx, if_neg hy] at hxy
    omega

/-- The relabelling that sends the vertex `a` to the word `1 2 … k`. -/
def normRelabelling (a : Vtx k) : Relabelling k where
  toFun := normLabel (a : List ℕ)
  inj := normLabel_injective _
  maps := by
    intro x hx
    have hmem : x ∈ (a : List ℕ) := by
      rw [← List.mem_toFinset, a.2.2]
      exact hx
    have hlt := List.idxOf_lt_length_of_mem hmem
    rw [a.2.length] at hlt
    unfold normLabel
    rw [if_pos hmem, Finset.mem_Icc]
    omega

/-- The word `1 2 … k`. -/
def idWord (k : ℕ) : List ℕ := List.range' 1 k

theorem idWord_isPermWord (k : ℕ) : IsPermWord k (idWord k) := by
  refine ⟨List.nodup_range', ?_⟩
  ext x
  simp only [idWord, List.mem_toFinset, List.mem_range'_1, Finset.mem_Icc]
  omega

/-- The vertex `1 2 … k`. -/
def idVtx (k : ℕ) : Vtx k := ⟨idWord k, idWord_isPermWord k⟩

theorem relabelV_normRelabelling (a : Vtx k) : relabelV (normRelabelling a) a = idVtx k := by
  apply Subtype.ext
  change (a : List ℕ).map (normLabel (a : List ℕ)) = List.range' 1 k
  apply List.ext_getElem
  · simp [a.2.length]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range']
    have hi : i < (a : List ℕ).length := by simpa using h1
    unfold normLabel
    rw [if_pos (List.getElem_mem hi), a.2.nodup.idxOf_getElem i hi]
    omega

/-- Every `EntriesChain` has the same list of piece sizes as one whose first vertex is the word
`1 2 … k`. -/
theorem EntriesChain.exists_normalised (hk : 2 ≤ k) {L : List (List (Vtx k))}
    (h : EntriesChain k L) :
    ∃ L' : List (List (Vtx k)), EntriesChain k L' ∧
      L'.map List.length = L.map List.length ∧
      ∃ tail rest, L' = (idVtx k :: tail) :: rest := by
  obtain ⟨P, rest, rfl⟩ := List.exists_cons_of_ne_nil h.ne
  obtain ⟨a, tail, rfl⟩ := List.exists_cons_of_ne_nil (h.pieces_ne P List.mem_cons_self)
  refine ⟨((a :: tail) :: rest).map (List.map (relabelV (normRelabelling a))),
    h.relabel hk _, ?_, ?_⟩
  · rw [List.map_map]
    apply List.map_congr_left
    intro Q _
    simp
  · refine ⟨tail.map (relabelV (normRelabelling a)),
      rest.map (List.map (relabelV (normRelabelling a))), ?_⟩
    rw [List.map_cons, List.map_cons, relabelV_normRelabelling]

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.relabelV_tau2V
#print axioms SuperpermLowerBounds.ew_relabelV
#print axioms SuperpermLowerBounds.EntriesChain.relabel
#print axioms SuperpermLowerBounds.relabelV_normRelabelling
#print axioms SuperpermLowerBounds.EntriesChain.exists_normalised
