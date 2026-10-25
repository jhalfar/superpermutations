import K6.TightAlong
import K6.Cap
import LowerBounds.NTheorem

/-!
# The tight case from the parts of the search

`tight_contra`: a family of `T ≤ 3` chains of words with the numbers of a configuration of defect 4
(its first chain with the largest `rows - holes`) and no dead class cannot exist if every part of
the search answers `false`.  The proof relabels the symbols so that the first word is
`1 2 3 4 5 6`, picks the part that the family belongs to and applies `along` and `not_kalong`.

`fam_words`: a valid configuration of cost at most 28 gives such a family (its open trails; its
loops cover every other class).  `no_config_28_of_parts`: hence no valid configuration has cost
at most 28, given the parts.
-/

namespace K6

open SuperpermLowerBounds SuperpermLowerBounds.S SuperpermLowerBounds.PS Hunter PreimageChain

theorem noDeadW_congr {W W' : List (List ℕ)} (h : ∀ u, u ∈ W ↔ u ∈ W') (hd : NoDeadW W) :
    NoDeadW W' := by
  intro v hv hnew
  obtain ⟨Q, h1, h2, h3, h4, h5, h6⟩ := hd v hv (fun u hu => hnew u ((h u).mp hu))
  exact ⟨Q, h1, h2, h3, h4, h5, fun x hx u hu => h6 x hx u ((h u).mpr hu)⟩

/-- The part keys of a family. -/
def keyAt (rows : List (List (List ℕ))) (j : ℕ) : ℕ :=
  match rows[j]? with
  | some P => keyR P
  | none => 0

/-- **The tight case, for a family that starts at `1 2 3 4 5 6`.** -/
theorem tight_contra_id {T g0 n0 n1 fuel : ℕ} (hTle : T ≤ 3) (hg0 : 1 < g0)
    (hparts : ∀ p0, p0 < n0 → ∀ p1, p1 < n1 → part (famRules T g0 n0 p0 n1 p1) fuel = false)
    (hn0 : 0 < n0) (hn1 : 0 < n1)
    (R1 : List (List ℕ)) (C1 : List (List (List ℕ))) (Ds : List (List (List (List ℕ))))
    (hlen : Ds.length + 1 = T)
    (hch : ∀ C ∈ (([1, 2, 3, 4, 5, 6] :: R1) :: C1) :: Ds, IsWChain 6 C ∧ C ≠ [])
    (hcl : List.Pairwise (fun u v : List ℕ => ¬ u ~r v)
      ((([1, 2, 3, 4, 5, 6] :: R1) :: C1) :: Ds).flatten.flatten)
    (hG : hW (([1, 2, 3, 4, 5, 6] :: R1) :: C1) + (Ds.map hW).sum + 5 * (T - 1) ≤ 20)
    (hval : 8 + 4 * (T - 1) + hW (([1, 2, 3, 4, 5, 6] :: R1) :: C1) + (Ds.map hW).sum ≤
      (C1.length + 1) + (Ds.map List.length).sum)
    (hord : ∀ D ∈ Ds, D.length + hW (([1, 2, 3, 4, 5, 6] :: R1) :: C1) ≤ (C1.length + 1) + hW D)
    (hdead : NoDeadW ((([1, 2, 3, 4, 5, 6] :: R1) :: C1) :: Ds).flatten.flatten) : False := by
  have hwordsF : ∀ u ∈ ((([1, 2, 3, 4, 5, 6] :: R1) :: C1) :: Ds).flatten.flatten, PermW 6 u := by
    intro u hu
    obtain ⟨P, hP, huP⟩ := List.mem_flatten.mp hu
    obtain ⟨C, hC, hPC⟩ := List.mem_flatten.mp hP
    exact (hch C hC).1.words P hPC u huP
  -- the part of the family
  set p0 := keyAt ((([1, 2, 3, 4, 5, 6] :: R1) :: C1) :: Ds).flatten (g0 - 1) % n0 with hp0
  set p1 := (match Ds.head? with
    | some D => (match D.head? with
      | some P => keyR P
      | none => 0)
    | none => 0) % n1 with hp1
  have hs := hparts p0 (Nat.mod_lt _ hn0) p1 (Nat.mod_lt _ hn1)
  -- the sequence of rows
  have hFw := (hch _ List.mem_cons_self).1
  have hseq : IsSeq 6 (tagF 2 ((([1, 2, 3, 4, 5, 6] :: R1) :: C1) :: Ds)) :=
    isSeq_tagF (fun C hC => (hch C hC).1) (fun C hC => (hch C hC).2) hcl
      (isChain_trivial (fun _ _ _ _ _ _ => ⟨fun h => absurd h (by decide),
        fun h => absurd h (by decide)⟩) _)
  rw [tagF_cons2] at hseq
  have hsplit : tagC 2 (([1, 2, 3, 4, 5, 6] :: R1) :: C1) ++ tagF 2 Ds =
      (2, [1, 2, 3, 4, 5, 6] :: R1) :: ((C1.map fun Q => (0, Q)) ++ tagF 2 Ds) := by
    simp [tagC]
  rw [hsplit] at hseq
  have hperm : ∀ w ∈ [1, 2, 3, 4, 5, 6] :: R1, PermW 6 w :=
    hFw.words _ List.mem_cons_self
  have hcl1 : List.Pairwise (fun a b => ¬ a ~r b) (([1, 2, 3, 4, 5, 6] :: R1) ++
      (((C1.map fun Q => (0, Q)) ++ tagF 2 Ds).map Prod.snd).flatten) := by
    have := hseq.classes
    simp only [List.map_cons, List.flatten_cons] at this
    exact this
  have hcl1' := List.pairwise_append.mp hcl1
  have hsz := hseq.size_le (2, [1, 2, 3, 4, 5, 6] :: R1) List.mem_cons_self
  have hR1l : R1.length ≤ 4 := by
    simp only [List.length_cons] at hsz
    omega
  have hdoor := S.door_chain (by norm_num) _ hperm
    (hseq.doors (2, [1, 2, 3, 4, 5, 6] :: R1) List.mem_cons_self) hcl1'.1
  have hcont := pcont_of_seq (by norm_num) _ (2, [1, 2, 3, 4, 5, 6] :: R1)
    ([1, 2, 3, 4, 5, 6] :: R1) (List.cons_ne_nil _ _) hseq hcl1'.2.2
  -- the rule along the family
  have hhW1 : hW (([1, 2, 3, 4, 5, 6] :: R1) :: C1) = (4 - R1.length) + hW C1 := by
    rw [hW_cons]
    simp only [List.length_cons]
    omega
  rw [hhW1] at hG hval hord
  have hinv : Inv T g0 n0 p0 n1 p1 Ds C1
      ((famRules T g0 n0 p0 n1 p1).init (4 - R1.length)
        (enc (([1, 2, 3, 4, 5, 6] :: R1).getLast (List.cons_ne_nil _ _))))
      ([1, 2, 3, 4, 5, 6] :: R1) := by
    refine ⟨?_, ?_, fun C hC => hch C (List.mem_cons_of_mem _ hC), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · show 0 + 1 + Ds.length = T
      omega
    · rcases C1 with _ | ⟨Q, C1⟩
      · exact Or.inl rfl
      · exact Or.inr (hFw.infix ⟨[[1, 2, 3, 4, 5, 6] :: R1], [], by simp⟩)
    · show 0 + (4 - R1.length) + hW C1 + (Ds.map hW).sum ≤ 20 - 5 * (T - 1)
      omega
    · show 8 + 4 * (T - 1) + 0 + (4 - R1.length) + hW C1 + (Ds.map hW).sum ≤
        0 + 1 + C1.length + (Ds.map List.length).sum
      omega
    · intro _ C hC
      have h1 := hord C hC
      show C.length + ((4 - R1.length) + hW C1) ≤ (1 + C1.length) + hW C
      omega
    · intro ht
      exact absurd ht (by show ¬ 1 ≤ 0; omega)
    · intro hz
      exact absurd hz (by show ¬ g0 ≤ 1; omega)
    · intro ht
      exact absurd ht (by show ¬ 1 ≤ 0; omega)
    · intro _ P hP
      rw [hp0]
      unfold keyAt
      have e : ((([1, 2, 3, 4, 5, 6] :: R1) :: C1) :: Ds).flatten[g0 - 1]? =
          (C1 ++ Ds.flatten)[g0 - 1 - 1]? := by
        rw [List.flatten_cons, List.cons_append]
        rw [show g0 - 1 = (g0 - 1 - 1) + 1 by omega]
        simp
      change (C1 ++ Ds.flatten)[g0 - 1 - 1]? = some P at hP
      simp only [e, hP]
    · intro _ C hC P hP
      rw [hp1]
      rcases hDh : Ds.head? with _ | D
      · rw [hDh] at hC
        cases hC
      · rw [hDh] at hC
        obtain rfl := Option.mem_some_iff.mp hC
        rcases hDh2 : D.head? with _ | Q
        · rw [hDh2] at hP
          cases hP
        · rw [hDh2] at hP
          obtain rfl := Option.mem_some_iff.mp hP
          simp [hDh2]
    · intro u hu
      apply hwordsF
      simpa using hu
    · refine noDeadW_congr ?_ hdead
      intro u
      simp
  have hA := along (T := T) (g0 := g0) (n0 := n0) (p0 := p0) (n1 := n1) (p1 := p1) hTle Ds C1 _ _
    hinv
  exact not_kalong (famRules T g0 n0 p0 n1 p1) hs R1 _ hR1l hperm hdoor hcl1'.1
    (kcont_of_pcont _ _ _ hcont) hA

theorem flat_relab (e : List ℕ) : ∀ L : List (List (List (List ℕ))),
    (L.map (relabChain e)).flatten.flatten = L.flatten.flatten.map (List.map (relab e))
  | [] => rfl
  | C :: L => by
    simp only [List.map_cons, List.flatten_cons, List.flatten_append, List.map_append,
      flat_relab e L, relabChain, List.map_flatten]

theorem hW_relab (e : List ℕ) (C : List (List (List ℕ))) : hW (relabChain e C) = hW C := by
  unfold hW
  rw [wdef_relabChain]

theorem len_relab (e : List ℕ) (C : List (List (List ℕ))) : (relabChain e C).length = C.length := by
  simp [relabChain]

/-- **The tight case, for a family of chains of words.** -/
theorem tight_contra {T g0 n0 n1 fuel : ℕ} (hTle : T ≤ 3) (hg0 : 1 < g0)
    (hparts : ∀ p0, p0 < n0 → ∀ p1, p1 < n1 → part (famRules T g0 n0 p0 n1 p1) fuel = false)
    (hn0 : 0 < n0) (hn1 : 0 < n1)
    (C0 : List (List (List ℕ))) (Cs : List (List (List (List ℕ))))
    (hlen : Cs.length + 1 = T)
    (hch : ∀ C ∈ C0 :: Cs, IsWChain 6 C ∧ C ≠ [])
    (hcl : List.Pairwise (fun u v : List ℕ => ¬ u ~r v) (C0 :: Cs).flatten.flatten)
    (hG : hW C0 + (Cs.map hW).sum + 5 * (T - 1) ≤ 20)
    (hval : 8 + 4 * (T - 1) + hW C0 + (Cs.map hW).sum ≤ C0.length + (Cs.map List.length).sum)
    (hord : ∀ C ∈ Cs, C.length + hW C0 ≤ C0.length + hW C)
    (hdead : NoDeadW (C0 :: Cs).flatten.flatten) : False := by
  have hC0 := hch C0 List.mem_cons_self
  obtain ⟨P0, C0t, rfl⟩ := List.exists_cons_of_ne_nil hC0.2
  have hP0 : P0 ≠ [] := hC0.1.pieces_ne P0 List.mem_cons_self
  obtain ⟨v0, R0, rfl⟩ := List.exists_cons_of_ne_nil hP0
  have hv0 : PermW 6 v0 := hC0.1.words _ List.mem_cons_self v0 List.mem_cons_self
  have hwords0 : ∀ u ∈ (((v0 :: R0) :: C0t) :: Cs).flatten.flatten, PermW 6 u := by
    intro u hu
    obtain ⟨P, hP, huP⟩ := List.mem_flatten.mp hu
    obtain ⟨C, hC, hPC⟩ := List.mem_flatten.mp hP
    exact (hch C hC).1.words P hPC u huP
  have hid : v0.map (relab v0) = [1, 2, 3, 4, 5, 6] := by
    have e := map_relab_self hv0.1
    rw [hv0.2.1] at e
    rw [e]
    rfl
  have hC0r : relabChain v0 ((v0 :: R0) :: C0t) =
      ([1, 2, 3, 4, 5, 6] :: R0.map (List.map (relab v0))) :: relabChain v0 C0t := by
    simp [relabChain, hid]
  have hF : (((v0 :: R0) :: C0t) :: Cs).map (relabChain v0) =
      (([1, 2, 3, 4, 5, 6] :: R0.map (List.map (relab v0))) :: relabChain v0 C0t) ::
        Cs.map (relabChain v0) := by
    rw [List.map_cons, hC0r]
  have hflat := flat_relab v0 (((v0 :: R0) :: C0t) :: Cs)
  rw [hF] at hflat
  have hlen0 : (relabChain v0 C0t).length + 1 = ((v0 :: R0) :: C0t).length := by
    rw [len_relab]
    rfl
  have hmapW : (Cs.map (relabChain v0)).map hW = Cs.map hW := by
    rw [List.map_map]
    exact List.map_congr_left (fun C _ => hW_relab v0 C)
  have hmapL : (Cs.map (relabChain v0)).map List.length = Cs.map List.length := by
    rw [List.map_map]
    exact List.map_congr_left (fun C _ => len_relab v0 C)
  apply tight_contra_id hTle hg0 hparts hn0 hn1 (R0.map (List.map (relab v0)))
    (relabChain v0 C0t) (Cs.map (relabChain v0)) (by rw [List.length_map]; exact hlen)
  · intro C hC
    rw [← hF] at hC
    obtain ⟨C', hC', rfl⟩ := List.mem_map.mp hC
    refine ⟨(hch C' hC').1.relabel hv0, ?_⟩
    have := (hch C' hC').2
    unfold relabChain
    simpa using this
  · rw [hflat, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ hcl
    intro a b ha hb hab
    exact not_isRotated_map_relab hv0 (hwords0 a ha) (hwords0 b hb) hab
  · rw [← hC0r, hW_relab, hmapW]
    exact hG
  · rw [← hC0r, hW_relab, hmapW, hmapL, hlen0]
    exact hval
  · intro D hD
    obtain ⟨C', hC', rfl⟩ := List.mem_map.mp hD
    rw [← hC0r, hW_relab, hW_relab, len_relab, hlen0]
    exact hord C' hC'
  · rw [hflat]
    exact hdead.relabel hv0 hwords0

end K6

#print axioms K6.tight_contra
