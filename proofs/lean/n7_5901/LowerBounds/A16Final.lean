import LowerBounds.A16Pieces

/-!
# No valid configuration of cost at most 136 on 7 symbols
(the written proof `proofs/n7_5901/PROOF_5901.md`, sections 2 and 5)

`A16.no_config_136`: given the caps and the profile statements of the proof of 5,899 (`Caps`, `Profiles`),
the ring row of table T' (`KS.TableT`), Theorem K16 (`K16.TheoremK16`) and the joint statements of Table C
(`K16.Joint16`), no valid `NConfig 7` has cost at most 136.

The proof: Lemma ACC16 (`acc_value`, `acc_weight`), Lemma EPS16 (`eps_le_two`), at most 11 chains
(`famC_length_le`), the pieces of the kernel (`kernel_pieces16`) and of the hanging components
(`hanging_exts16`), and `core` (the knapsack, the tables and the joint statements).  No `native_decide`.
-/

namespace SuperpermLowerBounds
namespace A16

open Hunter PreimageChain T5899

theorem pairwise_of_subperm {α : Type} {R : α → α → Prop} (hs : ∀ {x y}, R x y → R y x)
    {l₁ l₂ : List α} (h : l₁.Subperm l₂) (h2 : l₂.Pairwise R) : l₁.Pairwise R := by
  obtain ⟨l, hp, hsub⟩ := h
  exact (hp.pairwise_iff hs).mp (h2.sublist hsub)

/-- **No valid configuration of cost at most 136.** -/
theorem no_config_136 (hC : Caps) (hF : Profiles) (hT : KS.TableT) (hK : K16.TheoremK16)
    (hJ : K16.Joint16) (c : NConfig 7) (hv : c.Valid) : ¬ c.cost ≤ 136 := by
  intro hc
  have hav := acc_value hv hc
  have haw := acc_weight hv hc
  have heps := eps_le_two hC hF hv hc
  have hlen := famC_length_le hC hv hc
  have hk := kernel_ok hv
  have hposK := hk.pos
  have hlenC : (famC c).length =
      (cutRows c.kernel).length + (c.hanging.flatMap famH).length := by
    unfold famC
    rw [List.length_append]
  have h11 : ∀ H ∈ c.hanging, (cutRows H.rows).length ≤ 11 := by
    intro H hH
    have hs : (famH H).Sublist (c.hanging.flatMap famH) := by
      rw [List.flatMap_def]
      exact List.sublist_flatten_of_mem (List.mem_map.mpr ⟨H, hH, rfl⟩)
    have h1 := hs.length_le
    have h2 := A15.cut_le_famH H
    omega
  obtain ⟨L0, es0, p0, l0, ok0, cnt0, sub0, v0, w0⟩ := kernel_pieces16 hk (by omega)
  obtain ⟨esH, okH, subH, vH', wH', cntH⟩ := hanging_exts16 hv h11 c.hanging (fun H hH => hH)
  refine core hK hT hJ p0 l0 (es0 ++ esH) ?_ ?_ ?_ ?_ ?_
  · intro e he
    rcases List.mem_append.mp he with h | h
    · exact ok0 e h
    · exact okH e h
  · rw [List.countP_append]
    unfold epsC at heps
    omega
  · have hd : (c.entries.map Subtype.val).Pairwise (fun u v : List ℕ => ¬ u ~r v) := by
      rw [List.pairwise_map]
      exact hv.distinct
    refine pairwise_of_subperm (fun h hr => h hr.symm) ?_ hd
    unfold NConfig.entries
    rw [List.flatMap_append, ← List.append_assoc, List.map_append]
    exact subperm_append sub0.subperm subH
  · rw [List.map_append, List.sum_append]
    linarith
  · rw [List.map_append, List.sum_append]
    omega

end A16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.A16.no_config_136
