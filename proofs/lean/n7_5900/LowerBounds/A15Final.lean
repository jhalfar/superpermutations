import LowerBounds.A15Pieces

/-!
# No valid configuration of cost at most 135 on 7 symbols
(the written proof, sections 3 and 6)

`A15.no_config_135`: given the caps and the profile statements of the proof of 5,899 (`Caps`,
`Profiles`), table T' (`KS.TableT`), Theorem K (`KS.TheoremK`) and the joint statements S1 .. S5
(`KS.Joint`), no valid `NConfig 7` has cost at most 135.

The proof: Lemma ACC15 (`acc_value`, `acc_weight`), Lemma EPS (`eps_le_one`), Lemma NCH
(`famC_length_le`: no component has more than 8 heavy seams), the pieces of the kernel
(`kernel_pieces`) and of the hanging components (`hanging_exts`), and `core` (the knapsack, the
tables and the joint statements).  No `native_decide`.
-/

namespace SuperpermLowerBounds
namespace A15

open Hunter PreimageChain T5899

/-- **No valid configuration of cost at most 135.** -/
theorem no_config_135 (hC : Caps) (hF : Profiles) (hT : KS.TableT) (hK : KS.TheoremK)
    (hJ : KS.Joint) (c : NConfig 7) (hv : c.Valid) : ¬ c.cost ≤ 135 := by
  intro hc
  have hav := acc_value hv hc
  have haw := acc_weight hv hc
  have heps := eps_le_one hC hF hv hc
  have hlen := famC_length_le hC hv hc
  have hk := kernel_ok hv
  have hposK := hk.pos
  have hlenC : (famC c).length =
      (cutRows c.kernel).length + (c.hanging.flatMap famH).length := by
    unfold famC
    rw [List.length_append]
  have h9 : ∀ H ∈ c.hanging, (cutRows H.rows).length ≤ 9 := by
    intro H hH
    have hs : (famH H).Sublist (c.hanging.flatMap famH) := by
      rw [List.flatMap_def]
      exact List.sublist_flatten_of_mem (List.mem_map.mpr ⟨H, hH, rfl⟩)
    have h1 := hs.length_le
    have h2 := cut_le_famH H
    omega
  have heK : epsR c.kernel ≤ 1 := by
    unfold epsC at heps
    omega
  have heH : ∀ H ∈ c.hanging, epsH H ≤ 1 := by
    intro H hH
    have h1 := nat_le_sum_of_mem (List.mem_map.mpr ⟨H, hH, rfl⟩ : epsH H ∈ c.hanging.map epsH)
    unfold epsC at heps
    omega
  obtain ⟨L0, es0, p0, l0, ok0, cnt0, sub0, v0, w0⟩ := kernel_pieces hk heK (by omega)
  obtain ⟨esH, okH, subH, vH', wH', cntH⟩ := hanging_exts hv heH h9 c.hanging (fun H hH => hH)
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
    refine hd.sublist ?_
    unfold NConfig.entries
    rw [List.flatMap_append, ← List.append_assoc, List.map_append]
    exact sub0.append subH
  · rw [List.map_append, List.sum_append]
    linarith
  · rw [List.map_append, List.sum_append]
    omega

end A15
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.A15.no_config_135
