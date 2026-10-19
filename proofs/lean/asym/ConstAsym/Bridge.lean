import Challenge
import Hunter.Bounds

/-!
# Covering words (Pantone) and superpermutations (Hunter–Raudvere)

Pantone's `SuperpermutationBounds.Covers w` (words `List (Fin k)`, letters `0, …, k-1`) says that every
duplicate-free list of length `k` is a factor of `w`.  The Hunter–Raudvere library (commit d452221) uses words
`List ℕ` with letters `1, …, k`: `Hunter.IsSuperperm k w` says that every `v` with `Hunter.IsPermWord k v`
(duplicate-free, set of letters exactly `{1, …, k}`) is a factor of `w`, and `Hunter.Ssuper k` is the least length of
such a word.

Adding one to every letter turns a covering word into a superpermutation of the library; subtracting one goes back.
Neither map changes the length.  This is `BridgeCore.lean` stated directly for the library's
own definitions (there they were restated and identified by `rfl`).
-/

namespace ConstAsym

open SuperpermutationBounds

/-- Letter `a` of `0, …, k-1` as letter `a + 1` of `1, …, k`. -/
def up {k : ℕ} (a : Fin k) : ℕ := a.val + 1

theorem up_injective {k : ℕ} : Function.Injective (up : Fin k → ℕ) := by
  intro a b h
  apply Fin.ext
  unfold up at h
  omega

/-- A letter of `1, …, k` as a letter of `0, …, k-1`; any other number goes somewhere. -/
def down (k : ℕ) (hk : 0 < k) (s : ℕ) : Fin k := ⟨(s - 1) % k, Nat.mod_lt _ hk⟩

theorem down_up {k : ℕ} (hk : 0 < k) (a : Fin k) : down k hk (up a) = a := by
  apply Fin.ext
  simp [down, up, Nat.mod_eq_of_lt a.isLt]

theorem up_down {k : ℕ} (hk : 0 < k) {s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ k) :
    up (down k hk s) = s := by
  have : (s - 1) % k = s - 1 := Nat.mod_eq_of_lt (by omega)
  simp only [up, down, this]
  omega

theorem isPermWord_length {k : ℕ} {w : List ℕ} (h : Hunter.IsPermWord k w) : w.length = k := by
  have h1 := List.toFinset_card_of_nodup h.1
  rw [h.2, Nat.card_Icc] at h1
  omega

/-- A permutation in Pantone's sense is one in Hunter–Raudvere's after the shift. -/
theorem isPermWord_map_up {k : ℕ} {p : List (Fin k)} (hlen : p.length = k) (hnd : p.Nodup) :
    Hunter.IsPermWord k (p.map up) := by
  have hnd' : (p.map up).Nodup := hnd.map up_injective
  refine ⟨hnd', ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    rw [Finset.mem_Icc]
    have := a.isLt
    unfold up
    omega
  · rw [List.toFinset_card_of_nodup hnd', Nat.card_Icc, List.length_map, hlen]
    omega

/-- Every permutation in Hunter–Raudvere's sense is the shift of one in Pantone's. -/
theorem exists_of_isPermWord {k : ℕ} {v : List ℕ} (hv : Hunter.IsPermWord k v) :
    ∃ p : List (Fin k), p.length = k ∧ p.Nodup ∧ p.map up = v := by
  have hmem : ∀ x ∈ v, 1 ≤ x ∧ x ≤ k := by
    intro x hx
    have hx' : x ∈ v.toFinset := List.mem_toFinset.mpr hx
    rw [hv.2] at hx'
    exact Finset.mem_Icc.mp hx'
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hnil : v = [] := by
      cases v with
      | nil => rfl
      | cons x t =>
        have := hmem x (by simp)
        omega
    exact ⟨[], rfl, List.nodup_nil, by simp [hnil]⟩
  · have hback : (v.map (down k hk)).map up = v := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id v]
      apply List.map_congr_left
      intro x hx
      exact up_down hk (hmem x hx).1 (hmem x hx).2
    refine ⟨v.map (down k hk), ?_, ?_, hback⟩
    · rw [List.length_map]
      exact isPermWord_length hv
    · apply List.Nodup.of_map up
      rw [hback]
      exact hv.1

/-- A covering word, shifted, is a superpermutation of the library. -/
theorem isSuperperm_map_up {k : ℕ} {w : List (Fin k)} (h : Covers w) :
    Hunter.IsSuperperm k (w.map up) := by
  intro v hv
  obtain ⟨p, hlen, hnd, rfl⟩ := exists_of_isPermWord hv
  obtain ⟨u, t, rfl⟩ := h p hlen hnd
  exact ⟨u.map up, t.map up, by simp [List.map_append]⟩

/-- A superpermutation of the library, shifted back, is a covering word. -/
theorem covers_map_down {k : ℕ} (hk : 0 < k) {w : List ℕ} (h : Hunter.IsSuperperm k w) :
    Covers (w.map (down k hk)) := by
  intro p hlen hnd
  obtain ⟨u, t, hut⟩ := h (p.map up) (isPermWord_map_up hlen hnd)
  refine ⟨u.map (down k hk), t.map (down k hk), ?_⟩
  have hp : (p.map up).map (down k hk) = p := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id p]
    apply List.map_congr_left
    intro a _
    exact down_up hk a
  rw [← hut, List.map_append, List.map_append, hp]

/-- Some superpermutation exists (all permutations of `1, …, k` written one after another). -/
theorem exists_isSuperperm (k : ℕ) : ∃ w : List ℕ, Hunter.IsSuperperm k w := by
  refine ⟨(List.range' 1 k).permutations.flatten, ?_⟩
  intro v hv
  apply List.infix_of_mem_flatten
  rw [List.mem_permutations]
  apply List.perm_of_nodup_nodup_toFinset_eq hv.1 List.nodup_range'
  rw [hv.2]
  ext x
  simp [List.mem_range'_1, Finset.mem_Icc]
  omega

/-- Every covering word has at least `Hunter.Ssuper k` letters. -/
theorem ssuper_le_length {k : ℕ} {w : List (Fin k)} (h : Covers w) :
    Hunter.Ssuper k ≤ w.length := by
  unfold Hunter.Ssuper
  exact Nat.sInf_le ⟨w.map up, isSuperperm_map_up h, by simp⟩

/-- A covering word of length exactly `Hunter.Ssuper k` exists (`0 < k`). -/
theorem exists_covers_length_eq {k : ℕ} (hk : 0 < k) :
    ∃ w : List (Fin k), Covers w ∧ w.length = Hunter.Ssuper k := by
  have hne : {m | ∃ w : List ℕ, Hunter.IsSuperperm k w ∧ w.length = m}.Nonempty := by
    obtain ⟨w, hw⟩ := exists_isSuperperm k
    exact ⟨w.length, w, hw, rfl⟩
  obtain ⟨w, hw, hl⟩ := Nat.sInf_mem hne
  exact ⟨w.map (down k hk), covers_map_down hk hw, by rw [List.length_map]; exact hl⟩

/-- `Hunter.Ssuper k` is the least length of a covering word in Pantone's sense (`0 < k`). -/
theorem ssuper_eq_sInf {k : ℕ} (hk : 0 < k) :
    Hunter.Ssuper k = sInf {m | ∃ w : List (Fin k), Covers w ∧ w.length = m} := by
  apply le_antisymm
  · obtain ⟨w, hw, hl⟩ := exists_covers_length_eq hk
    have hne : {m | ∃ w : List (Fin k), Covers w ∧ w.length = m}.Nonempty := ⟨_, w, hw, hl⟩
    obtain ⟨w', hw', hl'⟩ := Nat.sInf_mem hne
    rw [← hl']
    exact ssuper_le_length hw'
  · obtain ⟨w, hw, hl⟩ := exists_covers_length_eq hk
    exact Nat.sInf_le ⟨w, hw, hl⟩

end ConstAsym
