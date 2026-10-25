import K6.Family

/-!
# The family of a whole configuration on 6 symbols

`opens c`, `closeds c`, `loops c`: the pieces of the kernel and of all hanging components.
`fam_spec`: they are the rows of the configuration up to order, the open trails are trails (at
least one), the closed trails are `Closed`, the loops have 4 blocks, and
`(open trails) + rows ≤ cost + 1`.  `fam_count`: with the number of blocks (at least 120, one per
rotation class), the three numbers that the arithmetic of `Knap.lean` and `Tight.lean` uses.
-/

namespace K6

open SuperpermLowerBounds Hunter PreimageChain

variable {c : NConfig 6}

/-- The open trails of a configuration. -/
noncomputable def opens (c : NConfig 6) : List (List (NRow 6)) :=
  cutRows c.kernel ++ c.hanging.flatMap famO

/-- The closed trails of a configuration. -/
noncomputable def closeds (c : NConfig 6) : List (List (NRow 6)) := c.hanging.flatMap famC

/-- The loops of a configuration. -/
noncomputable def loops (c : NConfig 6) : List (NRow 6) := c.hanging.flatMap famL

/-- All rows of a configuration. -/
def allRows (c : NConfig 6) : List (NRow 6) := c.kernel ++ c.hanging.flatMap NHanging.rows

theorem perm_rearrange {α : Type*} {a b c' d e f X Y : List α} (h1 : (a ++ c' ++ e).Perm X)
    (h2 : (b ++ d ++ f).Perm Y) : ((a ++ b) ++ (c' ++ d) ++ (e ++ f)).Perm (X ++ Y) := by
  refine List.Perm.trans ?_ (h1.append h2)
  classical
  rw [List.perm_iff_count]
  intro x
  simp only [List.count_append]
  omega

theorem hang_sum (hv : c.Valid) : ∀ hs : List (NHanging 6), (∀ H ∈ hs, H ∈ c.hanging) →
    (∀ A ∈ hs.flatMap famO, Trail 6 A) ∧
      ((hs.flatMap famO).flatten ++ (hs.flatMap famC).flatten ++ hs.flatMap famL).Perm
        (hs.flatMap NHanging.rows) ∧
      (hs.flatMap famO).length + (hs.flatMap NHanging.rows).length ≤ (hs.map NHanging.cost).sum ∧
      (∀ C ∈ hs.flatMap famC, Closed C) ∧ (∀ r ∈ hs.flatMap famL, r.len = 4)
  | [], _ => by simp
  | H :: hs, h => by
    obtain ⟨t1, p1, c1, k1, l1⟩ := hang_spec hv (h H List.mem_cons_self)
    obtain ⟨t2, p2, c2, k2, l2⟩ := hang_sum hv hs (fun H' hH' => h H' (List.mem_cons_of_mem _ hH'))
    simp only [List.flatMap_cons, List.flatten_append, List.length_append, List.map_cons,
      List.sum_cons, List.mem_append]
    refine ⟨?_, perm_rearrange p1 p2, by omega, ?_, ?_⟩
    · rintro A (hA | hA)
      · exact t1 A hA
      · exact t2 A hA
    · rintro C (hC | hC)
      · exact k1 C hC
      · exact k2 C hC
    · rintro r (hr | hr)
      · exact l1 r hr
      · exact l2 r hr

/-- **The family of a configuration.** -/
theorem fam_spec (hv : c.Valid) :
    opens c ≠ [] ∧ (∀ A ∈ opens c, Trail 6 A) ∧
      ((opens c).flatten ++ (closeds c).flatten ++ loops c).Perm (allRows c) ∧
      (∀ C ∈ closeds c, Closed C) ∧ (∀ r ∈ loops c, r.len = 4) ∧
      (opens c).length + (allRows c).length ≤ c.cost + 1 := by
  have hk := kernel_ok hv
  obtain ⟨t2, p2, c2, k2, l2⟩ := hang_sum hv c.hanging (fun H hH => hH)
  have hcost : c.cost = (c.kernel.length + rX c.kernel) + (c.hanging.map NHanging.cost).sum := rfl
  have hcnt := hk.cnt
  have hpos := hk.pos
  unfold opens closeds loops allRows
  refine ⟨?_, ?_, ?_, k2, l2, ?_⟩
  · intro h
    have := congrArg List.length h
    simp only [List.length_append, List.length_nil] at this
    omega
  · intro A hA
    rcases List.mem_append.mp hA with h1 | h1
    · exact hk.fam.trails A h1
    · exact t2 A h1
  · rw [List.flatten_append, hk.inv.flat]
    have e : c.kernel ++ (c.hanging.flatMap famO).flatten ++ (c.hanging.flatMap famC).flatten ++
        c.hanging.flatMap famL =
        c.kernel ++ ((c.hanging.flatMap famO).flatten ++ (c.hanging.flatMap famC).flatten ++
          c.hanging.flatMap famL) := by simp
    rw [e]
    exact p2.append_left _
  · simp only [List.length_append]
    omega

theorem rowsEntries_allRows (c : NConfig 6) : rowsEntries (allRows c) = c.entries := by
  unfold allRows NConfig.entries rowsEntries
  rw [List.flatMap_append, List.flatMap_assoc]

/-- A valid configuration on 6 symbols has at least 120 blocks. -/
theorem entries_length_ge (hv : c.Valid) : 120 ≤ c.entries.length := by
  have hall : ∀ v : Vtx 6, v ∈ lineWalk c.entries :=
    fun v => (mem_lineWalk (by norm_num)).mpr (hv.cover v)
  have h1 : Fintype.card (Vtx 6) ≤ (lineWalk c.entries).length := by
    calc Fintype.card (Vtx 6) = (Finset.univ : Finset (Vtx 6)).card := Finset.card_univ.symm
      _ ≤ (lineWalk c.entries).toFinset.card :=
          Finset.card_le_card (fun v _ => List.mem_toFinset.mpr (hall v))
      _ ≤ (lineWalk c.entries).length := List.toFinset_card_le _
  rw [Hunter.ProofsRecursion.card_Vtx, length_lineWalk] at h1
  have h6 : Nat.factorial 6 = 720 := by decide
  omega

theorem rowsHoles_loops {L : List (NRow 6)} (h : ∀ r ∈ L, r.len = 4) : rowsHoles 6 L = L.length := by
  induction L with
  | nil => rfl
  | cons r L ih =>
    rw [rowsHoles_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), h r List.mem_cons_self]
    simp only [List.length_cons]
    omega

/-- **The numbers of the family.**  `RO, HO` rows and holes of the open trails, `RC, HC` of the
closed trails, `L` loops, `N` blocks. -/
theorem fam_count (hv : c.Valid) :
    (rowsEntries ((opens c).flatten ++ (closeds c).flatten ++ loops c)).length +
        rowsHoles 6 (opens c).flatten + rowsHoles 6 (closeds c).flatten + (loops c).length =
      5 * ((opens c).flatten.length + (closeds c).flatten.length + (loops c).length) ∧
    120 ≤ (rowsEntries ((opens c).flatten ++ (closeds c).flatten ++ loops c)).length ∧
    (opens c).length + ((opens c).flatten.length + (closeds c).flatten.length + (loops c).length)
      ≤ c.cost + 1 := by
  obtain ⟨_, _, hp, _, hl, hcst⟩ := fam_spec hv
  have hlen := hv.len_le (by norm_num : 2 ≤ 6)
  have hall : ∀ r ∈ allRows c, r.len ≤ 5 := by
    intro r hr
    unfold allRows at hr
    rcases List.mem_append.mp hr with h | h
    · exact hlen.1 r h
    · obtain ⟨H, hH, hrH⟩ := List.mem_flatMap.mp h
      exact hlen.2 H hH r hrH
  have hall' : ∀ r ∈ (opens c).flatten ++ (closeds c).flatten ++ loops c, r.len ≤ 5 :=
    fun r hr => hall r (hp.subset hr)
  have hE := rowsEntries_length_add_holes (k := 6) hall'
  have hN : (rowsEntries ((opens c).flatten ++ (closeds c).flatten ++ loops c)).length =
      c.entries.length := by
    rw [← rowsEntries_allRows]
    unfold rowsEntries
    exact (List.Perm.flatMap_right NRow.entries hp).length_eq
  have hrl := hp.length_eq
  simp only [rowsHoles_append, List.length_append] at hE hrl
  rw [rowsHoles_loops hl] at hE
  refine ⟨by omega, by rw [hN]; exact entries_length_ge hv, by omega⟩

end K6
