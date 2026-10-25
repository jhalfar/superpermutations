import LowerBounds.PGlue
import LowerBounds.PTrails

/-!
# The family of a configuration on 6 symbols

A valid standard configuration (`NConfig 6`, `NConfig.Valid`) falls into

* **open trails**: the kernel cut at its seams of weight other than 3; every hanging component with
  a paid attachment cut the same way; every hanging component with a free attachment and at least
  one heavy seam, cut and read cyclically (its last trail glued in front of its first one, which is
  possible because the free attachment is a seam of weight 3, `free_geom`);
* **closed trails**: the hanging components with a free attachment, no heavy seam and at least two
  rows;
* **loops**: the hanging components with a free attachment and one row; that row has 4 blocks.

`fam_spec`: these rows are the rows of the configuration (up to order), the open trails are trails,
there is at least one, every closed trail glues through the class it skips into a trail with one
row and 6 holes fewer (`Closed`), every loop has 4 blocks, and
`(open trails) + rows ≤ cost + 1`.

This is the accounting of the 5,899 proof (`PShapes.lean`, `PHanging.lean` of `../n7`) on 6
symbols, cut down to what the proof of 871 and 872 needs: no sequences with links of weight 4 and no
rings, but the closed trails and the loops as objects of their own.  The lemmas `RowsOK`,
`free_geom`, `glue_ring` are those of `PShapes.lean` with 7 replaced by 6.
-/

namespace K6

open SuperpermLowerBounds Hunter PreimageChain

/-! ### Rows of a component (as in `PShapes.lean`) -/

/-- What the rows of a component of a valid configuration satisfy. -/
structure RowsOK (R : List (NRow 6)) : Prop where
  ne : R ≠ []
  len : ∀ r ∈ R, 1 ≤ r.len
  seams : ∀ w ∈ seamWeights R, 3 ≤ w
  classes : (rowsEntries R).Pairwise (NotRot (k := 6))

namespace RowsOK

variable {R : List (NRow 6)}

theorem inv (h : RowsOK R) : CutInv R (cutRows R) := cutRows_spec R h.seams

theorem fam (h : RowsOK R) : TrailFam 6 (cutRows R) :=
  cutRows_trailFam h.seams h.len h.classes

theorem cnt (h : RowsOK R) : (cutRows R).length ≤ rX R + 1 := h.inv.cnt h.ne

theorem pos (h : RowsOK R) : 1 ≤ (cutRows R).length := by
  have hf := h.inv.flat
  cases hS : cutRows R with
  | nil =>
      rw [hS] at hf
      exact absurd hf.symm h.ne
  | cons A S => simp

theorem len_le (h : RowsOK R) : ∀ r ∈ R, r.len ≤ 5 :=
  fun _ hr => len_le_of_rowsEntries_pairwise (by norm_num) h.classes hr

/-- With at least two trails: the first and the last trail and their end rows. -/
theorem decomp2 (h : RowsOK R) (h2 : 2 ≤ (cutRows R).length) :
    ∃ (first last : List (NRow 6)) (mid : List (List (NRow 6))) (r₁ r : NRow 6)
      (A B : List (NRow 6)), cutRows R = first :: (mid ++ [last]) ∧ first = r₁ :: B ∧
        last = A ++ [r] ∧ R.head? = some r₁ ∧ R.getLast? = some r := by
  obtain ⟨first, mid, last, hS⟩ := exists_first_mid_last h2
  have inv := h.inv
  have hfne : first ≠ [] := inv.ne first (by rw [hS]; exact List.mem_cons_self)
  have hlne : last ≠ [] := inv.ne last (by rw [hS]; simp)
  obtain ⟨r₁, B, hf⟩ := List.exists_cons_of_ne_nil hfne
  have hl : last = last.dropLast ++ [last.getLast hlne] :=
    (List.dropLast_concat_getLast hlne).symm
  refine ⟨first, last, mid, r₁, last.getLast hlne, last.dropLast, B, hS, hf, hl, ?_, ?_⟩
  · rw [← inv.flat, hS, hf]
    rfl
  · rw [← inv.flat, hS]
    have e : (first :: (mid ++ [last])).flatten =
        (first ++ mid.flatten ++ last.dropLast) ++ [last.getLast hlne] := by
      rw [List.flatten_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.append_assoc, List.append_assoc, ← hl]
    rw [e, List.getLast?_concat]

/-- With one trail: the rows are that trail and no seam is heavy. -/
theorem single (h : RowsOK R) (h1 : (cutRows R).length = 1) :
    cutRows R = [R] ∧ Trail 6 R ∧ rX R = 0 := by
  obtain ⟨X, hX⟩ := List.length_eq_one_iff.mp h1
  have hf := h.inv.flat
  rw [hX, List.flatten_cons, List.flatten_nil, List.append_nil] at hf
  subst hf
  exact ⟨hX, h.fam.trails X (by rw [hX]; exact List.mem_singleton_self _), h.inv.single h1⟩

end RowsOK

variable {c : NConfig 6} {H : NHanging 6}

theorem hanging_entries_sublist (hH : H ∈ c.hanging) :
    (rowsEntries H.rows).Sublist c.entries := by
  unfold NConfig.entries
  refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
  rw [List.flatMap_def]
  exact List.sublist_flatten_of_mem (List.mem_map.mpr ⟨H, hH, rfl⟩)

theorem hanging_ok (hv : c.Valid) (hH : H ∈ c.hanging) : RowsOK H.rows :=
  ⟨hv.hanging_ne H hH, hv.hanging_len H hH, hv.hanging_seams H hH,
    hv.distinct.sublist (hanging_entries_sublist hH)⟩

theorem kernel_ok (hv : c.Valid) : RowsOK c.kernel :=
  ⟨hv.kernel_ne, hv.kernel_len, hv.kernel_seams,
    hv.distinct.sublist (List.sublist_append_left _ _)⟩

/-- **A free attachment** as a junction (the two end rows and the class between them merge),
with the link of weight 3 from the last row to the first one. -/
theorem free_geom (hv : c.Valid) (hH : H ∈ c.hanging) (ha : H.att = 0) {r r₁ : NRow 6}
    (hr : H.rows.getLast? = some r) (hr₁ : H.rows.head? = some r₁) :
    Junction 6 r r₁ (tau2V r.lastEntry) [mergeRow r r₁] ∧ SLink 6 3 r.lastEntry r₁.entry ∧
      r₁.entry = tau2V (tau2V r.lastEntry) ∧
      ∀ e ∈ rowsEntries H.rows, NotRot (tau2V r.lastEntry) e := by
  have g0 := hv.w0_ge H hH
  have g1 := hv.w1_ge H hH
  have h0 : H.w0 = 2 := by unfold NHanging.att at ha; omega
  have h1 : H.w1 = 2 := by unfold NHanging.att at ha; omega
  obtain ⟨hs, he, _⟩ := hv.free_attachment (by norm_num) hH hr hr₁ h0 h1
  have hok := hanging_ok hv hH
  refine ⟨junction_merge (hok.len r (List.mem_of_getLast? hr)) (hok.len r₁ (List.mem_of_head? hr₁))
    he, ?_, he, ?_⟩
  · rw [he]
    exact sLink_three_tau2V_tau2V (by norm_num) r.lastEntry
  · intro e hem hrot
    apply hv.slot_not_own hH e hem
    rw [hs]
    have h2 : ((tau2V r.lastEntry : Vtx 6) : List ℕ) ~r
        ((sigmaInv (tau2V r.lastEntry) : Vtx 6) : List ℕ) := ⟨6 - 1, rfl⟩
    exact h2.symm.trans hrot

/-- Rows that form one trail, glued through a junction: the last row to the first row. -/
theorem glue_ring {R : List (NRow 6)} (hok : RowsOK R) (h1 : (cutRows R).length = 1)
    (hm : 2 ≤ R.length)
    {r r₁ : NRow 6} (hr : R.getLast? = some r) (hr₁ : R.head? = some r₁) {x : Vtx 6}
    {J : List (NRow 6)} (hJ : Junction 6 r r₁ x J) (hx : ∀ e ∈ rowsEntries R, NotRot x e) :
    ∃ T : List (NRow 6), Trail 6 T ∧ (rowsEntries T).Pairwise (NotRot (k := 6)) ∧
      T.length + 2 = R.length + J.length ∧ (∀ j ∈ J, j ∈ T) ∧
      rowsHoles 6 T + rowsHoles 6 [r, r₁] = rowsHoles 6 R + rowsHoles 6 J := by
  obtain ⟨_, hT, _⟩ := hok.single h1
  obtain ⟨r₁', A, r', hR⟩ := exists_first_mid_last hm
  have hh : R.head? = some r₁' := by rw [hR]; rfl
  have hg : R.getLast? = some r' := by
    rw [hR, ← List.cons_append, List.getLast?_concat]
  rw [hr₁] at hh
  rw [hr] at hg
  obtain rfl := Option.some.inj hh
  obtain rfl := Option.some.inj hg
  rw [hR] at hT hx
  have hcl := hok.classes
  rw [hR] at hcl
  obtain ⟨g1, g2, _⟩ := ring_glue hT hcl hJ hx
  refine ⟨glue A J [], g1, g2, ?_, ?_, ?_⟩
  · rw [ring_glue_length, hR]
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  · intro j hj
    unfold glue
    exact List.mem_append_right _ (List.mem_append_left _ hj)
  · rw [hR]
    exact ring_glue_holes A J r r₁

theorem holes_merge6 {r r₁ : NRow 6} (h : r.len + (r₁.len + 1) ≤ 5) :
    rowsHoles 6 [mergeRow r r₁] + 6 = rowsHoles 6 [r, r₁] := by
  simp only [rowsHoles, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mergeRow]
  omega

/-- `τ₂` has no period shorter than 5 on 6 symbols. -/
theorem tau2V_iterate_ne (e : Vtx 6) {j : ℕ} (h0 : 0 < j) (h5 : j < 5) : tau2V^[j] e ≠ e := by
  intro h
  have hne : (e : List ℕ) ≠ [] := by
    intro h'
    have hl := e.2.length
    rw [h'] at hl
    simp at hl
  have hv : (e : List ℕ) = (e : List ℕ).dropLast ++ [(e : List ℕ).getLast hne] :=
    (List.dropLast_append_getLast hne).symm
  have hlen : (e : List ℕ).dropLast.length = 5 := by
    rw [List.length_dropLast, e.2.length]
  have hval := tau2V_iterate_val (by norm_num) e _ _ hv j
  rw [h] at hval
  have hrot : (e : List ℕ).dropLast.rotate j = (e : List ℕ).dropLast := by
    have h2 := hval.symm.trans hv
    exact List.append_cancel_right h2.symm |>.symm
  have hnd : (e : List ℕ).dropLast.Nodup := e.2.nodup.sublist (List.dropLast_sublist _)
  rcases (hnd.rotate_eq_self_iff).mp hrot with h1 | h1
  · rw [hlen] at h1
    omega
  · rw [h1] at hlen
    simp at hlen

/-! ### The pieces of a hanging component -/

/-- A closed trail: a trail of at least two rows whose last row, the class it skips and its
first row glue into a trail with one row and 6 holes fewer and pairwise different classes. -/
structure Closed (C : List (NRow 6)) : Prop where
  trail : Trail 6 C
  two : 2 ≤ C.length
  glue : ∃ T : List (NRow 6), Trail 6 T ∧ (rowsEntries T).Pairwise (NotRot (k := 6)) ∧
    T.length + 1 = C.length ∧ rowsHoles 6 T + 6 = rowsHoles 6 C

/-- The open trails of a hanging component. -/
noncomputable def famO (H : NHanging 6) : List (List (NRow 6)) :=
  if H.att = 0 then (if 2 ≤ (cutRows H.rows).length then rotSegs (cutRows H.rows) else [])
  else cutRows H.rows

/-- The closed trail of a hanging component (none or one). -/
noncomputable def famC (H : NHanging 6) : List (List (NRow 6)) :=
  if H.att = 0 ∧ (cutRows H.rows).length < 2 ∧ 2 ≤ H.rows.length then [H.rows] else []

/-- The loop of a hanging component (none or one row). -/
noncomputable def famL (H : NHanging 6) : List (NRow 6) :=
  if H.att = 0 ∧ (cutRows H.rows).length < 2 ∧ H.rows.length < 2 then H.rows else []

theorem rot_rows_perm (first last : List (NRow 6)) (mid : List (List (NRow 6))) :
    ((mid ++ [last ++ first]).flatten).Perm ((first :: (mid ++ [last])).flatten) := by
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [← List.append_assoc]
  exact List.perm_append_comm

/-- **The pieces of a hanging component.** -/
theorem hang_spec (hv : c.Valid) (hH : H ∈ c.hanging) :
    (∀ A ∈ famO H, Trail 6 A) ∧
      ((famO H).flatten ++ (famC H).flatten ++ famL H).Perm H.rows ∧
      (famO H).length + H.rows.length ≤ H.cost ∧ (∀ C ∈ famC H, Closed C) ∧
      (∀ r ∈ famL H, r.len = 4) := by
  have hok := hanging_ok hv hH
  have inv := hok.inv
  have hcost : H.cost = H.rows.length + rX H.rows + H.att := rfl
  by_cases ha : H.att = 0
  · by_cases h2 : 2 ≤ (cutRows H.rows).length
    · -- free attachment with heavy seams: the trails read cyclically
      obtain ⟨first, last, mid, r₁, r, A, B, hS, hf, hl, hh, hg⟩ := hok.decomp2 h2
      obtain ⟨_, hlink, _, _⟩ := free_geom hv hH ha hg hh
      have hO : famO H = mid ++ [last ++ first] := by
        unfold famO
        rw [if_pos ha, if_pos h2, hS, rotSegs_eq]
      have hC : famC H = [] := by
        unfold famC
        rw [if_neg (by omega)]
      have hL : famL H = [] := by
        unfold famL
        rw [if_neg (by omega)]
      have hc : RowLink 6 3 last first := by
        rw [rowLink_iff]
        intro a ha' b hb
        rw [hl, List.getLast?_concat] at ha'
        rw [hf] at hb
        simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at ha' hb
        subst ha'
        subst hb
        exact hlink
      have hF : TrailFam 6 (first :: (mid ++ [last])) := by
        rw [← hS]
        exact hok.fam
      have hflat : (first :: (mid ++ [last])).flatten = H.rows := by
        rw [← hS]
        exact inv.flat
      have hlenS : (cutRows H.rows).length = mid.length + 2 := by
        rw [hS]
        simp
      have hcnt := hok.cnt
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hO]
        exact (hF.rot hc).trails
      · rw [hO, hC, hL]
        simp only [List.flatten_nil, List.append_nil]
        rw [← hflat]
        exact rot_rows_perm first last mid
      · rw [hO, hcost]
        simp only [List.length_append, List.length_singleton]
        omega
      · rw [hC]
        simp
      · rw [hL]
        simp
    · have h1 : (cutRows H.rows).length = 1 := by
        have := hok.pos
        omega
      obtain ⟨_, hT, hX⟩ := hok.single h1
      have hO : famO H = [] := by
        unfold famO
        rw [if_pos ha, if_neg h2]
      by_cases hm : 2 ≤ H.rows.length
      · -- a closed trail
        have hC : famC H = [H.rows] := by
          unfold famC
          rw [if_pos ⟨ha, by omega, hm⟩]
        have hL : famL H = [] := by
          unfold famL
          rw [if_neg (by omega)]
        refine ⟨by rw [hO]; simp, ?_, ?_, ?_, by rw [hL]; simp⟩
        · rw [hO, hC, hL]
          simp
        · rw [hO, hcost]
          simp only [List.length_nil, Nat.zero_add]
          omega
        · rw [hC]
          intro C hCm
          rw [List.mem_singleton.mp hCm]
          obtain ⟨r₁, A, r, hR⟩ := exists_first_mid_last hm
          have hh : H.rows.head? = some r₁ := by rw [hR]; rfl
          have hg : H.rows.getLast? = some r := by
            rw [hR, ← List.cons_append, List.getLast?_concat]
          obtain ⟨hJ, _, _, hx⟩ := free_geom hv hH ha hg hh
          obtain ⟨T, hTt, hTcl, hTl, hJT, hTh⟩ := glue_ring hok h1 hm hg hh hJ hx
          refine ⟨hT, hm, T, hTt, hTcl, by simp only [List.length_singleton] at hTl; omega, ?_⟩
          have hmem : mergeRow r r₁ ∈ T := hJT _ (List.mem_singleton_self _)
          have hlen5 := len_le_of_rowsEntries_pairwise (by norm_num) hTcl hmem
          have hmh := holes_merge6 (r := r) (r₁ := r₁) (by simp only [mergeRow] at hlen5; omega)
          omega
      · -- a loop
        have hC : famC H = [] := by
          unfold famC
          rw [if_neg (by omega)]
        have hL : famL H = H.rows := by
          unfold famL
          rw [if_pos ⟨ha, by omega, by omega⟩]
        obtain ⟨r, hR⟩ : ∃ r, H.rows = [r] := by
          have hne := hok.ne
          match hrows : H.rows, hne, hm with
          | [r], _, _ => exact ⟨r, rfl⟩
          | [], hne, _ => exact absurd rfl hne
          | _ :: _ :: _, _, hm => simp at hm
        refine ⟨by rw [hO]; simp, ?_, ?_, by rw [hC]; simp, ?_⟩
        · rw [hO, hC, hL]
          simp
        · rw [hO, hcost]
          simp only [List.length_nil, Nat.zero_add]
          omega
        · rw [hL, hR]
          intro r' hr'
          rw [List.mem_singleton.mp hr']
          have hg : H.rows.getLast? = some r := by rw [hR]; rfl
          have hh : H.rows.head? = some r := by rw [hR]; rfl
          obtain ⟨_, _, he, hx⟩ := free_geom hv hH ha hg hh
          have h1l := hok.len r (by rw [hR]; exact List.mem_singleton_self _)
          have h5l := hok.len_le r (by rw [hR]; exact List.mem_singleton_self _)
          have hmem : r.entry ∈ rowsEntries H.rows := by
            rw [hR, rowsEntries_cons]
            exact List.mem_append_left _ (NRow.entry_mem r h1l)
          have hX := hx r.entry hmem
          -- `τ₂ (lastEntry) = τ₂^[len] entry` and `entry = τ₂^[len + 1] entry`
          have eX : tau2V r.lastEntry = tau2V^[r.len] r.entry := by
            unfold NRow.lastEntry
            rw [← Function.iterate_succ_apply' tau2V]
            congr 1
            omega
          have eE : tau2V^[r.len + 1] r.entry = r.entry := by
            rw [Function.iterate_succ_apply', ← eX]
            exact he.symm
          by_contra hne4
          rcases Nat.lt_or_gt_of_ne hne4 with hlt | hgt
          · exact tau2V_iterate_ne r.entry (by omega) (by omega) eE
          · have h5 : r.len = 5 := by omega
            have hper := tau2V_period (k := 6) (by norm_num) r.entry
            rw [eX, h5] at hX
            exact hX (by rw [hper])
  · -- paid attachment: the trails as they are
    have hO : famO H = cutRows H.rows := by
      unfold famO
      rw [if_neg ha]
    have hC : famC H = [] := by
      unfold famC
      rw [if_neg (by tauto)]
    have hL : famL H = [] := by
      unfold famL
      rw [if_neg (by tauto)]
    have hcnt := hok.cnt
    refine ⟨?_, ?_, ?_, by rw [hC]; simp, by rw [hL]; simp⟩
    · rw [hO]
      exact hok.fam.trails
    · rw [hO, hC, hL]
      simp only [List.flatten_nil, List.append_nil]
      rw [inv.flat]
    · rw [hO, hcost]
      omega

end K6
