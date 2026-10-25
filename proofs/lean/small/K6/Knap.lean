import K6.FamilyC
import K6.CapFinal

/-!
# The arithmetic of the family on 6 symbols: L(6) ≥ 871

For a valid configuration of cost at most `24 + D` (defect at most `D`) with `t` open trails,
`fam_count` gives

    Σ_{open, closed} (rows - holes) ≥ 24 - 4 D + 4 (t - 1),
    Σ_{open, closed} holes + loops   ≤ 5 D - 5 (t - 1).

An open trail with `x ≤ 20` holes has at most `W6[x]` rows (`chainCap6`); a closed trail with `x`
holes glues into a trail with `x - 6` holes and one row fewer, so it has at most `1 + W6[x - 6]` rows.
`KT F n g` is the best total of `F` over `n` items with `g` holes in all (a knapsack table, computed
by Lean), and `knapL` bounds the sum of a list by it.  `chk3`, `chk4` (by `decide +kernel`) compare
the tables with the bounds above.

* `no_config_27`: no valid configuration has cost at most 27 (defect 3), hence
  `covers_871`: every superpermutation on 6 symbols has at least 871 letters.
* `tight_shape`: a valid configuration of cost at most 28 (defect 4) has no closed trail and at most
  3 open trails.
-/

namespace K6

open SuperpermLowerBounds Hunter PreimageChain

/-! ### Knapsack tables -/

/-- The value of an open trail with `x` holes and the most rows. -/
def FO (x : ℕ) : ℤ := (W6.getD x 0 : ℤ) - x

/-- The value of a closed trail with `x` holes and the most rows. -/
def FCl (x : ℕ) : ℤ := if 6 ≤ x then 1 + (W6.getD (x - 6) 0 : ℤ) - x else -1000

/-- The largest element of `l`, or `b`. -/
def lmax (b : ℤ) (l : List ℤ) : ℤ := l.foldl max b

theorem le_lmax_init : ∀ (b : ℤ) (l : List ℤ), b ≤ lmax b l
  | b, [] => le_refl b
  | b, a :: l => (le_max_left b a).trans (le_lmax_init (max b a) l)

theorem le_lmax_mem : ∀ (b : ℤ) (l : List ℤ) (a : ℤ), a ∈ l → a ≤ lmax b l
  | _, [], _, h => absurd h List.not_mem_nil
  | b, x :: l, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact (le_max_right b a).trans (le_lmax_init (max b a) l)
    · exact le_lmax_mem (max b x) l a h

/-- `KTL F n`: the knapsack table of `n` items for `0 … 20` holes. -/
def KTL (F : ℕ → ℤ) : ℕ → List ℤ
  | 0 => List.replicate 21 0
  | n + 1 => (List.range 21).map fun g =>
      lmax (-1000000) ((List.range (g + 1)).map fun x => F x + (KTL F n).getD (g - x) 0)

/-- The best total of `F` over `n` items with `g ≤ 20` holes in all. -/
def KT (F : ℕ → ℤ) (n g : ℕ) : ℤ := (KTL F n).getD g 0

theorem KT_zero (F : ℕ → ℤ) {g : ℕ} (hg : g ≤ 20) : KT F 0 g = 0 := by
  unfold KT KTL
  interval_cases g <;> rfl

theorem KT_step (F : ℕ → ℤ) (n : ℕ) {g x : ℕ} (hx : x ≤ g) (hg : g ≤ 20) :
    F x + KT F n (g - x) ≤ KT F (n + 1) g := by
  unfold KT
  have e : (KTL F (n + 1)).getD g 0 =
      lmax (-1000000) ((List.range (g + 1)).map fun x => F x + (KTL F n).getD (g - x) 0) := by
    show ((List.range 21).map fun g =>
      lmax (-1000000) ((List.range (g + 1)).map fun x => F x + (KTL F n).getD (g - x) 0)).getD g 0 = _
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; omega)]
    simp only [List.getElem_map, List.getElem_range]
  rw [e]
  apply le_lmax_mem
  exact List.mem_map.mpr ⟨x, List.mem_range.mpr (by omega), rfl⟩

/-- The value `rows - holes` of a list of rows. -/
def valRows (A : List (NRow 6)) : ℤ := (A.length : ℤ) - rowsHoles 6 A

theorem sum_holes_flatten : ∀ l : List (List (NRow 6)),
    (l.map (rowsHoles 6)).sum = rowsHoles 6 l.flatten
  | [] => rfl
  | A :: l => by
    rw [List.map_cons, List.sum_cons, sum_holes_flatten l, List.flatten_cons, rowsHoles_append]

theorem sum_val_flatten : ∀ l : List (List (NRow 6)),
    (l.map valRows).sum = (l.flatten.length : ℤ) - rowsHoles 6 l.flatten
  | [] => by simp [rowsHoles]
  | A :: l => by
    rw [List.map_cons, List.sum_cons, sum_val_flatten l, List.flatten_cons, rowsHoles_append,
      List.length_append]
    unfold valRows
    push_cast
    ring

theorem holes_le_of_mem {A : List (NRow 6)} {l : List (List (NRow 6))} (h : A ∈ l) :
    rowsHoles 6 A ≤ rowsHoles 6 l.flatten := by
  rw [← sum_holes_flatten]
  exact List.le_sum_of_mem (List.mem_map_of_mem h)

/-- **The knapsack bound** for a list of items with at most 20 holes in all. -/
theorem knapL {F : ℕ → ℤ} : ∀ (l : List (List (NRow 6))),
    (∀ A ∈ l, valRows A ≤ F (rowsHoles 6 A)) → (l.map (rowsHoles 6)).sum ≤ 20 →
    (l.map valRows).sum ≤ KT F l.length (l.map (rowsHoles 6)).sum
  | [], _, _ => by simp [KT_zero F (le_refl _ |>.trans (by norm_num : 0 ≤ 20))]
  | A :: l, h, hs => by
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hs ⊢
    have h1 := h A List.mem_cons_self
    have h2 := knapL l (fun B hB => h B (List.mem_cons_of_mem _ hB)) (by omega)
    have h3 := KT_step F l.length (g := rowsHoles 6 A + (l.map (rowsHoles 6)).sum)
      (x := rowsHoles 6 A) (by omega) hs
    rw [show rowsHoles 6 A + (l.map (rowsHoles 6)).sum - rowsHoles 6 A =
      (l.map (rowsHoles 6)).sum by omega] at h3
    linarith

/-! ### The checks -/

/-- Defect 3: every number of open and closed trails fails. -/
theorem chk3 : (List.range 5).all (fun t => t == 0 || (List.range 4).all fun cc =>
    (List.range 16).all fun g1 => (List.range 16).all fun g2 =>
      !(g1 + g2 + 5 * (t - 1) ≤ 15) ||
        decide (KT FO t g1 + KT FCl cc g2 < 12 + 4 * ((t : ℤ) - 1))) = true := by
  decide +kernel

/-- Defect 4: every case with a closed trail or with more than 3 open trails fails. -/
theorem chk4 : (List.range 6).all (fun t => t == 0 || (List.range 4).all fun cc =>
    (cc == 0 && t ≤ 3) || (List.range 21).all fun g1 => (List.range 21).all fun g2 =>
      !(g1 + g2 + 5 * (t - 1) ≤ 20) ||
        decide (KT FO t g1 + KT FCl cc g2 < 8 + 4 * ((t : ℤ) - 1))) = true := by
  decide +kernel

/-! ### The family against the tables -/

variable {c : NConfig 6}

/-- The rows of the family have pairwise different classes. -/
theorem fam_classes (hv : c.Valid) :
    (rowsEntries ((opens c).flatten ++ (closeds c).flatten ++ loops c)).Pairwise
      (NotRot (k := 6)) := by
  obtain ⟨_, _, hp, _, _, _⟩ := fam_spec hv
  have h := hv.distinct
  rw [← rowsEntries_allRows] at h
  refine pairwise_of_perm h ?_
  unfold rowsEntries
  exact List.Perm.flatMap_right NRow.entries hp

theorem open_val (hv : c.Valid) {A : List (NRow 6)} (hA : A ∈ opens c) (h20 : rowsHoles 6 A ≤ 20) :
    valRows A ≤ FO (rowsHoles 6 A) := by
  obtain ⟨_, ht, _, _, _, _⟩ := fam_spec hv
  have hcl : (rowsEntries A).Pairwise (NotRot (k := 6)) := by
    refine (fam_classes hv).sublist ?_
    rw [rowsEntries_append, rowsEntries_append]
    exact ((rowsEntries_sublist_flatten hA).trans (List.sublist_append_left _ _)).trans
      (List.sublist_append_left _ _)
  have hcap := chainCap6 _ ((ht A hA).isModelChain (by norm_num) hcl)
    (by rw [holesL_rows]; exact h20)
  rw [List.length_map, holesL_rows] at hcap
  unfold valRows FO
  have e : PS.capF [W6] 0 (rowsHoles 6 A) = W6.getD (rowsHoles 6 A) 0 := rfl
  rw [e] at hcap
  have : (A.length : ℤ) ≤ (W6.getD (rowsHoles 6 A) 0 : ℤ) := by exact_mod_cast hcap
  linarith

theorem closed_val (hv : c.Valid) {C : List (NRow 6)} (hC : C ∈ closeds c)
    (h20 : rowsHoles 6 C ≤ 26) : valRows C ≤ FCl (rowsHoles 6 C) ∧ 6 ≤ rowsHoles 6 C := by
  obtain ⟨_, _, _, hcl, _, _⟩ := fam_spec hv
  obtain ⟨_, _, T, hT, hTcl, hTl, hTh⟩ := hcl C hC
  have hcap := chainCap6 _ (hT.isModelChain (by norm_num) hTcl)
    (by rw [holesL_rows]; omega)
  rw [List.length_map, holesL_rows] at hcap
  have e : PS.capF [W6] 0 (rowsHoles 6 T) = W6.getD (rowsHoles 6 T) 0 := rfl
  rw [e] at hcap
  refine ⟨?_, by omega⟩
  unfold valRows FCl
  rw [if_pos (by omega)]
  have e2 : rowsHoles 6 C - 6 = rowsHoles 6 T := by omega
  rw [e2]
  have : (T.length : ℤ) ≤ (W6.getD (rowsHoles 6 T) 0 : ℤ) := by exact_mod_cast hcap
  have hl : (C.length : ℤ) = T.length + 1 := by exact_mod_cast hTl.symm
  have hh : (rowsHoles 6 C : ℤ) = rowsHoles 6 T + 6 := by exact_mod_cast hTh.symm
  linarith

theorem closed_six (hv : c.Valid) : ∀ l : List (List (NRow 6)), (∀ C ∈ l, C ∈ closeds c) →
    6 * l.length ≤ (l.map (rowsHoles 6)).sum
  | [], _ => by simp
  | C :: l, h => by
    obtain ⟨_, _, _, hcl, _, _⟩ := fam_spec hv
    obtain ⟨_, _, T, _, _, _, hTh⟩ := hcl C (h C List.mem_cons_self)
    have := closed_six hv l (fun C' hC' => h C' (List.mem_cons_of_mem _ hC'))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- **The family against the tables**: for a valid configuration of cost at most `24 + D` with
`t` open trails and `cc` closed trails, the knapsack values reach what the counting asks. -/
theorem fam_tables (hv : c.Valid) {D : ℕ} (hc : c.cost ≤ 24 + D) :
    1 ≤ (opens c).length ∧
      rowsHoles 6 (opens c).flatten + rowsHoles 6 (closeds c).flatten + 5 * ((opens c).length - 1)
        ≤ 5 * D ∧
      6 * (closeds c).length ≤ rowsHoles 6 (closeds c).flatten ∧
      (24 - 4 * (D : ℤ) + 4 * (((opens c).length : ℤ) - 1) ≤
        ((((opens c).flatten.length : ℤ) - rowsHoles 6 (opens c).flatten) +
          (((closeds c).flatten.length : ℤ) - rowsHoles 6 (closeds c).flatten))) ∧
      (rowsHoles 6 (opens c).flatten + rowsHoles 6 (closeds c).flatten ≤ 20 →
        ((((opens c).flatten.length : ℤ) - rowsHoles 6 (opens c).flatten) +
          (((closeds c).flatten.length : ℤ) - rowsHoles 6 (closeds c).flatten)) ≤
        KT FO (opens c).length (rowsHoles 6 (opens c).flatten) +
          KT FCl (closeds c).length (rowsHoles 6 (closeds c).flatten)) := by
  obtain ⟨hne, _, _, _, _, _⟩ := fam_spec hv
  obtain ⟨n1, n2, n3⟩ := fam_count hv
  have ht : 1 ≤ (opens c).length := by
    rcases h : opens c with _ | ⟨A, l⟩
    · exact absurd h hne
    · simp
  have h6 := closed_six hv (closeds c) (fun C hC => hC)
  rw [sum_holes_flatten] at h6
  refine ⟨ht, by omega, h6, ?_, ?_⟩
  · omega
  · intro h20
    have hO := knapL (F := FO) (opens c) (fun A hA => open_val hv hA (by
      have := holes_le_of_mem hA
      omega)) (by rw [sum_holes_flatten]; omega)
    have hC := knapL (F := FCl) (closeds c) (fun C hC => (closed_val hv hC (by
      have := holes_le_of_mem hC
      omega)).1) (by rw [sum_holes_flatten]; omega)
    rw [sum_val_flatten, sum_holes_flatten] at hO hC
    linarith

end K6
