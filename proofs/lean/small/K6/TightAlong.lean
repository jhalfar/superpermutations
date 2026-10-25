import K6.TightSem

/-!
# The rule of the tight case holds along a family

`along`: a family of chains of words (trails, joined by jumps) whose numbers satisfy what the
accounting of a configuration of defect 4 gives — at most `G = 20 - 5 (T - 1)` holes in all, at
least `need = 8 + 4 (T - 1)` more rows than holes, every trail after the first with no more
`rows - holes` than the first, the part keys of `(p0, p1)`, and no dead class — satisfies the rule
`famRules T g0 n0 p0 n1 p1` along its rows (`KAlong`).  The proof follows the rows with the
invariant `Inv`: inside a trail the rule `keepN` holds because the rest of the trail and the later
trails obey the caps (`bt_sound`), at a jump `keepJ` holds for the same reason with the later
trails only, and at the end `bad` holds because the leaf test finds no dead class (`deadB_false`).
-/

namespace K6

open SuperpermLowerBounds SuperpermLowerBounds.S SuperpermLowerBounds.PS

/-- The index of the last word of a row. -/
def keyR (P : List (List ℕ)) : ℕ := enc (P.getLast?.getD [])

theorem keyR_cons (v : List ℕ) (R : List (List ℕ)) :
    keyR (v :: R) = enc ((v :: R).getLast (List.cons_ne_nil v R)) := by
  unfold keyR
  rw [List.getLast?_eq_some_getLast (List.cons_ne_nil v R)]
  rfl

theorem hW_cons (P : List (List ℕ)) (C : List (List (List ℕ))) :
    hW (P :: C) = (5 - P.length) + hW C := by
  unfold hW wdef
  simp

theorem hW_nil : hW [] = 0 := rfl

theorem tagF_cons2 (C : List (List (List ℕ))) (F : List (List (List (List ℕ)))) :
    tagF 2 (C :: F) = tagC 2 C ++ tagF 2 F := by
  unfold tagF
  simp

theorem gate_true {g0 n0 p0 n1 p1 : ℕ} {c : FC} (h0 : g0 ≤ c.z → c.k0 % n0 = p0)
    (h1 : 1 ≤ c.t → c.k1 % n1 = p1) : gateOK g0 n0 p0 n1 p1 c = true := by
  unfold gateOK
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · by_cases hz : c.z < g0
    · exact Or.inl hz
    · exact Or.inr (h0 (by omega))
  · by_cases ht : c.t = 0
    · exact Or.inl ht
    · exact Or.inr (h1 (by omega))

theorem ord_true {c : FC} (h : 1 ≤ c.t → c.r + c.d1 ≤ c.r1 + c.d) : ordOK c = true := by
  unfold ordOK
  simp only [Bool.or_eq_true, beq_iff_eq, Nat.ble_eq]
  by_cases ht : c.t = 0
  · exact Or.inl ht
  · exact Or.inr (h (by omega))

section Along

variable (T g0 n0 p0 n1 p1 : ℕ)

/-- The invariant along a family: the counters `c` after the rows `used`, the rest `cur` of the
current trail and the later trails `later`. -/
structure Inv (later : List (List (List (List ℕ)))) (cur : List (List (List ℕ))) (c : FC)
    (used : List (List ℕ)) : Prop where
  hT : c.t + 1 + later.length = T
  hcur : cur = [] ∨ IsWChain 6 cur
  hlat : ∀ C ∈ later, IsWChain 6 C ∧ C ≠ []
  hG : c.B + c.d + hW cur + (later.map hW).sum ≤ 20 - 5 * (T - 1)
  hval : 8 + 4 * (T - 1) + c.B + c.d + hW cur + (later.map hW).sum ≤
    c.A + c.r + cur.length + (later.map List.length).sum
  hord0 : c.t = 0 → ∀ C ∈ later, C.length + (c.d + hW cur) ≤ (c.r + cur.length) + hW C
  hord1 : 1 ≤ c.t → c.r + cur.length + c.d1 ≤ c.r1 + c.d + hW cur ∧
    ∀ C ∈ later, C.length + c.d1 ≤ c.r1 + hW C
  hg0 : g0 ≤ c.z → c.k0 % n0 = p0
  hg1 : 1 ≤ c.t → c.k1 % n1 = p1
  hf0 : c.z < g0 → ∀ P, (cur ++ later.flatten)[g0 - c.z - 1]? = some P → keyR P % n0 = p0
  hf1 : c.t = 0 → ∀ C ∈ later.head?, ∀ P ∈ C.head?, keyR P % n1 = p1
  hwords : ∀ u ∈ used ++ (cur ++ later.flatten).flatten, PermW 6 u
  hdead : NoDeadW (used ++ (cur ++ later.flatten).flatten)

variable {T g0 n0 p0 n1 p1}

/-- The end of the family: `bad`. -/
theorem inv_end {c : FC} {used : List (List ℕ)} (h : Inv T g0 n0 p0 n1 p1 [] [] c used) :
    (famRules T g0 n0 p0 n1 p1).bad c (maskOf used) = true := by
  have hT := h.hT
  have hG := h.hG
  have hval := h.hval
  simp only [List.length_nil, hW_nil, List.map_nil, List.sum_nil, Nat.add_zero] at hT hG hval
  have hw := h.hwords
  have hd := h.hdead
  simp only [List.nil_append, List.flatten_nil, List.append_nil] at hw hd
  have hdb := deadB_false hw hd
  show (gateOK g0 n0 p0 n1 p1 c && (c.t + 1 == T) && ordOK c &&
    Nat.ble (c.B + c.d) (20 - 5 * (T - 1)) && Nat.ble (8 + 4 * (T - 1) + c.d + c.B) (c.r + c.A) &&
    !deadB (maskOf used)) = true
  rw [gate_true h.hg0 h.hg1, ord_true (fun ht => by
    have := (h.hord1 ht).1
    simp only [hW_nil, List.length_nil, Nat.add_zero] at this
    omega), hdb]
  simp only [Bool.true_and, Bool.not_false, Bool.and_true, Bool.and_eq_true, beq_iff_eq,
    Nat.ble_eq]
  omega

/-- A row inside a trail: `keepN`, and the invariant after the row. -/
theorem inv_seam (hTle : T ≤ 3) {later : List (List (List (List ℕ)))} {v : List ℕ}
    {R : List (List ℕ)} {cur : List (List (List ℕ))} {c : FC} {used : List (List ℕ)}
    (h : Inv T g0 n0 p0 n1 p1 later ((v :: R) :: cur) c used) :
    (famRules T g0 n0 p0 n1 p1).keepN c = true ∧
      Inv T g0 n0 p0 n1 p1 later cur ((famRules T g0 n0 p0 n1 p1).stN c (4 - R.length)
        (keyR (v :: R))) (used ++ v :: R) := by
  have hcw : IsWChain 6 ((v :: R) :: cur) := by
    rcases h.hcur with h' | h'
    · exact absurd h' (List.cons_ne_nil _ _)
    · exact h'
  have hRl : R.length ≤ 4 := by
    have := hcw.size_le (v :: R) List.mem_cons_self
    simp only [List.length_cons] at this
    omega
  have hhW : hW ((v :: R) :: cur) = (4 - R.length) + hW cur := by
    rw [hW_cons]
    simp only [List.length_cons]
    omega
  have hT := h.hT
  have hG := h.hG
  have hval := h.hval
  rw [hhW] at hG hval
  simp only [List.length_cons] at hval
  refine ⟨?_, ?_⟩
  · -- `keepN`
    have hbt := bt_sound (((v :: R) :: cur) :: later)
      (by
        intro C hC
        rcases List.mem_cons.mp hC with rfl | hC
        · exact hcw
        · exact (h.hlat C hC).1)
      (by simp only [List.length_cons]; omega)
      (g := 20 - 5 * (T - 1) - c.B - c.d) (by omega)
      (by simp only [List.map_cons, List.sum_cons]; rw [hhW]; omega)
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hbt
    rw [hhW] at hbt
    show (gateOK g0 n0 p0 n1 p1 c && Nat.ble (c.B + c.d) (20 - 5 * (T - 1)) &&
      Nat.ble (8 + 4 * (T - 1) + c.d + c.B)
        (c.r + c.A + bt (T - c.t) (20 - 5 * (T - 1) - c.B - c.d))) = true
    rw [gate_true h.hg0 h.hg1]
    have e : T - c.t = later.length + 1 := by omega
    rw [e]
    simp only [Bool.true_and, Bool.and_eq_true, Nat.ble_eq]
    omega
  · -- the invariant after the row
    have hcur' : cur = [] ∨ IsWChain 6 cur := by
      rcases cur with _ | ⟨Q, cur⟩
      · exact Or.inl rfl
      · exact Or.inr (hcw.infix ⟨[v :: R], [], by simp⟩)
    refine ⟨hT, hcur', h.hlat, ?_, ?_, ?_, ?_, ?_, h.hg1, ?_, h.hf1, ?_, ?_⟩
    · show c.B + (c.d + (4 - R.length)) + hW cur + (later.map hW).sum ≤ _
      omega
    · show _ + c.B + (c.d + (4 - R.length)) + hW cur + (later.map hW).sum ≤
        c.A + (c.r + 1) + cur.length + _
      omega
    · intro ht C hC
      have := h.hord0 ht C hC
      rw [hhW] at this
      simp only [List.length_cons] at this
      show C.length + (c.d + (4 - R.length) + hW cur) ≤ (c.r + 1 + cur.length) + hW C
      omega
    · intro ht
      have h1 := h.hord1 ht
      rw [hhW] at h1
      simp only [List.length_cons] at h1
      refine ⟨?_, h1.2⟩
      show c.r + 1 + cur.length + c.d1 ≤ c.r1 + (c.d + (4 - R.length)) + hW cur
      omega
    · intro hz
      show (cond (c.z + 1 == g0) (keyR (v :: R)) c.k0) % n0 = p0
      by_cases he : c.z + 1 = g0
      · have hb : (c.z + 1 == g0) = true := by simp [he]
        rw [hb, cond_true]
        exact h.hf0 (by omega) (v :: R) (by rw [show g0 - c.z - 1 = 0 by omega]; simp)
      · have hb : (c.z + 1 == g0) = false := by simp [he]
        rw [hb, cond_false]
        exact h.hg0 (by show g0 ≤ c.z; change g0 ≤ c.z + 1 at hz; omega)
    · intro hz P hP
      apply h.hf0 (by change c.z + 1 < g0 at hz; omega) P
      change (cur ++ later.flatten)[g0 - (c.z + 1) - 1]? = some P at hP
      rw [show g0 - c.z - 1 = (g0 - (c.z + 1) - 1) + 1 by change c.z + 1 < g0 at hz; omega]
      simpa using hP
    · have := h.hwords
      simpa using this
    · have := h.hdead
      simpa using this

/-- A jump to the next trail: `keepJ`, and the invariant after the first row of that trail. -/
theorem inv_jump (hTle : T ≤ 3) {later : List (List (List (List ℕ)))} {v : List ℕ}
    {R : List (List ℕ)} {Ct : List (List (List ℕ))} {c : FC} {used : List (List ℕ)}
    (h : Inv T g0 n0 p0 n1 p1 (((v :: R) :: Ct) :: later) [] c used) :
    (famRules T g0 n0 p0 n1 p1).keepJ c = true ∧
      Inv T g0 n0 p0 n1 p1 later Ct ((famRules T g0 n0 p0 n1 p1).stJ c (4 - R.length)
        (keyR (v :: R))) (used ++ v :: R) := by
  have hcw : IsWChain 6 ((v :: R) :: Ct) := (h.hlat _ List.mem_cons_self).1
  have hRl : R.length ≤ 4 := by
    have := hcw.size_le (v :: R) List.mem_cons_self
    simp only [List.length_cons] at this
    omega
  have hhW : hW ((v :: R) :: Ct) = (4 - R.length) + hW Ct := by
    rw [hW_cons]
    simp only [List.length_cons]
    omega
  have hT := h.hT
  have hG := h.hG
  have hval := h.hval
  simp only [List.length_cons, List.map_cons, List.sum_cons, hW_nil, Nat.add_zero,
    List.length_nil] at hT hG hval
  rw [hhW] at hG hval
  refine ⟨?_, ?_⟩
  · -- `keepJ`
    have hbt := bt_sound (((v :: R) :: Ct) :: later)
      (fun C hC => (h.hlat C hC).1)
      (by simp only [List.length_cons]; omega)
      (g := 20 - 5 * (T - 1) - c.B - c.d) (by omega)
      (by simp only [List.map_cons, List.sum_cons]; rw [hhW]; omega)
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hbt
    rw [hhW] at hbt
    show (gateOK g0 n0 p0 n1 p1 c && Nat.blt (c.t + 1) T && ordOK c &&
      Nat.ble (c.B + c.d) (20 - 5 * (T - 1)) &&
      Nat.ble (8 + 4 * (T - 1) + c.d + c.B)
        (c.r + c.A + bt (T - c.t - 1) (20 - 5 * (T - 1) - c.B - c.d))) = true
    rw [gate_true h.hg0 h.hg1,
      ord_true (fun ht => by have := (h.hord1 ht).1; simp [hW_nil] at this; omega)]
    have e : T - c.t - 1 = later.length + 1 := by omega
    rw [e]
    simp only [Bool.true_and, Bool.and_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
    omega
  · -- the invariant after the first row of the next trail
    have hCt : Ct = [] ∨ IsWChain 6 Ct := by
      rcases Ct with _ | ⟨Q, Ct⟩
      · exact Or.inl rfl
      · exact Or.inr (hcw.infix ⟨[v :: R], [], by simp⟩)
    refine ⟨?_, hCt, fun C hC => h.hlat C (List.mem_cons_of_mem _ hC), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · show c.t + 1 + 1 + later.length = T
      omega
    · show c.B + c.d + (4 - R.length) + hW Ct + (later.map hW).sum ≤ _
      omega
    · show _ + (c.B + c.d) + (4 - R.length) + hW Ct + (later.map hW).sum ≤
        c.A + c.r + 1 + Ct.length + _
      omega
    · intro ht
      exact absurd ht (by show c.t + 1 ≠ 0; omega)
    · intro _
      show 1 + Ct.length + cond (c.t == 0) c.d c.d1 ≤ cond (c.t == 0) c.r c.r1 + (4 - R.length) +
        hW Ct ∧ ∀ C ∈ later, C.length + cond (c.t == 0) c.d c.d1 ≤ cond (c.t == 0) c.r c.r1 + hW C
      by_cases ht : c.t = 0
      · have hb : (c.t == 0) = true := by simp [ht]
        rw [hb, cond_true, cond_true]
        have h0 := h.hord0 ht
        simp only [hW_nil, List.length_nil, Nat.add_zero] at h0
        have hC := h0 _ List.mem_cons_self
        rw [hhW] at hC
        simp only [List.length_cons] at hC
        refine ⟨by omega, fun C hC' => h0 C (List.mem_cons_of_mem _ hC')⟩
      · have hb : (c.t == 0) = false := by simp [ht]
        rw [hb, cond_false, cond_false]
        have h1 := h.hord1 (by omega)
        have hC := h1.2 _ List.mem_cons_self
        rw [hhW] at hC
        simp only [List.length_cons] at hC
        refine ⟨by omega, fun C hC' => h1.2 C (List.mem_cons_of_mem _ hC')⟩
    · intro hz
      show (cond (c.z + 1 == g0) (keyR (v :: R)) c.k0) % n0 = p0
      by_cases he : c.z + 1 = g0
      · have hb : (c.z + 1 == g0) = true := by simp [he]
        rw [hb, cond_true]
        exact h.hf0 (by omega) (v :: R) (by rw [show g0 - c.z - 1 = 0 by omega]; simp)
      · have hb : (c.z + 1 == g0) = false := by simp [he]
        rw [hb, cond_false]
        exact h.hg0 (by change g0 ≤ c.z + 1 at hz; omega)
    · intro _
      show (cond (c.t == 0) (keyR (v :: R)) c.k1) % n1 = p1
      by_cases ht : c.t = 0
      · have hb : (c.t == 0) = true := by simp [ht]
        rw [hb, cond_true]
        exact h.hf1 ht ((v :: R) :: Ct) (by simp) (v :: R) (by simp)
      · have hb : (c.t == 0) = false := by simp [ht]
        rw [hb, cond_false]
        exact h.hg1 (by omega)
    · intro hz P hP
      apply h.hf0 (by change c.z + 1 < g0 at hz; omega) P
      change (Ct ++ later.flatten)[g0 - (c.z + 1) - 1]? = some P at hP
      rw [show g0 - c.z - 1 = (g0 - (c.z + 1) - 1) + 1 by change c.z + 1 < g0 at hz; omega]
      simpa using hP
    · intro ht
      exact absurd ht (by show c.t + 1 ≠ 0; omega)
    · have := h.hwords
      simpa using this
    · have := h.hdead
      simpa using this

/-- **The rule holds along a family.** -/
theorem along (hTle : T ≤ 3) : ∀ (later : List (List (List (List ℕ)))) (cur : List (List (List ℕ)))
    (c : FC) (used : List (List ℕ)), Inv T g0 n0 p0 n1 p1 later cur c used →
    KAlong (famRules T g0 n0 p0 n1 p1) c used (cur.map (fun Q => (0, Q)) ++ tagF 2 later) := by
  intro later
  induction later with
  | nil =>
    intro cur
    induction cur with
    | nil =>
      intro c used h
      exact inv_end h
    | cons Q cur ih =>
      intro c used h
      have hQne : Q ≠ [] := by
        rcases h.hcur with h' | h'
        · exact absurd h' (List.cons_ne_nil _ _)
        · exact h'.pieces_ne Q List.mem_cons_self
      obtain ⟨v, R, rfl⟩ := List.exists_cons_of_ne_nil hQne
      obtain ⟨hk, h'⟩ := inv_seam hTle h
      refine ⟨by simpa [keepC] using hk, ?_⟩
      have e : stepC (famRules T g0 n0 p0 n1 p1) c 0 (4 - R.length)
          (enc ((v :: R).getLast (List.cons_ne_nil v R))) =
          (famRules T g0 n0 p0 n1 p1).stN c (4 - R.length) (keyR (v :: R)) := by
        rw [keyR_cons]
        rfl
      rw [e]
      exact ih _ _ h'
  | cons C later ihl =>
    intro cur
    induction cur with
    | nil =>
      intro c used h
      have hCne : C ≠ [] := (h.hlat C List.mem_cons_self).2
      obtain ⟨Q, Ct, rfl⟩ := List.exists_cons_of_ne_nil hCne
      have hQne : Q ≠ [] := (h.hlat _ List.mem_cons_self).1.pieces_ne Q List.mem_cons_self
      obtain ⟨v, R, rfl⟩ := List.exists_cons_of_ne_nil hQne
      obtain ⟨hk, h'⟩ := inv_jump hTle h
      rw [List.map_nil, List.nil_append, tagF_cons2]
      show KAlong (famRules T g0 n0 p0 n1 p1) c used
        ((2, v :: R) :: (Ct.map fun Q => (0, Q)) ++ tagF 2 later)
      refine ⟨by simpa [keepC] using hk, ?_⟩
      have e : stepC (famRules T g0 n0 p0 n1 p1) c 2 (4 - R.length)
          (enc ((v :: R).getLast (List.cons_ne_nil v R))) =
          (famRules T g0 n0 p0 n1 p1).stJ c (4 - R.length) (keyR (v :: R)) := by
        rw [keyR_cons]
        rfl
      rw [e]
      exact ihl Ct _ _ h'
    | cons Q cur ih =>
      intro c used h
      have hQne : Q ≠ [] := by
        rcases h.hcur with h' | h'
        · exact absurd h' (List.cons_ne_nil _ _)
        · exact h'.pieces_ne Q List.mem_cons_self
      obtain ⟨v, R, rfl⟩ := List.exists_cons_of_ne_nil hQne
      obtain ⟨hk, h'⟩ := inv_seam hTle h
      refine ⟨by simpa [keepC] using hk, ?_⟩
      have e : stepC (famRules T g0 n0 p0 n1 p1) c 0 (4 - R.length)
          (enc ((v :: R).getLast (List.cons_ne_nil v R))) =
          (famRules T g0 n0 p0 n1 p1).stN c (4 - R.length) (keyR (v :: R)) := by
        rw [keyR_cons]
        rfl
      rw [e]
      exact ih _ _ h'

end Along

end K6
