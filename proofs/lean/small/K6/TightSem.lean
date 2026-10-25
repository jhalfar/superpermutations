import K6.Sound
import K6.TightRules
import K6.Knap

/-!
# The leaf test of the tight case and the knapsack table `bt`

* `NoDeadW W`: every class outside the words `W` lies in a row of 4 blocks (a loop) that avoids
  them.  `deadB_false`: then the search's test `deadB` on the set of classes of `W` answers `false`.
  `NoDeadW.relabel`: the property survives a relabelling of the symbols.
* `bt_sound`: the table `bt` bounds `Σ (rows - holes)` of chains of words (from `wcap6` and the
  knapsack table `KT FO` of `Knap.lean`).
-/

namespace K6

open SuperpermLowerBounds SuperpermLowerBounds.S

/-! ### Two more table checks -/

theorem chk_rep : (List.range 120).all (fun c => rep c < 720 && ci (rep c) == c) = true := by
  decide +kernel

theorem chk_bt : (List.range 4).all (fun n => (List.range 21).all fun g =>
    (List.range (g + 1)).all fun g' => decide (KT FO n g' ≤ (bt n g : ℤ))) = true := by
  decide +kernel

/-! ### Loops avoiding a set of words -/

/-- Every class outside the words `W` lies in a row of 4 blocks that avoids them. -/
def NoDeadW (W : List (List ℕ)) : Prop :=
  ∀ v, PermW 6 v → (∀ u ∈ W, ¬ u ~r v) →
    ∃ Q : List (List ℕ), Q.length = 4 ∧ (∀ x ∈ Q, PermW 6 x) ∧ List.IsChain (WLink 6 2) Q ∧
      List.Pairwise (fun a b => ¬ a ~r b) Q ∧ (∃ x ∈ Q, x ~r v) ∧ ∀ x ∈ Q, ∀ u ∈ W, ¬ u ~r x

theorem testBit_loopMask (i b : ℕ) : (loopMask i).testBit b = true ↔
    b = ci i ∨ b = ci (nx i) ∨ b = ci (nx (nx i)) ∨ b = ci (nx (nx (nx i))) := by
  unfold loopMask
  simp only [Nat.testBit_or, testBit_bit, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (((h | h) | h) | h) <;> simp [h]
  · rintro (h | h | h | h) <;> simp [h]

/-- **The leaf test is sound**: if every class outside `W` lies in a loop that avoids `W`, the
search does not call any class dead. -/
theorem deadB_false {W : List (List ℕ)} (hW : ∀ u ∈ W, PermW 6 u) (h : NoDeadW W) :
    deadB (maskOf W) = false := by
  by_contra hd
  rw [Bool.not_eq_false] at hd
  unfold deadB at hd
  rw [List.any_eq_true] at hd
  obtain ⟨c, hc, hc2⟩ := hd
  have hc120 : c < 120 := List.mem_range.mp hc
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hc2
  obtain ⟨hfree, hall⟩ := hc2
  have hr := all_range chk_rep hc120
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
  set v := pw (rep c) with hv
  have hvp : PermW 6 v := permW_pw hr.1
  have hvc : ci (enc v) = c := by rw [hv, enc_pw hr.1, hr.2]
  have hnew : ∀ u ∈ W, ¬ u ~r v := by
    intro u hu hrot
    have := (ci_eq_iff (hW u hu) hvp).mpr hrot
    have hb : (maskOf W).testBit c = true := (testBit_maskOf W c).mpr ⟨u, hu, by rw [this, hvc]⟩
    rw [hb] at hfree
    cases hfree
  obtain ⟨Q, hQl, hQp, hQd, hQpw, ⟨x, hxQ, hxv⟩, hQa⟩ := h v hvp hnew
  obtain ⟨x0, x1, x2, x3, rfl⟩ : ∃ x0 x1 x2 x3, Q = [x0, x1, x2, x3] := by
    match Q, hQl with
    | [x0, x1, x2, x3], _ => exact ⟨x0, x1, x2, x3, rfl⟩
  have hdoor := S.door_chain (by norm_num) _ hQp hQd hQpw
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hdoor
  have p0 := hQp x0 (by simp)
  have p1 := hQp x1 (by simp)
  have p2 := hQp x2 (by simp)
  have e1 := nx_enc p0 hdoor.1
  have e2 := nx_enc p1 hdoor.2.1
  have e3 := nx_enc p2 hdoor.2.2
  have hi := hall (enc x0) (enc_lt p0)
  have hmc : (loopMask (enc x0)).testBit c = true := by
    rw [testBit_loopMask, e1, e2, e3]
    have hx := (ci_eq_iff (hQp x hxQ) hvp).mpr hxv
    rw [hvc] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hxQ
    rcases hxQ with rfl | rfl | rfl | rfl
    · exact Or.inl hx.symm
    · exact Or.inr (Or.inl hx.symm)
    · exact Or.inr (Or.inr (Or.inl hx.symm))
    · exact Or.inr (Or.inr (Or.inr hx.symm))
  rw [hmc] at hi
  simp only [Bool.not_true, Bool.false_or, bne_iff_ne, ne_eq] at hi
  have hi' : loopMask (enc x0) &&& maskOf W ≠ 0 := by
    rcases hi with h | h
    · cases h
    · exact h
  obtain ⟨b, hb⟩ := Nat.exists_testBit_of_ne_zero hi'
  rw [Nat.testBit_and, Bool.and_eq_true] at hb
  obtain ⟨u, hu, hub⟩ := (testBit_maskOf W b).mp hb.2
  have hbl := (testBit_loopMask _ b).mp hb.1
  rw [e1, e2, e3] at hbl
  have key : ∀ y ∈ [x0, x1, x2, x3], ci (enc y) = b → False := by
    intro y hy hyb
    exact hQa y hy u hu ((ci_eq_iff (hW u hu) (hQp y hy)).mp (by rw [hub, hyb]))
  rcases hbl with h | h | h | h
  · exact key x0 (by simp) h.symm
  · exact key x1 (by simp) h.symm
  · exact key x2 (by simp) h.symm
  · exact key x3 (by simp) h.symm

/-! ### Relabelling -/

/-- The inverse relabelling. -/
def invW (e : List ℕ) : List ℕ := (List.range' 1 6).map (relab e)

theorem permW_invW {e : List ℕ} (he : PermW 6 e) : PermW 6 (invW e) :=
  he.map_relab (permW_of_perm (by decide))

theorem relab_relab_inv {e : List ℕ} (he : PermW 6 e) {a : ℕ} (ha : 1 ≤ a ∧ a ≤ 6) :
    relab e (relab (invW e) a) = a := by
  have hmem : a ∈ invW e := ((permW_invW he).2.2 a).mpr ha
  have hlt := List.idxOf_lt_length_of_mem hmem
  have hget := List.getElem_idxOf hlt
  have e2 : (invW e)[(invW e).idxOf a] = relab e ((invW e).idxOf a + 1) := by
    simp only [invW, List.getElem_map, List.getElem_range']
    congr 1
    omega
  calc relab e (relab (invW e) a) = relab e ((invW e).idxOf a + 1) := rfl
    _ = (invW e)[(invW e).idxOf a] := e2.symm
    _ = a := hget

theorem map_relab_inv {e : List ℕ} (he : PermW 6 e) {v : List ℕ} (hv : PermW 6 v) :
    (v.map (relab (invW e))).map (relab e) = v := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id v]
  apply List.map_congr_left
  intro a ha
  exact relab_relab_inv he ((hv.2.2 a).mp ha)

/-- **The leaf property survives a relabelling.** -/
theorem NoDeadW.relabel {e : List ℕ} (he : PermW 6 e) {W : List (List ℕ)}
    (hW : ∀ u ∈ W, PermW 6 u) (h : NoDeadW W) : NoDeadW (W.map (List.map (relab e))) := by
  intro v hv hnew
  set v0 := v.map (relab (invW e)) with hv0
  have hv0p : PermW 6 v0 := (permW_invW he).map_relab hv
  have hback : v0.map (relab e) = v := map_relab_inv he hv
  have hnew0 : ∀ u ∈ W, ¬ u ~r v0 := by
    intro u hu hrot
    apply hnew (u.map (relab e)) (List.mem_map.mpr ⟨u, hu, rfl⟩)
    rw [← hback]
    exact hrot.map _
  obtain ⟨Q, hQl, hQp, hQd, hQpw, ⟨x, hxQ, hxv⟩, hQa⟩ := h v0 hv0p hnew0
  refine ⟨Q.map (List.map (relab e)), by simp [hQl], ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨y0, hy0, rfl⟩ := List.mem_map.mp hy
    exact he.map_relab (hQp y0 hy0)
  · rw [List.isChain_map]
    exact hQd.imp (fun a b hab => hab.map _)
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ hQpw
    intro a b ha hb hab
    exact not_isRotated_map_relab he (hQp a ha) (hQp b hb) hab
  · refine ⟨x.map (relab e), List.mem_map.mpr ⟨x, hxQ, rfl⟩, ?_⟩
    rw [← hback]
    exact hxv.map _
  · intro y hy u hu
    obtain ⟨y0, hy0, rfl⟩ := List.mem_map.mp hy
    obtain ⟨u0, hu0, rfl⟩ := List.mem_map.mp hu
    exact not_isRotated_map_relab he (hW u0 hu0) (hQp y0 hy0) (hQa y0 hy0 u0 hu0)

/-! ### The table `bt` -/

/-- The holes of a chain of words. -/
def hW (C : List (List (List ℕ))) : ℕ := (wdef 6 C).sum

/-- The knapsack bound for any items. -/
theorem knapG {α : Type} {F : ℕ → ℤ} (len hol : α → ℕ) : ∀ (l : List α),
    (∀ a ∈ l, (len a : ℤ) - hol a ≤ F (hol a)) → (l.map hol).sum ≤ 20 →
    (l.map fun a => (len a : ℤ) - hol a).sum ≤ KT F l.length (l.map hol).sum
  | [], _, _ => by simp [KT_zero F (by norm_num : 0 ≤ 20)]
  | a :: l, h, hs => by
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hs ⊢
    have h1 := h a List.mem_cons_self
    have h2 := knapG len hol l (fun b hb => h b (List.mem_cons_of_mem _ hb)) (by omega)
    have h3 := KT_step F l.length (g := hol a + (l.map hol).sum) (x := hol a) (by omega) hs
    rw [show hol a + (l.map hol).sum - hol a = (l.map hol).sum by omega] at h3
    linarith

theorem sum_sub (l : List (List (List (List ℕ)))) :
    (l.map fun C => (C.length : ℤ) - hW C).sum = ((l.map List.length).sum : ℤ) - ((l.map hW).sum : ℤ) := by
  induction l with
  | nil => simp
  | cons C l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    push_cast
    ring

/-- **`bt` bounds chains of words**: `n ≤ 3` chains with at most `g ≤ 20` holes in all have at
most `holes + bt n g` rows. -/
theorem bt_sound (l : List (List (List (List ℕ)))) (hl : ∀ C ∈ l, IsWChain 6 C)
    (hn : l.length ≤ 3) {g : ℕ} (hg : g ≤ 20) (hs : (l.map hW).sum ≤ g) :
    (l.map List.length).sum ≤ (l.map hW).sum + bt l.length g := by
  have hk := knapG (F := FO) List.length hW l (fun C hC => by
    have h20 : hW C ≤ 20 := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := hW) hC)
      omega
    have hcap := wcap6 C (hl C hC) h20
    unfold FO
    have e : PS.capF [W6] 0 (hW C) = W6.getD (hW C) 0 := rfl
    unfold hW at hcap e ⊢
    rw [e] at hcap
    have : (C.length : ℤ) ≤ (W6.getD (wdef 6 C).sum 0 : ℤ) := by exact_mod_cast hcap
    linarith) (by omega)
  have hb := all_range chk_bt (show l.length < 4 by omega)
  have hb2 := all_range hb (show g < 21 by omega)
  have hb3 := all_range hb2 (show (l.map hW).sum < g + 1 by omega)
  simp only [decide_eq_true_eq] at hb3
  rw [sum_sub] at hk
  have : ((l.map List.length).sum : ℤ) ≤ ((l.map hW).sum : ℤ) + (bt l.length g : ℤ) := by linarith
  exact_mod_cast this

end K6
