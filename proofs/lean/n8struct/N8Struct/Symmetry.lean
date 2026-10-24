import N8Struct.Definitions

/-!
# Renaming the letters 0..5

General lemmas: renaming commutes with `gstep` and with walks, keeps states states, and keeps loops
apart.  Facts about all 720 states are proved by `decide +kernel` through `forall_state`, which turns
a statement about every state into a nested bounded quantifier with 720 leaves.
-/

namespace N8Struct

open SuperpermutationUpperBound

/-- A statement about all states follows from its check on the 720 orderings of 0..5. -/
theorem forall_state {P : State → Prop}
    (h : ∀ a, a < 6 → ∀ b, b < 6 → b ≠ a → ∀ c, c < 6 → c ≠ a → c ≠ b →
      ∀ d, d < 6 → d ≠ a → d ≠ b → d ≠ c → ∀ e, e < 6 → e ≠ a → e ≠ b → e ≠ c → e ≠ d →
      ∀ f, f < 6 → f ≠ a → f ≠ b → f ≠ c → f ≠ d → f ≠ e → P [a, b, c, d, e, f]) :
    ∀ x, IsState x → P x := by
  intro x ⟨hl, hn, hb⟩
  match x, hl with
  | [a, b, c, d, e, f], _ =>
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    refine h a ?_ b ?_ ?_ c ?_ ?_ ?_ d ?_ ?_ ?_ ?_ e ?_ ?_ ?_ ?_ ?_ f ?_ ?_ ?_ ?_ ?_ ?_ <;> omega

/-- The Boolean check of `p` on the 720 orderings of 0..5, by nested loops that skip repeated
letters. -/
def allStatesB (p : State → Bool) : Bool :=
  (List.range 6).all fun a => (List.range 6).all fun b => b == a ||
  (List.range 6).all fun c => c == a || c == b ||
  (List.range 6).all fun d => d == a || d == b || d == c ||
  (List.range 6).all fun e => e == a || e == b || e == c || e == d ||
  (List.range 6).all fun f => f == a || f == b || f == c || f == d || f == e ||
  p [a, b, c, d, e, f]

/-- A decidable statement about all states follows from the kernel evaluation of `allStatesB`. -/
theorem forall_stateP {P : State → Prop} [DecidablePred P]
    (h : allStatesB (fun x => decide (P x)) = true) : ∀ x, IsState x → P x := by
  apply forall_state
  intro a ha b hb hba c hc hca hcb d hd hda hdb hdc e he hea heb hec hed f hf hfa hfb hfc hfd hfe
  simp only [allStatesB, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  have h1 := h a ha b hb
  simp only [hba, false_or] at h1
  have h2 := h1 c hc
  simp only [hca, hcb, false_or] at h2
  have h3 := h2 d hd
  simp only [hda, hdb, hdc, false_or] at h3
  have h4 := h3 e he
  simp only [hea, heb, hec, hed, false_or] at h4
  have h5 := h4 f hf
  simp only [hfa, hfb, hfc, hfd, hfe, false_or] at h5
  exact h5

theorem map_rotateLeft {α β : Type} (f : α → β) (l : List α) (n : Nat) :
    (l.map f).rotateLeft n = (l.rotateLeft n).map f := by
  unfold List.rotateLeft
  simp only [List.length_map]
  split <;> simp [List.map_take, List.map_drop]

theorem gstep_map (f : Nat → Nat) (x : State) (v : Nat) :
    gstep (x.map f) v = (gstep x v).map f := by
  unfold gstep
  split <;> simp [List.map_take, List.map_drop]

theorem walkRows_relabel (σ : State) (x : State) (vs : List Nat) :
    walkRows (relabel σ x) vs = (walkRows x vs).map (relabelRow σ) := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih =>
    simp only [walkRows, List.map_cons]
    have h : gstep (relabel σ x) v = relabel σ (gstep x v) := gstep_map _ _ _
    rw [h, ih]
    rfl

theorem walkEnd_relabel (σ : State) (x : State) (vs : List Nat) :
    walkEnd (relabel σ x) vs = relabel σ (walkEnd x vs) := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih =>
    simp only [walkEnd]
    have h : gstep (relabel σ x) v = relabel σ (gstep x v) := gstep_map _ _ _
    rw [h, ih]

/-! ## Facts checked on all 720 states -/

theorem canon_rotateLeft_all : ∀ x, IsState x → ∀ j, j < 6 → canon (x.rotateLeft j) = canon x :=
  forall_stateP (by decide +kernel)

theorem idxOf_zero_lt_all : ∀ x, IsState x → x.idxOf 0 < 6 :=
  forall_stateP (by decide +kernel)

theorem gstep_state_all : ∀ x, IsState x → ∀ v, v < 7 → 1 ≤ v → IsState (gstep x v) :=
  forall_stateP (by decide +kernel)

theorem app_lt_all : ∀ σ, IsState σ → ∀ a, a < 6 → app σ a < 6 :=
  forall_stateP (by decide +kernel)

theorem app_inj_all : ∀ σ, IsState σ → ∀ a, a < 6 → ∀ b, b < 6 → app σ a = app σ b → a = b :=
  forall_stateP (by decide +kernel)

/-- The inverse renaming. -/
def inv (σ : State) : State := (List.range 6).map (fun a => σ.idxOf a)

theorem inv_all : ∀ σ, IsState σ → IsState (inv σ) ∧
    ∀ a, a < 6 → app (inv σ) (app σ a) = a ∧ app σ (app (inv σ) a) = a :=
  forall_stateP (by decide +kernel)

theorem relabel_inv_self_all : ∀ σ, IsState σ → relabel (inv σ) σ = id6 :=
  forall_stateP (by decide +kernel)

/-! ## Consequences -/

theorem relabel_state {σ x : State} (hσ : IsState σ) (hx : IsState x) : IsState (relabel σ x) := by
  obtain ⟨hl, hn, hb⟩ := hx
  refine ⟨by simp [relabel, hl], ?_, ?_⟩
  · unfold relabel
    rw [List.Nodup, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ hn
    intro a b ha hb' hab heq
    exact hab (app_inj_all σ hσ a (hb a ha) b (hb b hb') heq)
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    exact app_lt_all σ hσ a (hb a ha)

theorem relabel_relabel_inv {σ x : State} (hσ : IsState σ) (hx : IsState x) :
    relabel σ (relabel (inv σ) x) = x := by
  unfold relabel
  rw [List.map_map]
  conv => rhs; rw [← List.map_id x]
  apply List.map_congr_left
  intro a ha
  exact ((inv_all σ hσ).2 a (hx.2.2 a ha)).2

theorem relabel_inv_relabel {σ x : State} (hσ : IsState σ) (hx : IsState x) :
    relabel (inv σ) (relabel σ x) = x := by
  unfold relabel
  rw [List.map_map]
  conv => rhs; rw [← List.map_id x]
  apply List.map_congr_left
  intro a ha
  exact ((inv_all σ hσ).2 a (hx.2.2 a ha)).1

/-- `canon (σ x)` depends only on the loop of `x`. -/
theorem canon_relabel_canon {σ x : State} (hσ : IsState σ) (hx : IsState x) :
    canon (relabel σ (canon x)) = canon (relabel σ x) := by
  have hk := idxOf_zero_lt_all x hx
  have h1 : relabel σ (canon x) = (relabel σ x).rotateLeft (x.idxOf 0) := by
    unfold relabel canon
    rw [map_rotateLeft]
  rw [h1]
  exact canon_rotateLeft_all _ (relabel_state hσ hx) _ hk

theorem canon_relabel_congr {σ x y : State} (hσ : IsState σ) (hx : IsState x) (hy : IsState y)
    (h : canon x = canon y) : canon (relabel σ x) = canon (relabel σ y) := by
  rw [← canon_relabel_canon hσ hx, ← canon_relabel_canon hσ hy, h]

theorem walkRows_states {g : State} {vs : List Nat} (hg : IsState g)
    (hv : ∀ v ∈ vs, 1 ≤ v ∧ v ≤ 6) : ∀ r ∈ walkRows g vs, IsState r.base := by
  induction vs generalizing g with
  | nil => simp [walkRows]
  | cons v vs ih =>
    intro r hr
    simp only [walkRows, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact hg
    · have hv1 := hv v (by simp)
      exact ih (gstep_state_all g hg v (by omega) hv1.1)
        (fun w hw => hv w (List.mem_cons_of_mem _ hw)) r hr

/-- Renaming cannot make two disjoint lists of rows meet: if the renamed lists are disjoint, so
are the lists. -/
theorem disj_of_relabel {σ : State} {P R : List (Row Nat)} (hσ : IsState σ)
    (hP : ∀ r ∈ P, IsState r.base) (hR : ∀ s ∈ R, IsState s.base)
    (h : Disj (P.map (relabelRow σ)) (R.map (relabelRow σ))) : Disj P R := by
  intro r hr s hs he
  exact h (relabelRow σ r) (List.mem_map_of_mem hr) (relabelRow σ s) (List.mem_map_of_mem hs)
    (canon_relabel_congr hσ (hP r hr) (hR s hs) he)

theorem relabelRow_inv {σ : State} (hσ : IsState σ) {P : List (Row Nat)}
    (hP : ∀ r ∈ P, IsState r.base) : (P.map (relabelRow σ)).map (relabelRow (inv σ)) = P := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id P]
  apply List.map_congr_left
  intro r hr
  simp only [Function.comp, relabelRow, relabel_inv_relabel hσ (hP r hr), id]

/-- Renaming keeps disjoint lists of rows disjoint. -/
theorem relabel_disj {σ : State} {P R : List (Row Nat)} (hσ : IsState σ)
    (hP : ∀ r ∈ P, IsState r.base) (hR : ∀ s ∈ R, IsState s.base) (h : Disj P R) :
    Disj (P.map (relabelRow σ)) (R.map (relabelRow σ)) := by
  have hi := (inv_all σ hσ).1
  have hP' : ∀ r ∈ P.map (relabelRow σ), IsState r.base := by
    intro r hr
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
    exact relabel_state hσ (hP t ht)
  have hR' : ∀ r ∈ R.map (relabelRow σ), IsState r.base := by
    intro r hr
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
    exact relabel_state hσ (hR t ht)
  apply disj_of_relabel hi hP' hR'
  rw [relabelRow_inv hσ hP, relabelRow_inv hσ hR]
  exact h

end N8Struct
