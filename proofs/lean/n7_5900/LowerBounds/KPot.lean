import LowerBounds.KRev
import LowerBounds.KSound

/-!
# The potential, Lemma REV and Lemma CUT (the written proof, sections 4.4 and 4.5)

`phiAt k a b h A B` is the potential of the cut between the rows `A` and the rows `B` of the
sequence `A ++ B`: `a · rows(A) - b · holes(A) - 2 h · (links of weight 4 inside A)`, less `h` if
the link at the cut has weight 4; `0` for the cut before the first row.

* `phiAt_mirror` (Lemma REV): the cut of the reversed sequence that corresponds to a cut has the
  potential of the whole sequence less the potential of the cut.
* `Good L`: for every cut there is a cut such that the two potentials add up to at least the
  potential of the whole sequence (this is `m + M ≥ phi_T`).  `good_or_rev`: a sequence or its
  reversal is good.
* `ruleK_of_good` (Lemma CUT and section 4.5): along a good counterexample with the fewest rows
  the rule of the search holds.
* `seqCap_levelK`: if the rule holds along no sequence (`KStmt`), the statement F(s; lo - 1, hi)
  holds, given the rows of fewer links up to `hi` holes and the row of `s` links below `lo`.
-/

namespace SuperpermLowerBounds
namespace KS

open PS (TRow IsSeq holesT linksT SeqCapLt)

variable {k : ℕ}

/-! ### Folds -/

theorem anyLe_true {p : ℕ → Bool} : ∀ {n x : ℕ}, x ≤ n → p x = true → anyLe p n = true
  | 0, x, hx, hp => by
    have h0 : x = 0 := by omega
    subst h0
    simpa [anyLe] using hp
  | n + 1, x, hx, hp => by
    simp only [anyLe, Bool.or_eq_true]
    by_cases h : x = n + 1
    · subst h
      exact Or.inl hp
    · exact Or.inr (anyLe_true (by omega) hp)

theorem minLe_le {p : ℕ → Bool} {f : ℕ → ℤ} {init : ℤ} :
    ∀ {n x : ℕ}, x ≤ n → p x = true → minLe p f init n ≤ f x
  | 0, x, hx, hp => by
    have h0 : x = 0 := by omega
    subst h0
    simp only [minLe, hp, if_true]
    exact min_le_right _ _
  | n + 1, x, hx, hp => by
    by_cases h : x = n + 1
    · subst h
      simp only [minLe, hp, if_true]
      exact min_le_right _ _
    · have ih := minLe_le (init := init) (f := f) (show x ≤ n by omega) hp
      simp only [minLe]
      split_ifs
      · exact le_trans (min_le_left _ _) ih
      · exact ih

theorem le_maxLe {f : ℕ → ℤ} : ∀ {n x : ℕ}, x ≤ n → f x ≤ maxLe f n
  | 0, x, hx => by
    have h0 : x = 0 := by omega
    subst h0
    exact le_refl _
  | n + 1, x, hx => by
    simp only [maxLe]
    by_cases h : x = n + 1
    · subst h
      exact le_max_right _ _
    · exact le_trans (le_maxLe (by omega)) (le_max_left _ _)

theorem le_maxLeN {f : ℕ → ℕ} : ∀ {n x : ℕ}, x ≤ n → f x ≤ maxLeN f n
  | 0, x, hx => by
    have h0 : x = 0 := by omega
    subst h0
    exact le_refl _
  | n + 1, x, hx => by
    simp only [maxLeN]
    by_cases h : x = n + 1
    · subst h
      exact le_max_right _ _
    · exact le_trans (le_maxLeN (by omega)) (le_max_left _ _)

/-! ### The potential -/

theorem potN_eq (a b h t r d : ℕ) :
    potN a b h t r d = (a : ℤ) * r - (b : ℤ) * d - 2 * (h : ℤ) * t := by
  simp only [potN]
  push_cast
  ring

theorem potS_eq (a b h t r d : ℕ) :
    potS a b h t r d = (a : ℤ) * r - (b : ℤ) * d - 2 * (h : ℤ) * t - h := by
  simp only [potS, potN_eq]

theorem fK_eq (a b h kd t r d : ℕ) (hkd : kd ≤ 1) :
    fK (potN a b h) (potS a b h) kd t r d
      = (a : ℤ) * r - (b : ℤ) * d - 2 * (h : ℤ) * t - (h : ℤ) * kd := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkd with rfl | rfl
  · simp [fK, potN_eq]
  · simp [fK, potS_eq]

theorem fK_le (a b h kd t r d : ℕ) :
    fK (potN a b h) (potS a b h) kd t r d ≤ potN a b h t r d := by
  unfold fK
  split_ifs
  · exact le_refl _
  · rw [potS_eq, potN_eq]
    have : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
    linarith

theorem potN_mono (a b h t d : ℕ) {r r' : ℕ} (hr : r ≤ r') :
    potN a b h t r d ≤ potN a b h t r' d := by
  rw [potN_eq, potN_eq]
  have : (a : ℤ) * r ≤ (a : ℤ) * r' := by exact_mod_cast Nat.mul_le_mul_left a hr
  linarith

/-- The potential of two parts joined by a link is at most the sum of their potentials. -/
theorem potN_add (a b h t z u r r' d d' : ℕ) :
    potN a b h (t + z + u) (r + r') (d + d') ≤ potN a b h t r d + potN a b h u r' d' := by
  rw [potN_eq, potN_eq, potN_eq]
  push_cast
  have hz : (0 : ℤ) ≤ 2 * (h : ℤ) * (z : ℤ) := by positivity
  nlinarith [hz]

/-- The kind of the first row (`0` if there is none). -/
def hdK : List TRow → ℕ
  | [] => 0
  | y :: _ => y.1

/-- The potential of the cut between the rows `A` and the rows `B`. -/
def phiAt (k a b h : ℕ) (A B : List TRow) : ℤ :=
  if A = [] then 0
  else fK (potN a b h) (potS a b h) (hdK B) (linksT A) A.length (holesT k A)

theorem phiAt_nil (a b h : ℕ) (B : List TRow) : phiAt k a b h [] B = 0 := if_pos rfl

theorem phiAt_end (a b h : ℕ) {A : List TRow} (hA : A ≠ []) :
    phiAt k a b h A [] = potN a b h (linksT A) A.length (holesT k A) := by
  unfold phiAt
  rw [if_neg hA]
  rfl

theorem phiAt_cons (a b h : ℕ) {A : List TRow} (hA : A ≠ []) (y : TRow) (B : List TRow) :
    phiAt k a b h A (y :: B)
      = fK (potN a b h) (potS a b h) y.1 (linksT A) A.length (holesT k A) := by
  unfold phiAt
  rw [if_neg hA]
  rfl

/-- The potential of a cut depends on the first row behind the cut only. -/
theorem phiAt_append (a b h : ℕ) (A1 : List TRow) {A2 : List TRow} (hA2 : A2 ≠ [])
    (B : List TRow) : phiAt k a b h A1 (A2 ++ B) = phiAt k a b h A1 A2 := by
  obtain ⟨y, A2', rfl⟩ := List.exists_cons_of_ne_nil hA2
  unfold phiAt
  rfl

/-- The reversed sequence is cut where the sequence is. -/
theorem revA_split (A B : List TRow) :
    revA k 0 (A ++ B) = revA k 0 B ++ revA k (hdK B) A := by
  cases B with
  | nil => simp [revA, hdK]
  | cons y B' => exact revA_append 0 y B' A

/-- **Lemma REV.** -/
theorem phiAt_mirror (a b h : ℕ) {A B : List TRow} (hne : A ++ B ≠ [])
    (hk1 : ∀ x ∈ A ++ B, x.1 ≤ 1) :
    phiAt k a b h (revA k 0 B) (revA k (hdK B) A)
      = phiAt k a b h (A ++ B) [] - phiAt k a b h A B := by
  cases A with
  | nil =>
    have hB : B ≠ [] := by simpa using hne
    have e : revA k (hdK B) [] = [] := rfl
    rw [e, List.nil_append, phiAt_nil, phiAt_end a b h (revA_ne_nil 0 hB), phiAt_end a b h hB,
      linksT_revA, length_revA, holesT_revA, sub_zero]
  | cons x A' =>
    cases B with
    | nil =>
      have e : revA k 0 [] = [] := rfl
      rw [e, phiAt_nil, List.append_nil, sub_self]
    | cons y B' =>
      have hA : x :: A' ≠ [] := List.cons_ne_nil x A'
      have hy : y.1 ≤ 1 := hk1 y (by simp)
      obtain ⟨Q, T, hQ⟩ := revA_head (k := k) y.1 x A'
      have e0 : hdK (y :: B') = y.1 := rfl
      have hl := PS.linksT_append (x :: A') y B' hA
      have hz : (if y.1 = 0 then 0 else 1) = y.1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with h0 | h0 <;> simp [h0]
      rw [hz] at hl
      rw [e0, hQ, phiAt_cons a b h (revA_ne_nil 0 (List.cons_ne_nil y B')) (y.1, Q) T,
        phiAt_end a b h hne, phiAt_cons a b h hA y B', linksT_revA, length_revA, holesT_revA,
        hl, List.length_append, PS.holesT_append, fK_eq _ _ _ _ _ _ _ hy, fK_eq _ _ _ _ _ _ _ hy,
        potN_eq]
      push_cast
      ring

/-- A cut of the reversed sequence comes from a cut of the sequence. -/
theorem split_rev {L A' B' : List TRow} (h : revA k 0 L = A' ++ B') :
    ∃ A B, L = A ++ B ∧ A' = revA k 0 B ∧ B' = revA k (hdK B) A := by
  have hlen : A'.length ≤ L.length := by
    have := congrArg List.length h
    rw [length_revA, List.length_append] at this
    omega
  refine ⟨L.take (L.length - A'.length), L.drop (L.length - A'.length),
    (List.take_append_drop _ _).symm, ?_⟩
  have h2 := revA_split (k := k) (L.take (L.length - A'.length))
    (L.drop (L.length - A'.length))
  rw [List.take_append_drop] at h2
  rw [h2] at h
  have hl : (revA k 0 (L.drop (L.length - A'.length))).length = A'.length := by
    rw [length_revA, List.length_drop]
    omega
  obtain ⟨e1, e2⟩ := List.append_inj h hl
  exact ⟨e1.symm, e2.symm⟩

/-- For every cut there is a cut such that the two potentials add up to at least the potential of
the whole sequence. -/
def Good (k a b h : ℕ) (L : List TRow) : Prop :=
  ∀ A0 B0, L = A0 ++ B0 → ∃ A1 B1, L = A1 ++ B1 ∧
    phiAt k a b h L [] ≤ phiAt k a b h A0 B0 + phiAt k a b h A1 B1

/-- **A sequence or its reversal is good** (section 4.4, (4.1)). -/
theorem good_or_rev (a b h : ℕ) {L : List TRow} (hne : L ≠ []) (hk1 : ∀ x ∈ L, x.1 ≤ 1) :
    Good k a b h L ∨ Good k a b h (revA k 0 L) := by
  by_cases hg : Good k a b h L
  · exact Or.inl hg
  right
  unfold Good at hg
  push Not at hg
  obtain ⟨A0, B0, hL0, hbad⟩ := hg
  intro A' B' hsplit
  obtain ⟨A2, B2, hL2, hA', hB'⟩ := split_rev hsplit
  refine ⟨revA k 0 B0, revA k (hdK B0) A0, by rw [hL0]; exact revA_split A0 B0, ?_⟩
  have m0 := phiAt_mirror (k := k) a b h (A := A0) (B := B0) (by rw [← hL0]; exact hne)
    (by rw [← hL0]; exact hk1)
  have m2 := phiAt_mirror (k := k) a b h (A := A2) (B := B2) (by rw [← hL2]; exact hne)
    (by rw [← hL2]; exact hk1)
  have eT : phiAt k a b h (revA k 0 L) [] = phiAt k a b h L [] := by
    rw [phiAt_end a b h (revA_ne_nil 0 hne), phiAt_end a b h hne, linksT_revA, length_revA,
      holesT_revA]
  rw [← hL0] at m0
  rw [← hL2] at m2
  rw [hA', hB', eT, m2, m0]
  have := hbad A2 B2 hL2
  linarith

/-! ### Lemma CUT -/

/-- The cut in table form allows the continuation, from the three cases of Lemma CUT. -/
theorem cut_of_cases {P : ℕ → ℕ → ℕ} {s lo hi a b h t r d x : ℕ} {m' M' phiT : ℤ}
    (hall : allowedF P s lo t r d x = true) (hxhi : x ≤ hi)
    (hT : cF P s a b h x ≤ phiT)
    (hcase : m' < 0 → ∃ φ : ℤ, phiT ≤ m' + φ ∧ (φ ≤ M' ∨ ∃ e, e ≤ x - d ∧
      φ ≤ uF P s a b h t (d + e) ∧ φ ≤ potN a b h t r d + segF P s a b h t e)) :
    cutF (a1F P s lo hi a b h) (a2F (uF P s a b h) (segF P s a b h) P s lo hi a b h) t r d m' M'
      = true := by
  simp only [cutF, Bool.or_eq_true, decide_eq_true_eq]
  by_cases h0 : 0 ≤ m'
  · exact Or.inl (Or.inl h0)
  obtain ⟨φ, h1, h2⟩ := hcase (by omega)
  rcases h2 with h2 | ⟨e, he, hU, hS⟩
  · left
    right
    have ha1 : a1F P s lo hi a b h t r d ≤ cF P s a b h x := minLe_le hxhi hall
    linarith
  · right
    have hpk : φ ≤ pkF (uF P s a b h) (segF P s a b h) (potN a b h t r d) t d x := by
      unfold pkF
      exact le_trans (le_min hU hS)
        (le_maxLe (f := fun e => min (uF P s a b h t (d + e))
          (potN a b h t r d + segF P s a b h t e)) he)
    have ha2 : a2F (uF P s a b h) (segF P s a b h) P s lo hi a b h t r d
        ≤ cF P s a b h x - pkF (uF P s a b h) (segF P s a b h) (potN a b h t r d) t d x :=
      minLe_le (f := fun x => cF P s a b h x
        - pkF (uF P s a b h) (segF P s a b h) (potN a b h t r d) t d x) hxhi hall
    linarith

theorem linksT_le_left (U : List TRow) : ∀ X : List TRow, linksT X ≤ linksT (U ++ X)
  | [] => Nat.zero_le _
  | x :: X' => by
    cases U with
    | nil => exact le_refl _
    | cons u U' =>
      have := PS.linksT_append (u :: U') x X' (List.cons_ne_nil u U')
      omega

theorem linksT_le_right (X : List TRow) : ∀ W : List TRow, linksT X ≤ linksT (X ++ W)
  | [] => by simp
  | w :: W' => by
    cases X with
    | nil => exact Nat.zero_le _
    | cons x X' =>
      have := PS.linksT_append (x :: X') w W' (List.cons_ne_nil x X')
      omega

set_option maxHeartbeats 1600000 in
/-- **Lemma CUT, section 4.5.** Along a good sequence that is above its cap, while all its parts
obey the caps, the rule of the search holds. -/
theorem ruleK_of_good {P : ℕ → ℕ → ℕ} {s lo hi a b h : ℕ} {L : List TRow}
    (hk1 : ∀ x ∈ L, x.1 ≤ 1) (hs : linksT L = s) (hlo : lo ≤ holesT k L)
    (hhi : holesT k L ≤ hi) (hbig : P s (holesT k L) < L.length)
    (hpart : ∀ U X W, L = U ++ X ++ W → X ≠ [] → X.length < L.length →
      X.length ≤ P (linksT X) (holesT k X))
    (hgood : Good k a b h L) :
    ∀ (B A : List TRow) (m M : ℤ), L = A ++ B → A ≠ [] →
      (∃ A1 A2, A = A1 ++ A2 ∧ A2 ≠ [] ∧ phiAt k a b h A1 (A2 ++ B) = m) →
      (∀ A1 A2, A = A1 ++ A2 → A2 ≠ [] → phiAt k a b h A1 (A2 ++ B) ≤ M) →
      RuleK k (codeF P s lo hi) (potN a b h) (potS a b h)
        (cutF (a1F P s lo hi a b h) (a2F (uF P s a b h) (segF P s a b h) P s lo hi a b h))
        (linksT A) A.length (holesT k A) m M B := by
  intro B
  induction B with
  | nil =>
    intro A m M hL hA _ _
    have hLA : L = A := by simpa using hL
    subst hLA
    show codeF P s lo hi (linksT L) L.length (holesT k L) = 1
    have hb : kBad P s lo hi (linksT L) L.length (holesT k L) = true := by
      simp only [kBad, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact ⟨⟨⟨hs, hlo⟩, hhi⟩, hbig⟩
    simp only [codeF, hb, if_true]
  | cons y B' ih =>
    intro A m M hL hA hm hM
    obtain ⟨kd, Q⟩ := y
    have hLne : L ≠ [] := by
      rw [hL]
      simp
    have hkd : kd ≤ 1 := hk1 (kd, Q) (by rw [hL]; simp)
    have hApos : 0 < A.length := List.length_pos_iff.mpr hA
    have hlenL : L.length = A.length + ((kd, Q) :: B').length := by
      rw [hL, List.length_append]
    have hholes : holesT k L = holesT k A + holesT k ((kd, Q) :: B') := by
      rw [hL, PS.holesT_append]
    have hlinks := PS.linksT_append A (kd, Q) B' hA
    rw [← hL, hs] at hlinks
    have hz : (if ((kd, Q) : TRow).1 = 0 then 0 else 1) = kd := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkd with h0 | h0 <;> simp [h0]
    rw [hz] at hlinks
    -- the parts obey the caps
    have hBpart : ((kd, Q) :: B').length
        ≤ P (linksT ((kd, Q) :: B')) (holesT k ((kd, Q) :: B')) :=
      hpart A _ [] (by rw [hL]; simp) (by simp) (by omega)
    have hApart : A.length ≤ P (linksT A) (holesT k A) :=
      hpart [] A ((kd, Q) :: B') (by rw [hL]; simp) hA (by rw [hlenL]; simp)
    -- the plain rule
    have hnb : kBad P s lo hi (linksT A) A.length (holesT k A) = false := by
      rw [Bool.eq_false_iff]
      intro hb
      simp only [kBad, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
      obtain ⟨⟨⟨h1, _⟩, _⟩, h4⟩ := hb
      rw [h1] at hApart
      omega
    have hN : kd = 0 →
        kLevN P s lo (linksT A) A.length (holesT k A) (holesT k L) = true := by
      intro h0
      simp only [kLevN, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨by omega, hlo⟩, by omega⟩, ?_⟩
      have e1 : s - linksT A = linksT ((kd, Q) :: B') := by omega
      have e2 : holesT k L - holesT k A = holesT k ((kd, Q) :: B') := by omega
      rw [e1, e2]
      omega
    have hS : kd = 1 →
        kLevS P s lo (linksT A) A.length (holesT k A) (holesT k L) = true := by
      intro h0
      simp only [kLevS, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨by omega, hlo⟩, by omega⟩, ?_⟩
      have e1 : s - linksT A - 1 = linksT ((kd, Q) :: B') := by omega
      have e2 : holesT k L - holesT k A = holesT k ((kd, Q) :: B') := by omega
      rw [e1, e2]
      omega
    have hall : allowedF P s lo (linksT A) A.length (holesT k A) (holesT k L) = true := by
      unfold allowedF
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkd with h0 | h0
      · rw [hN h0]
        rfl
      · rw [hS h0]
        exact Bool.or_true _
    have hcode : codeF P s lo hi (linksT A) A.length (holesT k A) = 4 ∨
        codeF P s lo hi (linksT A) A.length (holesT k A) = 2 + kd := by
      unfold codeF
      rw [hnb]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkd with h0 | h0
      · have hN' := anyLe_true hhi (hN h0)
        rw [hN', h0]
        by_cases hS' : anyLe (kLevS P s lo (linksT A) A.length (holesT k A)) hi = true
        · simp [hS']
        · simp [hS']
      · have hS' := anyLe_true hhi (hS h0)
        rw [hS', h0]
        by_cases hN' : anyLe (kLevN P s lo (linksT A) A.length (holesT k A)) hi = true
        · simp [hN']
        · simp [hN']
    -- the potential of the cut behind `A`
    have hf : phiAt k a b h A ((kd, Q) :: B')
        = fK (potN a b h) (potS a b h) kd (linksT A) A.length (holesT k A) :=
      phiAt_cons a b h hA (kd, Q) B'
    have hphiT : phiAt k a b h L [] = potN a b h s L.length (holesT k L) := by
      rw [phiAt_end a b h hLne, hs]
    have hT : cF P s a b h (holesT k L) ≤ phiAt k a b h L [] := by
      rw [hphiT]
      exact potN_mono a b h s (holesT k L) hbig
    have hcut : cutF (a1F P s lo hi a b h)
        (a2F (uF P s a b h) (segF P s a b h) P s lo hi a b h) (linksT A) A.length (holesT k A)
        (min m (fK (potN a b h) (potS a b h) kd (linksT A) A.length (holesT k A)))
        (max M (fK (potN a b h) (potS a b h) kd (linksT A) A.length (holesT k A))) = true := by
      refine cut_of_cases hall hhi hT ?_
      intro hneg
      -- the least potential is attained at a cut
      obtain ⟨A0, B0, hL0, hphi0⟩ : ∃ A0 B0, L = A0 ++ B0 ∧ phiAt k a b h A0 B0
          = min m (fK (potN a b h) (potS a b h) kd (linksT A) A.length (holesT k A)) := by
        by_cases hmf : m ≤ fK (potN a b h) (potS a b h) kd (linksT A) A.length (holesT k A)
        · obtain ⟨A1, A2, hA12, _, hphi⟩ := hm
          refine ⟨A1, A2 ++ (kd, Q) :: B', by rw [hL, hA12, List.append_assoc], ?_⟩
          rw [min_eq_left hmf]
          exact hphi
        · refine ⟨A, (kd, Q) :: B', hL, ?_⟩
          rw [min_eq_right (by omega), hf]
      obtain ⟨A1, B1, hL1, hge⟩ := hgood A0 B0 hL0
      rw [hphi0] at hge
      refine ⟨phiAt k a b h A1 B1, hge, ?_⟩
      have hsplit : A ++ (kd, Q) :: B' = A1 ++ B1 := by rw [← hL, hL1]
      rcases List.append_eq_append_iff.mp hsplit with ⟨E, hA1, hBE⟩ | ⟨A2, hA12, hB1⟩
      · -- the cut is behind `A`
        by_cases hE : E = []
        · left
          subst hE
          rw [List.append_nil] at hA1
          rw [List.nil_append] at hBE
          rw [hA1, ← hBE, hf]
          exact le_max_right _ _
        right
        have hB1 : B1 ≠ [] := by
          intro h0
          rw [h0, List.append_nil] at hL1
          rw [h0, ← hL1] at hge
          omega
        have hA1ne : A1 ≠ [] := by
          rw [hA1]
          simp [hA]
        obtain ⟨e0, E', rfl⟩ := List.exists_cons_of_ne_nil hE
        obtain ⟨b1, B1', rfl⟩ := List.exists_cons_of_ne_nil hB1
        have hLE : L = A ++ (e0 :: E') ++ (b1 :: B1') := by rw [hL1, hA1]
        have hlenE : L.length = A.length + (e0 :: E').length + (b1 :: B1').length := by
          rw [hLE, List.length_append, List.length_append]
        have hholesE : holesT k L
            = holesT k A + holesT k (e0 :: E') + holesT k (b1 :: B1') := by
          rw [hLE, PS.holesT_append, PS.holesT_append]
        have hEpart : (e0 :: E').length ≤ P (linksT (e0 :: E')) (holesT k (e0 :: E')) :=
          hpart A (e0 :: E') (b1 :: B1') hLE (by simp) (by rw [hlenE]; omega)
        have hA1part : A1.length ≤ P (linksT A1) (holesT k A1) :=
          hpart [] A1 (b1 :: B1') (by rw [hL1]; simp) hA1ne
            (by rw [hL1, List.length_append]; simp)
        have hlA1 := PS.linksT_append A e0 E' hA
        rw [← hA1] at hlA1
        have hlL := PS.linksT_append A1 b1 B1' hA1ne
        rw [← hL1, hs] at hlL
        have hhA1 : holesT k A1 = holesT k A + holesT k (e0 :: E') := by
          rw [hA1, PS.holesT_append]
        have hlenA1 : A1.length = A.length + (e0 :: E').length := by
          rw [hA1, List.length_append]
        have hphi1 : phiAt k a b h A1 (b1 :: B1') ≤ potN a b h (linksT A1) A1.length
            (holesT k A1) := by
          rw [phiAt_cons a b h hA1ne]
          exact fK_le _ _ _ _ _ _ _
        refine ⟨holesT k (e0 :: E'), by omega, ?_, ?_⟩
        · -- the prefix of the peak obeys its cap
          have h1 : potN a b h (linksT A1) A1.length (holesT k A1)
              ≤ lin P a b h (linksT A1) (holesT k A1) := potN_mono a b h _ _ hA1part
          have h2 : lin P a b h (linksT A + (linksT A1 - linksT A))
              (holesT k A + holesT k (e0 :: E')) ≤ uF P s a b h (linksT A)
                (holesT k A + holesT k (e0 :: E')) :=
            le_maxLe (f := fun i => lin P a b h (linksT A + i)
              (holesT k A + holesT k (e0 :: E'))) (show linksT A1 - linksT A ≤ s - linksT A by
                omega)
          have e : linksT A + (linksT A1 - linksT A) = linksT A1 := by omega
          rw [e, ← hhA1] at h2
          rw [← hhA1]
          exact le_trans hphi1 (le_trans h1 h2)
        · -- the part between the cut and the peak obeys its cap
          have h1 : lin P a b h (linksT (e0 :: E')) (holesT k (e0 :: E'))
              ≤ segF P s a b h (linksT A) (holesT k (e0 :: E')) :=
            le_maxLe (f := fun u => lin P a b h u (holesT k (e0 :: E')))
              (show linksT (e0 :: E') ≤ s - linksT A by omega)
          have h2 : potN a b h (linksT (e0 :: E')) (e0 :: E').length (holesT k (e0 :: E'))
              ≤ lin P a b h (linksT (e0 :: E')) (holesT k (e0 :: E')) :=
            potN_mono a b h _ _ hEpart
          have h3 : potN a b h (linksT A1) A1.length (holesT k A1)
              ≤ potN a b h (linksT A) A.length (holesT k A)
                + potN a b h (linksT (e0 :: E')) (e0 :: E').length (holesT k (e0 :: E')) := by
            rw [hlA1, hlenA1, hhA1]
            exact potN_add a b h _ _ _ _ _ _ _
          linarith only [hphi1, h1, h2, h3]
      · -- the cut is not behind `A`
        left
        by_cases hA2 : A2 = []
        · subst hA2
          rw [List.append_nil] at hA12
          rw [List.nil_append] at hB1
          rw [← hA12, hB1, hf]
          exact le_max_right _ _
        · rw [hB1]
          exact le_trans (hM A1 A2 hA12 hA2) (le_max_left _ _)
    -- the rule along the rest
    have e1 : linksT (A ++ [((kd, Q) : TRow)]) = linksT A + kd := by
      have h1 := PS.linksT_append A (kd, Q) [] hA
      have e0 : linksT [((kd, Q) : TRow)] = 0 := rfl
      rw [h1, e0, hz, Nat.add_zero]
    have e2 : (A ++ [((kd, Q) : TRow)]).length = A.length + 1 := by simp
    have e3 : holesT k (A ++ [((kd, Q) : TRow)]) = holesT k A + (k - 1 - Q.length) := by
      rw [PS.holesT_append]
      simp [holesT]
    have hrec := ih (A ++ [(kd, Q)])
      (min m (fK (potN a b h) (potS a b h) kd (linksT A) A.length (holesT k A)))
      (max M (fK (potN a b h) (potS a b h) kd (linksT A) A.length (holesT k A)))
      (by rw [hL]; simp) (by simp)
      (by
        by_cases hmf : m ≤ fK (potN a b h) (potS a b h) kd (linksT A) A.length (holesT k A)
        · obtain ⟨A1, A2, hA12, hA2, hphi⟩ := hm
          refine ⟨A1, A2 ++ [(kd, Q)], by rw [hA12, List.append_assoc], by simp, ?_⟩
          rw [min_eq_left hmf, List.append_assoc]
          exact hphi
        · refine ⟨A, [(kd, Q)], rfl, by simp, ?_⟩
          rw [min_eq_right (by omega)]
          exact hf)
      (by
        intro A1 A2 hA12 hA2
        have hA2' : A2 = A2.dropLast ++ [A2.getLast hA2] := (List.dropLast_append_getLast hA2).symm
        rw [hA2', ← List.append_assoc] at hA12
        obtain ⟨hAeq, hlast⟩ := List.append_inj' hA12 rfl
        rw [hA2', List.append_assoc, ← hlast]
        by_cases hd : A2.dropLast = []
        · rw [hd, List.append_nil] at hAeq
          rw [hd, List.nil_append, ← hAeq]
          have e : [((kd, Q) : TRow)] ++ B' = (kd, Q) :: B' := rfl
          rw [e, hf]
          exact le_max_right _ _
        · have e : A2.dropLast ++ ([((kd, Q) : TRow)] ++ B') = A2.dropLast ++ (kd, Q) :: B' := rfl
          rw [e]
          exact le_trans (hM A1 A2.dropLast hAeq hd) (le_max_left _ _))
    rw [e1, e2, e3] at hrec
    simp only [RuleK]
    exact ⟨hkd, hcode, hcut, hrec⟩

/-! ### The statement by levels -/

/-- **Shortest counterexample with the reversal cut.**  F(s; lo - 1, hi) holds if the rule of the
search holds along no sequence, given the rows of fewer links up to `hi` holes and the row of `s`
links below `lo`. -/
theorem seqCap_levelK {P : ℕ → ℕ → ℕ} {s lo hi a b h : ℕ} (hk : 4 ≤ k)
    (hlow : ∀ j, j < s → SeqCapLt k j (P j) (hi + 1))
    (hprev : SeqCapLt k s (P s) lo)
    (hst : KStmt k (codeF P s lo hi) (potN a b h) (potS a b h)
      (cutF (a1F P s lo hi a b h) (a2F (uF P s a b h) (segF P s a b h) P s lo hi a b h))) :
    SeqCapLt k s (P s) (hi + 1) := by
  suffices hmain : ∀ n : ℕ, ∀ L : List TRow, L.length = n → IsSeq k L → (∀ x ∈ L, x.1 ≤ 1) →
      linksT L = s → holesT k L < hi + 1 → L.length ≤ P s (holesT k L) from
    fun L h1 h2 h3 h4 => hmain L.length L rfl h1 h2 h3 h4
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L hlen hL htag hlinks hholes
    by_cases hlo : holesT k L < lo
    · exact hprev L hL htag hlinks hlo
    by_cases hne : L = []
    · subst hne
      simp
    by_contra hnb
    -- every proper part of a sequence with `n` rows obeys its cap
    have hparts : ∀ L' : List TRow, L'.length = n → IsSeq k L' → (∀ x ∈ L', x.1 ≤ 1) →
        linksT L' = s → holesT k L' < hi + 1 → ∀ U X W, L' = U ++ X ++ W → X ≠ [] →
        X.length < L'.length → X.length ≤ P (linksT X) (holesT k X) := by
      intro L' hlen' hL' htag' hlinks' hholes' U X W hUXW _ hXlen
      have hX : IsSeq k X := hL'.infix ⟨U, W, hUXW.symm⟩
      have hXtag : ∀ y ∈ X, y.1 ≤ 1 := fun y hy => htag' y (by rw [hUXW]; simp [hy])
      have hXholes : holesT k X ≤ holesT k L' := by
        rw [hUXW, PS.holesT_append, PS.holesT_append]
        omega
      have hXlinks : linksT X ≤ s := by
        rw [← hlinks', hUXW]
        exact le_trans (linksT_le_left U X) (linksT_le_right (U ++ X) W)
      by_cases hsX : linksT X < s
      · exact hlow _ hsX X hX hXtag rfl (by omega)
      · have hs : linksT X = s := by omega
        rw [hs]
        by_cases hloX : holesT k X < lo
        · exact hprev X hX hXtag hs hloX
        · exact ih X.length (by omega) X rfl hX hXtag hs (by omega)
    -- the sequence or its reversal is good
    have hrev : ∀ L' : List TRow, L'.length = n → IsSeq k L' → (∀ x ∈ L', x.1 ≤ 1) →
        linksT L' = s → holesT k L' = holesT k L → Good k a b h L' → False := by
      intro L' hlen' hL' htag' hlinks' hholes' hgood
      have hne' : L' ≠ [] := by
        intro h0
        rw [h0] at hlen'
        rw [← hlen] at hlen'
        exact hne (List.length_eq_zero_iff.mp hlen'.symm)
      obtain ⟨x0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne'
      have hrule := ruleK_of_good (P := P) (s := s) (lo := lo) (hi := hi) (a := a) (b := b)
        (h := h) htag' hlinks' (by rw [hholes']; omega) (by rw [hholes']; omega)
        (by rw [hholes', hlen', ← hlen]; omega)
        (hparts _ hlen' hL' htag' hlinks' (by omega)) hgood rest [x0] 0 0 rfl (by simp)
        ⟨[], [x0], rfl, by simp, phiAt_nil a b h _⟩
        (by
          intro A1 A2 hA12 hA2
          have hA1 : A1 = [] := by
            have hl := congrArg List.length hA12
            rw [List.length_append] at hl
            have : 0 < A2.length := List.length_pos_iff.mpr hA2
            simp only [List.length_cons, List.length_nil] at hl
            exact List.length_eq_zero_iff.mp (by omega)
          rw [hA1, phiAt_nil])
      have e1 : linksT [x0] = 0 := rfl
      have e2 : ([x0] : List TRow).length = 1 := rfl
      have e3 : holesT k [x0] = k - 1 - x0.2.length := by simp [holesT]
      rw [e1, e2, e3] at hrule
      exact hst x0 rest hL' hrule
    rcases good_or_rev (k := k) a b h hne htag with hg | hg
    · exact hrev L hlen hL htag hlinks rfl hg
    · exact hrev (revA k 0 L) (by rw [length_revA, hlen]) (isSeq_revA hk 0 hL)
        (kinds_revA (Nat.zero_le 1) htag) (by rw [linksT_revA, hlinks]) (holesT_revA 0 L) hg

end KS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.KS.good_or_rev
#print axioms SuperpermLowerBounds.KS.seqCap_levelK
