import LowerBounds.KPot

/-!
# From search equations to the statements F(s; lo - 1, hi)

* The tables of the compiled search are the functions they tabulate (`tabA_get`, `look2_tab2`,
  `codeT_eq`), the mask has the bits that the search needs (`maskG_bit`), and the cut read from
  tables allows at least what the cut allows (`cutT_of_cutF`).
* `kstmt_of_search`, `kstmt_of_searchA`: if every part of the compiled search (of the search with
  arithmetic tables) answers `false`, the rule of section 4.4 holds along no sequence.
* `seqCap_of_ksearch`, `seqCap_of_ksearchA`: then F(s; lo - 1, hi) holds, given the rows of fewer
  links up to `hi` holes and the row of `s` links below `lo`.
-/

namespace SuperpermLowerBounds
namespace KS

open PS (TRow IsSeq holesT linksT SeqCapLt capF)

/-! ### Tables -/

theorem tabA_get {α : Type} [Inhabited α] (A B C : ℕ) (f : ℕ → ℕ → ℕ → α) {t r d : ℕ}
    (ht : t < A) (hr : r < B) (hd : d < C) : (tabA A B C f)[(t * B + r) * C + d]! = f t r d := by
  have hi : (t * B + r) * C + d < A * B * C := by
    have h1 : t * B + r + 1 ≤ A * B := by nlinarith
    have h2 : (t * B + r + 1) * C ≤ A * B * C := Nat.mul_le_mul_right _ h1
    nlinarith
  have hsz : (t * B + r) * C + d < (tabA A B C f).size := by
    unfold tabA
    rw [Array.size_ofFn]
    exact hi
  rw [getElem!_pos (tabA A B C f) ((t * B + r) * C + d) hsz]
  simp only [tabA, Array.getElem_ofFn, S.mul_add_div' hd, S.mul_add_mod' hd,
    S.mul_add_div' hr, S.mul_add_mod' hr]

theorem look2_tab2 {α : Type} [Inhabited α] (A C : ℕ) (f : ℕ → ℕ → α) :
    look2 A C (tab2 A C f) f = f := by
  funext t y
  unfold look2
  by_cases h : (decide (t < A) && decide (y < C)) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨ht, hy⟩ := h
    have hi : t * C + y < A * C := by nlinarith
    have hsz : t * C + y < (tab2 A C f).size := by
      unfold tab2
      rw [Array.size_ofFn]
      exact hi
    rw [getElem!_pos (tab2 A C f) (t * C + y) hsz]
    simp only [tab2, Array.getElem_ofFn, S.mul_add_div' hy, S.mul_add_mod' hy]
  · rw [if_neg h]

theorem anyLe_congr {p q : ℕ → Bool} : ∀ {n : ℕ}, (∀ x, x ≤ n → p x = q x) →
    anyLe p n = anyLe q n
  | 0, h => h 0 (le_refl 0)
  | n + 1, h => by
    simp only [anyLe]
    rw [h (n + 1) (le_refl _), anyLe_congr (fun x hx => h x (by omega))]

theorem anyLe_false {p : ℕ → Bool} : ∀ {n : ℕ}, (∀ x, x ≤ n → p x = false) → anyLe p n = false
  | 0, h => h 0 (le_refl 0)
  | n + 1, h => by
    simp only [anyLe]
    rw [h (n + 1) (le_refl _), anyLe_false (fun x hx => h x (by omega))]
    rfl

/-- Above every cap of the row the code does not depend on the number of rows. -/
theorem codeF_big {P : ℕ → ℕ → ℕ} {s lo hi R t r d : ℕ} (hR : ∀ x, x ≤ hi → P s x < R)
    (hr : R ≤ r) : codeF P s lo hi t r d = codeF P s lo hi t R d := by
  have hbad : kBad P s lo hi t r d = kBad P s lo hi t R d := by
    simp only [kBad]
    by_cases hd : d ≤ hi
    · have h1 := hR d hd
      have h2 : P s d < r := by omega
      simp [h1, h2]
    · simp [hd]
  have hN : ∀ x, x ≤ hi → kLevN P s lo t r d x = kLevN P s lo t R d x := by
    intro x hx
    have h0 := hR x hx
    have h1 : P s x < r + P (s - t) (x - d) := by omega
    have h2 : P s x < R + P (s - t) (x - d) := by omega
    simp [kLevN, h1, h2]
  have hS : ∀ x, x ≤ hi → kLevS P s lo t r d x = kLevS P s lo t R d x := by
    intro x hx
    have h0 := hR x hx
    have h1 : P s x < r + P (s - t - 1) (x - d) := by omega
    have h2 : P s x < R + P (s - t - 1) (x - d) := by omega
    simp [kLevS, h1, h2]
  unfold codeF
  rw [hbad, anyLe_congr hN, anyLe_congr hS]

/-- With more than `s` links the code is `0`. -/
theorem codeF_t {P : ℕ → ℕ → ℕ} {s lo hi t r d : ℕ} (ht : s < t) :
    codeF P s lo hi t r d = 0 := by
  have hbad : kBad P s lo hi t r d = false := by
    have : ¬ t = s := by omega
    simp [kBad, this]
  have hN : anyLe (kLevN P s lo t r d) hi = false :=
    anyLe_false (fun x _ => by
      have : ¬ t ≤ s := by omega
      simp [kLevN, this])
  have hS : anyLe (kLevS P s lo t r d) hi = false :=
    anyLe_false (fun x _ => by
      have : ¬ t < s := by omega
      simp [kLevS, this])
  simp [codeF, hbad, hN, hS]

/-- With more than `hi` holes the code is `0`. -/
theorem codeF_d {P : ℕ → ℕ → ℕ} {s lo hi t r d : ℕ} (hd : hi < d) :
    codeF P s lo hi t r d = 0 := by
  have hbad : kBad P s lo hi t r d = false := by
    have : ¬ d ≤ hi := by omega
    simp [kBad, this]
  have hN : anyLe (kLevN P s lo t r d) hi = false :=
    anyLe_false (fun x hx => by
      have : ¬ d ≤ x := by omega
      simp [kLevN, this])
  have hS : anyLe (kLevS P s lo t r d) hi = false :=
    anyLe_false (fun x hx => by
      have : ¬ d ≤ x := by omega
      simp [kLevS, this])
  simp [codeF, hbad, hN, hS]

/-- The code read from its table is the code. -/
theorem codeT_eq {P : ℕ → ℕ → ℕ} {s lo hi R : ℕ} (hR : ∀ x, x ≤ hi → P s x < R) :
    codeT (s + 1) R (hi + 1) (tabA (s + 1) (R + 1) (hi + 1) (codeF P s lo hi))
      = codeF P s lo hi := by
  funext t r d
  unfold codeT
  by_cases h : (decide (t < s + 1) && decide (d < hi + 1)) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [tabA_get _ _ _ _ h.1 (show min r R < R + 1 by omega) h.2]
    by_cases hr : r ≤ R
    · rw [min_eq_left hr]
    · rw [min_eq_right (by omega)]
      exact (codeF_big hR (by omega)).symm
  · rw [if_neg h]
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h
    by_cases ht : t < s + 1
    · exact (codeF_d (by have := h ht; omega)).symm
    · exact (codeF_t (by omega)).symm

/-- The mask has the bit of every row behind which the code is not `0`. -/
theorem maskG_bit (code : ℕ → ℕ → ℕ → ℕ) (t r d : ℕ) : ∀ (n j : ℕ), j < n →
    code t r (d + (n - 1 - j)) ≠ 0 → (maskG code t r d n / 2 ^ j) % 2 = 1
  | 0, j, hj, _ => absurd hj (Nat.not_lt_zero _)
  | n + 1, 0, _, h => by
    have e : n + 1 - 1 - 0 = n := by omega
    rw [e] at h
    have hb : (code t r (d + n) != 0) = true := by simpa using h
    simp only [maskG, pow_zero, Nat.div_one, hb, if_true]
    omega
  | n + 1, j + 1, hj, h => by
    have e0 : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
    rw [e0] at h
    have ih := maskG_bit code t r d n j (by omega) h
    have e : (2 * maskG code t r d n + (if (code t r (d + n) != 0) = true then 1 else 0))
        / 2 ^ (j + 1) = maskG code t r d n / 2 ^ j := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, ← Nat.div_div_eq_div_mul]
      congr 1
      split_ifs <;> omega
    simp only [maskG]
    rw [e]
    exact ih

/-- The cut read from tables allows what the cut allows. -/
theorem cutT_of_cutF {A B C : ℕ} {a1 a2 : ℕ → ℕ → ℕ → ℤ} (t r d : ℕ) (m M : ℤ)
    (h : cutF a1 a2 t r d m M = true) :
    cutT A B C (tabA A B C a1) (tabA A B C a2) t r d m M = true := by
  unfold cutT
  by_cases hin : (decide (t < A) && decide (r < B) && decide (d < C)) = true
  · have hin' := hin
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hin'
    obtain ⟨⟨ht, hr⟩, hd⟩ := hin'
    rw [tabA_get A B C a1 ht hr hd, tabA_get A B C a2 ht hr hd, hin]
    simp only [cutF, Bool.or_eq_true, decide_eq_true_eq] at h
    simp only [Bool.not_true, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq]
    exact h
  · have hf : (decide (t < A) && decide (r < B) && decide (d < C)) = false := by
      simpa using hin
    rw [hf]
    simp

/-- The rule along a sequence, with the same code and a cut that allows more. -/
theorem ruleK_mono {k : ℕ} {code code' : ℕ → ℕ → ℕ → ℕ} {fN fS : ℕ → ℕ → ℕ → ℤ}
    {cut cut' : ℕ → ℕ → ℕ → ℤ → ℤ → Bool} (hc : ∀ t r d, code t r d = code' t r d)
    (hcut : ∀ t r d m M, cut t r d m M = true → cut' t r d m M = true) :
    ∀ (rest : List TRow) (t r d : ℕ) (m M : ℤ), RuleK k code fN fS cut t r d m M rest →
      RuleK k code' fN fS cut' t r d m M rest
  | [], t, r, d, m, M, h => by
    simp only [RuleK] at h ⊢
    rw [← hc]
    exact h
  | (kd, Q) :: rest, t, r, d, m, M, h => by
    simp only [RuleK] at h ⊢
    rw [← hc]
    exact ⟨h.1, h.2.1, hcut _ _ _ _ _ h.2.2.1, ruleK_mono hc hcut rest _ _ _ _ _ h.2.2.2⟩

/-! ### From a search to the rule -/

section Search

variable {k : ℕ} {caps : List (List ℕ)} {s lo hi a b h fuel ds nt : ℕ}

/-- The number of rows from which the code does not change. -/
def rowsR (caps : List (List ℕ)) (s hi : ℕ) : ℕ := maxLeN (capF caps s) hi + 1

theorem rowsR_spec (caps : List (List ℕ)) (s hi : ℕ) :
    ∀ x, x ≤ hi → capF caps s x < rowsR caps s hi :=
  fun _ hx => Nat.lt_succ_of_le (le_maxLeN hx)

/-- The compiled search, with its tables written out. -/
theorem seqSearch_eq (k : ℕ) (caps : List (List ℕ)) (s lo hi a b h fuel ds nt pa pb : ℕ) :
    seqSearch k caps s lo hi a b h fuel ds nt pa pb =
      par (fun tp => searchPart (fun i => (PS.ciTab k (PS.permCodes k k))[i]!)
        (fun i => (PS.nxtTab k (PS.permCodes k k))[i]!)
        (fun i => (PS.sdTab k 3 (PS.permCodes k k))[i]!)
        (fun i => (PS.sdTab k 4 (PS.permCodes k k))[i]!)
        ((PS.permCodes k k).idxOf (PS.idcF k)) (k - 1)
        (codeT (s + 1) (rowsR caps s hi) (hi + 1)
          (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (codeF (capF caps) s lo hi)))
        (maskT (s + 1) (rowsR caps s hi + 1) (hi + 1) (maskG (fun _ _ _ => 1) 0 0 0 (k - 1))
          (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (fun t r d =>
            maskG (codeT (s + 1) (rowsR caps s hi) (hi + 1)
              (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (codeF (capF caps) s lo hi)))
              t r d (k - 1))))
        (potN a b h) (potS a b h)
        (cutT (s + 1) (rowsR caps s hi + 1) (hi + 1)
          (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (a1F (capF caps) s lo hi a b h))
          (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1)
            (a2F (uF (capF caps) s a b h) (segF (capF caps) s a b h) (capF caps) s lo hi a b h)))
        (PS.permCodes k k).length fuel (fuel - ds) nt tp) pa pb := by
  simp only [seqSearch, look2_tab2, rowsR]

/-- **The compiled search proves that the rule holds along no sequence** (`4 ≤ k ≤ 15`).  The
parts may be evaluated in several ranges. -/
theorem kstmt_of_search (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      seqSearch k caps s lo hi a b h fuel ds nt pa pb = false) :
    KStmt k (codeF (capF caps) s lo hi) (potN a b h) (potS a b h)
      (cutF (a1F (capF caps) s lo hi a b h)
        (a2F (uF (capF caps) s a b h) (segF (capF caps) s a b h) (capF caps) s lo hi a b h)) := by
  have hcode := codeT_eq (lo := lo) (rowsR_spec caps s hi)
  have hstmt : KStmt k (codeT (s + 1) (rowsR caps s hi) (hi + 1)
      (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (codeF (capF caps) s lo hi)))
      (potN a b h) (potS a b h)
      (cutT (s + 1) (rowsR caps s hi + 1) (hi + 1)
        (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (a1F (capF caps) s lo hi a b h))
        (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1)
          (a2F (uF (capF caps) s a b h) (segF (capF caps) s a b h) (capF caps) s lo hi a b
            h))) := by
    refine kstmt_of_parts (PS.encB_enc k hk hk15) (by omega) hnt
      (mask := maskT (s + 1) (rowsR caps s hi + 1) (hi + 1) (maskG (fun _ _ _ => 1) 0 0 0 (k - 1))
        (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (fun t r d =>
          maskG (codeT (s + 1) (rowsR caps s hi) (hi + 1)
            (tabA (s + 1) (rowsR caps s hi + 1) (hi + 1) (codeF (capF caps) s lo hi)))
            t r d (k - 1))))
      (sz := (PS.permCodes k k).length) (fuel := fuel) (fg := fuel - ds) ?_ ?_
    · intro t r d j hj hne
      unfold maskT
      by_cases hin : (decide (t < s + 1) && decide (r < rowsR caps s hi + 1)
          && decide (d < hi + 1)) = true
      · rw [if_pos hin]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
        rw [tabA_get _ _ _ _ hin.1.1 hin.1.2 hin.2]
        exact maskG_bit _ t r d (k - 1) j hj (by
          rw [show k - 1 - 1 - j = k - 2 - j from by omega]
          exact hne)
      · rw [if_neg hin]
        exact maskG_bit (fun _ _ _ => 1) 0 0 0 (k - 1) j hj (by simp)
    · intro tp htp
      obtain ⟨pa, pb, h1, h2, hsr⟩ := hs tp htp
      rw [seqSearch_eq] at hsr
      exact par_false hsr tp h1 h2
  intro x rest hL hrule
  exact hstmt x rest hL (ruleK_mono (fun t r d => by rw [hcode])
    (fun t r d m M hc => cutT_of_cutF t r d m M hc) rest _ _ _ _ _ hrule)

/-- **The search with arithmetic tables proves that the rule holds along no sequence.** -/
theorem kstmt_of_searchA (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      seqSearchA k caps s lo hi a b h fuel ds nt pa pb = false) :
    KStmt k (codeF (capF caps) s lo hi) (potN a b h) (potS a b h)
      (cutF (a1F (capF caps) s lo hi a b h)
        (a2F (uF (capF caps) s a b h) (segF (capF caps) s a b h) (capF caps) s lo hi a b h)) :=
  kstmt_of_parts (PS.encA k hk hk15) (by omega) hnt
    (mask := fun t r d => maskG (codeF (capF caps) s lo hi) t r d (k - 1))
    (sz := k ^ (k - 1)) (fuel := fuel) (fg := fuel - ds)
    (fun t r d j hj hne => maskG_bit _ t r d (k - 1) j hj (by
      rw [show k - 1 - 1 - j = k - 2 - j from by omega]
      exact hne))
    (fun tp htp => by
      obtain ⟨pa, pb, h1, h2, hsr⟩ := hs tp htp
      exact par_false hsr tp h1 h2)

/-- **F(s; lo - 1, hi) from the compiled search.** -/
theorem seqCap_of_ksearch (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hlow : ∀ j, j < s → SeqCapLt k j (capF caps j) (hi + 1))
    (hprev : SeqCapLt k s (capF caps s) lo)
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      seqSearch k caps s lo hi a b h fuel ds nt pa pb = false) :
    SeqCapLt k s (capF caps s) (hi + 1) :=
  seqCap_levelK hk hlow hprev (kstmt_of_search hk hk15 hnt hs)

/-- **F(s; lo - 1, hi) from the search with arithmetic tables.** -/
theorem seqCap_of_ksearchA (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hlow : ∀ j, j < s → SeqCapLt k j (capF caps j) (hi + 1))
    (hprev : SeqCapLt k s (capF caps s) lo)
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      seqSearchA k caps s lo hi a b h fuel ds nt pa pb = false) :
    SeqCapLt k s (capF caps s) (hi + 1) :=
  seqCap_levelK hk hlow hprev (kstmt_of_searchA hk hk15 hnt hs)

end Search

end KS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.KS.seqCap_of_ksearch
#print axioms SuperpermLowerBounds.KS.seqCap_of_ksearchA
