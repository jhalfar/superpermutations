import LowerBounds.J16Rules

/-!
# A search of a run that finds nothing proves its statement on the class

`jw_of_partsV`: the proof of `J15Rules.jw_of_parts` on the normal form of `J16Norm.exists_nf`.
Along the normal form the engine's rule holds (`inner_minV` inside a piece, `along_minV` from the
end of a piece on), with the hooks of the runs: Rule PREV (`J16Rules.prev_cut`, `prev_end`), Rule
ORD (`ord_cut`, `ord_jump` below), the class of a ring, the ring targets with `T - H ≥ vlo` and the
clip of the need at 0.
-/

namespace SuperpermLowerBounds
namespace J16

open S (PermW WLink DoorEq)
open PS (TRow IsSeq holesT linksT Closes SeqCapLt LinkK relabSeq)
open KS (maxLe Good phiAt potN potS fK minLe)
open J15 (valK wtK lk IsPieceW IsPieceC Cyc Sh blocksR clsCount clsCount_perm clsCount_sublist
  firstB lastB lastB_eq lastB_snoc retag flatJ blocksR_flatJ blocksR_append valK_append wtK_append
  le_maxLe forall₂_app getD_mid drop_mid piece_prefix piece_suffix rowOk_of_split link_of_split
  closes_first_last valK_single_gt Gate Early FinOk RowOk Bud vOf k3Ok k4Ok negInf sval pval bestF
  bestStep tmax kdF loF hiF gprod gateD digs earlyD IsPieceW.isSeq IsPieceW.ne_nil IsPieceW.le_one)

variable {k : ℕ}

/-! ### The hooks -/

theorem xr_true (R : Rules) {kb np : ℕ} {kd : ℕ → ℕ} {Bf RBf sg : ℕ → ℕ → ℤ} {c i t r d : ℕ}
    {a : ℤ} {b : ℕ} {pm pM : ℤ}
    (hP : prevOn R kd i = true → prevOk sg (Bf i) kb R.pa R.pb R.ph c
      (potF R.pa R.pb R.ph 0 t r d) pm pM (kd i - 1 - t) (a - vOf kb t r d) (b - (d + kb * t)) = true)
    (hO : ordOn R np i = true →
      (if c = 0 then a ≤ 2 * (vOf kb t r d + RBf (kd i - 1 - t) (b - (d + kb * t))) + Bf (i + 1) b
      else a ≤ 2 * (vOf kb t r d - ((kb - 1 : ℕ) : ℤ) + RBf (kd i - 2 - t) (b - (d + kb * t) - kb)) +
        Bf (i + 1) b)) :
    xrF R kb np kd Bf RBf sg c i t r d a b pm pM = true := by
  unfold xrF
  rw [Bool.and_eq_true]
  constructor
  · by_cases h : prevOn R kd i = true
    · rw [hP h, Bool.or_true]
    · simp only [Bool.not_eq_true] at h
      rw [h]
      rfl
  · by_cases h : ordOn R np i = true
    · have h' := hO h
      by_cases hc : c = 0
      · rw [if_pos hc] at h' ⊢
        simp [h']
      · rw [if_neg hc] at h' ⊢
        simp [h']
    · simp only [Bool.not_eq_true] at h
      rw [h]
      rfl

theorem xc_true (R : Rules) {kb np : ℕ} {kd : ℕ → ℕ} {Bf : ℕ → ℕ → ℤ} {i t r d : ℕ}
    {a : ℤ} {b : ℕ} {pm pM : ℤ}
    (hC : kd i = 0 → vloF R i ≤ (r : ℤ) - d ∧ (r : ℤ) - d ≤ vhiF R i)
    (hP : prevOn R kd i = true → prevEnd (potF R.pa R.pb R.ph 0 t r d) pm pM = true)
    (hO : ordOn R np i = true → a ≤ 2 * vOf kb t r d + Bf (i + 1) (b - (d + kb * t))) :
    xcF R kb np kd Bf i t r d a b pm pM = true := by
  unfold xcF
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_cases h : kd i = 0
    · obtain ⟨h1, h2⟩ := hC h
      simp [h, h1, h2]
    · simp [h]
  · by_cases h : prevOn R kd i = true
    · rw [hP h, Bool.or_true]
    · simp only [Bool.not_eq_true] at h
      rw [h]
      rfl
  · by_cases h : ordOn R np i = true
    · simp [hO h]
    · simp only [Bool.not_eq_true] at h
      rw [h]
      rfl

theorem prevOn_spec {R : Rules} {kd : ℕ → ℕ} {i : ℕ} (h : prevOn R kd i = true) :
    i = R.rp ∧ kd i ≠ 0 := by
  unfold prevOn at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  exact h

theorem ordOn_spec {R : Rules} {np i : ℕ} (h : ordOn R np i = true) : i = R.oi ∧ i + 1 < np := by
  unfold ordOn at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h

/-! ### Positions in the list of kinds -/

theorem specs_at {qs qpre qpost : List Q} {q : Q} (h : qs = qpre ++ q :: qpost) :
    (qs.map Prod.fst).getD qpre.length (0, 0, 0) = q.1 ∧
      (qs.map Prod.fst).drop (qpre.length + 1) = qpost.map Prod.fst ∧ qs.getD qpre.length dq = q ∧
      qpre.length < qs.length := by
  subst h
  refine ⟨?_, ?_, getD_mid _ _ _ _, by simp⟩
  · rw [List.map_append, List.map_cons]
    have := getD_mid (qpre.map Prod.fst) q.1 (qpost.map Prod.fst) (0, 0, 0)
    rw [List.length_map] at this
    exact this
  · rw [List.map_append, List.map_cons]
    have := drop_mid (qpre.map Prod.fst) q.1 (qpost.map Prod.fst)
    rw [List.length_map] at this
    exact this

/-! ### The rule along the normal form -/

section Along

variable {qs : List Q} {V : ℤ} {W B sm : ℕ} {P : ℕ → ℕ → ℕ} {PR : ℕ → ℕ}
  {enc : List ℕ → ℕ} {kd lo hi : ℕ → ℕ} {bestLe : ℕ → ℕ → ℤ → Bool}
  {gLe : ℕ → ℕ → ℕ → ℤ → Bool} {fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool} {gi gr : ℕ} {R : Rules}

/-- The hypotheses of a run on its tables, its rules and its tests (see `jw_of_partsV`). -/
structure RunOK (k : ℕ) (qs : List Q) (W sm : ℕ) (P : ℕ → ℕ → ℕ) (PR : ℕ → ℕ)
    (kd lo hi : ℕ → ℕ) (bestLe : ℕ → ℕ → ℤ → Bool) (gLe : ℕ → ℕ → ℕ → ℤ → Bool)
    (fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool) (R : Rules) : Prop where
  hk : 4 ≤ k
  hc : CapsOKV k P PR W sm qs
  hsm : ∀ q ∈ qs, q.1.1 ≤ sm + 1
  hkd : ∀ i, i < qs.length → kd i = kdF (qs.map Prod.fst) i ∧ lo i = loF (qs.map Prod.fst) i ∧
    hi i = hiF (qs.map Prod.fst) i
  hR : ∀ i, i < qs.length → vloF R i = (qs.getD i dq).2.1 ∧ vhiF R i = (qs.getD i dq).2.2
  hpa : 0 < R.pa
  hab : R.pa ≤ R.pb
  hXL : 2 * R.ph ≤ (k - 1) * (R.pb - R.pa) + (k - 2) * R.pa
  hoi : R.oi + 1 < qs.length → (qs.getD R.oi dq).1.1 ≠ 0
  hclip : R.clip = true → ∀ q ∈ qs, q.1.1 = 0 → 0 ≤ q.2.1
  hbest : ∀ i y x, i < qs.length → y ≤ W →
    x ≤ bestF P PR (k - 1) ((qs.map Prod.fst).drop (i + 1)) y → bestLe i y x = true
  hg : ∀ i u y x, i < qs.length → y ≤ W → u < kd i →
    x ≤ bestF P PR (k - 1) ((u + 1, 0, 0) :: (qs.map Prod.fst).drop (i + 1)) y → gLe i u y x = true
  hf : ∀ i b r d x, i < qs.length → b ≤ W → kd i = 0 →
    x ≤ fG P PR (fun y => bestF P PR (k - 1) ((qs.map Prod.fst).drop (i + 1)) y) (lo i) (hi i)
      (vloF R i) b r d →
    (R.clip = true → 0 ≤ fG P PR (fun y => bestF P PR (k - 1) ((qs.map Prod.fst).drop (i + 1)) y)
      (lo i) (hi i) (vloF R i) b r d) →
    fLe i b r d x = true

/-- `Best` of the pieces after `i`. -/
def BfOf (k : ℕ) (P : ℕ → ℕ → ℕ) (PR : ℕ → ℕ) (qs : List Q) (i y : ℕ) : ℤ :=
  bestF P PR (k - 1) ((qs.map Prod.fst).drop (i + 1)) y

/-- The table bound of a rest of a sequence piece with at most `u` links, alone. -/
def RBfOf (k : ℕ) (P : ℕ → ℕ → ℕ) (PR : ℕ → ℕ) (u y : ℕ) : ℤ :=
  bestF P PR (k - 1) [(u + 1, 0, 0)] y

/-- The rule of a run along a list of rows. -/
abbrev JAlongR (k : ℕ) (qs : List Q) (P : ℕ → ℕ → ℕ) (PR : ℕ → ℕ) (enc : List ℕ → ℕ)
    (kd lo hi : ℕ → ℕ) (bestLe : ℕ → ℕ → ℤ → Bool) (gLe : ℕ → ℕ → ℕ → ℤ → Bool)
    (fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool) (R : Rules) (GP EP : ℕ → ℕ → ℕ → Prop) :=
  JAlong k qs.length enc kd lo hi bestLe gLe fLe
    (xrF R (k - 1) qs.length kd (BfOf k P PR qs) (RBfOf k P PR) (segF P (k - 1) R.pa R.pb R.ph))
    (xcF R (k - 1) qs.length kd (BfOf k P PR qs)) (fun c t r d => potF R.pa R.pb R.ph c t r d) GP EP

theorem RunOK.ringOK (H : RunOK k qs W sm P PR kd lo hi bestLe gLe fLe R) :
    ∀ q ∈ qs, RingOK k PR W q ∧ q.1.1 ≤ sm + 1 :=
  fun q hq => ⟨H.hc.ring q hq, H.hsm q hq⟩

/-- **Rule ORD at a cut**: the pieces `oi`, `oi + 1` are sorted. -/
theorem ord_cut (H : RunOK k qs W sm P PR kd lo hi bestLe gLe fLe R)
    {qpre : List Q} {Pre : List (List TRow)} {q q' : Q} {S S' : List TRow} {qpost' : List Q}
    {Post' : List (List TRow)}
    (M : MinAtV k qs V W B qpre Pre q S (q' :: qpost') (S' :: Post'))
    (hsorted : valK k S' ≤ valK k S) (h0 : q.1.1 ≠ 0)
    {u w : List TRow} {x : TRow} (hs : S = u ++ x :: w) (hu : u ≠ []) (hx : x.1 ≤ 1) :
    (if x.1 = 0 then
      V - (Pre.map (valK k)).sum ≤ 2 * (valK k u + RBfOf k P PR (q.1.1 - 1 - linksT u)
        (W - (Pre.map (wtK k)).sum - wtK k u)) +
        BfOf k P PR qs (qpre.length + 1) (W - (Pre.map (wtK k)).sum)
    else V - (Pre.map (valK k)).sum ≤ 2 * (valK k u - ((k - 1 - 1 : ℕ) : ℤ) +
        RBfOf k P PR (q.1.1 - 2 - linksT u) (W - (Pre.map (wtK k)).sum - wtK k u - (k - 1))) +
        BfOf k P PR qs (qpre.length + 1) (W - (Pre.map (wtK k)).sum)) := by
  have hsW := M.sumW
  have hsV := M.sumV
  simp only [List.map_cons, List.sum_cons] at hsW hsV
  have hpost := M.hPost
  have hp' := (List.forall₂_cons.mp hpost).2
  -- the pieces after `oi + 1`
  have hdrop : (qs.map Prod.fst).drop (qpre.length + 1 + 1) = qpost'.map Prod.fst := by
    rw [M.hspec, List.map_append, List.map_cons, List.map_cons]
    have := drop_mid (qpre.map Prod.fst ++ [q.1]) q'.1 (qpost'.map Prod.fst)
    simp only [List.length_append, List.length_map, List.length_singleton,
      List.append_assoc, List.singleton_append] at this
    exact this
  have hB2 : (Post'.map (valK k)).sum ≤
      BfOf k P PR qs (qpre.length + 1) (W - (Pre.map (wtK k)).sum) := by
    unfold BfOf
    rw [hdrop]
    exact best_boundV H.hc.seq qpost' Post' (hp'.imp fun _ _ h => h.1)
      (fun q0 hq0 => H.ringOK q0 (by rw [M.hspec]; simp [hq0])) _ (by omega) (by omega)
  have hw' : IsPieceW k q.1 (u ++ x :: w) := hs ▸ M.hS.1.1
  obtain ⟨hsuf, hlkS, _⟩ := piece_suffix hw' h0 hu
  have hvalS := valK_append (k := k) u x w hu
  have hwtS := wtK_append (k := k) u x w hu
  rw [← hs] at hvalS hwtS
  have hsm' := H.hsm q (by rw [M.hspec]; simp)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with hx0 | hx1
  · rw [if_pos hx0]
    have hlk0 : lk x = 0 := by unfold lk; simp [hx0]
    rw [hlk0] at hvalS hwtS hsuf hlkS
    have hwX : wtK k (x :: w) ≤ W - (Pre.map (wtK k)).sum - wtK k u := by
      simp only [Nat.mul_zero, Nat.add_zero] at hwtS
      omega
    have hX := best_boundV (P := P) (PR := PR) H.hc.seq
      [((q.1.1 - linksT u - 0, 0, 0), ((0 : ℤ), (0 : ℤ)))]
      [x :: w] (List.Forall₂.cons ⟨hsuf, fun h => absurd h (by simp; omega)⟩ List.Forall₂.nil)
      (fun q0 hq0 => by
        rw [List.mem_singleton] at hq0
        subst hq0
        exact ⟨fun h => absurd h (by simp; omega), by simp; omega⟩)
      (W - (Pre.map (wtK k)).sum - wtK k u) (by simpa using hwX) (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hX
    have e : q.1.1 - linksT u - 0 = q.1.1 - 1 - linksT u + 1 := by omega
    rw [e] at hX
    unfold RBfOf
    simp only [Nat.mul_zero, Nat.cast_zero, sub_zero] at hvalS
    linarith
  · rw [if_neg (by omega)]
    have hlk1 : lk x = 1 := by unfold lk; simp [hx1]
    rw [hlk1] at hvalS hwtS hsuf hlkS
    have hwX : wtK k (x :: w) ≤ W - (Pre.map (wtK k)).sum - wtK k u - (k - 1) := by
      simp only [Nat.mul_one] at hwtS
      omega
    have hX := best_boundV (P := P) (PR := PR) H.hc.seq
      [((q.1.1 - linksT u - 1, 0, 0), ((0 : ℤ), (0 : ℤ)))]
      [x :: w] (List.Forall₂.cons ⟨hsuf, fun h => absurd h (by simp; omega)⟩ List.Forall₂.nil)
      (fun q0 hq0 => by
        rw [List.mem_singleton] at hq0
        subst hq0
        exact ⟨fun h => absurd h (by simp; omega), by simp; omega⟩)
      (W - (Pre.map (wtK k)).sum - wtK k u - (k - 1)) (by simpa using hwX) (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hX
    have e : q.1.1 - linksT u - 1 = q.1.1 - 2 - linksT u + 1 := by omega
    rw [e] at hX
    unfold RBfOf
    simp only [Nat.mul_one] at hvalS
    linarith

/-- **Rule ORD at the end of piece `oi`.** -/
theorem ord_jump (H : RunOK k qs W sm P PR kd lo hi bestLe gLe fLe R)
    {qpre : List Q} {Pre : List (List TRow)} {q q' : Q} {S S' : List TRow} {qpost' : List Q}
    {Post' : List (List TRow)}
    (M : MinAtV k qs V W B qpre Pre q S (q' :: qpost') (S' :: Post'))
    (hsorted : valK k S' ≤ valK k S) :
    V - (Pre.map (valK k)).sum ≤ 2 * valK k S + BfOf k P PR qs (qpre.length + 1)
      (W - (Pre.map (wtK k)).sum - wtK k S) := by
  have hsW := M.sumW
  have hsV := M.sumV
  simp only [List.map_cons, List.sum_cons] at hsW hsV
  have hp' := (List.forall₂_cons.mp M.hPost).2
  have hdrop : (qs.map Prod.fst).drop (qpre.length + 1 + 1) = qpost'.map Prod.fst := by
    rw [M.hspec, List.map_append, List.map_cons, List.map_cons]
    have := drop_mid (qpre.map Prod.fst ++ [q.1]) q'.1 (qpost'.map Prod.fst)
    simp only [List.length_append, List.length_map, List.length_singleton,
      List.append_assoc, List.singleton_append] at this
    exact this
  have hB2 : (Post'.map (valK k)).sum ≤
      BfOf k P PR qs (qpre.length + 1) (W - (Pre.map (wtK k)).sum - wtK k S) := by
    unfold BfOf
    rw [hdrop]
    exact best_boundV H.hc.seq qpost' Post' (hp'.imp fun _ _ h => h.1)
      (fun q0 hq0 => H.ringOK q0 (by rw [M.hspec]; simp [hq0])) _ (by omega) (by omega)
  linarith

/-- The normal form gives Rule PREV at the piece `rp`. -/
theorem good_of_nf {qpre : List Q} {Pre : List (List TRow)} {q : Q} {S : List TRow}
    {qpost : List Q} {Post : List (List TRow)}
    (M : MinAtV k qs V W B qpre Pre q S qpost Post)
    (hnf : NF k qs R.rp R.pa R.pb R.ph R.oi (Pre ++ S :: Post))
    (hkdi : kd qpre.length = q.1.1) (h : prevOn R kd qpre.length = true) :
    Good k R.pa R.pb R.ph S := by
  obtain ⟨hi, hk0⟩ := prevOn_spec h
  obtain ⟨_, _, hq, hlt⟩ := specs_at M.hspec
  have := hnf.good (by rw [← hi]; exact hlt) (by rw [← hi, hq, ← hkdi]; exact hk0)
  rw [← hi, ← M.len, getD_mid] at this
  exact this

/-- The normal form gives Rule ORD at the piece `oi`. -/
theorem sorted_of_nf {qpre : List Q} {Pre : List (List TRow)} {q : Q} {S : List TRow}
    {qpost : List Q} {Post : List (List TRow)}
    (M : MinAtV k qs V W B qpre Pre q S qpost Post)
    (hnf : NF k qs R.rp R.pa R.pb R.ph R.oi (Pre ++ S :: Post))
    (h : ordOn R qs.length qpre.length = true) :
    ∃ q' qpost' S' Post', qpost = q' :: qpost' ∧ Post = S' :: Post' ∧ valK k S' ≤ valK k S := by
  obtain ⟨hi, hlt⟩ := ordOn_spec h
  have hlen := M.hPost.length_eq
  have hsp := M.hspec
  obtain ⟨q', qpost', rfl⟩ : ∃ q' qpost', qpost = q' :: qpost' := by
    cases qpost with
    | nil => rw [hsp] at hlt; simp at hlt
    | cons q' qpost' => exact ⟨q', qpost', rfl⟩
  obtain ⟨S', Post', rfl⟩ : ∃ S' Post', Post = S' :: Post' := by
    cases Post with
    | nil => simp at hlen
    | cons S' Post' => exact ⟨S', Post', rfl⟩
  refine ⟨q', qpost', S', Post', rfl, rfl, ?_⟩
  have := hnf.ord (by rw [← hi]; exact hlt)
  rw [← hi, ← M.len, getD_mid, getD_mid2] at this
  exact this

set_option maxHeartbeats 4000000 in
/-- The rule holds along the rest of a piece of the normal form, if it holds from the end of the
piece on. -/
theorem inner_minV (H : RunOK k qs W sm P PR kd lo hi bestLe gLe fLe R)
    {qpre : List Q} {Pre : List (List TRow)} {q : Q} {S : List TRow}
    {qpost : List Q} {Post : List (List TRow)}
    (M : MinAtV k qs V W B qpre Pre q S qpost Post)
    (hnf : NF k qs R.rp R.pa R.pb R.ph R.oi (Pre ++ S :: Post))
    (hend : ∀ m pm pM : ℤ, (q.1.1 ≠ 0 → m < valK k S) → PotI k R.pa R.pb R.ph S pm pM →
      JAlongR k qs P PR enc kd lo hi bestLe gLe fLe R (Gate gi gr 1 0) (Early gi gr 1 0)
        qpre.length (linksT S) S.length (holesT k S) (V - (Pre.map (valK k)).sum)
        (W - (Pre.map (wtK k)).sum) m pm pM (firstB S) (lastB S) (blocksR S) (flatJ Post)) :
    ∀ (rest u : List TRow) (m pm pM : ℤ), S = u ++ rest → u ≠ [] → (q.1.1 ≠ 0 → m < valK k S) →
      PotI k R.pa R.pb R.ph u pm pM →
      JAlongR k qs P PR enc kd lo hi bestLe gLe fLe R (Gate gi gr 1 0) (Early gi gr 1 0)
        qpre.length (linksT u) u.length (holesT k u) (V - (Pre.map (valK k)).sum)
        (W - (Pre.map (wtK k)).sum) m pm pM (firstB S) (lastB u) (blocksR u)
        (rest ++ flatJ Post) := by
  have hk := H.hk
  obtain ⟨hsp1, hdrop, hqget, hi_lt⟩ := specs_at M.hspec
  obtain ⟨hkdi, hloi, hhii⟩ := H.hkd _ hi_lt
  have hkd' : kd qpre.length = q.1.1 := by rw [hkdi]; unfold kdF; rw [hsp1]
  have hlo' : lo qpre.length = q.1.2.1 := by rw [hloi]; unfold loF; rw [hsp1]
  have hhi' : hi qpre.length = q.1.2.2 := by rw [hhii]; unfold hiF; rw [hsp1]
  have hvlo : vloF R qpre.length = q.2.1 := by rw [(H.hR _ hi_lt).1, hqget]
  have hseqS := M.hS.1.1.isSeq
  have hsW := M.sumW
  have hsV := M.sumV
  have hqpost : ∀ q0 ∈ qpost, RingOK k PR W q0 ∧ q0.1.1 ≤ sm + 1 :=
    fun q0 hq0 => H.ringOK q0 (by rw [M.hspec]; simp [hq0])
  have hsmq : q.1.1 ≤ sm + 1 := H.hsm q (by rw [M.hspec]; simp)
  have hpostV : List.Forall₂ (IsPieceV k) qpost Post := M.hPost.imp fun _ _ h => h.1
  intro rest
  induction rest with
  | nil =>
    intro u m pm pM hs hu hm hpi
    rw [List.append_nil] at hs
    subst hs
    rw [List.nil_append]
    exact hend m pm pM hm hpi
  | cons x w ih =>
    intro u m pm pM hs hu hm hpi
    obtain ⟨kdx, Q0⟩ := x
    have hSs : IsSeq k (u ++ (kdx, Q0) :: w) := hs ▸ hseqS
    have hQ : Q0 ≠ [] := hSs.pieces_ne (kdx, Q0) (by simp)
    obtain ⟨v, R0, rfl⟩ := List.exists_cons_of_ne_nil hQ
    obtain ⟨hrow, hnew⟩ := rowOk_of_split (by omega) hSs
    have hlink := link_of_split hSs hu
    have hk1x : kdx ≤ 1 := M.hS.1.1.le_one (kdx, v :: R0) (by rw [hs]; simp)
    -- the prefix with the row added
    have e1 : (u ++ [(kdx, v :: R0)]).length = u.length + 1 := by simp
    have hh1 : holesT k [(kdx, v :: R0)] = k - 2 - R0.length := by
      simp [holesT]
      omega
    have e2 : holesT k (u ++ [(kdx, v :: R0)]) = holesT k u + (k - 2 - R0.length) := by
      rw [PS.holesT_append, hh1]
    have e3 : blocksR (u ++ [(kdx, v :: R0)]) = blocksR u ++ v :: R0 := by
      rw [blocksR_append]
      simp [blocksR]
    have e4 := lastB_snoc u kdx v R0
    have e5 : linksT (u ++ [(kdx, v :: R0)]) = linksT u + lk (kdx, v :: R0) := by
      have h := PS.linksT_append u (kdx, v :: R0) [] hu
      have h0 : linksT [(kdx, v :: R0)] = 0 := rfl
      rw [h, h0]
      rfl
    have hs' : S = (u ++ [(kdx, v :: R0)]) ++ w := by
      rw [hs]
      simp
    have hIH := ih (u ++ [(kdx, v :: R0)]) (max m (valK k u))
      (min pm (potF R.pa R.pb R.ph kdx (linksT u) u.length (holesT k u)))
      (max pM (potF R.pa R.pb R.ph kdx (linksT u) u.length (holesT k u))) hs' (by simp)
      (fun h0 => max_lt (hm h0) (M.rec_lt h0 hs hu)) (potI_snoc hpi hu (kdx, v :: R0) hk1x)
    rw [e1, e2, e3, e4, e5] at hIH
    -- the cut
    have hlenS : S.length = u.length + (w.length + 1) := by
      rw [hs]
      simp
    have hholx : holesT k ((kdx, v :: R0) :: w) = (k - 2 - R0.length) + holesT k w := by
      have h := PS.holesT_append (k := k) [(kdx, v :: R0)] w
      rw [hh1] at h
      exact h
    have hholS : holesT k S = holesT k u + holesT k ((kdx, v :: R0) :: w) := by
      rw [hs, PS.holesT_append]
    have hwtS := wtK_append (k := k) u (kdx, v :: R0) w hu
    rw [← hs] at hwtS
    have hvalS := valK_append (k := k) u (kdx, v :: R0) w hu
    rw [← hs] at hvalS
    have hwx : k - 2 - R0.length ≤ wtK k ((kdx, v :: R0) :: w) := by
      unfold wtK
      omega
    have hgate : Gate gi gr 1 0 qpre.length u.length (enc (lastB u) + 8192 * holesT k u) :=
      Or.inr (Or.inr (Nat.mod_one _))
    rw [List.cons_append]
    by_cases h0 : q.1.1 = 0
    · -- a ring
      have hc0 : (q.1.1 == 0) = true := by simp [h0]
      have hw' := M.hS.1.1
      unfold IsPieceW at hw'
      rw [if_pos h0] at hw'
      obtain ⟨_, hk0, h2len, hcl, hlo, hhi⟩ := hw'
      have hcyc := M.hS.2 h0 u ((kdx, v :: R0) :: w) hs
      have hkx : kdx = 0 := hk0 (kdx, v :: R0) (by rw [hs]; simp)
      subst hkx
      have hlu : linksT u = 0 :=
        PS.linksT_zero fun y hy => hk0 y (by rw [hs]; exact List.mem_append_left _ hy)
      have hk0w : ∀ y ∈ ((0 : ℕ), v :: R0) :: w, y.1 = 0 :=
        fun y hy => hk0 y (by rw [hs]; exact List.mem_append_right _ hy)
      have hwtSe : wtK k S = holesT k S := ring_wt hk0
      have hvS : valK k S = (S.length : ℤ) - (holesT k S : ℤ) := ring_val hk0
      have hH : holesT k S ≤ W - (Pre.map (wtK k)).sum := by omega
      have hT1 : S.length ≤ PR (holesT k S) :=
        H.hc.ring q (by rw [M.hspec]; simp) h0 S M.hS.1 (by omega)
      have hrestseq : IsSeq k (((0 : ℕ), v :: R0) :: w) :=
        hSs.infix (List.suffix_append u _).isInfix
      have hT2 : w.length + 1 ≤ P 0 (holesT k (((0 : ℕ), v :: R0) :: w)) := by
        have h := H.hc.seq 0 (Nat.zero_le _) (((0 : ℕ), v :: R0) :: w) hrestseq
          (fun y hy => by rw [hk0w y hy]; omega) (PS.linksT_zero hk0w)
          (by rw [Nat.mul_zero, Nat.sub_zero]; omega)
        simpa using h
      have hT : S.length ≤ tmax P PR u.length (holesT k u) (holesT k S) := by
        have hd : holesT k S - holesT k u = holesT k (((0 : ℕ), v :: R0) :: w) := by omega
        unfold tmax
        rw [hd]
        by_cases hd0 : holesT k u = 0
        · rw [if_pos hd0]
          exact le_min hT1 (by omega)
        · rw [if_neg hd0]
          refine le_min (le_min hT1 (by omega)) ?_
          rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
          exact hcyc
      have hp := best_boundV H.hc.seq qpost Post hpostV hqpost
        (W - (Pre.map (wtK k)).sum - holesT k S) (by omega) (by omega)
      have hT' : (S.length : ℤ) ≤ ((tmax P PR u.length (holesT k u) (holesT k S) : ℕ) : ℤ) := by
        exact_mod_cast hT
      have hcls := (M.hS.1.2 h0).1
      rw [hvS] at hcls
      -- the ring's own target
      have hown : ((tmax P PR u.length (holesT k u) (holesT k S) : ℕ) : ℤ) - (holesT k S : ℤ) +
            bestF P PR (k - 1) (qpost.map Prod.fst) (W - (Pre.map (wtK k)).sum - holesT k S) ≤
          fG P PR (fun y => bestF P PR (k - 1) ((qs.map Prod.fst).drop (qpre.length + 1)) y)
            (lo qpre.length) (hi qpre.length) (vloF R qpre.length)
            (W - (Pre.map (wtK k)).sum) u.length (holesT k u) := by
        rw [hdrop, hlo', hhi', hvlo]
        unfold fG
        refine le_trans ?_ (le_maxLe _ _ (holesT k S) hH)
        show _ ≤ if q.1.2.1 ≤ holesT k S ∧ holesT k S ≤ q.1.2.2 ∧ holesT k u ≤ holesT k S ∧
            u.length + 1 ≤ tmax P PR u.length (holesT k u) (holesT k S) ∧
            q.2.1 ≤ ((tmax P PR u.length (holesT k u) (holesT k S) : ℕ) : ℤ) - (holesT k S : ℤ) then
          ((tmax P PR u.length (holesT k u) (holesT k S) : ℕ) : ℤ) - (holesT k S : ℤ) +
            bestF P PR (k - 1) (qpost.map Prod.fst) (W - (Pre.map (wtK k)).sum - holesT k S)
          else negInf
        rw [if_pos ⟨hlo, hhi, by omega, by omega, by linarith⟩]
      have hfle : fLe qpre.length (W - (Pre.map (wtK k)).sum) u.length (holesT k u)
          (V - (Pre.map (valK k)).sum) = true := by
        apply H.hf _ _ _ _ _ hi_lt (Nat.sub_le _ _) (by rw [hkd']; exact h0)
        · linarith
        · intro hcl'
          have hv0 := H.hclip hcl' q (by rw [M.hspec]; simp) h0
          have hb0 := best_nonneg (P := P) (PR := PR) qpost Post hpostV
            (fun q0 hq0 => ⟨(hqpost q0 hq0).1,
              H.hclip hcl' q0 (by rw [M.hspec]; simp [hq0])⟩)
            (W - (Pre.map (wtK k)).sum - holesT k S) (by omega) (by omega)
          linarith
      unfold JAlongR; rw [JAlong]
      refine ⟨hgate, hrow, ?_, ?_, hlink.1 rfl, hnew, ?_, ?_⟩
      · unfold k3Ok
        rw [hkd', if_pos hc0]
        exact hfle
      · apply xr_true
        · intro hP
          exact absurd h0 (by rw [← hkd']; exact (prevOn_spec hP).2)
        · intro hO
          have hn := H.hoi (by rw [← (ordOn_spec hO).1]; exact (ordOn_spec hO).2)
          rw [← (ordOn_spec hO).1, hqget] at hn
          exact absurd h0 hn
      · rw [hlu]
        omega
      · have e6 : lk ((0 : ℕ), v :: R0) = 0 := rfl
        rw [e6, Nat.add_zero] at hIH
        exact hIH
    · -- a sequence
      have hc0 : ¬ (q.1.1 == 0) = true := by simp [h0]
      have hw' : IsPieceW k q.1 (u ++ (kdx, v :: R0) :: w) := hs ▸ M.hS.1.1
      have hk1 := hw'.le_one (kdx, v :: R0) (by simp)
      obtain ⟨hsuf, hlkS, _⟩ := piece_suffix hw' h0 hu
      have hrest := M.rest_lt h0 hs hu
      have hb := best_boundV H.hc.seq
        (((q.1.1 - linksT u - lk (kdx, v :: R0), 0, 0), ((0 : ℤ), (0 : ℤ))) :: qpost)
        (((kdx, v :: R0) :: w) :: Post)
        (List.Forall₂.cons ⟨hsuf, fun h => absurd h (by simp; omega)⟩ hpostV)
        (by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact ⟨fun h => absurd h (by simp; omega), by simp; omega⟩
          · exact hqpost p hp')
        (W - (Pre.map (wtK k)).sum - wtK k u - (k - 1) * lk (kdx, v :: R0))
        (by simp only [List.map_cons, List.sum_cons]; omega) (by omega)
      simp only [List.map_cons, List.sum_cons] at hb
      -- Rule PREV at this cut
      have hprev : prevOn R kd qpre.length = true →
          prevOk (segF P (k - 1) R.pa R.pb R.ph) (BfOf k P PR qs qpre.length) (k - 1) R.pa R.pb
            R.ph kdx (potF R.pa R.pb R.ph 0 (linksT u) u.length (holesT k u)) pm pM
            (kd qpre.length - 1 - linksT u) (V - (Pre.map (valK k)).sum - valK k u)
            (W - (Pre.map (wtK k)).sum - wtK k u) = true := by
        intro hP
        have hgood := good_of_nf M hnf hkd' hP
        have hpost := best_boundV H.hc.seq qpost Post hpostV hqpost
          (W - (Pre.map (wtK k)).sum - wtK k u - (k - 1) * lk (kdx, v :: R0) -
            wtK k ((kdx, v :: R0) :: w)) (by omega) (by omega)
        have hlkS' : linksT S + 1 ≤ q.1.1 := by
          have hw2 := M.hS.1.1
          unfold IsPieceW at hw2
          rw [if_neg h0] at hw2
          exact hw2.2.2.2
        rw [hkd']
        refine prev_cut (by omega) H.hc.seq H.hpa H.hab H.hXL (BfOf k P PR qs qpre.length) hs hu
          hseqS M.hS.1.1.le_one hlkS' hsmq hgood hpi (by omega) (by omega) ?_
        unfold BfOf
        rw [hdrop]
        have e7 : k - 2 = k - 1 - 1 := by omega
        rw [e7]
        push_cast at hvalS ⊢
        linarith
      rcases (show kdx = 0 ∨ kdx = 1 by omega) with rfl | rfl
      · -- a link of weight 3
        have e6 : lk ((0 : ℕ), v :: R0) = 0 := rfl
        rw [e6] at hb hwtS hvalS hlkS hIH
        simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.cast_zero, sub_zero] at hb hwtS hvalS hlkS hIH
        have hv1 : 1 ≤ valK k u := by linarith
        unfold JAlongR; rw [JAlong]
        refine ⟨hgate, hrow, ?_, ?_, hlink.1 rfl, hnew, ?_, hIH⟩
        · unfold k3Ok
          rw [hkd', if_neg hc0, Bool.and_eq_true]
          refine ⟨decide_eq_true hv1, ?_⟩
          apply H.hg _ _ _ _ hi_lt (Nat.sub_le_of_le_add (by omega)) (by rw [hkd']; omega)
          rw [hdrop]
          have e7 : q.1.1 - 1 - linksT u + 1 = q.1.1 - linksT u := by omega
          rw [e7]
          show V - (Pre.map (valK k)).sum - valK k u ≤ bestF P PR (k - 1)
            ((q.1.1 - linksT u, 0, 0) :: qpost.map Prod.fst) (W - (Pre.map (wtK k)).sum - wtK k u)
          linarith
        · apply xr_true
          · exact hprev
          · intro hO
            obtain ⟨q', qpost', S', Post', hq1, hq2, hsorted⟩ := sorted_of_nf M hnf hO
            subst hq1 hq2
            have := ord_cut H M hsorted h0 hs hu (show (((0 : ℕ), v :: R0) : TRow).1 ≤ 1 by simp)
            rw [if_pos rfl] at this
            rw [if_pos rfl, hkd']
            exact this
        · show wtK k u + (k - 2 - R0.length) ≤ W - (Pre.map (wtK k)).sum
          omega
      · -- a link of weight 4
        have e6 : lk ((1 : ℕ), v :: R0) = 1 := rfl
        rw [e6] at hb hwtS hvalS hlkS hIH
        simp only [Nat.mul_one] at hb hwtS hvalS
        have e8 : ((k - 1 - 1 : ℕ) : ℤ) + 1 = ((k - 1 : ℕ) : ℤ) := by
          have : k - 1 - 1 + 1 = k - 1 := by omega
          exact_mod_cast this
        unfold JAlongR; rw [JAlong]
        refine ⟨hgate, hrow, ?_, ?_, hlink.2 rfl, hnew, ?_, hIH⟩
        · unfold k4Ok
          rw [hkd']
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨⟨by omega, ?_⟩, ?_⟩, ?_⟩
          · show ((k - 1 : ℕ) : ℤ) ≤ valK k u
            linarith
          · show k - 1 ≤ W - (Pre.map (wtK k)).sum - wtK k u
            omega
          · apply H.hg _ _ _ _ hi_lt
              (Nat.sub_le_of_le_add (Nat.sub_le_of_le_add (by omega))) (by rw [hkd']; omega)
            rw [hdrop]
            have e7 : q.1.1 - 2 - linksT u + 1 = q.1.1 - linksT u - 1 := by omega
            rw [e7]
            show V - (Pre.map (valK k)).sum - valK k u + ((k - 1 - 1 : ℕ) : ℤ) ≤
              bestF P PR (k - 1) ((q.1.1 - linksT u - 1, 0, 0) :: qpost.map Prod.fst)
                (W - (Pre.map (wtK k)).sum - wtK k u - (k - 1))
            linarith
        · apply xr_true
          · exact hprev
          · intro hO
            obtain ⟨q', qpost', S', Post', hq1, hq2, hsorted⟩ := sorted_of_nf M hnf hO
            subst hq1 hq2
            have := ord_cut H M hsorted h0 hs hu (show (((1 : ℕ), v :: R0) : TRow).1 ≤ 1 by simp)
            rw [if_neg (by simp)] at this
            rw [if_neg (by simp), hkd']
            exact this
        · show wtK k u + (k - 1) + (k - 2 - R0.length) ≤ W - (Pre.map (wtK k)).sum
          omega

set_option maxHeartbeats 4000000 in
/-- The rule holds from the end of a piece of the normal form on. -/
theorem along_minV (H : RunOK k qs W sm P PR kd lo hi bestLe gLe fLe R) :
    ∀ (Post : List (List TRow)) (qpost qpre : List Q) (Pre : List (List TRow)) (q : Q)
      (S : List TRow), MinAtV k qs V W B qpre Pre q S qpost Post →
      NF k qs R.rp R.pa R.pb R.ph R.oi (Pre ++ S :: Post) →
      ∀ m pm pM : ℤ, (q.1.1 ≠ 0 → m < valK k S) → PotI k R.pa R.pb R.ph S pm pM →
      JAlongR k qs P PR enc kd lo hi bestLe gLe fLe R (Gate gi gr 1 0) (Early gi gr 1 0)
        qpre.length (linksT S) S.length (holesT k S) (V - (Pre.map (valK k)).sum)
        (W - (Pre.map (wtK k)).sum) m pm pM (firstB S) (lastB S) (blocksR S) (flatJ Post) := by
  have hk := H.hk
  intro Post
  induction Post with
  | nil =>
    intro qpost qpre Pre q S M hnf m pm pM hm hpi
    have hsp0 : qpost = [] := by
      have := M.hPost
      cases this
      rfl
    subst hsp0
    obtain ⟨hsp1, _, hqget, hi_lt⟩ := specs_at M.hspec
    obtain ⟨hkdi, hloi, hhii⟩ := H.hkd _ hi_lt
    have hkd' : kd qpre.length = q.1.1 := by rw [hkdi]; unfold kdF; rw [hsp1]
    have hsV := M.sumV
    simp only [List.map_nil, List.sum_nil, add_zero] at hsV
    have hnp : qpre.length + 1 = qs.length := by rw [M.hspec]; simp
    have hfl : flatJ ([] : List (List TRow)) = [] := rfl
    rw [hfl]
    unfold JAlongR
    rw [JAlong]
    refine ⟨Or.inr (Or.inr (Nat.mod_one _)),
      J15.finOk_piece M.hS.toC hkd' (by rw [hloi]; unfold loF; rw [hsp1])
        (by rw [hhii]; unfold hiF; rw [hsp1]) hm, hnp, ?_, ?_⟩
    · show V - (Pre.map (valK k)).sum ≤ valK k S
      linarith
    · apply xc_true
      · intro h0
        rw [hkd'] at h0
        have hw := M.hS.1.1
        unfold IsPieceW at hw
        rw [if_pos h0] at hw
        have hcl := M.hS.1.2 h0
        rw [ring_val hw.2.1] at hcl
        rw [(H.hR _ hi_lt).1, (H.hR _ hi_lt).2, hqget]
        exact hcl
      · intro hP
        exact prev_end M.hS.1.1.ne_nil (good_of_nf M hnf hkd' hP) hpi
      · intro hO
        have := (ordOn_spec hO).2
        omega
  | cons S' Post' ih =>
    intro qpost qpre Pre q S M hnf m pm pM hm hpi
    obtain ⟨q', qpost', rfl⟩ : ∃ q' qpost', qpost = q' :: qpost' := by
      have := M.hPost
      cases this
      exact ⟨_, _, rfl⟩
    obtain ⟨hsp1, hdrop, hqget, hi_lt⟩ := specs_at M.hspec
    obtain ⟨hkdi, hloi, hhii⟩ := H.hkd _ hi_lt
    have hkd' : kd qpre.length = q.1.1 := by rw [hkdi]; unfold kdF; rw [hsp1]
    have hsW := M.sumW
    have hsV := M.sumV
    have M' := M.next
    have hnf' : NF k qs R.rp R.pa R.pb R.ph R.oi ((Pre ++ [S]) ++ S' :: Post') := by
      have e : (Pre ++ [S]) ++ S' :: Post' = Pre ++ S :: S' :: Post' := by simp
      rw [e]
      exact hnf
    have hS' := M'.hS
    obtain ⟨x0, S'', rfl⟩ := List.exists_cons_of_ne_nil hS'.1.1.ne_nil
    obtain ⟨kd0, Q0⟩ := x0
    have hseq' := hS'.1.1.isSeq
    have hQ0 : Q0 ≠ [] := hseq'.pieces_ne (kd0, Q0) List.mem_cons_self
    obtain ⟨v, R0, rfl⟩ := List.exists_cons_of_ne_nil hQ0
    obtain ⟨hrow, _⟩ := rowOk_of_split (by omega) (u := []) hseq'
    have hend' := ih qpost' (qpre ++ [q]) (Pre ++ [S]) q' ((kd0, v :: R0) :: S'') M' hnf'
    have hm0 : q'.1.1 ≠ 0 → -((k - 1 : ℕ) : ℤ) < valK k ((kd0, v :: R0) :: S'') := by
      intro h0
      have h1 := valK_single_gt (k := k) (kd := kd0) (v := v) (by omega) hrow.1
      cases S'' with
      | nil => exact h1
      | cons y w'' =>
        have h2 := M'.rec_lt h0 (u := [(kd0, v :: R0)]) (x := y) (w := w'') rfl (by simp)
        linarith
    have hinner := inner_minV H M' hnf' hend' S'' [(kd0, v :: R0)]
      (-((k - 1 : ℕ) : ℤ)) 0 0 rfl (by simp) hm0 (potI_one R.pa R.pb R.ph _)
    have f1 : (qpre ++ [q]).length = qpre.length + 1 := by simp
    have f2 : linksT [(kd0, v :: R0)] = 0 := rfl
    have f3 : [(kd0, v :: R0)].length = 1 := rfl
    have f4 : holesT k [(kd0, v :: R0)] = k - 2 - R0.length := by
      simp [holesT]
      omega
    have f5 : V - ((Pre ++ [S]).map (valK k)).sum
        = V - (Pre.map (valK k)).sum - valK k S := by
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      ring
    have f6 : W - ((Pre ++ [S]).map (wtK k)).sum
        = W - (Pre.map (wtK k)).sum - wtK k S := by
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega
    have f7 : firstB ((kd0, v :: R0) :: S'') = v := rfl
    have f8 := lastB_snoc [] kd0 v R0
    have f9 : blocksR [(kd0, v :: R0)] = v :: R0 := by simp [blocksR]
    rw [List.nil_append] at f8
    rw [f1, f2, f3, f4, f5, f6, f7, f8, f9] at hinner
    have hholx : holesT k ((kd0, v :: R0) :: S'') = (k - 2 - R0.length) + holesT k S'' := by
      have h := PS.holesT_append (k := k) [(kd0, v :: R0)] S''
      rw [f4] at h
      exact h
    simp only [List.map_cons, List.sum_cons] at hsW hsV
    have hp := best_boundV H.hc.seq (q' :: qpost') (((kd0, v :: R0) :: S'') :: Post')
      (M.hPost.imp fun _ _ h => h.1) (fun p hp => H.ringOK p (by rw [M.hspec]; simp [hp]))
      (W - (Pre.map (wtK k)).sum - wtK k S)
      (by simp only [List.map_cons, List.sum_cons]; omega) (by omega)
    simp only [List.map_cons, List.sum_cons] at hp
    show JAlongR k qs P PR enc kd lo hi bestLe gLe fLe R (Gate gi gr 1 0) (Early gi gr 1 0)
        qpre.length (linksT S) S.length (holesT k S) (V - (Pre.map (valK k)).sum)
        (W - (Pre.map (wtK k)).sum) m pm pM (firstB S) (lastB S) (blocksR S)
        ((2, v :: R0) :: (S'' ++ flatJ Post'))
    unfold JAlongR
    rw [JAlong]
    refine ⟨Or.inr (Or.inr (Nat.mod_one _)), hrow,
      J15.finOk_piece M.hS.toC hkd' (by rw [hloi]; unfold loF; rw [hsp1])
        (by rw [hhii]; unfold hiF; rw [hsp1]) hm, ?_, ?_, ?_, Or.inr (Or.inr (Nat.mod_one _)), ?_,
      hinner⟩
    · rw [M.hspec]
      simp only [List.length_append, List.length_cons]
      omega
    · apply H.hbest _ _ _ hi_lt (Nat.sub_le_of_le_add (by omega))
      rw [hdrop]
      show V - (Pre.map (valK k)).sum - valK k S ≤ bestF P PR (k - 1) ((q' :: qpost').map Prod.fst)
        (W - (Pre.map (wtK k)).sum - wtK k S)
      simp only [List.map_cons]
      linarith
    · apply xc_true
      · intro h0
        rw [hkd'] at h0
        have hw := M.hS.1.1
        unfold IsPieceW at hw
        rw [if_pos h0] at hw
        have hcl := M.hS.1.2 h0
        rw [ring_val hw.2.1] at hcl
        rw [(H.hR _ hi_lt).1, (H.hR _ hi_lt).2, hqget]
        exact hcl
      · intro hP
        exact prev_end M.hS.1.1.ne_nil (good_of_nf M hnf hkd' hP) hpi
      · intro hO
        obtain ⟨q2, qpost2, S2, Post2, hq1, hq2, hsorted⟩ := sorted_of_nf M hnf hO
        have e1 := (List.cons.inj hq1)
        have e2 := (List.cons.inj hq2)
        obtain ⟨rfl, rfl⟩ := e1
        obtain ⟨rfl, rfl⟩ := e2
        exact ord_jump H M hsorted
    · show k - 2 - R0.length ≤ W - (Pre.map (wtK k)).sum - wtK k S
      have : k - 2 - R0.length ≤ wtK k ((kd0, v :: R0) :: S'') := by
        unfold wtK
        omega
      omega

/-- **A run that finds nothing proves its statement on the class.** -/
theorem jw_of_partsV {ci nxt : ℕ → ℕ} {s3 s4 : ℕ → List ℕ} {jl : List ℕ} {st sz fuel : ℕ}
    {gs : List (ℕ × ℕ × ℕ)} (E : PS.Enc k enc ci nxt s3 s4 jl st)
    (H : RunOK k qs W sm P PR kd lo hi bestLe gLe fLe R) (hne : qs ≠ [])
    (hnp : qs.length ≤ 255) (hgs : ∀ g ∈ gs, 0 < g.2.2)
    (hoi : R.oi + 1 < qs.length → qs.getD R.oi dq = qs.getD (R.oi + 1) dq)
    (hs : ∀ tp, tp < gprod gs →
      searchPart ci nxt s3 s4 jl st (k - 1) qs.length B kd lo hi bestLe gLe fLe
        (xrF R (k - 1) qs.length kd (BfOf k P PR qs) (RBfOf k P PR) (segF P (k - 1) R.pa R.pb R.ph))
        (xcF R (k - 1) qs.length kd (BfOf k P PR qs)) (fun c t r d => potF R.pa R.pb R.ph c t r d)
        V W sz fuel (gateD (digs gs tp)) (earlyD (digs gs tp)) = false) :
    JV k qs V W B := by
  have hk := H.hk
  by_contra hfail
  obtain ⟨Ls, hce, hmin, hnf, kd0, R1, S1, Post1, rfl⟩ :=
    exists_nf hk R.rp R.pa R.pb R.ph R.oi hne hoi hfail
  obtain ⟨q0, qpost, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hfa := List.forall₂_cons.mp hce.1
  have M : MinAtV k (q0 :: qpost) V W B [] [] q0 ((kd0, List.range' 1 k :: R1) :: S1) qpost
      Post1 :=
    ⟨rfl, List.Forall₂.nil, hfa.1, hfa.2, hce.2.1, hce.2.2.1, hce.2.2.2, hmin⟩
  have hnf' : NF k (q0 :: qpost) R.rp R.pa R.pb R.ph R.oi
      ([] ++ ((kd0, List.range' 1 k :: R1) :: S1) :: Post1) := by
    rw [List.nil_append]
    exact hnf
  have hseq := M.hS.1.1.isSeq
  obtain ⟨⟨hR1, hperm, hdoor, hpw⟩, _⟩ := rowOk_of_split (by omega) (u := []) hseq
  have hend := along_minV (enc := enc) (gi := 0) (gr := 0) H Post1 qpost [] [] q0 _ M hnf'
  have hm0 : q0.1.1 ≠ 0 →
      -((k - 1 : ℕ) : ℤ) < valK k ((kd0, List.range' 1 k :: R1) :: S1) := by
    intro h0
    have h1 := valK_single_gt (k := k) (kd := kd0) (v := List.range' 1 k) (by omega) hR1
    cases S1 with
    | nil => exact h1
    | cons y w'' =>
      have h2 := M.rec_lt h0 (u := [(kd0, List.range' 1 k :: R1)]) (x := y) (w := w'') rfl
        (by simp)
      linarith
  have hinner := inner_minV (enc := enc) (gi := 0) (gr := 0) H M hnf' hend S1
    [(kd0, List.range' 1 k :: R1)] (-((k - 1 : ℕ) : ℤ)) 0 0 rfl (by simp) hm0
    (potI_one R.pa R.pb R.ph _)
  have f2 : linksT [(kd0, List.range' 1 k :: R1)] = 0 := rfl
  have f3 : [(kd0, List.range' 1 k :: R1)].length = 1 := rfl
  have f4 : holesT k [(kd0, List.range' 1 k :: R1)] = k - 2 - R1.length := by
    simp [holesT]
    omega
  have f7 : firstB ((kd0, List.range' 1 k :: R1) :: S1) = List.range' 1 k := rfl
  have f8 := lastB_snoc [] kd0 (List.range' 1 k) R1
  have f9 : blocksR [(kd0, List.range' 1 k :: R1)] = List.range' 1 k :: R1 := by simp [blocksR]
  rw [List.nil_append] at f8
  rw [f2, f3, f4, f7, f8, f9] at hinner
  simp only [List.map_nil, List.sum_nil, sub_zero, Nat.sub_zero, List.length_nil] at hinner
  have hsW := M.sumW
  have hholx : holesT k ((kd0, List.range' 1 k :: R1) :: S1)
      = (k - 2 - R1.length) + holesT k S1 := by
    have h := PS.holesT_append (k := k) [(kd0, List.range' 1 k :: R1)] S1
    rw [f4] at h
    exact h
  refine not_along_of_parts (gi := 0) (gr := 0) E (by omega) hnp (PS.permW_range' k) hgs hs R1
    (S1 ++ flatJ Post1) hR1 hperm hdoor hpw ?_ ?_ hinner
  · have : k - 2 - R1.length ≤ wtK k ((kd0, List.range' 1 k :: R1) :: S1) := by
      unfold wtK
      omega
    simp only [List.map_nil, List.sum_nil] at hsW
    omega
  · have e : (List.range' 1 k :: R1) ++ blocksR (S1 ++ flatJ Post1)
        = blocksR ((((kd0, List.range' 1 k :: R1) :: S1) :: Post1).flatten) := by
      rw [blocksR_append, blocksR_flatJ]
      show _ = blocksR (((kd0, List.range' 1 k :: R1) :: S1) ++ Post1.flatten)
      rw [blocksR_append, J15.blocksR_cons, List.append_assoc]
    have c0 : clsCount [] = 0 := by simp [clsCount]
    have hsh := hce.2.1
    unfold Sh at hsh
    unfold Bud
    rw [e, c0, List.nil_append]
    omega

end Along

end J16
end SuperpermLowerBounds
