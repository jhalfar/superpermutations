import LowerBounds.J16Sound
import LowerBounds.J16Norm

/-!
# The rules of the runs hold along the normal form (the written proof, sections 4.2 to 4.6)

`CapsOKV`: the tables of a run.  The rows of sequences are valid within the weight of the run
(as in 5,900); the ring row needs to bound only the rings of the class of the run (a ring of a
kind `q` with its holes in the window and its value in the range of `q`).  This is what lets the
lower halves of the split VS read a ring row that is not valid for all rings (section 4.6, the
lemma that the ring row enters the search only as a bound on a whole ring piece: here the ring
row enters the proof only through `piece_leV` and the target of a ring prefix, both for a whole
ring piece of the class).

`jw_of_partsV`: if every part of the search answers `false`, `JV` holds.  The proof is that of
`J15Rules.jw_of_parts` on the normal form of `J16Norm.exists_nf`, with the hooks:

* Rule PREV (`prev_cut`, `prev_end`): the extremes of the potential along the prefix (`PotI`),
  Lemma PREV (`Good`), the table bound of a part of the rest (`SEG`) and the bound of the rest by
  the later pieces (`CN1`, `A2P`);
* Rule ORD (`ord_cut`, `ord_jump`): the pieces `oi`, `oi + 1` are sorted by value;
* the class of a ring at its end; the targets with `T - H ≥ vlo` (the ring's own target is
  one); the clip of the need at 0 (`best_nonneg`: the later pieces of a counterexample whose
  rings have value at least 0 leave a table value at least 0).
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

/-! ### Tables -/

/-- The ring row bounds the rings of the kind `q` (if `q` is a ring kind). -/
def RingOK (k : ℕ) (PR : ℕ → ℕ) (W : ℕ) (q : Q) : Prop :=
  q.1.1 = 0 → ∀ L, IsPieceV k q L → holesT k L ≤ W → L.length ≤ PR (holesT k L)

/-- The tables of a run: `P t` for sequences with `t ≤ sm` links within weight `W`, `PR` for the
rings of the class. -/
structure CapsOKV (k : ℕ) (P : ℕ → ℕ → ℕ) (PR : ℕ → ℕ) (W sm : ℕ) (qs : List Q) : Prop where
  seq : ∀ t, t ≤ sm → SeqCapLt k t (P t) (W + 1 - (k - 1) * t)
  ring : ∀ q ∈ qs, RingOK k PR W q

section Bound

variable {P : ℕ → ℕ → ℕ} {PR : ℕ → ℕ} {W sm : ℕ} {qs : List Q}

theorem ring_val {L : List TRow} (hk0 : ∀ x ∈ L, x.1 = 0) :
    valK k L = (L.length : ℤ) - (holesT k L : ℤ) := by
  unfold valK vOf
  rw [PS.linksT_zero hk0]
  simp

theorem ring_wt {L : List TRow} (hk0 : ∀ x ∈ L, x.1 = 0) : wtK k L = holesT k L := by
  unfold wtK
  rw [PS.linksT_zero hk0]
  simp

/-- A single piece has at most its table value. -/
theorem piece_leV (hseq : ∀ t, t ≤ sm → SeqCapLt k t (P t) (W + 1 - (k - 1) * t)) (q : Q)
    (L : List TRow) (h : IsPieceV k q L) (hr : RingOK k PR W q) (hp : q.1.1 ≤ sm + 1)
    (hw : wtK k L ≤ W) : valK k L ≤ pval P PR (k - 1) q.1 (wtK k L) := by
  have h' := h.1
  unfold IsPieceW at h'
  by_cases h0 : q.1.1 = 0
  · rw [if_pos h0] at h'
    obtain ⟨hL, hk0, h2, hcl, hlo, hhi⟩ := h'
    have hw' := ring_wt (k := k) hk0
    have hcap := hr h0 L h (by rw [← hw']; exact hw)
    unfold pval
    rw [if_pos h0, hw', if_pos ⟨hlo, hhi⟩, ring_val hk0]
    have hcap' : (L.length : ℤ) ≤ (PR (holesT k L) : ℕ) := by exact_mod_cast hcap
    linarith
  · rw [if_neg h0] at h'
    obtain ⟨hL, _, hk1, hlk⟩ := h'
    have e1 : (k - 1) * linksT L ≤ wtK k L := by
      unfold wtK
      omega
    have e2 : wtK k L - (k - 1) * linksT L = holesT k L := by
      unfold wtK
      omega
    have hcap := hseq (linksT L) (by omega) L hL hk1 rfl (by unfold wtK at hw; omega)
    have hcap' : (L.length : ℤ) ≤ (P (linksT L) (holesT k L) : ℕ) := by exact_mod_cast hcap
    unfold pval
    rw [if_neg h0]
    refine le_trans ?_ (le_maxLe _ (q.1.1 - 1) (linksT L) (by omega))
    show valK k L ≤ if (k - 1) * linksT L ≤ wtK k L then
      sval P (k - 1) (linksT L) (wtK k L - (k - 1) * linksT L) else negInf
    rw [if_pos e1, e2]
    unfold valK vOf sval
    linarith

/-- **Table bound** for pieces of the class. -/
theorem best_boundV (hseq : ∀ t, t ≤ sm → SeqCapLt k t (P t) (W + 1 - (k - 1) * t)) :
    ∀ (qps : List Q) (Ps : List (List TRow)), List.Forall₂ (IsPieceV k) qps Ps →
    (∀ q ∈ qps, RingOK k PR W q ∧ q.1.1 ≤ sm + 1) →
    ∀ y, (Ps.map (wtK k)).sum ≤ y → y ≤ W →
      (Ps.map (valK k)).sum ≤ bestF P PR (k - 1) (qps.map Prod.fst) y := by
  intro qps Ps h
  induction h with
  | nil =>
    intro _ y _ _
    exact le_refl _
  | @cons q L qps' Ps' hpl _ ih =>
    intro hq y hy hyW
    simp only [List.map_cons, List.sum_cons] at hy ⊢
    have hq0 := hq q List.mem_cons_self
    have h1 := piece_leV hseq q L hpl hq0.1 hq0.2 (by omega)
    have h2 := ih (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq')) (y - wtK k L) (by omega)
      (by omega)
    show _ ≤ maxLe (fun w => pval P PR (k - 1) q.1 w + bestF P PR (k - 1) (qps'.map Prod.fst) (y - w)) y
    exact le_trans (add_le_add h1 h2) (le_maxLe _ y (wtK k L) (by omega))

/-- **The clip at 0** (section 4.2): pieces of the class whose rings have value at least 0 fit
into a weight whose table value is at least 0. -/
theorem best_nonneg :
    ∀ (qps : List Q) (Ps : List (List TRow)), List.Forall₂ (IsPieceV k) qps Ps →
    (∀ q ∈ qps, RingOK k PR W q ∧ (q.1.1 = 0 → 0 ≤ q.2.1)) →
    ∀ y, (Ps.map (wtK k)).sum ≤ y → y ≤ W → 0 ≤ bestF P PR (k - 1) (qps.map Prod.fst) y := by
  intro qps Ps h
  induction h with
  | nil =>
    intro _ y _ _
    exact le_refl _
  | @cons q L qps' Ps' hpl _ ih =>
    intro hq y hy hyW
    simp only [List.map_cons, List.sum_cons] at hy
    show 0 ≤ maxLe (fun w => pval P PR (k - 1) q.1 w + bestF P PR (k - 1) (qps'.map Prod.fst) (y - w)) y
    have h' := hpl.1
    unfold IsPieceW at h'
    by_cases h0 : q.1.1 = 0
    · rw [if_pos h0] at h'
      obtain ⟨hL, hk0, h2, hcl, hlo, hhi⟩ := h'
      have hw' := ring_wt (k := k) hk0
      have ih' := ih (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq')) (y - holesT k L)
        (by omega) (by omega)
      have hcap := (hq q List.mem_cons_self).1 h0 L hpl (by omega)
      have hv := (hpl.2 h0).1
      have hv0 := (hq q List.mem_cons_self).2 h0
      rw [ring_val hk0] at hv
      refine le_trans ?_ (le_maxLe _ y (holesT k L) (by omega))
      have hpv : pval P PR (k - 1) q.1 (holesT k L) = ((PR (holesT k L) : ℕ) : ℤ) - (holesT k L : ℤ) := by
        unfold pval
        rw [if_pos h0, if_pos ⟨hlo, hhi⟩]
      show 0 ≤ pval P PR (k - 1) q.1 (holesT k L) + bestF P PR (k - 1) (qps'.map Prod.fst) (y - holesT k L)
      rw [hpv]
      have hcap' : (L.length : ℤ) ≤ (PR (holesT k L) : ℕ) := by exact_mod_cast hcap
      linarith
    · rw [if_neg h0] at h'
      have ih' := ih (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq')) y (by omega) hyW
      refine le_trans ?_ (le_maxLe _ y 0 (Nat.zero_le _))
      have hp0 : sval P (k - 1) 0 0 ≤ pval P PR (k - 1) q.1 0 := by
        unfold pval
        rw [if_neg h0]
        refine le_trans ?_ (le_maxLe _ (q.1.1 - 1) 0 (Nat.zero_le _))
        show sval P (k - 1) 0 0 ≤ if (k - 1) * 0 ≤ 0 then sval P (k - 1) 0 (0 - (k - 1) * 0) else negInf
        simp
      have hs0 : (0 : ℤ) ≤ sval P (k - 1) 0 0 := by
        unfold sval
        simp
      rw [Nat.sub_zero]
      linarith

end Bound

/-! ### The piece of a counterexample with the fewest rows -/

/-- The piece `S` of a counterexample in the class with the fewest rows. -/
structure MinAtV (k : ℕ) (qs : List Q) (V : ℤ) (W B : ℕ)
    (qpre : List Q) (Pre : List (List TRow)) (q : Q) (S : List TRow)
    (qpost : List Q) (Post : List (List TRow)) : Prop where
  hspec : qs = qpre ++ q :: qpost
  hPre : List.Forall₂ (IsPieceCV k) qpre Pre
  hS : IsPieceCV k q S
  hPost : List.Forall₂ (IsPieceCV k) qpost Post
  hSh : Sh B (Pre ++ S :: Post)
  hW : ((Pre ++ S :: Post).map (wtK k)).sum ≤ W
  hV : V ≤ ((Pre ++ S :: Post).map (valK k)).sum
  hmin : ∀ Ls', CEV k qs V W B Ls' → (Pre ++ S :: Post).flatten.length ≤ Ls'.flatten.length

section Min

variable {qs : List Q} {V : ℤ} {W B : ℕ} {qpre : List Q} {Pre : List (List TRow)} {q : Q}
  {S : List TRow} {qpost : List Q} {Post : List (List TRow)}

theorem MinAtV.sumW (M : MinAtV k qs V W B qpre Pre q S qpost Post) :
    (Pre.map (wtK k)).sum + wtK k S + (Post.map (wtK k)).sum ≤ W := by
  have := M.hW
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at this
  omega

theorem MinAtV.sumV (M : MinAtV k qs V W B qpre Pre q S qpost Post) :
    V ≤ (Pre.map (valK k)).sum + valK k S + (Post.map (valK k)).sum := by
  have := M.hV
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at this
  linarith

theorem MinAtV.len (M : MinAtV k qs V W B qpre Pre q S qpost Post) : Pre.length = qpre.length :=
  M.hPre.length_eq.symm

theorem MinAtV.next {q' : Q} {S' : List TRow} {qpost' : List Q} {Post' : List (List TRow)}
    (M : MinAtV k qs V W B qpre Pre q S (q' :: qpost') (S' :: Post')) :
    MinAtV k qs V W B (qpre ++ [q]) (Pre ++ [S]) q' S' qpost' Post' := by
  have e : (Pre ++ [S]) ++ S' :: Post' = Pre ++ S :: S' :: Post' := by simp
  have hp := List.forall₂_cons.mp M.hPost
  refine ⟨by rw [M.hspec]; simp, forall₂_app M.hPre (List.Forall₂.cons M.hS List.Forall₂.nil),
    hp.1, hp.2, ?_, ?_, ?_, ?_⟩
  · rw [e]
    exact M.hSh
  · rw [e]
    exact M.hW
  · rw [e]
    exact M.hV
  · rw [e]
    exact M.hmin

/-- A sequence piece that replaces `S` does not have fewer rows. -/
theorem MinAtV.rep (M : MinAtV k qs V W B qpre Pre q S qpost Post) (h0 : q.1.1 ≠ 0)
    (S' : List TRow) (h1 : IsPieceW k q.1 S') (h2 : (blocksR S').Sublist (blocksR S))
    (h3 : wtK k S' ≤ wtK k S) (h4 : valK k S ≤ valK k S') : S.length ≤ S'.length := by
  have hce : CEV k qs V W B (Pre ++ S' :: Post) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [M.hspec]
      exact forall₂_app M.hPre (List.Forall₂.cons
        ⟨⟨h1, fun h' => absurd h' h0⟩, fun h' => absurd h' h0⟩ M.hPost)
    · have hs := M.hSh
      unfold Sh at hs ⊢
      simp only [List.flatten_append, List.flatten_cons, blocksR_append] at hs ⊢
      have hsub : (blocksR Pre.flatten ++ (blocksR S' ++ blocksR Post.flatten)).Sublist
          (blocksR Pre.flatten ++ (blocksR S ++ blocksR Post.flatten)) :=
        (List.Sublist.refl _).append (h2.append (List.Sublist.refl _))
      have := clsCount_sublist hsub
      omega
    · have := M.sumW
      simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      omega
    · have := M.sumV
      simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      linarith
  have := M.hmin _ hce
  simp only [List.flatten_append, List.flatten_cons, List.length_append] at this
  omega

theorem MinAtV.rec_lt (M : MinAtV k qs V W B qpre Pre q S qpost Post) (h0 : q.1.1 ≠ 0)
    {u : List TRow} {x : TRow} {w : List TRow} (hs : S = u ++ x :: w) (hu : u ≠ []) :
    valK k u < valK k S := by
  by_contra hcon
  have hw := M.hS.1.1
  rw [hs] at hw
  have h1 := piece_prefix hw h0 hu
  have h2 := M.rep h0 u h1
    (by rw [hs, blocksR_append]; exact List.sublist_append_left _ _)
    (by rw [hs, wtK_append u x w hu]; omega) (not_lt.mp hcon)
  rw [hs, List.length_append, List.length_cons] at h2
  omega

theorem MinAtV.rest_lt (M : MinAtV k qs V W B qpre Pre q S qpost Post) (h0 : q.1.1 ≠ 0)
    {u : List TRow} {x : TRow} {w : List TRow} (hs : S = u ++ x :: w) (hu : u ≠ []) :
    valK k (x :: w) < valK k S := by
  by_contra hcon
  have hw := M.hS.1.1
  rw [hs] at hw
  have h1 := (piece_suffix hw h0 hu).2.2
  have h2 := M.rep h0 (x :: w) h1
    (by rw [hs, blocksR_append]; exact List.sublist_append_right _ _)
    (by rw [hs, wtK_append u x w hu]; omega) (not_lt.mp hcon)
  have hpos := List.length_pos_of_ne_nil hu
  rw [hs, List.length_append] at h2
  omega

end Min

/-! ### The potential along a prefix -/

/-- `pm`, `pM` are the least and the largest potential of the cuts of the prefix `u` (the cut
behind the last row of `u` excluded), and both are taken. -/
def PotI (k pa pb ph : ℕ) (u : List TRow) (pm pM : ℤ) : Prop :=
  (∀ A B, u = A ++ B → B ≠ [] → pm ≤ phiAt k pa pb ph A B ∧ phiAt k pa pb ph A B ≤ pM) ∧
    (∃ A B, u = A ++ B ∧ B ≠ [] ∧ phiAt k pa pb ph A B = pm) ∧
    (∃ A B, u = A ++ B ∧ B ≠ [] ∧ phiAt k pa pb ph A B = pM)

theorem potI_one (pa pb ph : ℕ) (x : TRow) : PotI k pa pb ph [x] 0 0 := by
  have hsplit : ∀ A B : List TRow, [x] = A ++ B → B ≠ [] → A = [] := by
    intro A B h hB
    cases A with
    | nil => rfl
    | cons y A' =>
      have := congrArg List.length h
      simp only [List.length_cons, List.length_nil, List.length_append] at this
      have : B.length = 0 := by omega
      exact absurd (List.length_eq_zero_iff.mp this) hB
  refine ⟨fun A B h hB => ?_, ⟨[], [x], rfl, by simp, KS.phiAt_nil _ _ _ _⟩,
    ⟨[], [x], rfl, by simp, KS.phiAt_nil _ _ _ _⟩⟩
  rw [hsplit A B h hB, KS.phiAt_nil]
  exact ⟨le_refl _, le_refl _⟩

theorem potF_eq (pa pb ph c t r d : ℕ) (hc : c ≤ 1) :
    potF pa pb ph c t r d = fK (potN pa pb ph) (potS pa pb ph) c t r d := by
  rw [KS.fK_eq _ _ _ _ _ _ _ hc]
  unfold potF
  ring

theorem phiAt_snoc (pa pb ph : ℕ) {u : List TRow} (hu : u ≠ []) (x : TRow) (hx : x.1 ≤ 1)
    (w : List TRow) :
    phiAt k pa pb ph u (x :: w) = potF pa pb ph x.1 (linksT u) u.length (holesT k u) := by
  rw [KS.phiAt_cons pa pb ph hu x w, potF_eq _ _ _ _ _ _ _ hx]

/-- The prefix grows by a row. -/
theorem potI_snoc {pa pb ph : ℕ} {u : List TRow} {pm pM : ℤ} (h : PotI k pa pb ph u pm pM)
    (hu : u ≠ []) (x : TRow) (hx : x.1 ≤ 1) :
    PotI k pa pb ph (u ++ [x]) (min pm (potF pa pb ph x.1 (linksT u) u.length (holesT k u)))
      (max pM (potF pa pb ph x.1 (linksT u) u.length (holesT k u))) := by
  obtain ⟨h1, ⟨A0, B0, e0, hB0, hp0⟩, ⟨A1, B1, e1, hB1, hp1⟩⟩ := h
  have hf := phiAt_snoc (k := k) pa pb ph hu x hx []
  -- the cuts of `u ++ [x]`
  have hcuts : ∀ A B, u ++ [x] = A ++ B → B ≠ [] →
      (A = u ∧ B = [x]) ∨ (∃ B', u = A ++ B' ∧ B' ≠ [] ∧ B = B' ++ [x]) := by
    intro A B hAB hB
    obtain ⟨B', y, rfl⟩ : ∃ B' y, B = B' ++ [y] :=
      ⟨B.dropLast, B.getLast hB, (List.dropLast_append_getLast hB).symm⟩
    rw [← List.append_assoc] at hAB
    obtain ⟨e1, e2⟩ := List.append_inj' hAB rfl
    have hy : x = y := by simpa using e2
    subst hy
    by_cases hB' : B' = []
    · subst hB'
      left
      exact ⟨by simpa using e1.symm, rfl⟩
    · right
      exact ⟨B', e1, hB', rfl⟩
  refine ⟨fun A B hAB hB => ?_, ?_, ?_⟩
  · rcases hcuts A B hAB hB with ⟨rfl, rfl⟩ | ⟨B', e, hB', rfl⟩
    · rw [hf]
      exact ⟨min_le_right _ _, le_max_right _ _⟩
    · rw [KS.phiAt_append pa pb ph A hB' [x]]
      have := h1 A B' e hB'
      exact ⟨le_trans (min_le_left _ _) this.1, le_trans this.2 (le_max_left _ _)⟩
  · by_cases hm : pm ≤ potF pa pb ph x.1 (linksT u) u.length (holesT k u)
    · refine ⟨A0, B0 ++ [x], by rw [e0, List.append_assoc], by simp, ?_⟩
      rw [KS.phiAt_append pa pb ph A0 hB0 [x], hp0, min_eq_left hm]
    · refine ⟨u, [x], rfl, by simp, ?_⟩
      rw [hf, min_eq_right (le_of_lt (not_le.mp hm))]
  · by_cases hm : potF pa pb ph x.1 (linksT u) u.length (holesT k u) ≤ pM
    · refine ⟨A1, B1 ++ [x], by rw [e1, List.append_assoc], by simp, ?_⟩
      rw [KS.phiAt_append pa pb ph A1 hB1 [x], hp1, max_eq_left hm]
    · refine ⟨u, [x], rfl, by simp, ?_⟩
      rw [hf, max_eq_right (le_of_lt (not_le.mp hm))]

/-- A cut of `u ++ X` either lies in `u` (at its end included) or behind a non-empty part `Y`
of `X`. -/
theorem cut_cases {u X A1 B1 : List TRow} (h : u ++ X = A1 ++ B1) :
    (∃ a', u = A1 ++ a' ∧ B1 = a' ++ X) ∨ (∃ Y, Y ≠ [] ∧ A1 = u ++ Y ∧ X = Y ++ B1) := by
  rcases List.append_eq_append_iff.mp h.symm with ⟨a', e1, e2⟩ | ⟨c', e1, e2⟩
  · exact Or.inl ⟨a', e1, e2⟩
  · by_cases hc : c' = []
    · subst hc
      left
      exact ⟨[], by simpa using e1.symm, by simpa using e2.symm⟩
    · exact Or.inr ⟨c', hc, e1, e2⟩

/-- The potential at a cut inside the piece behind `u`: at most the potential of `u` plus the
term of the part `Y` (the link terms at the ends are at most 0). -/
theorem phi_part_le (pa pb ph : ℕ) {u Y B1 : List TRow} (hu : u ≠ []) (hY : Y ≠ []) :
    phiAt k pa pb ph (u ++ Y) B1 ≤
      potF pa pb ph 0 (linksT u) u.length (holesT k u) + (pa : ℤ) * Y.length -
        (pb : ℤ) * holesT k Y - 2 * (ph : ℤ) * (lk (Y.head hY) + linksT Y) := by
  have hne : u ++ Y ≠ [] := by simp [hu]
  unfold phiAt
  rw [if_neg hne]
  refine le_trans (KS.fK_le _ _ _ _ _ _ _) ?_
  obtain ⟨y, Y', rfl⟩ := List.exists_cons_of_ne_nil hY
  rw [KS.potN_eq, PS.linksT_append u y Y' hu, List.length_append, PS.holesT_append]
  unfold potF lk
  simp only [List.head_cons]
  push_cast
  ring_nf
  exact le_refl _

/-! ### Rule PREV -/

section Prev

variable {P : ℕ → ℕ → ℕ} {W sm : ℕ}

theorem minUp_le (f : ℕ → ℤ) {n w : ℕ} (hw : w ≤ n) : minUp f n ≤ f w :=
  KS.minLe_le (p := fun _ => true) hw rfl

theorem seg_le (P : ℕ → ℕ → ℕ) (c6 pa pb ph : ℕ) {tl w u e : ℕ} (hu : u ≤ tl) (he : e + c6 * u ≤ w) :
    (pa : ℤ) * (P u e : ℕ) - (pb : ℤ) * e - 2 * (ph : ℤ) * u ≤ segF P c6 pa pb ph tl w := by
  unfold segF
  refine le_trans ?_ (le_maxLe _ tl u hu)
  refine le_trans ?_ (le_maxLe _ w e (by omega))
  show _ ≤ if e + c6 * u ≤ w then (pa : ℤ) * (P u e : ℕ) - (pb : ℤ) * e - 2 * (ph : ℤ) * u
    else negInf
  rw [if_pos he]

set_option maxHeartbeats 2000000 in
/-- **Rules (L) and (H) of PREV.**  At a cut behind the prefix `u` of a sequence piece
`S = u ++ x :: w` with `delta ≥ 0`, the continuation is kept. -/
theorem prev_cut (hk : 3 ≤ k) (hseq : ∀ t, t ≤ sm → SeqCapLt k t (P t) (W + 1 - (k - 1) * t))
    {pa pb ph : ℕ} (hpa : 0 < pa) (hab : pa ≤ pb)
    (hXL : 2 * ph ≤ (k - 1) * (pb - pa) + (k - 2) * pa)
    {S u w : List TRow} {x : TRow} {pm pM : ℤ} {c : ℕ} {need : ℤ} {om : ℕ} (nx : ℕ → ℤ)
    (hs : S = u ++ x :: w) (hu : u ≠ []) (hS : IsSeq k S) (hk1 : ∀ y ∈ S, y.1 ≤ 1)
    (hlk : linksT S + 1 ≤ c) (hcsm : c ≤ sm + 1)
    (hgood : Good k pa pb ph S) (hpi : PotI k pa pb ph u pm pM)
    (hom : wtK k (x :: w) + (k - 1) * lk x ≤ om) (homW : om ≤ W)
    (hX : need + ((k - 2) * lk x : ℕ) - nx (om - (k - 1) * lk x - wtK k (x :: w)) ≤
      valK k (x :: w)) :
    prevOk (segF P (k - 1) pa pb ph) nx (k - 1) pa pb ph x.1
      (potF pa pb ph 0 (linksT u) u.length (holesT k u)) pm pM (c - 1 - linksT u) need om
      = true := by
  set f := potF pa pb ph 0 (linksT u) u.length (holesT k u) with hfdef
  have hx1 : x.1 ≤ 1 := hk1 x (by rw [hs]; simp)
  have hlkx : lk x = x.1 := by
    unfold lk
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx1 with h | h <;> simp [h]
  set fc := phiAt k pa pb ph u (x :: w) with hfc
  have hfc' : fc = f - (ph : ℤ) * x.1 := by
    rw [hfc, phiAt_snoc pa pb ph hu x hx1 w, hfdef]
    unfold potF
    ring
  set mj := min pm fc with hmj
  set Mj := max pM fc with hMj
  -- the total potential
  set Phi := phiAt k pa pb ph S [] with hPhi
  have hSne : S ≠ [] := by rw [hs]; simp
  have hlinks := PS.linksT_append u x w hu
  have hPhi' : Phi = f + (pa : ℤ) * (x :: w).length - (pb : ℤ) * holesT k (x :: w) -
      2 * (ph : ℤ) * (lk x + linksT (x :: w)) := by
    rw [hPhi, KS.phiAt_end pa pb ph hSne, KS.potN_eq, hs, hlinks, List.length_append,
      PS.holesT_append, hfdef]
    unfold potF lk
    push_cast
    ring
  -- the cut where the least potential of the cuts up to `u` is taken
  obtain ⟨A0, B0, e0, hm0⟩ : ∃ A0 B0, S = A0 ++ B0 ∧ phiAt k pa pb ph A0 B0 = mj := by
    by_cases hm : pm ≤ fc
    · obtain ⟨A, B, eAB, hB, hpA⟩ := hpi.2.1
      refine ⟨A, B ++ x :: w, by rw [hs, eAB, List.append_assoc], ?_⟩
      rw [KS.phiAt_append pa pb ph A hB, hpA, hmj, min_eq_left hm]
    · refine ⟨u, x :: w, hs, ?_⟩
      rw [hmj, min_eq_right (le_of_lt (not_le.mp hm))]
  obtain ⟨A1, B1, e1, hle⟩ := hgood A0 B0 e0
  rw [hm0] at hle
  -- the rest of the piece
  have hXseq : IsSeq k (x :: w) := hS.infix (by rw [hs]; exact (List.suffix_append u _).isInfix)
  have hlkX : linksT (x :: w) ≤ c - 1 - linksT u - lk x := by
    rw [hs, hlinks] at hlk
    unfold lk
    omega
  -- the value of the rest against the potential
  have hval : valK k (x :: w) = ((x :: w).length : ℤ) - (holesT k (x :: w) : ℤ) -
      (((k - 2) * linksT (x :: w) : ℕ) : ℤ) := by
    unfold valK vOf
    have : k - 1 - 1 = k - 2 := by omega
    rw [this]
  have hwX : wtK k (x :: w) = holesT k (x :: w) + (k - 1) * linksT (x :: w) := rfl
  have hPf : (pa : ℤ) * (need + ((k - 2) * lk x : ℕ) - nx (om - (k - 1) * lk x - wtK k (x :: w))) -
      ((pb : ℤ) - pa) * (wtK k (x :: w) : ℤ) - 2 * (ph : ℤ) * lk x ≤ Phi - f := by
    rw [hPhi']
    have h1 : (pa : ℤ) * (need + ((k - 2) * lk x : ℕ) - nx (om - (k - 1) * lk x - wtK k (x :: w)))
        ≤ (pa : ℤ) * valK k (x :: w) := mul_le_mul_of_nonneg_left hX (by positivity)
    have hXL' : (2 * ph : ℤ) ≤ ((k - 1 : ℕ) : ℤ) * ((pb : ℤ) - pa) + ((k - 2 : ℕ) : ℤ) * pa := by
      have : ((pb - pa : ℕ) : ℤ) = (pb : ℤ) - pa := by push_cast [Nat.cast_sub hab]; ring
      rw [← this]
      exact_mod_cast hXL
    rw [hval] at h1
    rw [hwX] at h1 ⊢
    have hlx : (0 : ℤ) ≤ (linksT (x :: w) : ℤ) := by positivity
    have e2 : (((k - 2) * linksT (x :: w) : ℕ) : ℤ) = ((k - 2 : ℕ) : ℤ) * linksT (x :: w) := by
      push_cast; ring
    have e3 : ((holesT k (x :: w) + (k - 1) * linksT (x :: w) : ℕ) : ℤ) =
        (holesT k (x :: w) : ℤ) + ((k - 1 : ℕ) : ℤ) * linksT (x :: w) := by push_cast; ring
    rw [e2] at h1
    rw [e3]
    have hm := mul_le_mul_of_nonneg_right hXL' hlx
    linarith
  -- the two cases of Lemma PREV
  have hcase : Phi ≤ mj + Mj ∨ Phi ≤ mj + f - 2 * (ph : ℤ) * lk x +
      segF P (k - 1) pa pb ph (c - 1 - linksT u - lk x) (wtK k (x :: w)) := by
    rcases cut_cases (u := u) (X := x :: w) (A1 := A1) (B1 := B1) (by rw [← hs]; exact e1) with ⟨a', ea, eb⟩ | ⟨Y, hY, eA, eX⟩
    · left
      have : phiAt k pa pb ph A1 B1 ≤ Mj := by
        by_cases ha : a' = []
        · subst ha
          have : A1 = u := by simpa using ea.symm
          subst this
          have : B1 = x :: w := by simpa using eb
          subst this
          exact le_max_right _ _
        · rw [eb, KS.phiAt_append pa pb ph A1 ha]
          exact le_trans (hpi.1 A1 a' ea ha).2 (le_max_left _ _)
      linarith
    · right
      have hp := phi_part_le (k := k) pa pb ph (B1 := B1) hu hY
      rw [← eA] at hp
      obtain ⟨y, Y', rfl⟩ := List.exists_cons_of_ne_nil hY
      have hy : y = x := by
        have := congrArg List.head? eX
        simpa using this.symm
      subst hy
      have hYseq : IsSeq k (y :: Y') := hXseq.infix (by rw [eX]; exact (List.prefix_append _ _).isInfix)
      have hlY : linksT (y :: Y') ≤ linksT (y :: w) := by
        rw [eX]
        exact KS.linksT_le_right _ _
      have hhY : holesT k (y :: Y') ≤ holesT k (y :: w) := by
        rw [eX, PS.holesT_append]
        omega
      have hcap := hseq (linksT (y :: Y')) (by omega) (y :: Y') hYseq
        (fun z hz => hk1 z (by rw [hs, eX]; simp at hz ⊢; tauto)) rfl (by
          have h1 := Nat.mul_le_mul_left (k - 1) hlY
          have h2 := hwX
          omega)
      have hcap' : ((y :: Y').length : ℤ) ≤ (P (linksT (y :: Y')) (holesT k (y :: Y')) : ℕ) := by
        exact_mod_cast hcap
      have hseg := seg_le P (k - 1) pa pb ph (tl := c - 1 - linksT u - lk y) (w := wtK k (y :: w))
        (u := linksT (y :: Y')) (e := holesT k (y :: Y')) (by omega)
        (by have := Nat.mul_le_mul_left (k - 1) hlY; rw [hwX]; omega)
      simp only [List.head_cons] at hp
      have hpa' : (0 : ℤ) ≤ pa := by positivity
      have := mul_le_mul_of_nonneg_left hcap' hpa'
      push_cast at hp hseg this ⊢
      linarith
  -- the rule
  unfold prevOk
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx1 with h0 | h0
  · -- a link of weight 3
    have hfc0 : fc = f := by rw [hfc', h0]; simp
    have hlk0 : lk x = 0 := by rw [hlkx, h0]
    rw [if_pos h0]
    rw [hlk0] at hPf hcase hom hX
    simp only [Nat.mul_zero, Nat.cast_zero, add_zero, Nat.sub_zero, mul_zero, sub_zero] at hPf hcase hom
    have hmj' : mj = min pm f := by rw [hmj, hfc0]
    have hMj' : Mj = max pM f := by rw [hMj, hfc0]
    rw [← hmj', ← hMj']
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rcases hcase with hc1 | hc1
    · left; right
      have hm1 : cn1F nx pa pb need om ≤ cF nx pa pb need om (wtK k (x :: w)) :=
        minUp_le (fun w' => cF nx pa pb need om w') (by omega)
      have hc : cF nx pa pb need om (wtK k (x :: w)) = (pa : ℤ) * (need - nx (om - wtK k (x :: w))) -
          ((pb : ℤ) - pa) * (wtK k (x :: w) : ℤ) := rfl
      linarith
    · right
      have hm1 : a2pF (segF P (k - 1) pa pb ph) nx pa pb (c - 1 - linksT u) need om ≤
          cF nx pa pb need om (wtK k (x :: w)) - segF P (k - 1) pa pb ph (c - 1 - linksT u) (wtK k (x :: w)) :=
        minUp_le (fun w' => cF nx pa pb need om w' - segF P (k - 1) pa pb ph (c - 1 - linksT u) w')
          (by omega)
      have hc : cF nx pa pb need om (wtK k (x :: w)) = (pa : ℤ) * (need - nx (om - wtK k (x :: w))) -
          ((pb : ℤ) - pa) * (wtK k (x :: w) : ℤ) := rfl
      linarith
  · -- a link of weight 4
    have hfc1 : fc = f - ph := by rw [hfc', h0]; simp
    have hlk1 : lk x = 1 := by rw [hlkx, h0]
    rw [if_neg (by omega)]
    rw [hlk1] at hPf hcase hom hX
    simp only [Nat.mul_one, Nat.cast_one, mul_one] at hPf hcase hom
    have hmj' : mj = min pm (f - ph) := by rw [hmj, hfc1]
    have hMj' : Mj = max pM (f - ph) := by rw [hMj, hfc1]
    rw [← hmj', ← hMj']
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    have e5 : (((k - 1 - 1 : ℕ)) : ℤ) = (((k - 2) : ℕ) : ℤ) := by
      have : k - 1 - 1 = k - 2 := by omega
      rw [this]
    rw [e5]
    have e6 : om - (k - 1) - wtK k (x :: w) = om - (k - 1) - wtK k (x :: w) := rfl
    rcases hcase with hc1 | hc1
    · left; right
      have hm1 : cn1F nx pa pb (need + ((k - 2 : ℕ) : ℤ)) (om - (k - 1)) ≤
          cF nx pa pb (need + ((k - 2 : ℕ) : ℤ)) (om - (k - 1)) (wtK k (x :: w)) :=
        minUp_le (fun w' => cF nx pa pb (need + ((k - 2 : ℕ) : ℤ)) (om - (k - 1)) w') (by omega)
      have hc : cF nx pa pb (need + ((k - 2 : ℕ) : ℤ)) (om - (k - 1)) (wtK k (x :: w)) =
          (pa : ℤ) * (need + ((k - 2 : ℕ) : ℤ) - nx (om - (k - 1) - wtK k (x :: w))) -
          ((pb : ℤ) - pa) * (wtK k (x :: w) : ℤ) := rfl
      linarith
    · right
      have e7 : c - 1 - linksT u - 1 = c - 1 - linksT u - 1 := rfl
      have hm1 : a2pF (segF P (k - 1) pa pb ph) nx pa pb (c - 1 - linksT u - 1)
            (need + ((k - 2 : ℕ) : ℤ)) (om - (k - 1)) ≤
          cF nx pa pb (need + ((k - 2 : ℕ) : ℤ)) (om - (k - 1)) (wtK k (x :: w)) -
            segF P (k - 1) pa pb ph (c - 1 - linksT u - 1) (wtK k (x :: w)) :=
        minUp_le (fun w' => cF nx pa pb (need + ((k - 2 : ℕ) : ℤ)) (om - (k - 1)) w' -
          segF P (k - 1) pa pb ph (c - 1 - linksT u - 1) w') (by omega)
      have hc : cF nx pa pb (need + ((k - 2 : ℕ) : ℤ)) (om - (k - 1)) (wtK k (x :: w)) =
          (pa : ℤ) * (need + ((k - 2 : ℕ) : ℤ) - nx (om - (k - 1) - wtK k (x :: w))) -
          ((pb : ℤ) - pa) * (wtK k (x :: w) : ℤ) := rfl
      linarith

/-- **Rule (T1) of PREV.**  A complete piece with `delta ≥ 0` passes the exact test. -/
theorem prev_end {pa pb ph : ℕ} {S : List TRow} {pm pM : ℤ} (hS : S ≠ [])
    (hgood : Good k pa pb ph S) (hpi : PotI k pa pb ph S pm pM) :
    prevEnd (potF pa pb ph 0 (linksT S) S.length (holesT k S)) pm pM = true := by
  have hf : phiAt k pa pb ph S [] = potF pa pb ph 0 (linksT S) S.length (holesT k S) := by
    rw [KS.phiAt_end pa pb ph hS, KS.potN_eq]
    unfold potF
    ring
  set f := potF pa pb ph 0 (linksT S) S.length (holesT k S)
  unfold prevEnd
  simp only [decide_eq_true_eq]
  obtain ⟨A0, B0, e0, hm0⟩ : ∃ A0 B0, S = A0 ++ B0 ∧ phiAt k pa pb ph A0 B0 = min pm f := by
    by_cases hm : pm ≤ f
    · obtain ⟨A, B, eAB, _, hpA⟩ := hpi.2.1
      exact ⟨A, B, eAB, by rw [hpA, min_eq_left hm]⟩
    · exact ⟨S, [], by simp, by rw [hf, min_eq_right (le_of_lt (not_le.mp hm))]⟩
  obtain ⟨A1, B1, e1, hle⟩ := hgood A0 B0 e0
  rw [hm0, hf] at hle
  have : phiAt k pa pb ph A1 B1 ≤ max pM f := by
    by_cases hB : B1 = []
    · subst hB
      have : A1 = S := by simpa using e1.symm
      subst this
      rw [hf]
      exact le_max_right _ _
    · exact le_trans (hpi.1 A1 B1 e1 hB).2 (le_max_left _ _)
  linarith

end Prev

end J16
end SuperpermLowerBounds
