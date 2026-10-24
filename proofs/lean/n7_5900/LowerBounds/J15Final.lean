import LowerBounds.J15Rules

/-!
# The joint statements of 5,900 from six searches (the written proof, sections 5.3 to 5.5)

`J15.joint_of_search`: the five joint statements S1 … S5 (`KS.Joint`), given that table T' is
valid (`KS.TableT`), given Theorem K (`KS.TheoremK`) and given the six evaluated statements
`J15.Evals`: the searches for S1, S3, S4, S5 and for the two parts S2a1 (rings with at least 16
holes) and S2a2 (rings with 8 to 15 holes) of S2 answer `false`.  S2 is searched with the ring
first; its third part S2b (rings with at most 7 holes) follows from Theorem K (section 5.5).

`jw_of_search`: the compiled search `jSearch` reads its rule from tables; the tables hold the
values of the functions `bestF`, `fF` of `J15Search.lean`, so `J15Rules.jw_of_parts` applies.

An evaluated statement is written with the formula of `PS.Covered` (every part lies in a range of
parts that answers `false`), so that this file needs no file of the proof of 5,899.
-/

namespace SuperpermLowerBounds
namespace J15

open S (PermW WLink DoorEq)
open PS (TRow IsSeq holesT linksT Closes SeqCapLt RingCapT capF)
open KS (tabA tab2 look2 maxLe maxLeN par)
open T5900

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

theorem tab2_get {α : Type} [Inhabited α] (A C : ℕ) (f : ℕ → ℕ → α) {t y : ℕ} (ht : t < A)
    (hy : y < C) : (tab2 A C f)[t * C + y]! = f t y := by
  have hi : t * C + y < A * C := by nlinarith
  have hsz : t * C + y < (tab2 A C f).size := by
    unfold tab2
    rw [Array.size_ofFn]
    exact hi
  rw [getElem!_pos (tab2 A C f) (t * C + y) hsz]
  simp only [tab2, Array.getElem_ofFn, S.mul_add_div' hy, S.mul_add_mod' hy]

theorem look2_tab2 {α : Type} [Inhabited α] (A C : ℕ) (f : ℕ → ℕ → α) :
    look2 A C (tab2 A C f) f = f := by
  funext t y
  unfold look2
  by_cases h : (decide (t < A) && decide (y < C)) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact tab2_get A C f h.1 h.2
  · rw [if_neg h]

theorem par_false {part : ℕ → Bool} {pa pb : ℕ} (h : par part pa pb = false) :
    ∀ tp, pa ≤ tp → tp < pb → part tp = false := by
  intro tp h1 h2
  unfold par at h
  rw [List.any_map, List.any_eq_false] at h
  have h3 := h (tp - pa) (List.mem_range.mpr (by omega))
  have e : pa + (tp - pa) = tp := by omega
  simpa [Task.spawn, e] using h3

theorem arr_map_get {α : Type} (l : List α) (f : α → ℕ) (d : α) {i : ℕ} (hi : i < l.length) :
    ((l.map f).toArray)[i]! = f (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp [hi]

/-- **The compiled search proves the statement** (`4 ≤ k ≤ 15`).  The parts may be evaluated in
several ranges. -/
theorem jw_of_search {k : ℕ} {caps : List (List ℕ)} {PRl : List ℕ}
    {specs : List (ℕ × ℕ × ℕ)} {V W B sm fuel : ℕ} {gs : List (ℕ × ℕ × ℕ)} (hk : 4 ≤ k)
    (hk15 : k ≤ 15)
    (hne : specs ≠ []) (hnp : specs.length ≤ 255) (hgs : ∀ g ∈ gs, 0 < g.2.2)
    (hc : CapsOK k (capF caps) (fun x => PRl.getD x 0) W sm) (hsm : ∀ p ∈ specs, p.1 ≤ sm + 1)
    (hs : ∀ tp, tp < gprod gs → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      jSearch k caps PRl specs V W B fuel gs pa pb = false) :
    JW k specs (V : ℤ) W B := by
  refine jw_of_parts (enc := PS.encB k) (PS.encB_enc k hk hk15) (by omega) hne hnp hgs hc hsm
    ?_ ?_ ?_ ?_ (fun tp htp => by
      obtain ⟨pa, pb, h1, h2, h⟩ := hs tp htp
      unfold jSearch at h
      simp only [look2_tab2] at h
      exact par_false h tp h1 h2)
  · intro i hi
    exact ⟨arr_map_get specs _ (0, 0, 0) hi, arr_map_get specs _ (0, 0, 0) hi,
      arr_map_get specs _ (0, 0, 0) hi⟩
  · intro i y x hi hy hx
    unfold bestT
    split_ifs with hcnd
    · rw [tab2_get _ _ _ hi (by omega)]
      exact decide_eq_true hx
    · rfl
  · intro i u y x hi hy _ hx
    unfold gT
    split_ifs with hcnd
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcnd
      obtain ⟨⟨h1, h2⟩, h3⟩ := hcnd
      rw [tabA_get _ _ _ _ h1 h2 h3]
      exact decide_eq_true hx
    · rfl
  · intro i b r d x hi hb hkd0 hx
    unfold fT
    split_ifs with hcnd
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcnd
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcnd
      have hib : i * (W + 1) + b < specs.length * (W + 1) := by nlinarith
      rw [tabA_get _ _ _ _ hib h3 h4]
      simp only [S.mul_add_div' h2, S.mul_add_mod' h2]
      beta_reduce at hkd0
      rw [hkd0, if_pos (show ((0 : ℕ) == 0) = true from rfl)]
      exact decide_eq_true hx
    · rfl

/-! ### The evaluated statements -/

/-- Every part `tp < nt` of a search lies in a range of parts that answers `false` (the formula
of `PS.Covered`). -/
def Cov (nt : ℕ) (f : ℕ → ℕ → Bool) : Prop :=
  ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧ f pa pb = false

/-- The search for J(specs; V, W; B) on table T' answers `false`, for some fuel and some gates
`(piece, rows, number of classes)`, in all `gprod gs` parts. -/
def Ev (specs : List (ℕ × ℕ × ℕ)) (V W B : ℕ) : Prop :=
  ∃ fuel gs, (∀ g ∈ gs, 0 < g.2.2) ∧ Cov (gprod gs) (jSearch 7 Ttab TRtab specs V W B fuel gs)

/-- The six evaluated statements.  A piece is `(c, lo, hi)`: `c = 0` a ring with `lo … hi` holes,
`c = s + 1` a sequence with at most `s` links. -/
structure Evals : Prop where
  /-- S1 = J(S4 S4; 55, 78; 1). -/
  s1 : Ev [(5, 0, 0), (5, 0, 0)] 55 78 1
  /-- S2a1 = J(R S5; 51, 83; 1) for rings with at least 16 holes. -/
  s2a1 : Ev [(0, 16, 83), (6, 0, 0)] 51 83 1
  /-- S2a2 = J(R S5; 51, 83; 1) for rings with 8 to 15 holes. -/
  s2a2 : Ev [(0, 8, 15), (6, 0, 0)] 51 83 1
  /-- S3 = J(S2 R R; 57, 76; 2). -/
  s3 : Ev [(3, 0, 0), (0, 0, 76), (0, 0, 76)] 57 76 2
  /-- S4 = J(S1 S1 R; 61, 71; 1). -/
  s4 : Ev [(2, 0, 0), (2, 0, 0), (0, 0, 71)] 61 71 1
  /-- S5 = J(S0 S0 R; 62, 70; 2). -/
  s5 : Ev [(1, 0, 0), (1, 0, 0), (0, 0, 70)] 62 70 2

/-- The rows of T' for at most 5 links reach to weight 83. -/
theorem tlen_ge : ∀ t ≤ 5, 84 - 6 * t ≤ KS.Tlen.getD t 0 := by decide

/-- Table T' gives the caps that the searches read, within weight 83 and to 5 links. -/
theorem capsOK_T (hT : KS.TableT) {W : ℕ} (hW : W ≤ 83) :
    CapsOK 7 (capF Ttab) (fun x => TRtab.getD x 0) W 5 := by
  constructor
  · intro t ht L h1 h2 h3 h4
    have hb := tlen_ge t ht
    exact hT.1 t (by omega) L h1 h2 h3 (by omega)
  · intro L h1 h2 h3 h4 h5
    exact hT.2 L h1 h2 h3 h4 (by omega)

theorem jw_of_ev (hT : KS.TableT) {specs : List (ℕ × ℕ × ℕ)} {V W B : ℕ} (hW : W ≤ 83)
    (hne : specs ≠ []) (hlen : specs.length ≤ 255) (hsm : ∀ p ∈ specs, p.1 ≤ 5 + 1)
    (h : Ev specs V W B) : JW 7 specs (V : ℤ) W B := by
  obtain ⟨fuel, gs, hgs, hcov⟩ := h
  exact jw_of_search (by norm_num) (by norm_num) hne hlen hgs (capsOK_T hT hW) hsm hcov

/-! ### From the statements on triples to the statements of the interface -/

theorem valT_eq (L : List TRow) : KS.valT L = valK 7 L := by
  unfold KS.valT valK vOf
  push_cast
  ring

theorem wtT_eq (L : List TRow) : KS.wtT L = wtK 7 L := rfl

theorem blocksR_flat : ∀ Ls : List (List TRow), blocksR Ls.flatten = Ls.flatMap KS.blocksT
  | [] => rfl
  | L :: Ls => by
    show blocksR (L ++ Ls.flatten) = KS.blocksT L ++ Ls.flatMap KS.blocksT
    rw [blocksR_append, blocksR_flat Ls]
    rfl

theorem sh_of_sharedLe {Ls : List (List TRow)} {B : ℕ} (h : KS.SharedLe Ls B) : Sh B Ls := by
  obtain ⟨keep, rem, hperm, hlen, hpw⟩ := h
  unfold Sh
  rw [blocksR_flat]
  have h1 := hperm.length_eq
  rw [List.length_append] at h1
  have h2 := clsCount_perm hperm
  have h3 := clsCount_le_append keep rem
  have h4 := clsCount_of_pairwise hpw
  omega

theorem sh_swap {A C : List TRow} {B : ℕ} (h : Sh B [A, C]) : Sh B [C, A] := by
  unfold Sh at h ⊢
  have hp : (blocksR [C, A].flatten).Perm (blocksR [A, C].flatten) := by
    show (blocksR (C ++ (A ++ []))).Perm (blocksR (A ++ (C ++ [])))
    rw [List.append_nil, List.append_nil, blocksR_append, blocksR_append]
    exact List.perm_append_comm
  rw [hp.length_eq, clsCount_perm hp]
  exact h

theorem seq_piece {s lo hi : ℕ} {L : List TRow} (h : KS.IsPiece (.seq s) L) :
    IsPieceW 7 (s + 1, lo, hi) L := by
  unfold IsPieceW
  rw [if_neg (Nat.succ_ne_zero s)]
  exact ⟨h.1, h.2.1, h.2.2.1, Nat.succ_le_succ h.2.2.2⟩

theorem ring_piece {lo hi : ℕ} {L : List TRow} (h : KS.IsPiece .ring L)
    (hlo : lo ≤ holesT 7 L) (hhi : holesT 7 L ≤ hi) : IsPieceW 7 (0, lo, hi) L := by
  unfold IsPieceW
  rw [if_pos rfl]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hlo, hhi⟩

theorem holes_le_wtT (L : List TRow) : holesT 7 L ≤ KS.wtT L := by
  unfold KS.wtT
  omega

theorem forall₂_two {α β : Type} {R : α → β → Prop} {a b : α} {l : List β}
    (h : List.Forall₂ R [a, b] l) : ∃ x y, l = [x, y] ∧ R a x ∧ R b y := by
  cases h with
  | cons h1 h' =>
    cases h' with
    | cons h2 h'' =>
      cases h''
      exact ⟨_, _, rfl, h1, h2⟩

theorem forall₂_three {α β : Type} {R : α → β → Prop} {a b c : α} {l : List β}
    (h : List.Forall₂ R [a, b, c] l) : ∃ x y z, l = [x, y, z] ∧ R a x ∧ R b y ∧ R c z := by
  cases h with
  | cons h1 h' =>
    obtain ⟨y, z, rfl, h2, h3⟩ := forall₂_two h'
    exact ⟨_, y, z, rfl, h1, h2, h3⟩

/-! ### The five statements -/

/-- S1. -/
theorem s1_of (hT : KS.TableT) (h : Ev [(5, 0, 0), (5, 0, 0)] 55 78 1) :
    KS.J [.seq 4, .seq 4] 55 78 1 := by
  have hjw := jw_of_ev hT (by norm_num) (by simp) (by simp) (by decide) h
  intro Ls hLs hsh hw
  obtain ⟨L1, L2, rfl, h1, h2⟩ := forall₂_two hLs
  have := hjw [L1, L2]
    (List.Forall₂.cons (seq_piece h1) (List.Forall₂.cons (seq_piece h2) List.Forall₂.nil))
    (sh_of_sharedLe hsh) (by simpa [wtT_eq] using hw)
  simpa [valT_eq] using this

/-- S3. -/
theorem s3_of (hT : KS.TableT) (h : Ev [(3, 0, 0), (0, 0, 76), (0, 0, 76)] 57 76 2) :
    KS.J [.seq 2, .ring, .ring] 57 76 2 := by
  have hjw := jw_of_ev hT (by norm_num) (by simp) (by simp) (by decide) h
  intro Ls hLs hsh hw
  obtain ⟨L1, L2, L3, rfl, h1, h2, h3⟩ := forall₂_three hLs
  have hw' : KS.wtT L1 + (KS.wtT L2 + KS.wtT L3) ≤ 76 := by simpa using hw
  have g2 := holes_le_wtT L2
  have g3 := holes_le_wtT L3
  have := hjw [L1, L2, L3]
    (List.Forall₂.cons (seq_piece h1) (List.Forall₂.cons (ring_piece h2 (Nat.zero_le _) (by omega))
      (List.Forall₂.cons (ring_piece h3 (Nat.zero_le _) (by omega)) List.Forall₂.nil)))
    (sh_of_sharedLe hsh) (by simpa [wtT_eq] using hw)
  simpa [valT_eq] using this

/-- S4. -/
theorem s4_of (hT : KS.TableT) (h : Ev [(2, 0, 0), (2, 0, 0), (0, 0, 71)] 61 71 1) :
    KS.J [.seq 1, .seq 1, .ring] 61 71 1 := by
  have hjw := jw_of_ev hT (by norm_num) (by simp) (by simp) (by decide) h
  intro Ls hLs hsh hw
  obtain ⟨L1, L2, L3, rfl, h1, h2, h3⟩ := forall₂_three hLs
  have hw' : KS.wtT L1 + (KS.wtT L2 + KS.wtT L3) ≤ 71 := by simpa using hw
  have g3 := holes_le_wtT L3
  have := hjw [L1, L2, L3]
    (List.Forall₂.cons (seq_piece h1) (List.Forall₂.cons (seq_piece h2)
      (List.Forall₂.cons (ring_piece h3 (Nat.zero_le _) (by omega)) List.Forall₂.nil)))
    (sh_of_sharedLe hsh) (by simpa [wtT_eq] using hw)
  simpa [valT_eq] using this

/-- S5. -/
theorem s5_of (hT : KS.TableT) (h : Ev [(1, 0, 0), (1, 0, 0), (0, 0, 70)] 62 70 2) :
    KS.J [.seq 0, .seq 0, .ring] 62 70 2 := by
  have hjw := jw_of_ev hT (by norm_num) (by simp) (by simp) (by decide) h
  intro Ls hLs hsh hw
  obtain ⟨L1, L2, L3, rfl, h1, h2, h3⟩ := forall₂_three hLs
  have hw' : KS.wtT L1 + (KS.wtT L2 + KS.wtT L3) ≤ 70 := by simpa using hw
  have g3 := holes_le_wtT L3
  have := hjw [L1, L2, L3]
    (List.Forall₂.cons (seq_piece h1) (List.Forall₂.cons (seq_piece h2)
      (List.Forall₂.cons (ring_piece h3 (Nat.zero_le _) (by omega)) List.Forall₂.nil)))
    (sh_of_sharedLe hsh) (by simpa [wtT_eq] using hw)
  simpa [valT_eq] using this

/-- Corollary K on table D: a sequence with at most 5 links within weight 83 has value at most
45. -/
theorem dtab_le : ∀ t < 6, ∀ e < 84, e + 6 * t ≤ 83 → capF Dtab t e ≤ e + 5 * t + 45 := by
  decide +kernel

/-- A ring with at most 7 holes has value at most 5 on table T'. -/
theorem trtab_le : ∀ H < 8, TRtab.getD H 0 ≤ H + 5 := by decide +kernel

/-- S2: the two searched parts and, for rings with at most 7 holes, Theorem K. -/
theorem s2_of (hT : KS.TableT) (hK : KS.TheoremK) (ha1 : Ev [(0, 16, 83), (6, 0, 0)] 51 83 1)
    (ha2 : Ev [(0, 8, 15), (6, 0, 0)] 51 83 1) : KS.J [.seq 5, .ring] 51 83 1 := by
  have hjw1 := jw_of_ev hT (by norm_num) (by simp) (by simp) (by decide) ha1
  have hjw2 := jw_of_ev hT (by norm_num) (by simp) (by simp) (by decide) ha2
  intro Ls hLs hsh hw
  obtain ⟨L1, L2, rfl, h1, h2⟩ := forall₂_two hLs
  have hw' : KS.wtT L1 + KS.wtT L2 ≤ 83 := by simpa using hw
  have g2 := holes_le_wtT L2
  have hsh' := sh_swap (sh_of_sharedLe hsh)
  by_cases h16 : 16 ≤ holesT 7 L2
  · have := hjw1 [L2, L1]
      (List.Forall₂.cons (ring_piece h2 h16 (by omega))
        (List.Forall₂.cons (seq_piece h1) List.Forall₂.nil)) hsh'
      (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ← wtT_eq]; omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ← valT_eq] at this ⊢
    push_cast at this
    linarith
  by_cases h8 : 8 ≤ holesT 7 L2
  · have := hjw2 [L2, L1]
      (List.Forall₂.cons (ring_piece h2 h8 (by omega))
        (List.Forall₂.cons (seq_piece h1) List.Forall₂.nil)) hsh'
      (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ← wtT_eq]; omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ← valT_eq] at this ⊢
    push_cast at this
    linarith
  · -- S2b
    obtain ⟨hR, hR0, hR2, hRc⟩ := h2
    obtain ⟨hS, _, hS1, hSl⟩ := h1
    have hlR : linksT L2 = 0 := PS.linksT_zero hR0
    have c1 := hT.2 L2 hR hR0 hR2 hRc (by omega)
    have c2 := trtab_le (holesT 7 L2) (by omega)
    have hwS : holesT 7 L1 + 6 * linksT L1 ≤ 83 := by
      unfold KS.wtT at hw'
      omega
    have c3 := hK (linksT L1) (by omega) L1 hS hS1 rfl (by omega)
    have c4 := dtab_le (linksT L1) (by omega) (holesT 7 L1) (by omega) hwS
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, KS.valT, hlR]
    have c1' : (L2.length : ℤ) ≤ (holesT 7 L2 : ℤ) + 5 := by exact_mod_cast le_trans c1 c2
    have c3' : (L1.length : ℤ) ≤ (holesT 7 L1 : ℤ) + 5 * (linksT L1 : ℤ) + 45 := by
      exact_mod_cast le_trans c3 c4
    push_cast
    linarith

/-- **The joint statements of 5,900**, from table T', Theorem K and the six evaluated
statements. -/
theorem joint_of_search (hT : KS.TableT) (hK : KS.TheoremK) (hE : Evals) : KS.Joint :=
  ⟨s1_of hT hE.s1, s2_of hT hK hE.s2a1 hE.s2a2, s3_of hT hE.s3, s4_of hT hE.s4, s5_of hT hE.s5⟩

end J15
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.J15.jw_of_search
#print axioms SuperpermLowerBounds.J15.joint_of_search
