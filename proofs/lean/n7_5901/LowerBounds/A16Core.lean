import LowerBounds.K16Defs
import LowerBounds.A16Arith
import LowerBounds.A15Core

/-!
# The pieces of a configuration at defect 16 against the tables and the joint statements
(the written proof `proofs/n7_5901/PROOF_5901.md`, sections 2.5 to 2.9)

No rows of the model here: only pieces on words (`KS.IsPiece`), their values and weights.

* The items are those of defect 15 (`A15.Ext`, kinds `R`, `E`, `AB` with the shifts 6/7, 10/12, 11/13);
  `OK16` is `A15.Ext.OK` with at most 10 links instead of 8.  The items F, A', A'' of the written proof
  are kept as items `E` (F) and `AB` (A', A''), whose shifts are smaller (a working note of mine, not in this repository).
* `core`: a kernel piece and items with total value at least 40 and total weight at most 96 (in the units
  of the components), at most two of them of kind `E`, do not exist, given Theorem K16, the ring row of
  table T' and the joint statements of Table C.  This is the knapsack (KN16 by hull tables), Lemma
  PIECE16, section 2.7 (rings of value at least 7 have at least 8 holes) and Proposition MAP in one
  statement.
-/

namespace SuperpermLowerBounds
namespace A16

open T5900 T5901

/-- What the piece behind an item satisfies (as `A15.Ext.OK`, with at most 10 links). -/
structure OK16 (e : A15.Ext) : Prop where
  ring : e.ty = .R → KS.IsPiece .ring e.L
  seq : e.ty ≠ .R → KS.IsPiece (.seq (PS.linksT e.L)) e.L
  blocks : (KS.blocksT e.L).Perm (e.own ++ e.bor)
  bor_len : e.bor.length ≤ 1
  bor_E : e.ty = .E → e.bor = []
  val : e.v + e.ty.dv ≤ KS.valT e.L
  wt : KS.wtT e.L + e.ty.dw ≤ e.w
  pos : 1 ≤ e.v
  links : PS.linksT e.L ≤ 10

theorem OK16.of_ok {e : A15.Ext} (h : e.OK) : OK16 e :=
  ⟨h.ring, h.seq, h.blocks, h.bor_len, h.bor_E, h.val, h.wt, h.pos, by have := h.links; omega⟩

/-! ### Pieces against the tables -/

theorem kwt (L : List PS.TRow) : 6 * PS.linksT L ≤ KS.wtT L := by unfold KS.wtT; omega

/-- Theorem K16 on a piece. -/
theorem seq_val (hK : K16.TheoremK16) {L : List PS.TRow} (h : KS.IsPiece (.seq (PS.linksT L)) L)
    (h10 : PS.linksT L ≤ 10) (hw : KS.wtT L ≤ 96) :
    KS.valT L ≤ ((Dv (PS.linksT L) (KS.wtT L) : ℕ) : ℤ) := by
  unfold KS.wtT at hw
  have hcap : L.length ≤ Dc (PS.linksT L) (PS.holesT 7 L) :=
    hK (PS.linksT L) h10 L h.1 h.2.2.1 rfl (by omega)
  have e : PS.holesT 7 L + 6 * PS.linksT L - 6 * PS.linksT L = PS.holesT 7 L := by omega
  unfold KS.valT KS.wtT Dv
  rw [if_pos (by omega), e]
  generalize Dc (PS.linksT L) (PS.holesT 7 L) = d at hcap ⊢
  omega

theorem seq_le_SK (hK : K16.TheoremK16) {L : List PS.TRow}
    (h : KS.IsPiece (.seq (PS.linksT L)) L) (h10 : PS.linksT L ≤ 10) {lo W : ℕ}
    (hlo : lo ≤ PS.linksT L) (hW : KS.wtT L ≤ W) (hW96 : W ≤ 96) :
    KS.valT L ≤ ((SK lo W : ℕ) : ℤ) := by
  have h1 := seq_val hK h h10 (by omega)
  have h2 : Dv (PS.linksT L) (KS.wtT L) ≤ SK lo W := Dv_le_SK hlo h10 hW hW96
  omega

/-- The ring row on a ring piece: table T' to 84 holes, and a ring is a chain. -/
theorem ring_val (hT : KS.TableT) (hK : K16.TheoremK16) {L : List PS.TRow} (h : KS.IsPiece .ring L)
    (hw : KS.wtT L ≤ 96) : KS.valT L ≤ ((Rv (PS.holesT 7 L) : ℕ) : ℤ) := by
  have hl : PS.linksT L = 0 := PS.linksT_zero h.2.1
  unfold KS.wtT at hw
  rw [hl] at hw
  have hc : L.length ≤ Dc 0 (PS.holesT 7 L) :=
    hK 0 (by omega) L h.1 (fun x hx => by rw [h.2.1 x hx]; omega) hl (by omega)
  have hR : L.length ≤ Rc (PS.holesT 7 L) := by
    unfold Rc
    by_cases h84 : PS.holesT 7 L ≤ 84
    · rw [if_pos h84]
      have ht : L.length ≤ TRtab.getD (PS.holesT 7 L) 0 :=
        hT.2 L h.1 h.2.1 h.2.2.1 h.2.2.2 h84
      exact le_min ht hc
    · rw [if_neg h84]
      exact hc
  unfold KS.valT Rv
  rw [hl]
  generalize Rc (PS.holesT 7 L) = d at hR
  omega

theorem ring_le_RH (hT : KS.TableT) (hK : K16.TheoremK16) {L : List PS.TRow}
    (h : KS.IsPiece .ring L) {W : ℕ} (hW : KS.wtT L ≤ W) (hW96 : W ≤ 96) :
    KS.valT L ≤ ((RH W : ℕ) : ℤ) := by
  have hl : PS.linksT L = 0 := PS.linksT_zero h.2.1
  have h1 := ring_val hT hK h (by omega)
  have h2 : Rv (PS.holesT 7 L) ≤ RH W := Rv_le_RH (by unfold KS.wtT at hW; rw [hl] at hW; omega) hW96
  omega

/-- A ring of value at least 6 has at least 8 holes (section 2.7). -/
theorem ring_holes8 (hT : KS.TableT) (hK : K16.TheoremK16) {L : List PS.TRow}
    (h : KS.IsPiece .ring L) (hw : KS.wtT L ≤ 96) (hv : 6 ≤ KS.valT L) : 8 ≤ PS.holesT 7 L := by
  by_contra hc
  have h1 := ring_val hT hK h hw
  have h2 := Rv_small (y := PS.holesT 7 L) (by omega)
  omega

/-! ### Items against the tables -/

section items

variable (hK : K16.TheoremK16) (hT : KS.TableT) {e : A15.Ext}

theorem ty_ne_R {e : A15.Ext} (h : e.ty ≠ .R) : 10 ≤ e.ty.dv ∧ 12 ≤ e.ty.dw := by
  cases hty : e.ty <;> simp_all [A15.Ty.dv, A15.Ty.dw]

include hK hT in
/-- The facts of a ring item. -/
theorem ringF (h : OK16 e) (ht : e.ty = .R) (hw : e.w ≤ 96) :
    KS.IsPiece .ring e.L ∧ e.v + 6 ≤ KS.valT e.L ∧ KS.wtT e.L + 7 ≤ e.w ∧ 1 ≤ e.v ∧
      8 ≤ PS.holesT 7 e.L ∧ KS.wtT e.L = PS.holesT 7 e.L := by
  have hval := h.val
  have hwt := h.wt
  rw [ht] at hval hwt
  simp only [A15.Ty.dv, A15.Ty.dw] at hval hwt
  have hp := h.ring ht
  have hl : PS.linksT e.L = 0 := PS.linksT_zero hp.2.1
  have hpos := h.pos
  refine ⟨hp, hval, hwt, hpos, ring_holes8 hT hK hp (by omega) (by omega), ?_⟩
  unfold KS.wtT
  rw [hl]
  rfl

/-- The facts of a sequence item. -/
theorem seqF (h : OK16 e) (ht : e.ty ≠ .R) :
    KS.IsPiece (.seq (PS.linksT e.L)) e.L ∧ e.v + 10 ≤ KS.valT e.L ∧ KS.wtT e.L + 12 ≤ e.w ∧
      1 ≤ e.v ∧ PS.linksT e.L ≤ 10 := by
  have hval := h.val
  have hwt := h.wt
  obtain ⟨d1, d2⟩ := ty_ne_R ht
  exact ⟨h.seq ht, by omega, by omega, h.pos, h.links⟩

include hK hT in
theorem item_R (h : OK16 e) (ht : e.ty = .R) (hw : e.w ≤ 96) : e.v ≤ ((IR e.w : ℕ) : ℤ) := by
  obtain ⟨hp, hval, hwt, hpos, _, _⟩ := ringF hK hT h ht hw
  have b := ring_le_RH hT hK hp (W := e.w - 7) (by omega) (by omega)
  unfold IR
  rw [if_pos (by omega)]
  generalize RH (e.w - 7) = d at b
  omega

include hK in
theorem item_S (h : OK16 e) (ht : e.ty ≠ .R) {lo : ℕ} (hlo : lo ≤ PS.linksT e.L) (hw : e.w ≤ 96) :
    e.v ≤ ((IS lo e.w : ℕ) : ℤ) := by
  obtain ⟨hp, hval, hwt, hpos, hl⟩ := seqF h ht
  have b := seq_le_SK hK hp hl (lo := lo) (W := e.w - 12) hlo (by omega) (by omega)
  unfold IS
  rw [if_pos (by omega)]
  generalize SK lo (e.w - 12) = d at b
  omega

include hK in
theorem item_A (h : OK16 e) (ht : e.ty = .AB) (hw : e.w ≤ 96) : e.v ≤ ((IA e.w : ℕ) : ℤ) := by
  have hval := h.val
  have hwt := h.wt
  rw [ht] at hval hwt
  simp only [A15.Ty.dv, A15.Ty.dw] at hval hwt
  have hne : e.ty ≠ .R := by rw [ht]; exact fun h => A15.Ty.noConfusion h
  have hpos := h.pos
  have b := seq_le_SK hK (h.seq hne) h.links (lo := 0) (W := e.w - 13) (by omega) (by omega)
    (by omega)
  unfold IA
  rw [if_pos (by omega)]
  generalize SK 0 (e.w - 13) = d at b
  omega

include hK hT in
theorem item_X (h : OK16 e) (hw : e.w ≤ 96) : e.v ≤ ((IX e.w : ℕ) : ℤ) := by
  by_cases ht : e.ty = .R
  · have := item_R hK hT h ht hw
    have : IR e.w ≤ IX e.w := le_max_left _ _
    omega
  · have := item_S hK h ht (lo := 0) (by omega) hw
    have : IS 0 e.w ≤ IX e.w := le_max_right _ _
    omega

end items

/-! ### Several items -/

theorem sumR (hK : K16.TheoremK16) (hT : KS.TableT) : ∀ rs : List A15.Ext,
    (∀ e ∈ rs, OK16 e ∧ e.ty = .R) → rs.length ≤ 4 → (rs.map A15.Ext.w).sum ≤ 96 →
    (rs.length : ℤ) ≤ (rs.map A15.Ext.v).sum ∧
      (rs.map A15.Ext.v).sum ≤ ((NR rs.length (rs.map A15.Ext.w).sum : ℕ) : ℤ)
  | [], _, _, _ => by simp
  | e :: es, hes, hl, hW => by
      rw [List.map_cons, List.sum_cons] at hW
      rw [List.length_cons] at hl
      obtain ⟨i1, i2⟩ := sumR hK hT es (fun e' he' => hes e' (List.mem_cons_of_mem _ he')) (by omega)
        (by omega)
      obtain ⟨he, ht⟩ := hes e List.mem_cons_self
      have hv := item_R hK hT he ht (by omega)
      have hpos := he.pos
      have hg : es.length = 0 ∨ 1 ≤ NR es.length (es.map A15.Ext.w).sum := by
        rcases Nat.eq_zero_or_pos es.length with h0 | h0
        · exact Or.inl h0
        · right
          have : (1 : ℤ) ≤ (es.length : ℤ) := by exact_mod_cast h0
          omega
      have hc := cNR (n := es.length) (w := e.w) (W := (es.map A15.Ext.w).sum) (by omega) hW
        (by omega) hg
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      constructor <;> omega

theorem sumS (hK : K16.TheoremK16) : ∀ ss : List A15.Ext,
    (∀ e ∈ ss, OK16 e ∧ e.ty ≠ .R) → ss.length ≤ 4 → (ss.map A15.Ext.w).sum ≤ 96 →
    (ss.length : ℤ) ≤ (ss.map A15.Ext.v).sum ∧
      (ss.map A15.Ext.v).sum ≤ ((NS ss.length (ss.map A15.Ext.w).sum : ℕ) : ℤ)
  | [], _, _, _ => by simp
  | e :: es, hes, hl, hW => by
      rw [List.map_cons, List.sum_cons] at hW
      rw [List.length_cons] at hl
      obtain ⟨i1, i2⟩ := sumS hK es (fun e' he' => hes e' (List.mem_cons_of_mem _ he')) (by omega)
        (by omega)
      obtain ⟨he, ht⟩ := hes e List.mem_cons_self
      have hv := item_S hK he ht (lo := 0) (by omega) (by omega)
      have hpos := he.pos
      have hg : es.length = 0 ∨ 1 ≤ NS es.length (es.map A15.Ext.w).sum := by
        rcases Nat.eq_zero_or_pos es.length with h0 | h0
        · exact Or.inl h0
        · right
          have : (1 : ℤ) ≤ (es.length : ℤ) := by exact_mod_cast h0
          omega
      have hc := cNS (n := es.length) (w := e.w) (W := (es.map A15.Ext.w).sum) (by omega) hW
        (by omega) hg
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      constructor <;> omega

theorem sumX (hK : K16.TheoremK16) (hT : KS.TableT) : ∀ es : List A15.Ext,
    (∀ e ∈ es, OK16 e) → (es.map A15.Ext.w).sum ≤ 96 →
    (es.length : ℤ) ≤ (es.map A15.Ext.v).sum ∧
      (es.map A15.Ext.v).sum ≤ ((NX (min es.length 5) (es.map A15.Ext.w).sum : ℕ) : ℤ)
  | [], _, _ => by simp
  | e :: es, hes, hW => by
      rw [List.map_cons, List.sum_cons] at hW
      obtain ⟨i1, i2⟩ := sumX hK hT es (fun e' he' => hes e' (List.mem_cons_of_mem _ he')) (by omega)
      have he := hes e List.mem_cons_self
      have hv := item_X hK hT he (by omega)
      have hpos := he.pos
      have hg : min es.length 5 = 0 ∨ 1 ≤ NX (min es.length 5) (es.map A15.Ext.w).sum := by
        rcases Nat.eq_zero_or_pos es.length with h0 | h0
        · left
          rw [h0]
          rfl
        · right
          have : (1 : ℤ) ≤ (es.length : ℤ) := by exact_mod_cast h0
          omega
      have hc := cNX (n := min es.length 5) (w := e.w) (W := (es.map A15.Ext.w).sum) (by omega) hW
        (by omega) hg
      have e1 : min (min es.length 5 + 1) 5 = min (es.length + 1) 5 := by omega
      rw [e1] at hc
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      constructor <;> omega

/-! ### Shared classes and the joint statements -/

theorem blocks_perm : ∀ es : List A15.Ext, (∀ e ∈ es, OK16 e) →
    ((es.map A15.Ext.L).flatMap KS.blocksT).Perm (es.flatMap A15.Ext.own ++ es.flatMap A15.Ext.bor)
  | [], _ => by simp
  | e :: es, h => by
      have ih := blocks_perm es (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
      have he := (h e List.mem_cons_self).blocks
      simp only [List.map_cons, List.flatMap_cons]
      exact (he.append ih).trans (A15.perm4 _ _ _ _)

theorem sharedLe_mk {L0 : List PS.TRow} {es : List A15.Ext} {B : ℕ} (hok : ∀ e ∈ es, OK16 e)
    (hcl : (KS.blocksT L0 ++ es.flatMap A15.Ext.own).Pairwise (fun u v => ¬ u ~r v))
    (hB : (es.map fun e => e.bor.length).sum ≤ B) : KS.SharedLe (L0 :: es.map A15.Ext.L) B := by
  refine ⟨KS.blocksT L0 ++ es.flatMap A15.Ext.own, es.flatMap A15.Ext.bor, ?_, ?_, hcl⟩
  · rw [List.flatMap_cons, List.append_assoc]
    exact List.Perm.append_left _ (blocks_perm es hok)
  · rw [List.length_flatMap]
    exact hB

theorem sharedLe_swap {a b : List PS.TRow} {l : List (List PS.TRow)} {B : ℕ}
    (h : KS.SharedLe (a :: b :: l) B) : KS.SharedLe (b :: a :: l) B := by
  obtain ⟨keep, rem, hp, hl, hk⟩ := h
  refine ⟨keep, rem, ?_, hl, hk⟩
  exact ((List.Perm.swap a b l).flatMap_right KS.blocksT).trans hp

theorem pairwise_comm {L0 : List PS.TRow} {as bs : List A15.Ext}
    (h : (KS.blocksT L0 ++ (as ++ bs).flatMap A15.Ext.own).Pairwise (fun u v => ¬ u ~r v)) :
    (KS.blocksT L0 ++ (bs ++ as).flatMap A15.Ext.own).Pairwise (fun u v => ¬ u ~r v) := by
  have hp : (KS.blocksT L0 ++ (as ++ bs).flatMap A15.Ext.own).Perm
      (KS.blocksT L0 ++ (bs ++ as).flatMap A15.Ext.own) :=
    List.Perm.append_left _ (List.perm_append_comm.flatMap_right _)
  exact (hp.pairwise_iff (fun h hr => h hr.symm)).mp h

theorem bor_sum (es : List A15.Ext) (h : ∀ e ∈ es, OK16 e) :
    (es.map fun e => e.bor.length).sum ≤ es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons]
      have h1 := (h e List.mem_cons_self).bor_len
      have h2 := ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
      omega

theorem bor_E0 {e : A15.Ext} (h : OK16 e) (ht : e.ty = .E) : e.bor.length = 0 := by
  rw [h.bor_E ht]
  rfl

/-! ### The cases -/

section cases

variable (hK : K16.TheoremK16) (hT : KS.TableT) {L0 : List PS.TRow}
  (h0 : KS.IsPiece (.seq (PS.linksT L0)) L0) (hl0 : PS.linksT L0 ≤ 10)

/-- Kernel bound with at least `lo` links. -/
theorem kb (hK : K16.TheoremK16) {L0 : List PS.TRow} (h0 : KS.IsPiece (.seq (PS.linksT L0)) L0)
    (hl0 : PS.linksT L0 ≤ 10) {lo : ℕ} (hlo : lo ≤ PS.linksT L0) (hw : KS.wtT L0 ≤ 96) :
    KS.valT L0 ≤ ((SK lo (KS.wtT L0) : ℕ) : ℤ) ∧ 6 * lo ≤ KS.wtT L0 := by
  have := kwt L0
  exact ⟨seq_le_SK hK h0 hl0 hlo le_rfl hw, by omega⟩

/-- T2 for a kernel piece with at most 7 links and a ring with 8 to 89 holes: the ten runs. -/
theorem t2_apply (hJ : K16.T2) {L1 : List PS.TRow} (p0 : KS.IsPiece (.seq 7) L0)
    (p1 : KS.IsPiece .ring L1) (h8 : 8 ≤ PS.holesT 7 L1) (h89 : PS.holesT 7 L1 ≤ 89)
    (hsh : KS.SharedLe [L0, L1] 1) (hw : KS.wtT L0 + KS.wtT L1 ≤ 89) :
    KS.valT L0 + KS.valT L1 < 46 := by
  have hsh' := sharedLe_swap hsh
  have hw' : (([L1, L0].map KS.wtT).sum) ≤ 89 := by simp; omega
  have hw'' : (([L0, L1].map KS.wtT).sum) ≤ 89 := by simp; omega
  obtain ⟨j1, j2, j3, j4, j5, j6, j7, j8, j9, j10⟩ := hJ
  have up : ∀ {P : List PS.TRow → Prop}, K16.JP P [.ring, .seq 7] 46 89 1 → P L1 →
      KS.valT L0 + KS.valT L1 < 46 := by
    intro P hP hp
    have h := hP [L1, L0] (.cons ⟨p1, hp⟩ (.cons p0 .nil)) hsh' hw'
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
    omega
  have lo : ∀ {P : List PS.TRow → Prop}, K16.JP P [.seq 7, .ring] 46 89 1 → P L1 →
      KS.valT L0 + KS.valT L1 < 46 := by
    intro P hP hp
    have h := hP [L0, L1] (.cons p0 (.cons ⟨p1, hp⟩ .nil)) hsh hw''
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
    omega
  by_cases a1 : PS.holesT 7 L1 ≤ 15
  · exact up j1 ⟨h8, a1⟩
  by_cases a2 : PS.holesT 7 L1 ≤ 23
  · exact up j2 ⟨by omega, a2⟩
  by_cases a3 : PS.holesT 7 L1 ≤ 31
  · exact up j3 ⟨by omega, a3⟩
  by_cases a4 : PS.holesT 7 L1 ≤ 39
  · by_cases v : 17 ≤ KS.valT L1
    · exact up j4 ⟨⟨by omega, a4⟩, v⟩
    · exact lo j5 ⟨⟨by omega, a4⟩, by omega⟩
  by_cases a5 : PS.holesT 7 L1 ≤ 47
  · by_cases v : 20 ≤ KS.valT L1
    · exact up j6 ⟨⟨by omega, a5⟩, v⟩
    · exact lo j7 ⟨⟨by omega, a5⟩, by omega⟩
  by_cases a6 : PS.holesT 7 L1 ≤ 55
  · by_cases v : 23 ≤ KS.valT L1
    · exact up j8 ⟨⟨by omega, a6⟩, v⟩
    · exact lo j9 ⟨⟨by omega, a6⟩, by omega⟩
  exact up j10 ⟨by omega, h89⟩

include hK hT h0 hl0

omit hT in
/-- No item: Corollary K16. -/
theorem case_0 (hv : 40 ≤ KS.valT L0) (hw : KS.wtT L0 ≤ 96) : False := by
  have b := seq_le_SK hK h0 hl0 (lo := 0) (W := 96) (by omega) hw le_rfl
  have c := fK
  omega

/-- One ring: T2. -/
theorem case_R (hJ : K16.T2) {r : A15.Ext} (hr : OK16 r) (tr : r.ty = .R)
    (hcl : (KS.blocksT L0 ++ ([r] ++ []).flatMap A15.Ext.own).Pairwise (fun u v => ¬ u ~r v))
    (hv : 40 ≤ KS.valT L0 + (([r] ++ []).map A15.Ext.v).sum)
    (hw : KS.wtT L0 + (([r] ++ []).map A15.Ext.w).sum ≤ 96) : False := by
  simp only [List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] at hv hw
  simp only [List.append_nil] at hcl
  obtain ⟨rp, rv, rw', rpos, r8, rh⟩ := ringF hK hT hr tr (by omega)
  have hs : PS.linksT L0 ≤ 7 := by
    by_contra hc
    obtain ⟨b0, a6⟩ := kb hK h0 hl0 (lo := 8) (by omega) (by omega)
    have b1 := item_R hK hT hr tr (by omega)
    have m1 : IR r.w ≤ IR (96 - KS.wtT L0) := IR_mono (by omega) (by omega)
    have c := chk1_spec fT2 (a := KS.wtT L0) (by omega) a6 (by omega)
    omega
  have hsh : KS.SharedLe [L0, r.L] 1 :=
    sharedLe_mk (es := [r]) (fun e he => by rw [List.mem_singleton.mp he]; exact hr) hcl
      (by simp; exact hr.bor_len)
  have h := t2_apply hJ (A15.isPiece_seq_mono h0 hs) rp r8 (by omega) hsh (by omega)
  omega

omit hT in
/-- One sequence: T1. -/
theorem case_S (hJ : K16.T1) {s : A15.Ext} (hs : OK16 s) (ts : s.ty ≠ .R)
    (hcl : (KS.blocksT L0 ++ ([] ++ [s]).flatMap A15.Ext.own).Pairwise (fun u v => ¬ u ~r v))
    (hv : 40 ≤ KS.valT L0 + (([] ++ [s]).map A15.Ext.v).sum)
    (hw : KS.wtT L0 + (([] ++ [s]).map A15.Ext.w).sum ≤ 96) : False := by
  simp only [List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] at hv hw
  simp only [List.nil_append] at hcl
  obtain ⟨sp, sv, sw, spos, sl⟩ := seqF hs ts
  have k7 : PS.linksT L0 ≤ 7 := by
    by_contra hc
    obtain ⟨b0, a6⟩ := kb hK h0 hl0 (lo := 8) (by omega) (by omega)
    have b1 := item_S hK hs ts (lo := 0) (by omega) (by omega)
    have m1 : IS 0 s.w ≤ IS 0 (96 - KS.wtT L0) := IS_mono (by omega) (by omega) (by omega)
    have c := chk1_spec fT1a (a := KS.wtT L0) (by omega) a6 (by omega)
    omega
  have s7 : PS.linksT s.L ≤ 7 := by
    by_contra hc
    obtain ⟨b0, _⟩ := kb hK h0 hl0 (lo := 0) (by omega) (by omega)
    have b1 := item_S hK hs ts (lo := 8) (by omega) (by omega)
    have m1 : IS 8 s.w ≤ IS 8 (96 - KS.wtT L0) := IS_mono (by omega) (by omega) (by omega)
    have c := chk1_spec fT1b (a := KS.wtT L0) (by omega) (by omega) (by omega)
    omega
  have hsh : KS.SharedLe [L0, s.L] 1 :=
    sharedLe_mk (es := [s]) (fun e he => by rw [List.mem_singleton.mp he]; exact hs) hcl
      (by simp; exact hs.bor_len)
  have h := A15.J2 hJ (A15.isPiece_seq_mono h0 k7) (A15.isPiece_seq_mono sp s7) hsh (by omega)
  omega

/-- Two rings: T3'. -/
theorem case_RR (hJ : K16.T3) {r1 r2 : A15.Ext} (h1 : OK16 r1) (h2 : OK16 r2) (t1 : r1.ty = .R)
    (t2 : r2.ty = .R)
    (hcl : (KS.blocksT L0 ++ ([r1, r2] ++ []).flatMap A15.Ext.own).Pairwise (fun u v => ¬ u ~r v))
    (hv : 40 ≤ KS.valT L0 + (([r1, r2] ++ []).map A15.Ext.v).sum)
    (hw : KS.wtT L0 + (([r1, r2] ++ []).map A15.Ext.w).sum ≤ 96) : False := by
  have hok : ∀ e ∈ [r1, r2], OK16 e ∧ e.ty = .R := by
    intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨h1, t1⟩
    · exact ⟨h2, t2⟩
  simp only [List.append_nil] at hv hw hcl
  obtain ⟨i1, i2⟩ := sumR hK hT [r1, r2] hok (by simp) (by simp at hw ⊢; omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hv hw i1 i2
  obtain ⟨rp1, rv1, rw1, _, r81, _⟩ := ringF hK hT h1 t1 (by omega)
  obtain ⟨rp2, rv2, rw2, _, r82, _⟩ := ringF hK hT h2 t2 (by omega)
  have hs : PS.linksT L0 ≤ 5 := by
    by_contra hc
    obtain ⟨b0, a6⟩ := kb hK h0 hl0 (lo := 6) (by omega) (by omega)
    have m1 : NR 2 (r1.w + r2.w) ≤ NR 2 (96 - KS.wtT L0) := NR_mono (by omega) (by omega) (by omega)
    have c := chk1_spec fT3 (a := KS.wtT L0) (by omega) a6 (by omega)
    omega
  have hsh : KS.SharedLe [L0, r1.L, r2.L] 2 :=
    sharedLe_mk (es := [r1, r2]) (fun e he => (hok e he).1) hcl
      (by simp; have := h1.bor_len; have := h2.bor_len; omega)
  have h := hJ [r1.L, L0, r2.L]
    (.cons ⟨rp1, r81, by unfold K16.RNN; omega⟩ (.cons (A15.isPiece_seq_mono h0 hs) (.cons ⟨rp2, r82, by unfold K16.RNN; omega⟩ .nil)))
    (sharedLe_swap hsh) (by simp; omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  omega

/-- A ring and a sequence: T4'. -/
theorem case_RS (hJ : K16.T4) {r s : A15.Ext} (hr : OK16 r) (hs : OK16 s) (tr : r.ty = .R)
    (ts : s.ty ≠ .R)
    (hcl : (KS.blocksT L0 ++ ([r] ++ [s]).flatMap A15.Ext.own).Pairwise (fun u v => ¬ u ~r v))
    (hv : 40 ≤ KS.valT L0 + (([r] ++ [s]).map A15.Ext.v).sum)
    (hw : KS.wtT L0 + (([r] ++ [s]).map A15.Ext.w).sum ≤ 96) : False := by
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] at hv hw
  simp only [List.cons_append, List.nil_append] at hcl
  obtain ⟨rp, rv, rw', rpos, r8, rh⟩ := ringF hK hT hr tr (by omega)
  obtain ⟨sp, sv, sw, spos, sl⟩ := seqF hs ts
  have bR := item_R hK hT hr tr (by omega)
  have k4 : PS.linksT L0 ≤ 4 := by
    by_contra hc
    obtain ⟨b0, a6⟩ := kb hK h0 hl0 (lo := 5) (by omega) (by omega)
    have b1 := item_S hK hs ts (lo := 0) (by omega) (by omega)
    have m1 : IS 0 s.w ≤ IS 0 (96 - KS.wtT L0 - r.w) := IS_mono (by omega) (by omega) (by omega)
    have c := chk2_spec fT4a (a := KS.wtT L0) (b := r.w) (by omega) a6 (by omega) (by omega)
    omega
  have s4 : PS.linksT s.L ≤ 4 := by
    by_contra hc
    obtain ⟨b0, _⟩ := kb hK h0 hl0 (lo := 0) (by omega) (by omega)
    have b1 := item_S hK hs ts (lo := 5) (by omega) (by omega)
    have m1 : IS 5 s.w ≤ IS 5 (96 - KS.wtT L0 - r.w) := IS_mono (by omega) (by omega) (by omega)
    have c := chk2_spec fT4b (a := KS.wtT L0) (b := r.w) (by omega) (by omega) (by omega) (by omega)
    omega
  have hsh : KS.SharedLe [L0, r.L, s.L] 2 :=
    sharedLe_mk (es := [r, s]) (fun e he => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
        rcases he with rfl | rfl
        · exact hr
        · exact hs) hcl
      (by simp; have := hr.bor_len; have := hs.bor_len; omega)
  have h := hJ [r.L, L0, s.L]
    (.cons ⟨rp, r8⟩ (.cons (A15.isPiece_seq_mono h0 k4) (.cons (A15.isPiece_seq_mono sp s4) .nil)))
    (sharedLe_swap hsh) (by simp; omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  omega

omit hT in
/-- Two sequences: T5. -/
theorem case_SS (hJ : K16.T5) {s1 s2 : A15.Ext} (h1 : OK16 s1) (h2 : OK16 s2) (t1 : s1.ty ≠ .R)
    (t2 : s2.ty ≠ .R)
    (hcl : (KS.blocksT L0 ++ ([] ++ [s1, s2]).flatMap A15.Ext.own).Pairwise (fun u v => ¬ u ~r v))
    (hv : 40 ≤ KS.valT L0 + (([] ++ [s1, s2]).map A15.Ext.v).sum)
    (hw : KS.wtT L0 + (([] ++ [s1, s2]).map A15.Ext.w).sum ≤ 96) : False := by
  have hok : ∀ e ∈ [s1, s2], OK16 e ∧ e.ty ≠ .R := by
    intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨h1, t1⟩
    · exact ⟨h2, t2⟩
  simp only [List.nil_append] at hv hw hcl
  obtain ⟨i1, i2⟩ := sumS hK [s1, s2] hok (by simp) (by simp at hw ⊢; omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hv hw i1 i2
  obtain ⟨sp1, sv1, sw1, _, _⟩ := seqF h1 t1
  obtain ⟨sp2, sv2, sw2, _, _⟩ := seqF h2 t2
  have k3 : PS.linksT L0 ≤ 3 := by
    by_contra hc
    obtain ⟨b0, a6⟩ := kb hK h0 hl0 (lo := 4) (by omega) (by omega)
    have m1 : NS 2 (s1.w + s2.w) ≤ NS 2 (96 - KS.wtT L0) := NS_mono (by omega) (by omega) (by omega)
    have c := chk1_spec fT5a (a := KS.wtT L0) (by omega) a6 (by omega)
    omega
  have sk : ∀ {x y : A15.Ext}, OK16 x → x.ty ≠ .R → OK16 y → y.ty ≠ .R →
      KS.wtT L0 + (x.w + y.w) ≤ 96 → 40 ≤ KS.valT L0 + (x.v + y.v) → PS.linksT x.L ≤ 3 := by
    intro x y hx tx hy ty hwxy hvxy
    by_contra hc
    obtain ⟨b0, _⟩ := kb hK h0 hl0 (lo := 0) (by omega) (by omega)
    have b1 := item_S hK hx tx (lo := 4) (by omega) (by omega)
    have b2 := item_S hK hy ty (lo := 0) (by omega) (by omega)
    have hp2 := hy.pos
    have hp1 := hx.pos
    have m1 : IS 0 y.w ≤ IS 0 (96 - KS.wtT L0 - x.w) := IS_mono (by omega) (by omega) (by omega)
    have c := chk2_spec fT5b (a := KS.wtT L0) (b := x.w) (by omega) (by omega) (by omega)
      (by omega)
    omega
  have s13 := sk h1 t1 h2 t2 (by omega) (by omega)
  have s23 := sk h2 t2 h1 t1 (by omega) (by omega)
  have hsh : KS.SharedLe [L0, s1.L, s2.L] 2 :=
    sharedLe_mk (es := [s1, s2]) (fun e he => (hok e he).1) hcl
      (by simp; have := h1.bor_len; have := h2.bor_len; omega)
  have h := A15.J3 hJ (A15.isPiece_seq_mono h0 k3) (A15.isPiece_seq_mono sp1 s13)
    (A15.isPiece_seq_mono sp2 s23) hsh (by omega)
  omega

/-- Three rings: T6'. -/
theorem case_RRR (hJ : K16.T6) {r1 r2 r3 : A15.Ext} (h1 : OK16 r1) (h2 : OK16 r2) (h3 : OK16 r3)
    (t1 : r1.ty = .R) (t2 : r2.ty = .R) (t3 : r3.ty = .R)
    (hcl : (KS.blocksT L0 ++ ([r1, r2, r3] ++ []).flatMap A15.Ext.own).Pairwise
      (fun u v => ¬ u ~r v))
    (hv : 40 ≤ KS.valT L0 + (([r1, r2, r3] ++ []).map A15.Ext.v).sum)
    (hw : KS.wtT L0 + (([r1, r2, r3] ++ []).map A15.Ext.w).sum ≤ 96) : False := by
  have hok : ∀ e ∈ [r1, r2, r3], OK16 e ∧ e.ty = .R := by
    intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨h1, t1⟩
    · exact ⟨h2, t2⟩
    · exact ⟨h3, t3⟩
  simp only [List.append_nil] at hv hw hcl
  obtain ⟨i1, i2⟩ := sumR hK hT [r1, r2, r3] hok (by simp) (by simp at hw ⊢; omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hv hw i1 i2
  obtain ⟨rp1, rv1, rw1, _, r81, _⟩ := ringF hK hT h1 t1 (by omega)
  obtain ⟨rp2, rv2, rw2, _, r82, _⟩ := ringF hK hT h2 t2 (by omega)
  obtain ⟨rp3, rv3, rw3, _, r83, _⟩ := ringF hK hT h3 t3 (by omega)
  have hs : PS.linksT L0 ≤ 2 := by
    by_contra hc
    obtain ⟨b0, a6⟩ := kb hK h0 hl0 (lo := 3) (by omega) (by omega)
    have m1 : NR 3 (r1.w + (r2.w + r3.w)) ≤ NR 3 (96 - KS.wtT L0) :=
      NR_mono (by omega) (by omega) (by omega)
    have c := chk1_spec fT6 (a := KS.wtT L0) (by omega) a6 (by omega)
    omega
  have hsh : KS.SharedLe [L0, r1.L, r2.L, r3.L] 3 :=
    sharedLe_mk (es := [r1, r2, r3]) (fun e he => (hok e he).1) hcl
      (by simp; have := h1.bor_len; have := h2.bor_len; have := h3.bor_len; omega)
  have h := hJ [L0, r1.L, r2.L, r3.L]
    (.cons (A15.isPiece_seq_mono h0 hs) (.cons ⟨rp1, r81, by unfold K16.RNN; omega⟩ (.cons ⟨rp2, r82, by unfold K16.RNN; omega⟩
      (.cons ⟨rp3, r83, by unfold K16.RNN; omega⟩ .nil)))) hsh (by simp; omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  omega

/-- Two rings and a sequence: T7. -/
theorem case_RRS (hJ : K16.T7) {r1 r2 s : A15.Ext} (h1 : OK16 r1) (h2 : OK16 r2) (hs : OK16 s)
    (t1 : r1.ty = .R) (t2 : r2.ty = .R) (ts : s.ty ≠ .R)
    (hcl : (KS.blocksT L0 ++ ([r1, r2] ++ [s]).flatMap A15.Ext.own).Pairwise (fun u v => ¬ u ~r v))
    (hv : 40 ≤ KS.valT L0 + (([r1, r2] ++ [s]).map A15.Ext.v).sum)
    (hw : KS.wtT L0 + (([r1, r2] ++ [s]).map A15.Ext.w).sum ≤ 96) : False := by
  have hok : ∀ e ∈ [r1, r2], OK16 e ∧ e.ty = .R := by
    intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨h1, t1⟩
    · exact ⟨h2, t2⟩
  have hcl' := pairwise_comm hcl
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] at hv hw
  simp only [List.cons_append, List.nil_append] at hcl'
  obtain ⟨i1, i2⟩ := sumR hK hT [r1, r2] hok (by simp) (by simp; omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at i1 i2
  obtain ⟨rp1, rv1, rw1, _, r81, _⟩ := ringF hK hT h1 t1 (by omega)
  obtain ⟨rp2, rv2, rw2, _, r82, _⟩ := ringF hK hT h2 t2 (by omega)
  obtain ⟨sp, sv, sw, spos, sl⟩ := seqF hs ts
  have m0 : NR 2 (r1.w + r2.w) ≤ NR 2 (r1.w + r2.w) := le_rfl
  have k1 : PS.linksT L0 ≤ 1 := by
    by_contra hc
    obtain ⟨b0, a6⟩ := kb hK h0 hl0 (lo := 2) (by omega) (by omega)
    have b1 := item_S hK hs ts (lo := 0) (by omega) (by omega)
    have m1 : IS 0 s.w ≤ IS 0 (96 - KS.wtT L0 - (r1.w + r2.w)) :=
      IS_mono (by omega) (by omega) (by omega)
    have c := chk2_spec fT7a (a := KS.wtT L0) (b := r1.w + r2.w) (by omega) a6 (by omega) (by omega)
    omega
  have s1 : PS.linksT s.L ≤ 1 := by
    by_contra hc
    obtain ⟨b0, _⟩ := kb hK h0 hl0 (lo := 0) (by omega) (by omega)
    have b1 := item_S hK hs ts (lo := 2) (by omega) (by omega)
    have m1 : IS 2 s.w ≤ IS 2 (96 - KS.wtT L0 - (r1.w + r2.w)) :=
      IS_mono (by omega) (by omega) (by omega)
    have c := chk2_spec fT7b (a := KS.wtT L0) (b := r1.w + r2.w) (by omega) (by omega) (by omega)
      (by omega)
    omega
  have hsh : KS.SharedLe [L0, s.L, r1.L, r2.L] 3 :=
    sharedLe_mk (es := [s, r1, r2]) (fun e he => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact hs
        · exact h1
        · exact h2) hcl'
      (by simp; have := h1.bor_len; have := h2.bor_len; have := hs.bor_len; omega)
  have h := hJ [L0, s.L, r1.L, r2.L]
    (.cons (A15.isPiece_seq_mono h0 k1) (.cons (A15.isPiece_seq_mono sp s1)
      (.cons ⟨rp1, by unfold K16.RNN; omega⟩ (.cons ⟨rp2, by unfold K16.RNN; omega⟩ .nil)))) hsh (by simp; omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  omega

/-- A ring and two sequences: T8, or the tables if both sequences borrow a class. -/
theorem case_RSS (hJ : K16.T8) {r s1 s2 : A15.Ext} (hr : OK16 r) (h1 : OK16 s1) (h2 : OK16 s2)
    (tr : r.ty = .R) (t1 : s1.ty ≠ .R) (t2 : s2.ty ≠ .R)
    (hcl : (KS.blocksT L0 ++ ([r] ++ [s1, s2]).flatMap A15.Ext.own).Pairwise (fun u v => ¬ u ~r v))
    (hv : 40 ≤ KS.valT L0 + (([r] ++ [s1, s2]).map A15.Ext.v).sum)
    (hw : KS.wtT L0 + (([r] ++ [s1, s2]).map A15.Ext.w).sum ≤ 96) : False := by
  have hok : ∀ e ∈ [s1, s2], OK16 e ∧ e.ty ≠ .R := by
    intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨h1, t1⟩
    · exact ⟨h2, t2⟩
  have hcl' := pairwise_comm hcl
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] at hv hw
  simp only [List.cons_append, List.nil_append] at hcl'
  obtain ⟨i1, i2⟩ := sumS hK [s1, s2] hok (by simp) (by simp; omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at i1 i2
  obtain ⟨rp, rv, rw', rpos, r8, rh⟩ := ringF hK hT hr tr (by omega)
  obtain ⟨sp1, sv1, sw1, sp1pos, _⟩ := seqF h1 t1
  obtain ⟨sp2, sv2, sw2, sp2pos, _⟩ := seqF h2 t2
  have bR := item_R hK hT hr tr (by omega)
  by_cases hAA : s1.ty = .AB ∧ s2.ty = .AB
  · obtain ⟨b0, _⟩ := kb hK h0 hl0 (lo := 0) (by omega) (by omega)
    have b1 := item_A hK h1 hAA.1 (by omega)
    have b2 := item_A hK h2 hAA.2 (by omega)
    have c2 := cNA2 (w := s1.w) (W := s2.w) (by omega) (by omega) (by omega)
    have m1 : NA2 (s1.w + s2.w) ≤ NA2 (96 - KS.wtT L0 - r.w) := NA2_mono (by omega) (by omega)
    have c := chk2_spec k1AA (a := KS.wtT L0) (b := r.w) (by omega) (by omega) (by omega) (by omega)
    omega
  have k0 : PS.linksT L0 ≤ 0 := by
    by_contra hc
    obtain ⟨b0, a6⟩ := kb hK h0 hl0 (lo := 1) (by omega) (by omega)
    have m1 : NS 2 (s1.w + s2.w) ≤ NS 2 (96 - KS.wtT L0 - r.w) :=
      NS_mono (by omega) (by omega) (by omega)
    have c := chk2_spec fT8a (a := KS.wtT L0) (b := r.w) (by omega) a6 (by omega) (by omega)
    omega
  have sk : ∀ {x y : A15.Ext}, OK16 x → x.ty ≠ .R → OK16 y → y.ty ≠ .R →
      KS.wtT L0 + (r.w + (x.w + y.w)) ≤ 96 → 40 ≤ KS.valT L0 + (r.v + (x.v + y.v)) →
      PS.linksT x.L ≤ 0 := by
    intro x y hx tx hy ty hwxy hvxy
    by_contra hc
    obtain ⟨b0, _⟩ := kb hK h0 hl0 (lo := 0) (by omega) (by omega)
    have b1 := item_S hK hx tx (lo := 1) (by omega) (by omega)
    have b2 := item_S hK hy ty (lo := 0) (by omega) (by omega)
    have hpx := hx.pos
    have hpy := hy.pos
    have c2 := cNS1 (w := x.w) (W := y.w) (by omega) (by omega) (by omega)
    have m1 : NS1 (x.w + y.w) ≤ NS1 (96 - KS.wtT L0 - r.w) := NS1_mono (by omega) (by omega)
    have c := chk2_spec fT8b (a := KS.wtT L0) (b := r.w) (by omega) (by omega) (by omega)
      (by omega)
    omega
  have l1 := sk h1 t1 h2 t2 (by omega) (by omega)
  have l2 := sk h2 t2 h1 t1 (by omega) (by omega)
  have hB : s1.bor.length + s2.bor.length ≤ 1 := by
    have a1 := h1.bor_len
    have a2 := h2.bor_len
    by_cases e1 : s1.ty = .E
    · have := bor_E0 h1 e1
      omega
    · by_cases e2 : s2.ty = .E
      · have := bor_E0 h2 e2
        omega
      · exfalso
        apply hAA
        constructor
        · cases hh : s1.ty <;> simp_all
        · cases hh : s2.ty <;> simp_all
  have hsh : KS.SharedLe [L0, s1.L, s2.L, r.L] 2 :=
    sharedLe_mk (es := [s1, s2, r]) (fun e he => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact h1
        · exact h2
        · exact hr) hcl'
      (by simp; have := hr.bor_len; omega)
  have h := hJ [L0, s1.L, s2.L, r.L]
    (.cons (A15.isPiece_seq_mono h0 k0) (.cons (A15.isPiece_seq_mono sp1 l1)
      (.cons (A15.isPiece_seq_mono sp2 l2) (.cons ⟨rp, by unfold K16.RNN; omega⟩ .nil)))) hsh (by simp; omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  omega

/-- Four rings: T9'. -/
theorem case_RRRR (hJ : K16.T9) {r1 r2 r3 r4 : A15.Ext} (h1 : OK16 r1) (h2 : OK16 r2)
    (h3 : OK16 r3) (h4 : OK16 r4) (t1 : r1.ty = .R) (t2 : r2.ty = .R) (t3 : r3.ty = .R)
    (t4 : r4.ty = .R)
    (hcl : (KS.blocksT L0 ++ ([r1, r2, r3, r4] ++ []).flatMap A15.Ext.own).Pairwise
      (fun u v => ¬ u ~r v))
    (hv : 40 ≤ KS.valT L0 + (([r1, r2, r3, r4] ++ []).map A15.Ext.v).sum)
    (hw : KS.wtT L0 + (([r1, r2, r3, r4] ++ []).map A15.Ext.w).sum ≤ 96) : False := by
  have hok : ∀ e ∈ [r1, r2, r3, r4], OK16 e ∧ e.ty = .R := by
    intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨h1, t1⟩
    · exact ⟨h2, t2⟩
    · exact ⟨h3, t3⟩
    · exact ⟨h4, t4⟩
  simp only [List.append_nil] at hv hw hcl
  obtain ⟨i1, i2⟩ := sumR hK hT [r1, r2, r3, r4] hok (by simp) (by simp at hw ⊢; omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hv hw i1 i2
  obtain ⟨rp1, rv1, rw1, _, r81, _⟩ := ringF hK hT h1 t1 (by omega)
  obtain ⟨rp2, rv2, rw2, _, r82, _⟩ := ringF hK hT h2 t2 (by omega)
  obtain ⟨rp3, rv3, rw3, _, r83, _⟩ := ringF hK hT h3 t3 (by omega)
  obtain ⟨rp4, rv4, rw4, _, r84, _⟩ := ringF hK hT h4 t4 (by omega)
  have hs : PS.linksT L0 ≤ 0 := by
    by_contra hc
    obtain ⟨b0, a6⟩ := kb hK h0 hl0 (lo := 1) (by omega) (by omega)
    have m1 : NR 4 (r1.w + (r2.w + (r3.w + r4.w))) ≤ NR 4 (96 - KS.wtT L0) :=
      NR_mono (by omega) (by omega) (by omega)
    have c := chk1_spec fT9 (a := KS.wtT L0) (by omega) a6 (by omega)
    omega
  have hsh : KS.SharedLe [L0, r1.L, r2.L, r3.L, r4.L] 4 :=
    sharedLe_mk (es := [r1, r2, r3, r4]) (fun e he => (hok e he).1) hcl
      (by simp; have := h1.bor_len; have := h2.bor_len; have := h3.bor_len; have := h4.bor_len; omega)
  have h := hJ [L0, r1.L, r2.L, r3.L, r4.L]
    (.cons (A15.isPiece_seq_mono h0 hs) (.cons ⟨rp1, r81, by unfold K16.RNN; omega⟩ (.cons ⟨rp2, r82, by unfold K16.RNN; omega⟩
      (.cons ⟨rp3, r83, by unfold K16.RNN; omega⟩ (.cons ⟨rp4, r84, by unfold K16.RNN; omega⟩ .nil))))) hsh (by simp; omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  omega

/-- Rings and sequences that the tables exclude: `nr` rings with `ns` sequences. -/
theorem case_kill {Rs Ss : List A15.Ext} (hR : ∀ e ∈ Rs, OK16 e ∧ e.ty = .R)
    (hS : ∀ e ∈ Ss, OK16 e ∧ e.ty ≠ .R)
    (hk : (Rs.length = 3 ∧ Ss.length = 1) ∨ (Rs.length = 2 ∧ Ss.length = 2) ∨
      (Rs.length = 1 ∧ Ss.length = 3) ∨ (Rs.length = 0 ∧ Ss.length = 4))
    (hv : 40 ≤ KS.valT L0 + ((Rs ++ Ss).map A15.Ext.v).sum)
    (hw : KS.wtT L0 + ((Rs ++ Ss).map A15.Ext.w).sum ≤ 96) : False := by
  rw [List.map_append, List.sum_append] at hv
  rw [List.map_append, List.sum_append] at hw
  obtain ⟨i1, i2⟩ := sumR hK hT Rs hR (by omega) (by omega)
  obtain ⟨j1, j2⟩ := sumS hK Ss hS (by omega) (by omega)
  obtain ⟨b0, _⟩ := kb hK h0 hl0 (lo := 0) (by omega) (by omega)
  generalize hWR : (Rs.map A15.Ext.w).sum = WR at *
  generalize hWS : (Ss.map A15.Ext.w).sum = WS at *
  rcases hk with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · rw [a] at i1 i2
    rw [b] at j1 j2
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.mp b
    have hs := hS s List.mem_cons_self
    have b1 := item_S hK hs.1 hs.2 (lo := 0) (by omega) (by simp at hWS; omega)
    simp at hWS j1
    have m1 : IS 0 s.w ≤ IS 0 (96 - KS.wtT L0 - WR) := IS_mono (by omega) (by omega) (by omega)
    have c := chk2_spec k31 (a := KS.wtT L0) (b := WR) (by omega) (by omega) (by omega) (by omega)
    simp at hv
    omega
  · rw [a] at i1 i2
    rw [b] at j1 j2
    have m1 : NS 2 WS ≤ NS 2 (96 - KS.wtT L0 - WR) := NS_mono (by omega) (by omega) (by omega)
    have c := chk2_spec k22 (a := KS.wtT L0) (b := WR) (by omega) (by omega) (by omega) (by omega)
    omega
  · rw [a] at i1 i2
    rw [b] at j1 j2
    have m0 : NR 1 WR ≤ NR 1 WR := le_rfl
    obtain ⟨r, rfl⟩ := List.length_eq_one_iff.mp a
    have hr := hR r List.mem_cons_self
    have b1 := item_R hK hT hr.1 hr.2 (by simp at hWR; omega)
    have hrp := hr.1.pos
    simp at hWR hv
    have m1 : NS 3 WS ≤ NS 3 (96 - KS.wtT L0 - r.w) := NS_mono (by omega) (by omega) (by omega)
    have c := chk2_spec k13 (a := KS.wtT L0) (b := r.w) (by omega) (by omega) (by omega) (by omega)
    omega
  · rw [b] at j1 j2
    have hR0 : Rs = [] := List.length_eq_zero_iff.mp a
    subst hR0
    simp at hWR hv
    have m1 : NS 4 WS ≤ NS 4 (96 - KS.wtT L0) := NS_mono (by omega) (by omega) (by omega)
    have c := chk1_spec k04 (a := KS.wtT L0) (by omega) (by omega) (by omega)
    omega

omit hT in
/-- Three sequences, not all of the kind that borrows nothing: the tables. -/
theorem case_SSS {s1 s2 s3 : A15.Ext} (h1 : OK16 s1) (h2 : OK16 s2) (h3 : OK16 s3)
    (t1 : s1.ty ≠ .R) (t2 : s2.ty ≠ .R) (t3 : s3.ty ≠ .R)
    (hE : ¬ (s1.ty = .E ∧ s2.ty = .E ∧ s3.ty = .E))
    (hv : 40 ≤ KS.valT L0 + (s1.v + (s2.v + s3.v)))
    (hw : KS.wtT L0 + (s1.w + (s2.w + s3.w)) ≤ 96) : False := by
  have key : ∀ {x y z : A15.Ext}, OK16 x → x.ty = .AB → OK16 y → y.ty ≠ .R → OK16 z → z.ty ≠ .R →
      40 ≤ KS.valT L0 + (x.v + (y.v + z.v)) → KS.wtT L0 + (x.w + (y.w + z.w)) ≤ 96 → False := by
    intro x y z hx tx hy ty hz tz hv' hw'
    have hok : ∀ e ∈ [y, z], OK16 e ∧ e.ty ≠ .R := by
      intro e he
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨hy, ty⟩
      · exact ⟨hz, tz⟩
    obtain ⟨j1, j2⟩ := sumS hK [y, z] hok (by simp) (by simp; omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at j1 j2
    obtain ⟨b0, _⟩ := kb hK h0 hl0 (lo := 0) (by omega) (by omega)
    have b1 := item_A hK hx tx (by omega)
    have hpx := hx.pos
    have m1 : NS 2 (y.w + z.w) ≤ NS 2 (96 - KS.wtT L0 - x.w) :=
      NS_mono (by omega) (by omega) (by omega)
    have c := chk2_spec k03 (a := KS.wtT L0) (b := x.w) (by omega) (by omega) (by omega) (by omega)
    omega
  have ab : ∀ {x : A15.Ext}, x.ty ≠ .R → x.ty ≠ .E → x.ty = .AB := by
    intro x h h'
    cases hh : x.ty <;> simp_all
  by_cases e1 : s1.ty = .E
  · by_cases e2 : s2.ty = .E
    · have e3 : s3.ty ≠ .E := fun e3 => hE ⟨e1, e2, e3⟩
      exact key h3 (ab t3 e3) h1 t1 h2 t2 (by omega) (by omega)
    · exact key h2 (ab t2 e2) h1 t1 h3 t3 (by omega) (by omega)
  · exact key h1 (ab t1 e1) h2 t2 h3 t3 hv hw

end cases

theorem countP_E_of {Ss : List A15.Ext} {s1 s2 s3 : A15.Ext} (h : Ss = [s1, s2, s3])
    (hc : Ss.countP (fun e => decide (e.ty = .E)) ≤ 2) : ¬ (s1.ty = .E ∧ s2.ty = .E ∧ s3.ty = .E) := by
  rintro ⟨a, b, c⟩
  subst h
  simp [a, b, c] at hc

/-- The items sorted: rings first, then sequences, at most four in all. -/
theorem core_sorted (hK : K16.TheoremK16) (hT : KS.TableT) (hJ : K16.Joint16)
    {L0 : List PS.TRow} (h0 : KS.IsPiece (.seq (PS.linksT L0)) L0) (hl0 : PS.linksT L0 ≤ 10)
    (Rs Ss : List A15.Ext) (hR : ∀ e ∈ Rs, OK16 e ∧ e.ty = .R) (hS : ∀ e ∈ Ss, OK16 e ∧ e.ty ≠ .R)
    (hE : Ss.countP (fun e => decide (e.ty = .E)) ≤ 2) (hlen : Rs.length + Ss.length ≤ 4)
    (hcl : (KS.blocksT L0 ++ (Rs ++ Ss).flatMap A15.Ext.own).Pairwise (fun u v => ¬ u ~r v))
    (hv : 40 ≤ KS.valT L0 + ((Rs ++ Ss).map A15.Ext.v).sum)
    (hw : KS.wtT L0 + ((Rs ++ Ss).map A15.Ext.w).sum ≤ 96) : False := by
  obtain ⟨j1, j2, j3, j4, j5, j6, j7, j8, j9⟩ := hJ
  rcases Rs with _ | ⟨r1, _ | ⟨r2, _ | ⟨r3, _ | ⟨r4, _ | ⟨r5, R'⟩⟩⟩⟩⟩ <;>
    rcases Ss with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, _ | ⟨s4, _ | ⟨s5, S'⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hlen <;> (try omega)
  · exact case_0 hK h0 hl0 (by simpa using hv) (by simpa using hw)
  · exact case_S hK h0 hl0 j1 (hS s1 (by simp)).1 (hS s1 (by simp)).2 hcl hv hw
  · exact case_SS hK h0 hl0 j5 (hS s1 (by simp)).1 (hS s2 (by simp)).1 (hS s1 (by simp)).2
      (hS s2 (by simp)).2 hcl hv hw
  · simp only [List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hv hw
    exact case_SSS hK h0 hl0 (hS s1 (by simp)).1 (hS s2 (by simp)).1 (hS s3 (by simp)).1
      (hS s1 (by simp)).2 (hS s2 (by simp)).2 (hS s3 (by simp)).2 (countP_E_of rfl hE) hv hw
  · exact case_kill hK hT h0 hl0 hR hS (by simp) hv hw
  · exact case_R hK hT h0 hl0 j2 (hR r1 (by simp)).1 (hR r1 (by simp)).2 hcl hv hw
  · exact case_RS hK hT h0 hl0 j4 (hR r1 (by simp)).1 (hS s1 (by simp)).1 (hR r1 (by simp)).2
      (hS s1 (by simp)).2 hcl hv hw
  · exact case_RSS hK hT h0 hl0 j8 (hR r1 (by simp)).1 (hS s1 (by simp)).1 (hS s2 (by simp)).1
      (hR r1 (by simp)).2 (hS s1 (by simp)).2 (hS s2 (by simp)).2 hcl hv hw
  · exact case_kill hK hT h0 hl0 hR hS (by simp) hv hw
  · exact case_RR hK hT h0 hl0 j3 (hR r1 (by simp)).1 (hR r2 (by simp)).1 (hR r1 (by simp)).2
      (hR r2 (by simp)).2 hcl hv hw
  · exact case_RRS hK hT h0 hl0 j7 (hR r1 (by simp)).1 (hR r2 (by simp)).1 (hS s1 (by simp)).1
      (hR r1 (by simp)).2 (hR r2 (by simp)).2 (hS s1 (by simp)).2 hcl hv hw
  · exact case_kill hK hT h0 hl0 hR hS (by simp) hv hw
  · exact case_RRR hK hT h0 hl0 j6 (hR r1 (by simp)).1 (hR r2 (by simp)).1 (hR r3 (by simp)).1
      (hR r1 (by simp)).2 (hR r2 (by simp)).2 (hR r3 (by simp)).2 hcl hv hw
  · exact case_kill hK hT h0 hl0 hR hS (by simp) hv hw
  · exact case_RRRR hK hT h0 hl0 j9 (hR r1 (by simp)).1 (hR r2 (by simp)).1 (hR r3 (by simp)).1
      (hR r4 (by simp)).1 (hR r1 (by simp)).2 (hR r2 (by simp)).2 (hR r3 (by simp)).2
      (hR r4 (by simp)).2 hcl hv hw

theorem filter_R_perm (es : List A15.Ext) :
    es.Perm (es.filter (fun e => decide (e.ty = .R)) ++ es.filter (fun e => !decide (e.ty = .R))) :=
  (List.filter_append_perm _ es).symm

/-- **A kernel piece and the items of a configuration do not exist** when the total value is at least
40 and the total weight at most 96, in the units of the components. -/
theorem core (hK : K16.TheoremK16) (hT : KS.TableT) (hJ : K16.Joint16) {L0 : List PS.TRow}
    (h0 : KS.IsPiece (.seq (PS.linksT L0)) L0) (hl0 : PS.linksT L0 ≤ 10) :
    ∀ es : List A15.Ext, (∀ e ∈ es, OK16 e) → es.countP (fun e => decide (e.ty = .E)) ≤ 2 →
      (KS.blocksT L0 ++ es.flatMap A15.Ext.own).Pairwise (fun u v => ¬ u ~r v) →
      40 ≤ KS.valT L0 + (es.map A15.Ext.v).sum → KS.wtT L0 + (es.map A15.Ext.w).sum ≤ 96 → False := by
  intro es hok hE hcl hv hw
  by_cases h5 : 5 ≤ es.length
  · obtain ⟨i1, i2⟩ := sumX hK hT es hok (by omega)
    have e5 : min es.length 5 = 5 := by omega
    rw [e5] at i2
    obtain ⟨b0, _⟩ := kb hK h0 hl0 (lo := 0) (by omega) (by omega)
    have m1 : NX 5 (es.map A15.Ext.w).sum ≤ NX 5 (96 - KS.wtT L0) :=
      NX_mono (by omega) (by omega) (by omega)
    have c := chk1_spec kX (a := KS.wtT L0) (by omega) (by omega) (by omega)
    omega
  have hp := filter_R_perm es
  refine core_sorted hK hT hJ h0 hl0 (es.filter (fun e => decide (e.ty = .R)))
    (es.filter (fun e => !decide (e.ty = .R))) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨h1, h2⟩ := List.mem_filter.mp he
    exact ⟨hok e h1, of_decide_eq_true h2⟩
  · intro e he
    obtain ⟨h1, h2⟩ := List.mem_filter.mp he
    refine ⟨hok e h1, ?_⟩
    simpa using h2
  · have h1 := hp.countP_eq (fun e => decide (e.ty = .E))
    rw [List.countP_append] at h1
    omega
  · have h1 := hp.length_eq
    rw [List.length_append] at h1
    omega
  · have hq : (KS.blocksT L0 ++ es.flatMap A15.Ext.own).Perm (KS.blocksT L0 ++
        (es.filter (fun e => decide (e.ty = .R)) ++
          es.filter (fun e => !decide (e.ty = .R))).flatMap A15.Ext.own) :=
      List.Perm.append_left _ (hp.flatMap_right _)
    exact (hq.pairwise_iff (fun h hr => h hr.symm)).mp hcl
  · rw [← (hp.map A15.Ext.v).sum_eq]
    exact hv
  · rw [← (hp.map A15.Ext.w).sum_eq]
    exact hw

end A16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.A16.core
