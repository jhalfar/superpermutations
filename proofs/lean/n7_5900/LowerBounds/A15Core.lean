import LowerBounds.KDefs
import LowerBounds.A15Arith

/-!
# The pieces of a configuration at defect 15 against the tables and the joint statements
(the written proof, sections 3.6, 3.7, 5.2, 5.3 and 6)

No rows of the model here: only pieces on words (`KS.IsPiece`), their values and weights.

* `Ext`: the piece behind a hanging item (or behind the second part of a kernel with excess),
  with the value `v` and the weight `w` of the component it comes from, its own blocks and the
  blocks it borrows.  Its kind `Ty` gives the shifts of Lemma PIECE: a ring (6 and 7, borrows a
  class), a sequence that borrows nothing (10 and 12), a sequence that borrows a class (11 and
  13).
* `core`: a kernel piece and pieces of hanging items with total value at least 45 and total
  weight at most 90 (in the units of the components), at most one of them of the kind that
  borrows nothing, do not exist, given Theorem K, table T' for rings and the joint statements.
  This is the knapsack, Lemma PIECE and the conclusion in one statement: by the arithmetic of
  `A15Arith.lean` the pieces are at most three and their numbers of links are those of one of
  S1 .. S5.
-/

namespace SuperpermLowerBounds
namespace A15

open T5900

/-- The kind of the piece of a hanging item: `R` a ring, `E` a sequence that borrows no class,
`AB` a sequence that borrows a class. -/
inductive Ty
  | R
  | E
  | AB
  deriving DecidableEq

/-- The shift of the value (Lemma PIECE). -/
def Ty.dv : Ty → ℤ
  | .R => 6
  | .E => 10
  | .AB => 11

/-- The shift of the weight (Lemma PIECE). -/
def Ty.dw : Ty → ℕ
  | .R => 7
  | .E => 12
  | .AB => 13

/-- The piece behind an item, with the value and weight of its component. -/
structure Ext where
  ty : Ty
  L : List PS.TRow
  own : List (List ℕ)
  bor : List (List ℕ)
  v : ℤ
  w : ℕ

/-- What the piece behind an item satisfies. -/
structure Ext.OK (e : Ext) : Prop where
  ring : e.ty = .R → KS.IsPiece .ring e.L
  seq : e.ty ≠ .R → KS.IsPiece (.seq (PS.linksT e.L)) e.L
  blocks : (KS.blocksT e.L).Perm (e.own ++ e.bor)
  bor_len : e.bor.length ≤ 1
  bor_E : e.ty = .E → e.bor = []
  val : e.v + e.ty.dv ≤ KS.valT e.L
  wt : KS.wtT e.L + e.ty.dw ≤ e.w
  pos : 1 ≤ e.v
  links : PS.linksT e.L ≤ 8

/-! ### Pieces against the tables -/

theorem isPiece_seq_mono {L : List PS.TRow} {s : ℕ} (h : KS.IsPiece (.seq (PS.linksT L)) L)
    (hs : PS.linksT L ≤ s) : KS.IsPiece (.seq s) L :=
  ⟨h.1, h.2.1, h.2.2.1, hs⟩

/-- Theorem K on a piece. -/
theorem seq_val (hK : KS.TheoremK) {L : List PS.TRow} (h : KS.IsPiece (.seq (PS.linksT L)) L)
    (h8 : PS.linksT L ≤ 8) (hw : KS.wtT L ≤ 90) :
    KS.valT L ≤ ((Dv (PS.linksT L) (KS.wtT L) : ℕ) : ℤ) := by
  unfold KS.wtT at hw
  have hcap : L.length ≤ Dc (PS.linksT L) (PS.holesT 7 L) :=
    hK (PS.linksT L) h8 L h.1 h.2.2.1 rfl (by omega)
  have e : PS.holesT 7 L + 6 * PS.linksT L - 6 * PS.linksT L = PS.holesT 7 L := by omega
  unfold KS.valT KS.wtT Dv
  rw [if_pos (by omega), e]
  generalize Dc (PS.linksT L) (PS.holesT 7 L) = d at hcap ⊢
  omega

theorem seq_le_SH (hK : KS.TheoremK) {L : List PS.TRow}
    (h : KS.IsPiece (.seq (PS.linksT L)) L) (h8 : PS.linksT L ≤ 8) {lo W : ℕ}
    (hlo : lo ≤ PS.linksT L) (hW : KS.wtT L ≤ W) (hW90 : W ≤ 90) :
    KS.valT L ≤ ((SH lo W : ℕ) : ℤ) := by
  have h1 := seq_val hK h h8 (by omega)
  have h2 : Dv (PS.linksT L) (KS.wtT L) ≤ SH lo W := Dv_le_SH hlo h8 hW hW90
  omega

/-- Table T' for rings on a piece. -/
theorem ring_le_RH (hT : KS.TableT) {L : List PS.TRow} (h : KS.IsPiece .ring L) {W : ℕ}
    (hW : KS.wtT L ≤ W) (hW84 : W ≤ 84) : KS.valT L ≤ ((RH W : ℕ) : ℤ) := by
  have hl : PS.linksT L = 0 := PS.linksT_zero h.2.1
  unfold KS.wtT at hW
  rw [hl] at hW
  have hcap : L.length ≤ Rc (PS.holesT 7 L) := hT.2 L h.1 h.2.1 h.2.2.1 h.2.2.2 (by omega)
  have h2 : Rv (PS.holesT 7 L) ≤ RH W := Rv_le_RH (by omega) hW84
  unfold Rv at h2
  unfold KS.valT
  rw [hl]
  generalize Rc (PS.holesT 7 L) = d at hcap h2
  omega

namespace Ext.OK

variable {e : Ext}

theorem dv_dw_of_ne (h : e.ty ≠ .R) : 10 ≤ e.ty.dv ∧ 12 ≤ e.ty.dw := by
  cases hty : e.ty <;> simp_all [Ty.dv, Ty.dw]

/-- The value of an item is at most the item table at its weight. -/
theorem le_HV (hK : KS.TheoremK) (hT : KS.TableT) (h : e.OK) (hw : e.w ≤ 90) :
    e.v ≤ ((HV e.w : ℕ) : ℤ) := by
  have c := cHV e.w hw
  have hval := h.val
  have hwt := h.wt
  rcases hty : e.ty with _ | _ | _
  · rw [hty] at hval hwt
    simp only [Ty.dv, Ty.dw] at hval hwt
    have b := ring_le_RH hT (h.ring hty) (W := e.w - 7) (by omega) (by omega)
    have c1 := c.1 (by omega)
    omega
  · have hne : e.ty ≠ .R := by rw [hty]; exact fun h => Ty.noConfusion h
    rw [hty] at hval hwt
    simp only [Ty.dv, Ty.dw] at hval hwt
    have b := seq_le_SH hK (h.seq hne) h.links (lo := 0) (W := e.w - 12) (by omega) (by omega)
      (by omega)
    have c1 := c.2.1 (by omega)
    omega
  · have hne : e.ty ≠ .R := by rw [hty]; exact fun h => Ty.noConfusion h
    rw [hty] at hval hwt
    simp only [Ty.dv, Ty.dw] at hval hwt
    have b := seq_le_SH hK (h.seq hne) h.links (lo := 0) (W := e.w - 13) (by omega) (by omega)
      (by omega)
    have c1 := c.2.2 (by omega)
    omega

end Ext.OK

/-- Hanging items: their total value is at most `Hn` of their number and their total weight. -/
theorem sum_le_Hn (hK : KS.TheoremK) (hT : KS.TableT) : ∀ es : List Ext, (∀ e ∈ es, e.OK) →
    (es.map Ext.w).sum ≤ 90 →
    (es.length : ℤ) ≤ (es.map Ext.v).sum ∧
      (es.map Ext.v).sum ≤ ((Hn (min es.length 3) (es.map Ext.w).sum : ℕ) : ℤ)
  | [], _, _ => by
      simp only [List.length_nil, List.map_nil, List.sum_nil, Nat.cast_zero]
      exact ⟨le_refl _, Int.natCast_nonneg _⟩
  | e :: es, hes, hW => by
      rw [List.map_cons, List.sum_cons] at hW
      obtain ⟨i1, i2⟩ := sum_le_Hn hK hT es (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
        (by omega)
      have he := hes e List.mem_cons_self
      have hv := he.le_HV hK hT (by omega)
      have hpos := he.pos
      have hguard : min es.length 3 = 0 ∨ 1 ≤ Hn (min es.length 3) (es.map Ext.w).sum := by
        rcases Nat.eq_zero_or_pos es.length with h0 | h0
        · left
          rw [h0]
          rfl
        · right
          have : (1 : ℤ) ≤ (es.length : ℤ) := by exact_mod_cast h0
          omega
      have hc := cHn (min es.length 3) e.w (es.map Ext.w).sum (by omega) hW (by omega) hguard
      have e1 : min (min es.length 3 + 1) 3 = min (es.length + 1) 3 := by omega
      rw [e1] at hc
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      constructor <;> omega

/-! ### Shared classes and the joint statements -/

theorem perm4 {α : Type} [DecidableEq α] (a b c d : List α) :
    ((a ++ b) ++ (c ++ d)).Perm ((a ++ c) ++ (b ++ d)) := by
  rw [List.perm_iff_count]
  intro x
  simp only [List.count_append]
  omega

theorem shared2 {L0 L1 : List PS.TRow} {own bor : List (List ℕ)}
    (hb : (KS.blocksT L1).Perm (own ++ bor))
    (hcl : (KS.blocksT L0 ++ own).Pairwise (fun u v => ¬ u ~r v)) {B : ℕ} (hB : bor.length ≤ B) :
    KS.SharedLe [L0, L1] B := by
  refine ⟨KS.blocksT L0 ++ own, bor, ?_, hB, hcl⟩
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.append_assoc]
  exact List.Perm.append_left _ hb

theorem shared3 {L0 L1 L2 : List PS.TRow} {o1 b1 o2 b2 : List (List ℕ)}
    (h1 : (KS.blocksT L1).Perm (o1 ++ b1)) (h2 : (KS.blocksT L2).Perm (o2 ++ b2))
    (hcl : (KS.blocksT L0 ++ (o1 ++ o2)).Pairwise (fun u v => ¬ u ~r v)) {B : ℕ}
    (hB : b1.length + b2.length ≤ B) : KS.SharedLe [L0, L1, L2] B := by
  refine ⟨KS.blocksT L0 ++ (o1 ++ o2), b1 ++ b2, ?_, by rw [List.length_append]; exact hB, hcl⟩
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.append_assoc]
  exact List.Perm.append_left _ ((h1.append h2).trans (perm4 o1 b1 o2 b2))

theorem J2 {k0 k1 : KS.Kind} {V : ℤ} {W B : ℕ} (hJ : KS.J [k0, k1] V W B) {L0 L1 : List PS.TRow}
    (p0 : KS.IsPiece k0 L0) (p1 : KS.IsPiece k1 L1) (hsh : KS.SharedLe [L0, L1] B)
    (hw : KS.wtT L0 + KS.wtT L1 ≤ W) : KS.valT L0 + KS.valT L1 < V := by
  have h := hJ [L0, L1] (.cons p0 (.cons p1 .nil)) hsh
    (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]; exact hw)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  exact h

theorem J3 {k0 k1 k2 : KS.Kind} {V : ℤ} {W B : ℕ} (hJ : KS.J [k0, k1, k2] V W B)
    {L0 L1 L2 : List PS.TRow} (p0 : KS.IsPiece k0 L0) (p1 : KS.IsPiece k1 L1)
    (p2 : KS.IsPiece k2 L2) (hsh : KS.SharedLe [L0, L1, L2] B)
    (hw : KS.wtT L0 + (KS.wtT L1 + KS.wtT L2) ≤ W) :
    KS.valT L0 + (KS.valT L1 + KS.valT L2) < V := by
  have h := hJ [L0, L1, L2] (.cons p0 (.cons p1 (.cons p2 .nil))) hsh
    (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]; exact hw)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  exact h

/-! ### The cases -/

section cases

variable (hK : KS.TheoremK) (hT : KS.TableT) (hJ : KS.Joint) {L0 : List PS.TRow}
  (h0 : KS.IsPiece (.seq (PS.linksT L0)) L0) (hl0 : PS.linksT L0 ≤ 8)

include hK hT hJ h0 hl0

/-- One hanging item, a ring: S2. -/
theorem core_R {e : Ext} (he : e.OK) (hty : e.ty = .R)
    (hcl : (KS.blocksT L0 ++ e.own).Pairwise (fun u v => ¬ u ~r v))
    (hv : 45 ≤ KS.valT L0 + e.v) (hw : KS.wtT L0 + e.w ≤ 90) : False := by
  have hval := he.val
  have hwt := he.wt
  rw [hty] at hval hwt
  simp only [Ty.dv, Ty.dw] at hval hwt
  have hs : PS.linksT L0 ≤ 5 := by
    by_contra hcon
    have b0 := seq_le_SH hK h0 hl0 (lo := 6) (W := KS.wtT L0) (by omega) (le_refl _) (by omega)
    have b1 := ring_le_RH hT (he.ring hty) (W := 83 - KS.wtT L0) (by omega) (by omega)
    have c := c1R (KS.wtT L0) (by omega)
    omega
  have h := J2 hJ.2.1 (isPiece_seq_mono h0 hs) (he.ring hty)
    (shared2 he.blocks hcl he.bor_len) (by omega)
  omega

omit hT in
/-- One hanging item, a sequence: S1. -/
theorem core_S {e : Ext} (he : e.OK) (hty : e.ty ≠ .R)
    (hcl : (KS.blocksT L0 ++ e.own).Pairwise (fun u v => ¬ u ~r v))
    (hv : 45 ≤ KS.valT L0 + e.v) (hw : KS.wtT L0 + e.w ≤ 90) : False := by
  have hval := he.val
  have hwt := he.wt
  obtain ⟨d1, d2⟩ := Ext.OK.dv_dw_of_ne hty
  have hs : PS.linksT L0 ≤ 4 := by
    by_contra hcon
    have b0 := seq_le_SH hK h0 hl0 (lo := 5) (W := KS.wtT L0) (by omega) (le_refl _) (by omega)
    have b1 := seq_le_SH hK (he.seq hty) he.links (lo := 0) (W := 78 - KS.wtT L0) (by omega)
      (by omega) (by omega)
    have c := c1S (KS.wtT L0) (by omega)
    omega
  have ht : PS.linksT e.L ≤ 4 := by
    by_contra hcon
    have b0 := seq_le_SH hK h0 hl0 (lo := 0) (W := 78 - KS.wtT e.L) (by omega) (by omega)
      (by omega)
    have b1 := seq_le_SH hK (he.seq hty) he.links (lo := 5) (W := KS.wtT e.L) (by omega)
      (le_refl _) (by omega)
    have c := c1S (KS.wtT e.L) (by omega)
    omega
  have h := J2 hJ.1 (isPiece_seq_mono h0 hs) (isPiece_seq_mono (he.seq hty) ht)
    (shared2 he.blocks hcl he.bor_len) (by omega)
  omega

/-- Two hanging items, both rings: S3. -/
theorem core_RR {e1 e2 : Ext} (he1 : e1.OK) (he2 : e2.OK) (hty1 : e1.ty = .R) (hty2 : e2.ty = .R)
    (hcl : (KS.blocksT L0 ++ (e1.own ++ e2.own)).Pairwise (fun u v => ¬ u ~r v))
    (hv : 45 ≤ KS.valT L0 + (e1.v + e2.v)) (hw : KS.wtT L0 + (e1.w + e2.w) ≤ 90) : False := by
  have hval1 := he1.val
  have hwt1 := he1.wt
  have hval2 := he2.val
  have hwt2 := he2.wt
  rw [hty1] at hval1 hwt1
  rw [hty2] at hval2 hwt2
  simp only [Ty.dv, Ty.dw] at hval1 hwt1 hval2 hwt2
  have hs : PS.linksT L0 ≤ 2 := by
    by_contra hcon
    have b0 := seq_le_SH hK h0 hl0 (lo := 3) (W := KS.wtT L0) (by omega) (le_refl _) (by omega)
    have b1 := ring_le_RH hT (he1.ring hty1) (W := KS.wtT e1.L) (le_refl _) (by omega)
    have b2 := ring_le_RH hT (he2.ring hty2) (W := 76 - KS.wtT L0 - KS.wtT e1.L) (by omega)
      (by omega)
    have c := cRR (KS.wtT L0) (KS.wtT e1.L) (by omega)
    omega
  have h := J3 hJ.2.2.1 (isPiece_seq_mono h0 hs) (he1.ring hty1) (he2.ring hty2)
    (shared3 he1.blocks he2.blocks hcl (by have := he1.bor_len; have := he2.bor_len; omega))
    (by omega)
  omega

/-- Two hanging items, a sequence that borrows nothing and a ring: S4. -/
theorem core_ER {e1 e2 : Ext} (he1 : e1.OK) (he2 : e2.OK) (hty1 : e1.ty = .E) (hty2 : e2.ty = .R)
    (hcl : (KS.blocksT L0 ++ (e1.own ++ e2.own)).Pairwise (fun u v => ¬ u ~r v))
    (hv : 45 ≤ KS.valT L0 + (e1.v + e2.v)) (hw : KS.wtT L0 + (e1.w + e2.w) ≤ 90) : False := by
  have hne : e1.ty ≠ .R := by rw [hty1]; exact fun h => Ty.noConfusion h
  have hval1 := he1.val
  have hwt1 := he1.wt
  have hval2 := he2.val
  have hwt2 := he2.wt
  rw [hty1] at hval1 hwt1
  rw [hty2] at hval2 hwt2
  simp only [Ty.dv, Ty.dw] at hval1 hwt1 hval2 hwt2
  have hs : PS.linksT L0 ≤ 1 := by
    by_contra hcon
    have b0 := seq_le_SH hK h0 hl0 (lo := 2) (W := KS.wtT L0) (by omega) (le_refl _) (by omega)
    have b1 := seq_le_SH hK (he1.seq hne) he1.links (lo := 0) (W := KS.wtT e1.L) (by omega)
      (le_refl _) (by omega)
    have b2 := ring_le_RH hT (he2.ring hty2) (W := 71 - KS.wtT L0 - KS.wtT e1.L) (by omega)
      (by omega)
    have c := cRE (KS.wtT L0) (KS.wtT e1.L) (by omega)
    omega
  have ht : PS.linksT e1.L ≤ 1 := by
    by_contra hcon
    have b0 := seq_le_SH hK h0 hl0 (lo := 0) (W := KS.wtT L0) (by omega) (le_refl _) (by omega)
    have b1 := seq_le_SH hK (he1.seq hne) he1.links (lo := 2) (W := KS.wtT e1.L) (by omega)
      (le_refl _) (by omega)
    have b2 := ring_le_RH hT (he2.ring hty2) (W := 71 - KS.wtT e1.L - KS.wtT L0) (by omega)
      (by omega)
    have c := cRE (KS.wtT e1.L) (KS.wtT L0) (by omega)
    omega
  have hb1 : e1.bor.length = 0 := by rw [he1.bor_E hty1]; rfl
  have h := J3 hJ.2.2.2.1 (isPiece_seq_mono h0 hs) (isPiece_seq_mono (he1.seq hne) ht)
    (he2.ring hty2)
    (shared3 he1.blocks he2.blocks hcl (by have := he2.bor_len; omega)) (by omega)
  omega

/-- Two hanging items, a sequence that borrows a class and a ring: S5. -/
theorem core_ABR {e1 e2 : Ext} (he1 : e1.OK) (he2 : e2.OK) (hty1 : e1.ty = .AB)
    (hty2 : e2.ty = .R)
    (hcl : (KS.blocksT L0 ++ (e1.own ++ e2.own)).Pairwise (fun u v => ¬ u ~r v))
    (hv : 45 ≤ KS.valT L0 + (e1.v + e2.v)) (hw : KS.wtT L0 + (e1.w + e2.w) ≤ 90) : False := by
  have hne : e1.ty ≠ .R := by rw [hty1]; exact fun h => Ty.noConfusion h
  have hval1 := he1.val
  have hwt1 := he1.wt
  have hval2 := he2.val
  have hwt2 := he2.wt
  have hp1 := he1.pos
  have hp2 := he2.pos
  rw [hty1] at hval1 hwt1
  rw [hty2] at hval2 hwt2
  simp only [Ty.dv, Ty.dw] at hval1 hwt1 hval2 hwt2
  have b2 := ring_le_RH hT (he2.ring hty2) (W := 70 - KS.wtT L0 - KS.wtT e1.L) (by omega)
    (by omega)
  have hs : PS.linksT L0 ≤ 0 := by
    by_contra hcon
    have b0 := seq_le_SH hK h0 hl0 (lo := 1) (W := KS.wtT L0) (by omega) (le_refl _) (by omega)
    have b1 := seq_le_SH hK (he1.seq hne) he1.links (lo := 0) (W := KS.wtT e1.L) (by omega)
      (le_refl _) (by omega)
    have c := cRABa (KS.wtT L0) (KS.wtT e1.L) (by omega) (by omega) (by omega)
    omega
  have ht : PS.linksT e1.L ≤ 0 := by
    by_contra hcon
    have b0 := seq_le_SH hK h0 hl0 (lo := 0) (W := KS.wtT L0) (by omega) (le_refl _) (by omega)
    have b1 := seq_le_SH hK (he1.seq hne) he1.links (lo := 1) (W := KS.wtT e1.L) (by omega)
      (le_refl _) (by omega)
    have c := cRABb (KS.wtT L0) (KS.wtT e1.L) (by omega) (by omega) (by omega)
    omega
  have h := J3 hJ.2.2.2.2 (isPiece_seq_mono h0 hs) (isPiece_seq_mono (he1.seq hne) ht)
    (he2.ring hty2)
    (shared3 he1.blocks he2.blocks hcl (by have := he1.bor_len; have := he2.bor_len; omega))
    (by omega)
  omega

omit hT hJ in
/-- Two hanging items, both sequences, not both of the kind that borrows nothing: the tables. -/
theorem core_SS {e1 e2 : Ext} (he1 : e1.OK) (he2 : e2.OK) (hty1 : e1.ty ≠ .R) (hty2 : e2.ty ≠ .R)
    (hE : ¬ (e1.ty = .E ∧ e2.ty = .E))
    (hv : 45 ≤ KS.valT L0 + (e1.v + e2.v)) (hw : KS.wtT L0 + (e1.w + e2.w) ≤ 90) : False := by
  have hval1 := he1.val
  have hwt1 := he1.wt
  have hval2 := he2.val
  have hwt2 := he2.wt
  have hd : 21 ≤ e1.ty.dv + e2.ty.dv ∧ 25 ≤ e1.ty.dw + e2.ty.dw := by
    cases h1 : e1.ty <;> cases h2 : e2.ty <;> simp_all [Ty.dv, Ty.dw]
  obtain ⟨d1, d2⟩ := hd
  have b0 := seq_le_SH hK h0 hl0 (lo := 0) (W := KS.wtT L0) (by omega) (le_refl _) (by omega)
  have b1 := seq_le_SH hK (he1.seq hty1) he1.links (lo := 0) (W := KS.wtT e1.L) (by omega)
    (le_refl _) (by omega)
  have b2 := seq_le_SH hK (he2.seq hty2) he2.links (lo := 0)
    (W := 65 - KS.wtT L0 - KS.wtT e1.L) (by omega) (by omega) (by omega)
  have c := cSSS (KS.wtT L0) (KS.wtT e1.L) (by omega)
  omega

end cases

theorem pairwise_swap {a b c : List (List ℕ)}
    (h : (a ++ (b ++ c)).Pairwise (fun u v => ¬ u ~r v)) :
    (a ++ (c ++ b)).Pairwise (fun u v => ¬ u ~r v) :=
  ((List.Perm.append_left a (List.perm_append_comm (l₁ := c) (l₂ := b))).pairwise_iff
    (fun h hr => h hr.symm)).mpr h

/-- **A kernel piece and the pieces of hanging items do not exist** when the total value is at
least 45 and the total weight at most 90, in the units of the components. -/
theorem core (hK : KS.TheoremK) (hT : KS.TableT) (hJ : KS.Joint) {L0 : List PS.TRow}
    (h0 : KS.IsPiece (.seq (PS.linksT L0)) L0) (hl0 : PS.linksT L0 ≤ 8) :
    ∀ es : List Ext, (∀ e ∈ es, e.OK) → es.countP (fun e => decide (e.ty = .E)) ≤ 1 →
      (KS.blocksT L0 ++ es.flatMap Ext.own).Pairwise (fun u v => ¬ u ~r v) →
      45 ≤ KS.valT L0 + (es.map Ext.v).sum → KS.wtT L0 + (es.map Ext.w).sum ≤ 90 → False
  | [], _, _, _, hv, hw => by
      simp only [List.map_nil, List.sum_nil, add_zero] at hv hw
      have b0 := seq_le_SH hK h0 hl0 (lo := 0) (W := 90) (by omega) hw (le_refl _)
      have c := cK
      omega
  | [e], hes, _, hcl, hv, hw => by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.flatMap_cons, List.flatMap_nil, List.append_nil] at hv hw hcl
      have he := hes e List.mem_cons_self
      by_cases hty : e.ty = .R
      · exact core_R hK hT hJ h0 hl0 he hty hcl hv hw
      · exact core_S hK hJ h0 hl0 he hty hcl hv hw
  | [e1, e2], hes, hE, hcl, hv, hw => by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.flatMap_cons, List.flatMap_nil, List.append_nil] at hv hw hcl
      have he1 := hes e1 List.mem_cons_self
      have he2 := hes e2 (List.mem_cons_of_mem _ List.mem_cons_self)
      have hv' : 45 ≤ KS.valT L0 + (e2.v + e1.v) := by omega
      have hw' : KS.wtT L0 + (e2.w + e1.w) ≤ 90 := by omega
      have hcl' := pairwise_swap hcl
      by_cases h1 : e1.ty = .R
      · by_cases h2 : e2.ty = .R
        · exact core_RR hK hT hJ h0 hl0 he1 he2 h1 h2 hcl hv hw
        · rcases h2' : e2.ty with _ | _ | _
          · exact absurd h2' h2
          · exact core_ER hK hT hJ h0 hl0 he2 he1 h2' h1 hcl' hv' hw'
          · exact core_ABR hK hT hJ h0 hl0 he2 he1 h2' h1 hcl' hv' hw'
      · by_cases h2 : e2.ty = .R
        · rcases h1' : e1.ty with _ | _ | _
          · exact absurd h1' h1
          · exact core_ER hK hT hJ h0 hl0 he1 he2 h1' h2 hcl hv hw
          · exact core_ABR hK hT hJ h0 hl0 he1 he2 h1' h2 hcl hv hw
        · refine core_SS hK h0 hl0 he1 he2 h1 h2 ?_ hv hw
          rintro ⟨g1, g2⟩
          simp [g1, g2] at hE
  | e1 :: e2 :: e3 :: rest, hes, _, _, hv, hw => by
      obtain ⟨i1, i2⟩ := sum_le_Hn hK hT (e1 :: e2 :: e3 :: rest) hes (by omega)
      have e : min (e1 :: e2 :: e3 :: rest).length 3 = 3 := by
        simp only [List.length_cons]
        omega
      rw [e] at i2
      have h3 : (3 : ℤ) ≤ ((e1 :: e2 :: e3 :: rest).length : ℤ) := by
        simp only [List.length_cons]
        push_cast
        omega
      have b0 := seq_le_SH hK h0 hl0 (lo := 0) (W := KS.wtT L0) (by omega) (le_refl _) (by omega)
      have hm := Hn3_mono (a := ((e1 :: e2 :: e3 :: rest).map Ext.w).sum) (b := 90 - KS.wtT L0)
        (by omega) (by omega)
      have c := cK3 (KS.wtT L0) (by omega) (by omega)
      omega

end A15
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.A15.core
