import LowerBounds.J15Rules
import LowerBounds.KPot

/-!
# Classes of objects and the normal form of a counterexample (the written proof, 4.1 to 4.4)

A kind of piece of a run is a triple of 5,900 `(c, lo, hi)` (`c = 0` a ring with `lo … hi` holes,
`c = s + 1` a sequence with at most `s` links) together with a range `(vlo, vhi)` of the value of
the ring (the class of section 4.1; ignored for a sequence piece).  `JV k qs V W B` is the joint
statement for the objects of this class.

`exists_nf`: if `JV` fails, there is a counterexample (rings read in the rotation of the cycle
lemma) with the fewest rows among all such counterexamples that

* starts at the word `1 2 … k` (renaming the symbols),
* is sorted by value on the pair of pieces `oi`, `oi + 1` of equal kind (Rule ORD, section 4.4),
* has `delta ≥ 0` on the sequence piece `rp` (Rule PREV, section 4.3: Lemma JRV and Lemma PREV;
  `KS.Good` is `m + M ≥ phi_T`).

Lemma L1 is the fact that each step keeps the class: the class is a condition on the holes and
the value of each ring, and every step keeps them.  The order of the steps: fewest rows, sort,
reverse every piece (if `delta < 0`), read the rings again in the rotation of the cycle lemma,
rename.  Every step keeps the number of rows, so the result has the fewest rows.
-/

namespace SuperpermLowerBounds
namespace J16

open S (PermW WLink DoorEq)
open PS (TRow IsSeq holesT linksT Closes relabSeq)
open J15 (valK wtK IsPieceW IsPieceC Cyc Sh blocksR clsCount clsCount_perm norm1 blocksR_append
  pieceC_relab flatten_relab blocksR_relab clsCount_map length_relab valK_relab wtK_relab
  holesT_relab linksT_relab forall₂_mem)
open KS (rho revA Good phiAt)

variable {k : ℕ}

/-! ### Classes -/

/-- A kind of piece of a run: the triple of 5,900 and the value range of a ring. -/
abbrev Q := (ℕ × ℕ × ℕ) × (ℤ × ℤ)

/-- The default kind. -/
def dq : Q := ((0, 0, 0), (0, 0))

/-- A piece of the kind `q.1` whose value lies in `q.2` if it is a ring. -/
def IsPieceV (k : ℕ) (q : Q) (L : List TRow) : Prop :=
  IsPieceW k q.1 L ∧ (q.1.1 = 0 → q.2.1 ≤ valK k L ∧ valK k L ≤ q.2.2)

/-- The same, a ring being read in the rotation of the cycle lemma. -/
def IsPieceCV (k : ℕ) (q : Q) (L : List TRow) : Prop := IsPieceV k q L ∧ (q.1.1 = 0 → Cyc k L)

/-- The joint statement on the class. -/
def JV (k : ℕ) (qs : List Q) (V : ℤ) (W B : ℕ) : Prop :=
  ∀ Ls : List (List TRow), List.Forall₂ (IsPieceV k) qs Ls → Sh B Ls →
    (Ls.map (wtK k)).sum ≤ W → (Ls.map (valK k)).sum < V

/-- A counterexample in the class. -/
def CEV (k : ℕ) (qs : List Q) (V : ℤ) (W B : ℕ) (Ls : List (List TRow)) : Prop :=
  List.Forall₂ (IsPieceCV k) qs Ls ∧ Sh B Ls ∧ (Ls.map (wtK k)).sum ≤ W ∧
    V ≤ (Ls.map (valK k)).sum

theorem IsPieceCV.toC {q : Q} {L : List TRow} (h : IsPieceCV k q L) : IsPieceC k q.1 L :=
  ⟨h.1.1, h.2⟩

/-! ### Rings in the rotation of the cycle lemma -/

theorem normV1 (q : Q) (L : List TRow) (h : IsPieceV k q L) :
    ∃ L', IsPieceCV k q L' ∧ L'.Perm L ∧ wtK k L' = wtK k L ∧ valK k L' = valK k L ∧
      (q.1.1 ≠ 0 → L' = L) := by
  by_cases h0 : q.1.1 = 0
  · obtain ⟨L', h1, h2, h3, h4⟩ := norm1 q.1 L h.1
    refine ⟨L', ⟨⟨h1.1, fun h0' => by rw [h4]; exact h.2 h0'⟩, h1.2⟩, h2, h3, h4,
      fun h' => absurd h0 h'⟩
  · exact ⟨L, ⟨h, fun h' => absurd h' h0⟩, List.Perm.refl _, rfl, rfl, fun _ => rfl⟩

theorem normV : ∀ (qs : List Q) (Ls : List (List TRow)), List.Forall₂ (IsPieceV k) qs Ls →
    ∃ Ls', List.Forall₂ (IsPieceCV k) qs Ls' ∧
      (blocksR Ls'.flatten).Perm (blocksR Ls.flatten) ∧ Ls'.map (wtK k) = Ls.map (wtK k) ∧
      Ls'.map (valK k) = Ls.map (valK k) ∧ Ls'.flatten.length = Ls.flatten.length ∧
      (∀ i, (qs.getD i dq).1.1 ≠ 0 → Ls'.getD i [] = Ls.getD i []) ∧
      ∀ i, valK k (Ls'.getD i []) = valK k (Ls.getD i []) := by
  intro qs Ls h
  induction h with
  | nil => exact ⟨[], List.Forall₂.nil, List.Perm.refl _, rfl, rfl, rfl, fun _ _ => rfl,
      fun _ => rfl⟩
  | @cons q L qs' Ps hpl _ ih =>
    obtain ⟨L', h1, h2, h3, h4, h5⟩ := normV1 q L hpl
    obtain ⟨Ls', g1, g2, g3, g4, g5, g6, g7⟩ := ih
    refine ⟨L' :: Ls', List.Forall₂.cons h1 g1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (blocksR (L' ++ Ls'.flatten)).Perm (blocksR (L ++ Ps.flatten))
      rw [blocksR_append, blocksR_append]
      exact ((h2.map Prod.snd).flatten).append g2
    · simp only [List.map_cons, h3, g3]
    · simp only [List.map_cons, h4, g4]
    · simp only [List.flatten_cons, List.length_append, g5, h2.length_eq]
    · intro i hi
      cases i with
      | zero => exact h5 hi
      | succ i => exact g6 i hi
    · intro i
      cases i with
      | zero => exact h4
      | succ i => exact g7 i

open Classical in
/-- A counterexample with the fewest rows. -/
theorem exists_minV {qs : List Q} {V : ℤ} {W B : ℕ} (h : ∃ Ls, CEV k qs V W B Ls) :
    ∃ Ls, CEV k qs V W B Ls ∧
      ∀ Ls', CEV k qs V W B Ls' → Ls.flatten.length ≤ Ls'.flatten.length := by
  have hex : ∃ n, ∃ Ls, CEV k qs V W B Ls ∧ Ls.flatten.length = n := by
    obtain ⟨Ls, hLs⟩ := h
    exact ⟨_, Ls, hLs, rfl⟩
  obtain ⟨Ls, hce, hn⟩ := Nat.find_spec hex
  refine ⟨Ls, hce, fun Ls' h' => ?_⟩
  rw [hn]
  exact Nat.find_min' hex ⟨Ls', h', rfl⟩

/-! ### Rule ORD: exchanging two pieces of equal kind -/

theorem forall₂_split3 {α β : Type} {R : α → β → Prop} : ∀ (oi : ℕ) (qs : List α)
    (Ls : List β), List.Forall₂ R qs Ls → oi + 1 < qs.length →
    ∃ qa q1 q2 qc A X Y C, qs = qa ++ q1 :: q2 :: qc ∧ Ls = A ++ X :: Y :: C ∧
      qa.length = oi ∧ A.length = oi ∧ List.Forall₂ R qa A ∧ R q1 X ∧ R q2 Y ∧
      List.Forall₂ R qc C
  | 0, _, _, List.Forall₂.cons h1 (List.Forall₂.cons h2 hc), _ =>
    ⟨[], _, _, _, [], _, _, _, rfl, rfl, rfl, rfl, List.Forall₂.nil, h1, h2, hc⟩
  | 0, _, _, List.Forall₂.nil, hl => by simp at hl
  | 0, _, _, List.Forall₂.cons _ List.Forall₂.nil, hl => by simp at hl
  | oi + 1, _, _, List.Forall₂.cons h1 hs, hl => by
    obtain ⟨qa, q1, q2, qc, A, X, Y, C, e1, e2, l1, l2, f1, f2, f3, f4⟩ :=
      forall₂_split3 oi _ _ hs (by simp only [List.length_cons] at hl; omega)
    exact ⟨_ :: qa, q1, q2, qc, _ :: A, X, Y, C, by rw [e1]; rfl, by rw [e2]; rfl,
      by simp [l1], by simp [l2], List.Forall₂.cons h1 f1, f2, f3, f4⟩
  | _ + 1, _, _, List.Forall₂.nil, hl => by simp at hl

theorem getD_mid2 {α : Type} (a : List α) (x y : α) (c : List α) (d : α) :
    (a ++ x :: y :: c).getD (a.length + 1) d = y := by
  induction a with
  | nil => rfl
  | cons z l ih => simpa using ih

theorem getD_mid1 {α : Type} (a : List α) (x y : α) (c : List α) (d : α) :
    (a ++ x :: y :: c).getD a.length d = x := by
  induction a with
  | nil => rfl
  | cons z l ih => simpa using ih

theorem getD_swap {α : Type} (a : List α) (x y : α) (c : List α) (d : α) (i : ℕ)
    (h1 : i ≠ a.length) (h2 : i ≠ a.length + 1) :
    (a ++ y :: x :: c).getD i d = (a ++ x :: y :: c).getD i d := by
  induction a generalizing i with
  | nil =>
    match i, h1, h2 with
    | i + 2, _, _ => rfl
  | cons z l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih i (by simpa using h1) (by simpa using h2)

/-- **Rule ORD.**  Two neighbouring pieces of equal kind may be exchanged. -/
theorem CEV.swap {qs : List Q} {V : ℤ} {W B : ℕ} {Ls : List (List TRow)} (oi : ℕ)
    (hlt : oi + 1 < qs.length) (hq : qs.getD oi dq = qs.getD (oi + 1) dq)
    (h : CEV k qs V W B Ls) :
    ∃ Ls', CEV k qs V W B Ls' ∧ Ls'.flatten.length = Ls.flatten.length ∧
      Ls'.getD oi [] = Ls.getD (oi + 1) [] ∧ Ls'.getD (oi + 1) [] = Ls.getD oi [] ∧
      ∀ i, i ≠ oi → i ≠ oi + 1 → Ls'.getD i [] = Ls.getD i [] := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨qa, q1, q2, qc, A, X, Y, C, e1, e2, l1, l2, f1, f2, f3, f4⟩ :=
    forall₂_split3 oi qs Ls h1 hlt
  subst e1 e2
  have hq' : q1 = q2 := by
    have h' := hq
    rw [← l1, getD_mid1, getD_mid2] at h'
    exact h'
  subst hq'
  have hperm : (blocksR (A ++ Y :: X :: C).flatten).Perm (blocksR (A ++ X :: Y :: C).flatten) := by
    simp only [List.flatten_append, List.flatten_cons, blocksR_append]
    refine List.Perm.append_left _ ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm
  refine ⟨A ++ Y :: X :: C, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact J15.forall₂_app f1 (List.Forall₂.cons f3 (List.Forall₂.cons f2 f4))
  · unfold Sh at h2 ⊢
    rw [hperm.length_eq, clsCount_perm hperm]
    exact h2
  · simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at h3 ⊢
    omega
  · simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at h4 ⊢
    linarith
  · simp only [List.flatten_append, List.flatten_cons, List.length_append]
    omega
  · rw [← l2, getD_mid1, getD_mid2]
  · rw [← l2, getD_mid1, getD_mid2]
  · intro i hi1 hi2
    exact getD_swap A X Y C [] i (by omega) (by omega)

/-! ### Lemma JRV: every piece read backwards -/

theorem rho_rot_iff {u v : List ℕ} (h : u ~r v) : rho k u ~r rho k v := by
  unfold rho
  have hu : u ~r u.rotate (k - 1) := ⟨k - 1, rfl⟩
  have hv : v ~r v.rotate (k - 1) := ⟨k - 1, rfl⟩
  exact List.isRotated_reverse_iff.mpr (hu.symm.trans (h.trans hv))

theorem blocks_last_bind {L : List TRow} (hne : ∀ x ∈ L, x.2 ≠ []) :
    L.getLast?.bind (fun x => x.2.getLast?) = (blocksR L).getLast? := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L x ih =>
    have hx : x.2 ≠ [] := hne x (by simp)
    rw [List.getLast?_append, List.getLast?_singleton]
    show x.2.getLast? = (blocksR (L ++ [x])).getLast?
    rw [blocksR_append]
    have e : blocksR [x] = x.2 := by simp [blocksR]
    rw [e, List.getLast?_append_of_ne_nil _ hx]

theorem blocks_head_bind {L : List TRow} (hne : ∀ x ∈ L, x.2 ≠ []) :
    L.head?.bind (fun x => x.2.head?) = (blocksR L).head? := by
  cases L with
  | nil => rfl
  | cons x L =>
    have hx : x.2 ≠ [] := hne x List.mem_cons_self
    show x.2.head? = (x.2 ++ blocksR L).head?
    rw [List.head?_append_of_ne_nil _ hx]

theorem blocksR_revA (L : List TRow) :
    blocksR (revA k 0 L) = ((blocksR L).map (rho k)).reverse := KS.blocks_revA 0 L

/-- A ring read backwards closes. -/
theorem closes_revA (hk : 4 ≤ k) {L : List TRow} (hL : IsSeq k L) (hc : Closes k L) :
    Closes k (revA k 0 L) := by
  have hL' : IsSeq k (revA k 0 L) := KS.isSeq_revA (by omega) 0 hL
  intro u hu v hv
  rw [blocks_last_bind hL'.pieces_ne, blocksR_revA, List.getLast?_reverse, List.head?_map] at hu
  rw [blocks_head_bind hL'.pieces_ne, blocksR_revA, List.head?_reverse, List.getLast?_map] at hv
  simp only [Option.mem_def, Option.map_eq_some_iff] at hu hv
  obtain ⟨u0, hu0, rfl⟩ := hu
  obtain ⟨v0, hv0, rfl⟩ := hv
  have hw : WLink k 3 v0 u0 := hc v0 (by rw [blocks_last_bind hL.pieces_ne]; exact hv0) u0
    (by rw [blocks_head_bind hL.pieces_ne]; exact hu0)
  have hu0m : u0 ∈ blocksR L := List.mem_of_mem_head? hu0
  have hv0m : v0 ∈ blocksR L := List.mem_of_mem_getLast? hv0
  exact KS.rho_wlink (by omega) (by omega) (hL.mem_perm hv0m).2.1 (hL.mem_perm hu0m).2.1 hw

theorem valK_revA (L : List TRow) : valK k (revA k 0 L) = valK k L := by
  unfold valK
  rw [KS.linksT_revA, KS.length_revA, KS.holesT_revA]

theorem wtK_revA (L : List TRow) : wtK k (revA k 0 L) = wtK k L := by
  unfold wtK
  rw [KS.linksT_revA, KS.holesT_revA]

/-- **Lemma JRV (a), (b)**: a piece read backwards is a piece of the same kind and class. -/
theorem pieceV_revA (hk : 4 ≤ k) {q : Q} {L : List TRow} (h : IsPieceV k q L) :
    IsPieceV k q (revA k 0 L) := by
  obtain ⟨hw, hcl⟩ := h
  refine ⟨?_, fun h0 => by rw [valK_revA]; exact hcl h0⟩
  unfold IsPieceW at hw ⊢
  by_cases h0 : q.1.1 = 0
  · rw [if_pos h0] at hw ⊢
    obtain ⟨hL, hk0, h2, hc, hlo, hhi⟩ := hw
    refine ⟨KS.isSeq_revA hk 0 hL, ?_, by rw [KS.length_revA]; exact h2, closes_revA (by omega) hL hc,
      by rw [KS.holesT_revA]; exact hlo, by rw [KS.holesT_revA]; exact hhi⟩
    intro z hz
    obtain ⟨_, _, _, h2'⟩ := KS.mem_revA hz
    rcases h2' with h2' | ⟨y, hy, h2'⟩
    · exact h2'
    · rw [h2']
      exact hk0 y hy
  · rw [if_neg h0] at hw ⊢
    obtain ⟨hL, hne, hk1, hlk⟩ := hw
    exact ⟨KS.isSeq_revA hk 0 hL, KS.revA_ne_nil 0 hne, KS.kinds_revA (le_refl _ |>.trans (Nat.zero_le 1)) hk1,
      by rw [KS.linksT_revA]; exact hlk⟩

theorem blocksR_flatten_revA (Ls : List (List TRow)) :
    (blocksR (Ls.map (revA k 0)).flatten).Perm ((blocksR Ls.flatten).map (rho k)) := by
  induction Ls with
  | nil => exact List.Perm.refl _
  | cons L Ls ih =>
    simp only [List.map_cons, List.flatten_cons, blocksR_append, List.map_append]
    rw [blocksR_revA]
    exact (List.reverse_perm _).append ih

/-- **Lemma JRV (c)**: reading every piece backwards keeps the bound on shared classes. -/
theorem sh_revA {B : ℕ} {Ls : List (List TRow)} (hw : ∀ w ∈ blocksR Ls.flatten, PermW k w)
    (h : Sh B Ls) : Sh B (Ls.map (revA k 0)) := by
  have hp := blocksR_flatten_revA (k := k) Ls
  unfold Sh at h ⊢
  rw [hp.length_eq, clsCount_perm hp, List.length_map, clsCount_map]
  · exact h
  · intro u _ v _ huv
    exact rho_rot_iff huv
  · intro u hu v hv huv
    by_contra hn
    exact KS.rho_rot hn huv

theorem forall₂_revA (hk : 4 ≤ k) {qs : List Q} {Ls : List (List TRow)}
    (h : List.Forall₂ (IsPieceV k) qs Ls) : List.Forall₂ (IsPieceV k) qs (Ls.map (revA k 0)) := by
  rw [List.forall₂_map_right_iff]
  exact h.imp fun _ _ hp => pieceV_revA hk hp

theorem getD_map' {α β : Type} (f : α → β) {d : α} {d' : β} (hf : f d = d') :
    ∀ (l : List α) (i : ℕ), (l.map f).getD i d' = f (l.getD i d)
  | [], _ => by simp [hf]
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => by
    simp only [List.map_cons, List.getD_cons_succ]
    exact getD_map' f hf l i

theorem rows_revA : ∀ Ls : List (List TRow), (Ls.map (revA k 0)).flatten.length = Ls.flatten.length
  | [] => rfl
  | L :: Ls => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, KS.length_revA]
    rw [rows_revA Ls]

theorem getD_revA (Ls : List (List TRow)) (i : ℕ) :
    (Ls.map (revA k 0)).getD i [] = revA k 0 (Ls.getD i []) := by
  exact getD_map' (revA k 0) (d := []) rfl Ls i

/-! ### Renaming the symbols -/

theorem hdK_relab (e : List ℕ) (B : List TRow) : KS.hdK (relabSeq e B) = KS.hdK B := by
  cases B <;> rfl

theorem phiAt_relab (a b h : ℕ) (e : List ℕ) (A B : List TRow) :
    phiAt k a b h (relabSeq e A) (relabSeq e B) = phiAt k a b h A B := by
  unfold phiAt
  by_cases hA : A = []
  · subst hA
    rfl
  · have hA' : relabSeq e A ≠ [] := by
      intro h'
      apply hA
      have := congrArg List.length h'
      rw [length_relab] at this
      exact List.length_eq_zero_iff.mp this
    rw [if_neg hA, if_neg hA', hdK_relab, linksT_relab, length_relab, holesT_relab]

theorem good_relab {a b h : ℕ} (e : List ℕ) {L : List TRow} (hg : Good k a b h L) :
    Good k a b h (relabSeq e L) := by
  intro A0' B0' hs
  obtain ⟨A0, B0, e0, hA0, hB0⟩ := List.map_eq_append_iff.mp hs
  obtain ⟨A1, B1, e1, hle⟩ := hg A0 B0 e0
  refine ⟨relabSeq e A1, relabSeq e B1, by rw [e1]; exact List.map_append, ?_⟩
  have eT : phiAt k a b h (relabSeq e L) [] = phiAt k a b h L [] := phiAt_relab a b h e L []
  rw [eT, ← hA0, ← hB0]
  show _ ≤ phiAt k a b h (relabSeq e A0) (relabSeq e B0) + phiAt k a b h (relabSeq e A1) (relabSeq e B1)
  rw [phiAt_relab, phiAt_relab]
  exact hle

theorem pieceV_relab {e : List ℕ} (he : PermW k e) {q : Q} {L : List TRow}
    (h : IsPieceCV k q L) : IsPieceCV k q (relabSeq e L) := by
  have h1 := pieceC_relab he h.toC
  exact ⟨⟨h1.1, fun h0 => by rw [valK_relab]; exact h.1.2 h0⟩, h1.2⟩

/-- The blocks of a counterexample are permutation words. -/
theorem CEV.words {qs : List Q} {V : ℤ} {W B : ℕ} {Ls : List (List TRow)}
    (h : CEV k qs V W B Ls) : ∀ w ∈ blocksR Ls.flatten, PermW k w := by
  intro w hw
  unfold blocksR at hw
  obtain ⟨Q', hQ, hwQ⟩ := List.mem_flatten.mp hw
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hQ
  obtain ⟨L, hL, hxL⟩ := List.mem_flatten.mp hx
  obtain ⟨p, _, hp⟩ := forall₂_mem h.1 L hL
  exact hp.1.1.isSeq.words x hxL w hwQ

theorem CEV.relabel {qs : List Q} {V : ℤ} {W B : ℕ} {Ls : List (List TRow)}
    (h : CEV k qs V W B Ls) {e : List ℕ} (he : PermW k e) :
    CEV k qs V W B (Ls.map (relabSeq e)) ∧
      (Ls.map (relabSeq e)).flatten.length = Ls.flatten.length := by
  have hwords := h.words
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [List.forall₂_map_right_iff]
    exact h1.imp fun _ _ hp => pieceV_relab he hp
  · unfold Sh at h2 ⊢
    rw [flatten_relab, blocksR_relab, List.length_map, clsCount_map]
    · exact h2
    · intro u _ v _ huv
      exact huv.map _
    · intro u hu v hv huv
      by_contra hn
      exact S.not_isRotated_map_relab he (hwords u hu) (hwords v hv) hn huv
  · rw [List.map_map]
    have e1 : wtK k ∘ relabSeq e = wtK k := funext fun L => wtK_relab e L
    rw [e1]
    exact h3
  · rw [List.map_map]
    have e1 : valK k ∘ relabSeq e = valK k := funext fun L => valK_relab e L
    rw [e1]
    exact h4
  · rw [flatten_relab, length_relab]

theorem getD_relab (e : List ℕ) (Ls : List (List TRow)) (i : ℕ) :
    (Ls.map (relabSeq e)).getD i [] = relabSeq e (Ls.getD i []) := by
  exact getD_map' (relabSeq e) (d := []) rfl Ls i

/-! ### The normal form -/

/-- The properties of the normal form: Rule PREV on piece `rp`, Rule ORD on the pieces `oi`,
`oi + 1`. -/
structure NF (k : ℕ) (qs : List Q) (rp pa pb ph oi : ℕ) (Ls : List (List TRow)) : Prop where
  good : rp < qs.length → (qs.getD rp dq).1.1 ≠ 0 → Good k pa pb ph (Ls.getD rp [])
  ord : oi + 1 < qs.length → valK k (Ls.getD (oi + 1) []) ≤ valK k (Ls.getD oi [])

theorem forall₂_getD {α β : Type} {R : α → β → Prop} {da : α} {db : β} :
    ∀ {l : List α} {u : List β}, List.Forall₂ R l u → ∀ i, i < l.length →
      R (l.getD i da) (u.getD i db)
  | _, _, List.Forall₂.nil, i, hi => by simp at hi
  | _, _, List.Forall₂.cons h hs, 0, _ => h
  | _, _, List.Forall₂.cons _ hs, i + 1, hi => by
    simp only [List.getD_cons_succ]
    exact forall₂_getD hs i (by simpa using hi)

/-- **The normal form** of a counterexample (sections 4.1 to 4.4). -/
theorem exists_nf (hk : 4 ≤ k) {qs : List Q} {V : ℤ} {W B : ℕ} (rp pa pb ph oi : ℕ)
    (hne : qs ≠ [])
    (hoi : oi + 1 < qs.length → qs.getD oi dq = qs.getD (oi + 1) dq)
    (hfail : ¬ JV k qs V W B) :
    ∃ Ls, CEV k qs V W B Ls ∧
      (∀ Ls', CEV k qs V W B Ls' → Ls.flatten.length ≤ Ls'.flatten.length) ∧
      NF k qs rp pa pb ph oi Ls ∧
      ∃ kd0 R1 S1 Post1, Ls = ((kd0, List.range' 1 k :: R1) :: S1) :: Post1 := by
  -- a counterexample, its rings in the rotation of the cycle lemma
  unfold JV at hfail
  push Not at hfail
  obtain ⟨Ls0, hLs, hSh, hW, hV⟩ := hfail
  obtain ⟨Ls1, g1, g2, g3, g4, _, _, _⟩ := normV qs Ls0 hLs
  have hce1 : CEV k qs V W B Ls1 := by
    refine ⟨g1, ?_, by rw [g3]; exact hW, by rw [g4]; exact hV⟩
    unfold Sh at hSh ⊢
    rw [g2.length_eq, clsCount_perm g2]
    exact hSh
  -- the fewest rows
  obtain ⟨Ls2, hce2, hmin2⟩ := exists_minV ⟨Ls1, hce1⟩
  -- Rule ORD
  obtain ⟨Ls3, hce3, hrows3, hord3⟩ : ∃ Ls3, CEV k qs V W B Ls3 ∧
      Ls3.flatten.length = Ls2.flatten.length ∧
      (oi + 1 < qs.length → valK k (Ls3.getD (oi + 1) []) ≤ valK k (Ls3.getD oi [])) := by
    by_cases ho : oi + 1 < qs.length ∧ valK k (Ls2.getD oi []) < valK k (Ls2.getD (oi + 1) [])
    · obtain ⟨Ls3, h1, h2, h3, h4, _⟩ := CEV.swap oi ho.1 (hoi ho.1) hce2
      refine ⟨Ls3, h1, h2, fun _ => ?_⟩
      rw [h3, h4]
      exact le_of_lt ho.2
    · refine ⟨Ls2, hce2, rfl, fun hlt => ?_⟩
      push Not at ho
      exact ho hlt
  have hmin3 : ∀ Ls', CEV k qs V W B Ls' → Ls3.flatten.length ≤ Ls'.flatten.length := by
    intro Ls' h'
    rw [hrows3]
    exact hmin2 Ls' h'
  -- Rule PREV: the object or its reversal
  obtain ⟨Ls4, hce4, hrows4, hnf4⟩ : ∃ Ls4, CEV k qs V W B Ls4 ∧
      Ls4.flatten.length = Ls3.flatten.length ∧ NF k qs rp pa pb ph oi Ls4 := by
    by_cases hg : rp < qs.length → (qs.getD rp dq).1.1 ≠ 0 → Good k pa pb ph (Ls3.getD rp [])
    · exact ⟨Ls3, hce3, rfl, ⟨hg, hord3⟩⟩
    · push Not at hg
      obtain ⟨hrp, hseq, hbad⟩ := hg
      have hpc := forall₂_getD (da := dq) (db := []) hce3.1 rp hrp
      have hpw := hpc.1.1
      unfold IsPieceW at hpw
      rw [if_neg hseq] at hpw
      have hgr := KS.good_or_rev (k := k) pa pb ph hpw.2.1 hpw.2.2.1
      have hgood : Good k pa pb ph (revA k 0 (Ls3.getD rp [])) := hgr.resolve_left hbad
      -- read every piece backwards, then the rings again in the rotation of the cycle lemma
      have hV3 := forall₂_revA hk (hce3.1.imp fun _ _ h => h.1)
      obtain ⟨Ls4, f1, f2, f3, f4, f5, f6, f7⟩ := normV qs _ hV3
      have hsh := sh_revA hce3.words hce3.2.1
      refine ⟨Ls4, ⟨f1, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
      · unfold Sh at hsh ⊢
        rw [f2.length_eq, clsCount_perm f2]
        exact hsh
      · rw [f3, List.map_map]
        have e1 : wtK k ∘ revA k 0 = wtK k := funext fun L => wtK_revA L
        rw [e1]
        exact hce3.2.2.1
      · rw [f4, List.map_map]
        have e1 : valK k ∘ revA k 0 = valK k := funext fun L => valK_revA L
        rw [e1]
        exact hce3.2.2.2
      · rw [f5, rows_revA]
      · intro _ _
        rw [f6 rp hseq, getD_revA]
        exact hgood
      · intro hlt
        rw [f7, f7, getD_revA, getD_revA, valK_revA, valK_revA]
        exact hord3 hlt
  have hmin4 : ∀ Ls', CEV k qs V W B Ls' → Ls4.flatten.length ≤ Ls'.flatten.length := by
    intro Ls' h'
    rw [hrows4]
    exact hmin3 Ls' h'
  -- renaming: piece 1 starts at 1 2 … k
  obtain ⟨sp0, spost, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨S0, Post, rfl⟩ : ∃ S0 Post, Ls4 = S0 :: Post := by
    have := hce4.1
    cases this
    exact ⟨_, _, rfl⟩
  have hS0 := (List.forall₂_cons.mp hce4.1).1
  obtain ⟨x0, S0', rfl⟩ := List.exists_cons_of_ne_nil hS0.1.1.ne_nil
  obtain ⟨kd0, Q0⟩ := x0
  have hQ0 := hS0.1.1.isSeq.pieces_ne (kd0, Q0) List.mem_cons_self
  obtain ⟨v0, R0, rfl⟩ := List.exists_cons_of_ne_nil hQ0
  have hv0 : PermW k v0 := hS0.1.1.isSeq.words _ List.mem_cons_self v0 List.mem_cons_self
  obtain ⟨hce5, hrows5⟩ := hce4.relabel hv0
  refine ⟨_, hce5, fun Ls' h' => by rw [hrows5]; exact hmin4 Ls' h', ⟨?_, ?_⟩,
    kd0, R0.map (List.map (S.relab v0)), relabSeq v0 S0', Post.map (relabSeq v0), ?_⟩
  · intro h1 h2
    rw [getD_relab]
    exact good_relab v0 (hnf4.good h1 h2)
  · intro hlt
    rw [getD_relab, getD_relab, valK_relab, valK_relab]
    exact hnf4.ord hlt
  · simp [relabSeq, S.map_relab_self hv0.1, hv0.2.1]

end J16
end SuperpermLowerBounds
