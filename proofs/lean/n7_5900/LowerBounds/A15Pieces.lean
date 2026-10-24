import LowerBounds.A15Cut
import LowerBounds.A15Core
import LowerBounds.PRules

/-!
# From the components of a configuration to pieces on words
(the written proof, sections 3.4, 3.5 and 5.2: Lemma ITEM, the cut at the dear place, Lemma PIECE)

* `segSeq_spec`, `ringSeq_spec`: a list of trails joined by links of weight 4, and a trail that
  closes, as pieces on words (`KS.IsPiece`) with their rows, holes, links and blocks.
* `kernel_pieces`: the kernel as one piece, or, when one of its seams has weight 5, as the piece
  before that seam and an item for the piece behind it.
* `hanging_ext` (Lemma ITEM with Lemma PIECE): a hanging component whose link costs have excess
  at most 1 has value at most 0 or gives an item with a piece: a ring (H0b; H1 without heavy
  seam), a sequence that borrows a class (H0a and H1 with attachment cost at most 1, cut at the
  first heavy seam or at the seam of weight 5), or a sequence that borrows nothing (H1 with
  attachment cost 2).  An item of a component with a seam of weight 5 is kept with the shifts 11
  and 13 of the items without excess, which are smaller than its own shifts 16 and 19.
* `hanging_exts`: the items of all hanging components.
-/

namespace SuperpermLowerBounds
namespace A15

open Hunter PreimageChain T5899

/-! ### Rows as pieces on words -/

/-- The rows of a list of trails as rows on words; the first row of every trail is entered by a
link of weight 4. -/
noncomputable def segSeq (S : List (List (NRow 7))) : List PS.TRow := PS.seqOf 1 (toFam S)

/-- The rows of a trail as rows on words. -/
noncomputable def ringSeq (T : List (NRow 7)) : List PS.TRow := PS.seqOf 0 [T.map NRow.entries]

theorem toW_flatten (F : List (List (List (Vtx 7)))) :
    (F.map PS.toW).flatten.flatten = F.flatten.flatten.map Subtype.val := by
  symm
  rw [List.map_flatten, List.map_flatten]
  rfl

/-- A list of trails joined by links of weight 4 is a sequence on words. -/
theorem segSeq_spec {S : List (List (NRow 7))} (h : TrailFam 7 S)
    (hl : S.IsChain (RowLink 7 4)) (hne : S ≠ []) :
    KS.IsPiece (.seq (PS.linksT (segSeq S))) (segSeq S) ∧ PS.linksT (segSeq S) + 1 = S.length ∧
      (segSeq S).length = S.flatten.length ∧ PS.holesT 7 (segSeq S) = rowsHoles 7 S.flatten ∧
      KS.blocksT (segSeq S) = (rowsEntries S.flatten).map Subtype.val := by
  have hP : IsPath 7 (toFam S) := h.isPath (by norm_num) hl
  have hseq : PS.IsSeq 7 (PS.seqOf 1 (toFam S)) := PS.isSeq_seqOf hP.toIsFamily (by
    rw [List.isChain_map]
    exact hP.links.imp (fun A B hAB =>
      PS.chainLink_words (kd := 1) (fun h0 => absurd h0 (by decide)) (fun _ => rfl) hAB))
  have hne' : ∀ C ∈ (toFam S).map PS.toW, C ≠ [] := by
    intro C hC
    obtain ⟨C0, hC0, rfl⟩ := List.mem_map.mp hC
    exact fun e => hP.ne C0 hC0 (List.map_eq_nil_iff.mp e)
  have hlinks : PS.linksT (PS.seqOf 1 (toFam S)) = S.length - 1 := by
    unfold PS.seqOf
    rw [PS.linksT_tagF (by decide) _ hne', List.length_map, toFam_length]
  have hlen : (PS.seqOf 1 (toFam S)).length = S.flatten.length := by
    rw [PS.famRows_seqOf, famRows_toFam]
  have hhol : PS.holesT 7 (PS.seqOf 1 (toFam S)) = rowsHoles 7 S.flatten := by
    rw [PS.famHoles_seqOf, famHoles_toFam]
  have hpos : 1 ≤ S.length := List.length_pos_iff.mpr hne
  have hfl : S.flatten ≠ [] := by
    obtain ⟨A, S', rfl⟩ := List.exists_cons_of_ne_nil hne
    intro e
    rw [List.flatten_cons] at e
    exact (h.trails A List.mem_cons_self).ne (List.append_eq_nil_iff.mp e).1
  refine ⟨⟨hseq, ?_, PS.tag_le_one (le_refl 1), le_refl _⟩, ?_, hlen, hhol, ?_⟩
  · intro e
    have h0 : (PS.seqOf 1 (toFam S)).length = 0 := by
      show (segSeq S).length = 0
      rw [e]
      rfl
    rw [hlen] at h0
    exact hfl (List.length_eq_zero_iff.mp h0)
  · show PS.linksT (PS.seqOf 1 (toFam S)) + 1 = S.length
    omega
  · show ((PS.seqOf 1 (toFam S)).map Prod.snd).flatten = _
    unfold PS.seqOf
    rw [PS.tagF_snd, toW_flatten, toFam_flatten]

/-- A trail with pairwise different classes that closes at weight 3 is a ring on words. -/
theorem ringSeq_spec {T : List (NRow 7)} (hT : Trail 7 T)
    (hcl : (rowsEntries T).Pairwise (NotRot (k := 7))) (h2 : 2 ≤ T.length)
    (hc : RowLink 7 3 T T) :
    KS.IsPiece .ring (ringSeq T) ∧ (ringSeq T).length = T.length ∧
      PS.holesT 7 (ringSeq T) = rowsHoles 7 T ∧
      KS.blocksT (ringSeq T) = (rowsEntries T).map Subtype.val := by
  have hC : IsRing 7 (T.map NRow.entries) :=
    ⟨hT.isModelChain (by norm_num) hcl, by rw [List.length_map]; exact h2,
      chainLink_rows hT.len hT.len hc⟩
  generalize hCd : T.map NRow.entries = C at hC
  have hne : C ≠ [] := by
    intro e
    have := hC.two
    rw [e] at this
    simp at this
  have hfam : IsFamily 7 [C] :=
    ⟨fun D hD => by rw [List.mem_singleton.mp hD]; exact hC.chain,
      fun D hD => by rw [List.mem_singleton.mp hD]; exact hne,
      by
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
        exact hC.chain.classes⟩
  have hseq : PS.IsSeq 7 (PS.seqOf 0 [C]) := PS.isSeq_seqOf hfam (List.isChain_singleton _)
  have h0 : ∀ x ∈ PS.seqOf 0 [C], x.1 = 0 := by
    intro x hx
    obtain ⟨D, _, hxD⟩ := PS.mem_tagF hx
    rcases PS.tagC_tag 0 D x hxD with h | h <;> exact h
  have hlen : (PS.seqOf 0 [C]).length = C.length := by
    rw [PS.famRows_seqOf]
    simp [famRows]
  have hh : PS.holesT 7 (PS.seqOf 0 [C]) = holesL 7 C := by
    rw [PS.famHoles_seqOf]
    simp [famHoles]
  have hsnd : (PS.seqOf 0 [C]).map Prod.snd = PS.toW C := by
    unfold PS.seqOf
    rw [PS.tagF_snd]
    simp
  have hclo : PS.Closes 7 (PS.seqOf 0 [C]) := by
    intro u hu v hv
    have hu' : u ∈ ((PS.seqOf 0 [C]).map Prod.snd).getLast?.bind List.getLast? := by
      rw [List.getLast?_map]
      cases hq : (PS.seqOf 0 [C]).getLast? with
      | none => rw [hq] at hu; cases hu
      | some x => rw [hq] at hu; exact hu
    have hv' : v ∈ ((PS.seqOf 0 [C]).map Prod.snd).head?.bind List.head? := by
      rw [List.head?_map]
      cases hq : (PS.seqOf 0 [C]).head? with
      | none => rw [hq] at hv; cases hv
      | some x => rw [hq] at hv; exact hv
    rw [hsnd] at hu' hv'
    exact (PS.chainLink_words (kd := 0) (fun _ => rfl) (fun h1 => absurd h1 (by decide))
      hC.closes u hu' v hv').1 rfl
  have hCl : C.length = T.length := by rw [← hCd, List.length_map]
  unfold ringSeq
  rw [hCd]
  refine ⟨⟨hseq, h0, by rw [hlen]; exact hC.two, hclo⟩, by rw [hlen, hCl], ?_, ?_⟩
  · rw [hh, ← hCd, holesL_rows]
  · show ((PS.seqOf 0 [C]).map Prod.snd).flatten = _
    rw [hsnd, ← hCd, ← rowsEntries_eq]
    unfold PS.toW
    rw [List.map_flatten]

/-! ### Items from rows -/

/-- The item of a list of trails joined by links of weight 4. -/
theorem mk_seq_ext (ty : Ty) (hty : ty ≠ .R) {G : List (List (NRow 7))} (hG : TrailFam 7 G)
    (hch : G.IsChain (RowLink 7 4)) (hne : G ≠ []) (h9 : G.length ≤ 9)
    {own bor : List (Vtx 7)} (hperm : (rowsEntries G.flatten).Perm (bor ++ own))
    (hbor : bor.length ≤ 1) (hborE : ty = .E → bor = []) {v : ℤ} {w : ℕ} (hpos : 1 ≤ v)
    (hval : v + ty.dv ≤
      (G.flatten.length : ℤ) - (rowsHoles 7 G.flatten : ℤ) - 5 * ((G.length : ℤ) - 1))
    (hwt : rowsHoles 7 G.flatten + 6 * (G.length - 1) + ty.dw ≤ w) :
    ∃ e : Ext, e.OK ∧ e.v = v ∧ e.w = w ∧ e.own = own.map Subtype.val ∧ e.ty = ty := by
  obtain ⟨p, hl, hlen, hhol, hbl⟩ := segSeq_spec hG hch hne
  refine ⟨⟨ty, segSeq G, own.map Subtype.val, bor.map Subtype.val, v, w⟩, ?_, rfl, rfl, rfl, rfl⟩
  refine ⟨fun h => absurd h hty, fun _ => p, ?_, by simpa using hbor, ?_, ?_, ?_, hpos, by
    show PS.linksT (segSeq G) ≤ 8
    omega⟩
  · show (KS.blocksT (segSeq G)).Perm (own.map Subtype.val ++ bor.map Subtype.val)
    rw [hbl, ← List.map_append]
    exact (hperm.trans List.perm_append_comm).map _
  · intro h
    show bor.map Subtype.val = []
    rw [hborE h]
    rfl
  · show v + ty.dv ≤ KS.valT (segSeq G)
    unfold KS.valT
    rw [hlen, hhol]
    have h1 : (PS.linksT (segSeq G) : ℤ) = (G.length : ℤ) - 1 := by
      have h2 : ((PS.linksT (segSeq G) + 1 : ℕ) : ℤ) = (G.length : ℤ) := by rw [hl]
      push_cast at h2
      linarith
    rw [h1]
    exact hval
  · show KS.wtT (segSeq G) + ty.dw ≤ w
    unfold KS.wtT
    rw [hhol]
    have h1 : PS.linksT (segSeq G) = G.length - 1 := by omega
    rw [h1]
    exact hwt

/-- The item of a trail that closes, with the class `x` it borrows. -/
theorem mk_ring_ext {T : List (NRow 7)} (hT : Trail 7 T)
    (hcl : (rowsEntries T).Pairwise (NotRot (k := 7))) (h2 : 2 ≤ T.length)
    (hc : RowLink 7 3 T T) {own : List (Vtx 7)} {x : Vtx 7}
    (hperm : (rowsEntries T).Perm (x :: own)) {v : ℤ} {w : ℕ} (hpos : 1 ≤ v)
    (hval : v + 6 ≤ (T.length : ℤ) - (rowsHoles 7 T : ℤ)) (hwt : rowsHoles 7 T + 7 ≤ w) :
    ∃ e : Ext, e.OK ∧ e.v = v ∧ e.w = w ∧ e.own = own.map Subtype.val ∧ e.ty = .R := by
  obtain ⟨p, hlen, hhol, hbl⟩ := ringSeq_spec hT hcl h2 hc
  have hl0 : PS.linksT (ringSeq T) = 0 := PS.linksT_zero p.2.1
  refine ⟨⟨.R, ringSeq T, own.map Subtype.val, [x.val], v, w⟩, ?_, rfl, rfl, rfl, rfl⟩
  refine ⟨fun _ => p, fun h => absurd rfl h, ?_, by simp, fun h => Ty.noConfusion h, ?_, ?_, hpos,
    by
      show PS.linksT (ringSeq T) ≤ 8
      omega⟩
  · show (KS.blocksT (ringSeq T)).Perm (own.map Subtype.val ++ [x.val])
    rw [hbl]
    have h1 := hperm.map Subtype.val
    rw [List.map_cons] at h1
    exact h1.trans (List.perm_append_singleton _ _).symm
  · show v + 6 ≤ KS.valT (ringSeq T)
    unfold KS.valT
    rw [hlen, hhol, hl0]
    push_cast
    linarith
  · show KS.wtT (ringSeq T) + 7 ≤ w
    unfold KS.wtT
    rw [hhol, hl0]
    omega

/-! ### The kernel -/

theorem trailFam_left {S₁ S₂ : List (List (NRow 7))} (h : TrailFam 7 (S₁ ++ S₂)) :
    TrailFam 7 S₁ :=
  h.of_subperm (List.sublist_append_left S₁ S₂).subperm

theorem trailFam_right {S₁ S₂ : List (List (NRow 7))} (h : TrailFam 7 (S₁ ++ S₂)) :
    TrailFam 7 S₂ :=
  h.of_subperm (List.sublist_append_right S₁ S₂).subperm

/-- **The kernel as pieces.**  Without excess it is one sequence.  With a seam of weight 5 it is
cut there: the first part is the kernel piece and the second part gives an item that borrows
nothing, which is left out if its value is not positive. -/
theorem kernel_pieces {R : List (NRow 7)} (hok : RowsOK R) (he : epsR R ≤ 1)
    (h9 : (cutRows R).length ≤ 9) :
    ∃ (L0 : List PS.TRow) (es : List Ext), KS.IsPiece (.seq (PS.linksT L0)) L0 ∧
      PS.linksT L0 ≤ 8 ∧ (∀ e ∈ es, e.OK) ∧
      es.countP (fun e => decide (e.ty = .E)) ≤ epsR R ∧
      (KS.blocksT L0 ++ es.flatMap Ext.own).Sublist ((rowsEntries R).map Subtype.val) ∧
      valR R (rX R) ≤ KS.valT L0 + (es.map Ext.v).sum ∧
      KS.wtT L0 + (es.map Ext.w).sum ≤ wtR R (rX R) := by
  have hadd := hok.eps_add
  have hpos := hok.pos
  have inv := hok.inv
  by_cases h0 : epsR R = 0
  · have hlinks : rX R + 1 = (cutRows R).length := by omega
    have hne : cutRows R ≠ [] := List.length_pos_iff.mp hpos
    obtain ⟨p, hl, hlen, hhol, hbl⟩ := segSeq_spec hok.fam (inv.eq4 hlinks) hne
    rw [inv.flat] at hlen hhol hbl
    refine ⟨segSeq (cutRows R), [], p, by omega, fun e he => absurd he List.not_mem_nil, by simp,
      ?_, ?_, ?_⟩
    · simp only [List.flatMap_nil, List.append_nil]
      rw [hbl]
    · simp only [List.map_nil, List.sum_nil, add_zero]
      unfold valR KS.valT
      rw [hlen, hhol]
      have h1 : (PS.linksT (segSeq (cutRows R)) : ℤ) = (rX R : ℤ) := by
        have h2 : PS.linksT (segSeq (cutRows R)) = rX R := by omega
        rw [h2]
      rw [h1]
    · simp only [List.map_nil, List.sum_nil, add_zero]
      unfold wtR KS.wtT
      rw [hhol]
      have h2 : PS.linksT (segSeq (cutRows R)) = rX R := by omega
      rw [h2]
  · have h1 : rX R = (cutRows R).length := by omega
    obtain ⟨S₁, S₂, hS, n1, n2, c1, c2⟩ := cut5 R hok.seams hok.ne h1
    have hfam := hok.fam
    rw [hS] at hfam
    obtain ⟨p1, hl1, hlen1, hhol1, hbl1⟩ := segSeq_spec (trailFam_left hfam) c1 n1
    obtain ⟨p2, hl2, hlen2, hhol2, hbl2⟩ := segSeq_spec (trailFam_right hfam) c2 n2
    have hflat : S₁.flatten ++ S₂.flatten = R := by
      rw [← List.flatten_append, ← hS]
      exact inv.flat
    have hSl : (cutRows R).length = S₁.length + S₂.length := by
      rw [hS, List.length_append]
    have hRl : R.length = S₁.flatten.length + S₂.flatten.length := by
      rw [← hflat, List.length_append]
    have hRh : rowsHoles 7 R = rowsHoles 7 S₁.flatten + rowsHoles 7 S₂.flatten := by
      rw [← hflat, rowsHoles_append]
    have hRe : (rowsEntries R).map Subtype.val =
        KS.blocksT (segSeq S₁) ++ KS.blocksT (segSeq S₂) := by
      rw [hbl1, hbl2, ← hflat, rowsEntries_append, List.map_append]
    have hV : valR R (rX R) = KS.valT (segSeq S₁) + (KS.valT (segSeq S₂) - 10) := by
      unfold valR KS.valT
      rw [hlen1, hhol1, hlen2, hhol2, hRl, hRh, h1, hSl, ← hl1, ← hl2]
      push_cast
      ring
    have hW : wtR R (rX R) = KS.wtT (segSeq S₁) + (KS.wtT (segSeq S₂) + 12) := by
      unfold wtR KS.wtT
      rw [hhol1, hhol2, hRh, h1, hSl, ← hl1, ← hl2]
      ring
    by_cases hv2 : 1 ≤ KS.valT (segSeq S₂) - 10
    · refine ⟨segSeq S₁, [⟨.E, segSeq S₂, KS.blocksT (segSeq S₂), [],
        KS.valT (segSeq S₂) - 10, KS.wtT (segSeq S₂) + 12⟩], p1, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · intro e he
        rw [List.mem_singleton.mp he]
        exact ⟨fun h => Ty.noConfusion h, fun _ => p2, by simp, by simp, fun _ => rfl,
          by simp [Ty.dv], by simp [Ty.dw], hv2, by
            show PS.linksT (segSeq S₂) ≤ 8
            omega⟩
      · simp only [List.countP_cons, List.countP_nil]
        simp
        omega
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [hRe]
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rw [hV]
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rw [hW]
    · refine ⟨segSeq S₁, [], p1, by omega, fun e he => absurd he List.not_mem_nil, by simp,
        ?_, ?_, ?_⟩
      · simp only [List.flatMap_nil, List.append_nil]
        rw [hRe]
        exact List.sublist_append_left _ _
      · simp only [List.map_nil, List.sum_nil, add_zero]
        rw [hV]
        omega
      · simp only [List.map_nil, List.sum_nil, add_zero]
        rw [hW]
        omega

/-! ### Hanging components -/

theorem split_ends {α : Type} {first last : α} {mid T₁ T₂ : List α}
    (hT : first :: (mid ++ [last]) = T₁ ++ T₂) (h1 : T₁ ≠ []) (h2 : T₂ ≠ []) :
    ∃ S₁ S₂, T₁ = first :: S₁ ∧ T₂ = S₂ ++ [last] := by
  obtain ⟨a, S₁, rfl⟩ := List.exists_cons_of_ne_nil h1
  have e2 : T₂ = T₂.dropLast ++ [T₂.getLast h2] := (List.dropLast_concat_getLast h2).symm
  rw [e2, List.cons_append] at hT
  injection hT with ha ht
  rw [← List.append_assoc] at ht
  obtain ⟨_, hb⟩ := List.append_inj' ht rfl
  refine ⟨S₁, T₂.dropLast, by rw [ha], ?_⟩
  rw [e2]
  simp only [List.cons.injEq, and_true] at hb
  rw [hb]
  simp

/-- The trails of a component with excess at most 1 and at least two trails, as two lists joined
by links of weight 4: cut behind the first trail, or at the seam of weight 5. -/
theorem comp_split {R : List (NRow 7)} (hok : RowsOK R) (he : epsR R ≤ 1)
    {first last : List (NRow 7)} {mid : List (List (NRow 7))}
    (hS : cutRows R = first :: (mid ++ [last])) :
    ∃ S₁ S₂ : List (List (NRow 7)), cutRows R = (first :: S₁) ++ (S₂ ++ [last]) ∧
      (first :: S₁).IsChain (RowLink 7 4) ∧ (S₂ ++ [last]).IsChain (RowLink 7 4) := by
  have hadd := hok.eps_add
  by_cases h0 : epsR R = 0
  · have hch := hok.inv.eq4 (by omega)
    rw [hS] at hch
    refine ⟨[], mid, by rw [hS]; rfl, List.isChain_singleton _, ?_⟩
    have := hch.tail
    rwa [List.tail_cons] at this
  · obtain ⟨T₁, T₂, hT, n1, n2, c1, c2⟩ := cut5 R hok.seams hok.ne (by omega)
    rw [hS] at hT
    obtain ⟨S₁, S₂, rfl, rfl⟩ := split_ends hT n1 n2
    exact ⟨S₁, S₂, by rw [hS, hT], c1, c2⟩

section hanging

variable {R J : List (NRow 7)} {r r₁ : NRow 7} {x : Vtx 7}

/-- A component with at least two trails, read cyclically from the cut and glued through a
junction: the item of a sequence that borrows the class of the junction. -/
theorem glued_seq_ext (hok : RowsOK R) (he : epsR R ≤ 1) (h2 : 2 ≤ (cutRows R).length)
    (h9 : (cutRows R).length ≤ 9) (hr : R.getLast? = some r) (hr₁ : R.head? = some r₁)
    (hJ : Junction 7 r r₁ x J) (hx : ∀ e ∈ rowsEntries R, NotRot x e) {δ : ℕ}
    (hholes : (∀ j ∈ J, j.len ≤ 6) → rowsHoles 7 J + δ = rowsHoles 7 [r, r₁]) {v : ℤ} {w : ℕ}
    (hpos : 1 ≤ v)
    (hval : v + 11 + 2 + ((rowsHoles 7 R : ℤ) - (δ : ℤ)) + 5 * (((cutRows R).length : ℤ) - 2) ≤
      (R.length : ℤ) + (J.length : ℤ))
    (hwt : rowsHoles 7 R + 6 * ((cutRows R).length - 2) + 13 ≤ w + δ) :
    ∃ e : Ext, e.OK ∧ e.v = v ∧ e.w = w ∧ e.own = (rowsEntries R).map Subtype.val ∧
      e.ty = .AB := by
  obtain ⟨first, last, mid, r₁', r', A, B, hS, hf, hl, hh, hg⟩ := hok.decomp2 h2
  rw [hr₁] at hh
  rw [hr] at hg
  obtain rfl := Option.some.inj hh
  obtain rfl := Option.some.inj hg
  obtain ⟨S₁, S₂, hsp, c1, c2⟩ := comp_split hok he hS
  have inv := hok.inv
  have hflat : ((first :: S₁) ++ (S₂ ++ [last])).flatten = R := by rw [← hsp]; exact inv.flat
  have hfam : TrailFam 7 ((first :: S₁) ++ (S₂ ++ [last])) := by rw [← hsp]; exact hok.fam
  obtain ⟨G, Gch, Glen, Ghol, Gperm⟩ :=
    glue_split hfam c1 c2 hf hl hJ (by rw [hflat]; exact hx)
  rw [hflat] at Glen Ghol Gperm
  have hJlen : ∀ j ∈ J, j.len ≤ 6 := by
    intro j hj
    refine len_le_of_rowsEntries_pairwise (by norm_num) G.classes ?_
    refine List.mem_flatten.mpr ⟨glue A J B, by simp, ?_⟩
    unfold glue
    exact List.mem_append_right _ (List.mem_append_left _ hj)
  have hh' := hholes hJlen
  have hSl : (cutRows R).length = S₁.length + S₂.length + 2 := by
    rw [hsp]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hGl : (S₂ ++ glue A J B :: S₁).length = S₁.length + S₂.length + 1 := by
    simp only [List.length_append, List.length_cons]
    omega
  refine mk_seq_ext .AB (fun h => Ty.noConfusion h) G Gch (by simp) (by omega)
    (bor := [x]) (by simpa using Gperm) (by simp) (fun h => Ty.noConfusion h) hpos ?_ ?_
  · have e1 : ((S₂ ++ glue A J B :: S₁).flatten.length : ℤ) + 2 =
        (R.length : ℤ) + (J.length : ℤ) := by exact_mod_cast Glen
    have e2 : (rowsHoles 7 (S₂ ++ glue A J B :: S₁).flatten : ℤ) + (δ : ℤ) =
        (rowsHoles 7 R : ℤ) := by
      have : rowsHoles 7 (S₂ ++ glue A J B :: S₁).flatten + δ = rowsHoles 7 R := by omega
      exact_mod_cast this
    have e3 : (((S₂ ++ glue A J B :: S₁).length : ℕ) : ℤ) = ((cutRows R).length : ℤ) - 1 := by
      rw [hGl, hSl]
      push_cast
      ring
    rw [e3]
    simp only [Ty.dv]
    linarith
  · rw [hGl]
    simp only [Ty.dw]
    omega

/-- A component that is one trail, glued through a junction: the item of a ring that borrows the
class of the junction. -/
theorem glued_ring_ext (hok : RowsOK R) (h1 : (cutRows R).length = 1) (hm : 2 ≤ R.length)
    (hr : R.getLast? = some r) (hr₁ : R.head? = some r₁)
    (hJ : Junction 7 r r₁ x J) (hx : ∀ e ∈ rowsEntries R, NotRot x e) {δ : ℕ}
    (hholes : (∀ j ∈ J, j.len ≤ 6) → rowsHoles 7 J + δ = rowsHoles 7 [r, r₁])
    (hlen : 4 ≤ R.length + J.length) {v : ℤ} {w : ℕ} (hpos : 1 ≤ v)
    (hval : v + 6 + 2 + ((rowsHoles 7 R : ℤ) - (δ : ℤ)) ≤ (R.length : ℤ) + (J.length : ℤ))
    (hwt : rowsHoles 7 R + 7 ≤ w + δ) :
    ∃ e : Ext, e.OK ∧ e.v = v ∧ e.w = w ∧ e.own = (rowsEntries R).map Subtype.val ∧
      e.ty = .R := by
  obtain ⟨T, hT, hcl, hclose, hTl, hJT, hTh, hperm⟩ := glue_ring' hok h1 hm hr hr₁ hJ hx
  have hh' := hholes
    (fun j hj => len_le_of_rowsEntries_pairwise (by norm_num) hcl (hJT j hj))
  refine mk_ring_ext hT hcl (by omega) hclose hperm hpos ?_ (by omega)
  have e1 : (T.length : ℤ) + 2 = (R.length : ℤ) + (J.length : ℤ) := by exact_mod_cast hTl
  have e2 : (rowsHoles 7 T : ℤ) + (δ : ℤ) = (rowsHoles 7 R : ℤ) := by
    have : rowsHoles 7 T + δ = rowsHoles 7 R := by omega
    exact_mod_cast this
  linarith

end hanging

variable {c : NConfig 7} {H : NHanging 7}

/-- A hanging component contributes at least one trail less than it has. -/
theorem cut_le_famH (H : NHanging 7) : (cutRows H.rows).length ≤ (famH H).length + 1 := by
  unfold famH
  by_cases ha : H.att = 0
  · rw [if_pos ha]
    by_cases h2 : 2 ≤ (cutRows H.rows).length
    · rw [if_pos h2]
      have := rotSegs_length h2
      omega
    · omega
  · rw [if_neg ha]
    omega

/-- **Lemma ITEM with Lemma PIECE.**  A hanging component whose link costs have excess at most 1
has value at most 0, or it gives an item with a piece. -/
theorem hanging_ext (hv : c.Valid) (hH : H ∈ c.hanging) (he : epsH H ≤ 1)
    (h9 : (cutRows H.rows).length ≤ 9) :
    vH H ≤ 0 ∨ ∃ e : Ext, e.OK ∧ e.v = vH H ∧ e.w = wH H ∧
      e.own = (rowsEntries H.rows).map Subtype.val ∧ (e.ty = .E → epsH H = 1) := by
  by_cases hp : vH H ≤ 0
  · exact Or.inl hp
  right
  have hp1 : 1 ≤ vH H := by omega
  have hok := hanging_ok hv hH
  have inv := hok.inv
  have hadd := hok.eps_add
  have hpos := hok.pos
  unfold epsH at he
  obtain ⟨r₁, hr₁⟩ : ∃ r₁, H.rows.head? = some r₁ := by
    obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil hok.ne
    exact ⟨a, by rw [hl]; rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, H.rows.getLast? = some r :=
    ⟨H.rows.getLast hok.ne, List.getLast?_eq_some_getLast hok.ne⟩
  have hRpos : 1 ≤ H.rows.length := List.length_pos_iff.mpr hok.ne
  by_cases ha : H.att = 0
  · -- free attachment
    obtain ⟨hJ, _, hx⟩ := free_geom hv hH ha hr hr₁
    have hholes : (∀ j ∈ [mergeRow r r₁], j.len ≤ 6) →
        rowsHoles 7 [mergeRow r r₁] + 7 = rowsHoles 7 [r, r₁] :=
      fun hj => holes_merge (hj _ (List.mem_singleton_self _))
    have hv0 : vH H = valR H.rows (rX H.rows) := by
      unfold vH
      rw [ha, Nat.add_zero]
    have hw0 : wH H = wtR H.rows (rX H.rows) := by
      unfold wH
      rw [ha, Nat.add_zero]
    rw [hv0] at hp1
    unfold valR at hp1
    by_cases h2 : 2 ≤ (cutRows H.rows).length
    · obtain ⟨e, eok, ev, ew, eown, ety⟩ := glued_seq_ext hok (by omega) h2 h9 hr hr₁ hJ hx hholes
        (v := vH H) (w := wH H) (by rw [hv0]; unfold valR; exact hp1)
        (by
          rw [hv0]
          unfold valR
          simp only [List.length_singleton]
          have e1 : ((rX H.rows : ℕ) : ℤ) + 1 =
              (epsR H.rows : ℤ) + ((cutRows H.rows).length : ℤ) := by
            exact_mod_cast hadd.symm
          push_cast
          have e0 : (0 : ℤ) ≤ (epsR H.rows : ℤ) := Int.natCast_nonneg _
          linarith)
        (by
          rw [hw0]
          unfold wtR
          omega)
      exact ⟨e, eok, ev, ew, eown, fun h => by rw [ety] at h; exact Ty.noConfusion h⟩
    · have h1 : (cutRows H.rows).length = 1 := by omega
      obtain ⟨_, _, hX⟩ := hok.single h1
      by_cases h3 : 3 ≤ H.rows.length
      · obtain ⟨e, eok, ev, ew, eown, ety⟩ := glued_ring_ext hok h1 (by omega) hr hr₁ hJ hx hholes
          (by simp only [List.length_singleton]; omega) (v := vH H) (w := wH H)
          (by rw [hv0]; unfold valR; exact hp1)
          (by
            rw [hv0]
            unfold valR
            rw [hX]
            simp only [List.length_singleton]
            push_cast
            linarith)
          (by
            rw [hw0]
            unfold wtR
            omega)
        exact ⟨e, eok, ev, ew, eown, fun h => by rw [ety] at h; exact Ty.noConfusion h⟩
      · have := free_small hv hH ha h1 (by omega)
        rw [hv0] at this
        unfold valR at this
        omega
  · by_cases ha1 : H.att = 1
    · -- attachment of cost 1
      have hv1 : vH H = valR H.rows (rX H.rows + 1) := by
        unfold vH
        rw [ha1]
      have hw1 : wH H = wtR H.rows (rX H.rows + 1) := by
        unfold wH
        rw [ha1]
      rw [hv1] at hp1
      unfold valR at hp1
      have key : ∀ {x : Vtx 7} {J : List (NRow 7)}, Junction 7 r r₁ x J →
          (∀ e ∈ rowsEntries H.rows, NotRot x e) → J.length = 2 →
          ((∀ j ∈ J, j.len ≤ 6) → rowsHoles 7 J + 1 = rowsHoles 7 [r, r₁]) →
          ∃ e : Ext, e.OK ∧ e.v = vH H ∧ e.w = wH H ∧
            e.own = (rowsEntries H.rows).map Subtype.val ∧ (e.ty = .E → epsH H = 1) := by
        intro x J hJ hx hJ2 hholes
        by_cases h2 : 2 ≤ (cutRows H.rows).length
        · obtain ⟨e, eok, ev, ew, eown, ety⟩ := glued_seq_ext hok (by omega) h2 h9 hr hr₁ hJ hx
            hholes (v := vH H) (w := wH H) (by rw [hv1]; unfold valR; exact hp1)
            (by
              rw [hv1]
              unfold valR
              rw [hJ2]
              have e1 : ((rX H.rows : ℕ) : ℤ) + 1 =
                  (epsR H.rows : ℤ) + ((cutRows H.rows).length : ℤ) := by
                exact_mod_cast hadd.symm
              push_cast
              have e0 : (0 : ℤ) ≤ (epsR H.rows : ℤ) := Int.natCast_nonneg _
              linarith)
            (by
              rw [hw1]
              unfold wtR
              omega)
          exact ⟨e, eok, ev, ew, eown, fun h => by rw [ety] at h; exact Ty.noConfusion h⟩
        · have h1 : (cutRows H.rows).length = 1 := by omega
          obtain ⟨_, _, hX⟩ := hok.single h1
          rw [hX] at hp1
          have hm : 2 ≤ H.rows.length := by
            push_cast at hp1
            omega
          obtain ⟨e, eok, ev, ew, eown, ety⟩ := glued_ring_ext hok h1 hm hr hr₁ hJ hx hholes
            (by omega) (v := vH H) (w := wH H)
            (by rw [hv1]; unfold valR; rw [hX]; exact hp1)
            (by
              rw [hv1]
              unfold valR
              rw [hX, hJ2]
              push_cast
              linarith)
            (by
              rw [hw1]
              unfold wtR
              omega)
          exact ⟨e, eok, ev, ew, eown, fun h => by rw [ety] at h; exact Ty.noConfusion h⟩
      rcases cost_one_geom hv hH ha1 hr hr₁ with ⟨hJ, hx⟩ | ⟨y, hJ, hx⟩
      · exact key hJ hx rfl (fun hj => holes_extLast (hj (extLast r) (by simp)))
      · exact key hJ hx rfl (fun hj => holes_extFirst (hj (extFirst y r₁) (by simp)))
    · -- attachment of cost 2, no excess of the seams
      have ha2 : H.att = 2 := by omega
      have he0 : epsR H.rows = 0 := by omega
      have hlinks : rX H.rows + 1 = (cutRows H.rows).length := by omega
      have hne : cutRows H.rows ≠ [] := List.length_pos_iff.mp hpos
      have hv2 : vH H = valR H.rows (rX H.rows + 2) := by
        unfold vH
        rw [ha2]
      have hw2 : wH H = wtR H.rows (rX H.rows + 2) := by
        unfold wH
        rw [ha2]
      obtain ⟨e, eok, ev, ew, eown, ety⟩ := mk_seq_ext .E (fun h => Ty.noConfusion h) hok.fam
        (inv.eq4 hlinks) hne h9 (own := rowsEntries H.rows) (bor := [])
        (by rw [inv.flat]; exact List.Perm.refl _) (by simp) (fun _ => rfl) (v := vH H)
        (w := wH H) hp1
        (by
          rw [inv.flat, hv2]
          unfold valR
          simp only [Ty.dv]
          have e1 : ((rX H.rows : ℕ) : ℤ) + 1 = ((cutRows H.rows).length : ℤ) := by
            exact_mod_cast hlinks
          push_cast
          linarith)
        (by
          rw [inv.flat, hw2]
          unfold wtR
          simp only [Ty.dw]
          omega)
      refine ⟨e, eok, ev, ew, eown, fun _ => ?_⟩
      unfold epsH
      omega

/-- **The items of the hanging components.** -/
theorem hanging_exts (hv : c.Valid) (he : ∀ H ∈ c.hanging, epsH H ≤ 1)
    (h9 : ∀ H ∈ c.hanging, (cutRows H.rows).length ≤ 9) :
    ∀ Hs : List (NHanging 7), (∀ H ∈ Hs, H ∈ c.hanging) →
      ∃ es : List Ext, (∀ e ∈ es, e.OK) ∧
        (es.flatMap Ext.own).Sublist
          ((Hs.flatMap fun H => rowsEntries H.rows).map Subtype.val) ∧
        (Hs.map vH).sum ≤ (es.map Ext.v).sum ∧ (es.map Ext.w).sum ≤ (Hs.map wH).sum ∧
        es.countP (fun e => decide (e.ty = .E)) ≤ (Hs.map epsH).sum
  | [], _ => ⟨[], fun e he => absurd he List.not_mem_nil, by simp, by simp, by simp, by simp⟩
  | H :: Hs, h => by
      obtain ⟨es, ok, sub, sv, sw, cnt⟩ :=
        hanging_exts hv he h9 Hs (fun H' hH' => h H' (List.mem_cons_of_mem _ hH'))
      have hH := h H List.mem_cons_self
      rcases hanging_ext hv hH (he H hH) (h9 H hH) with hle | ⟨e, eok, ev, ew, eown, ety⟩
      · refine ⟨es, ok, ?_, ?_, ?_, ?_⟩
        · rw [List.flatMap_cons, List.map_append]
          exact sub.trans (List.sublist_append_right _ _)
        · rw [List.map_cons, List.sum_cons]
          linarith
        · rw [List.map_cons, List.sum_cons]
          omega
        · rw [List.map_cons, List.sum_cons]
          omega
      · refine ⟨e :: es, ?_, ?_, ?_, ?_, ?_⟩
        · intro e' he'
          rcases List.mem_cons.mp he' with rfl | he'
          · exact eok
          · exact ok e' he'
        · rw [List.flatMap_cons, List.flatMap_cons, List.map_append, eown]
          exact (List.Sublist.refl _).append sub
        · rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ev]
          linarith
        · rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ew]
          omega
        · rw [List.map_cons, List.sum_cons, List.countP_cons]
          by_cases hE : e.ty = .E
          · have := ety hE
            simp only [hE, decide_true, if_true]
            omega
          · simp only [hE, decide_false, Bool.false_eq_true, if_false]
            omega

end A15
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.A15.segSeq_spec
#print axioms SuperpermLowerBounds.A15.ringSeq_spec
#print axioms SuperpermLowerBounds.A15.kernel_pieces
#print axioms SuperpermLowerBounds.A15.hanging_ext
#print axioms SuperpermLowerBounds.A15.hanging_exts
