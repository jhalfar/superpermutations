import LowerBounds.A16Cut
import LowerBounds.A16Core
import LowerBounds.A15Pieces

/-!
# From the components of a configuration to pieces on words at defect 16
(the written proof `proofs/n7_5901/PROOF_5901.md`, sections 2.3, 2.4 and 2.6: Lemma CUT16, Lemma ITEM16,
Lemma PIECE16)

* `groups_ext`: groups of trails joined by links of weight 4 (the parts behind dear seams) as items `E`.
* `kernel_pieces16` (case (lin)): the kernel cut at its dear seams: the first group is the kernel piece,
  every other group an item `E`.
* `cyc_ext` (case (cyc)): a component with free attachment or attachment cost 1 and at least two trails,
  read cyclically: the last and the first group glued through the junction give an item `AB` (it borrows
  the class of the junction), the groups between dear seams give items `E`.
* `hanging_ext16`: every hanging component: as above, a ring (no heavy seam), or (case (lin'),
  attachment cost at least 2) every group an item `E`; items of value at most 0 are left out.
* `hanging_exts16`: the items of all hanging components.
-/

namespace SuperpermLowerBounds
namespace A16

open Hunter PreimageChain T5899

/-! ### Items from rows -/

/-- The item of a list of trails joined by links of weight 4 (at most 11 trails). -/
theorem mk_seq_ext16 (ty : A15.Ty) (hty : ty ≠ .R) {G : List (List (NRow 7))} (hG : TrailFam 7 G)
    (hch : G.IsChain (RowLink 7 4)) (hne : G ≠ []) (h11 : G.length ≤ 11)
    {own bor : List (Vtx 7)} (hperm : (rowsEntries G.flatten).Perm (bor ++ own))
    (hbor : bor.length ≤ 1) (hborE : ty = .E → bor = []) {v : ℤ} {w : ℕ} (hpos : 1 ≤ v)
    (hval : v + ty.dv ≤
      (G.flatten.length : ℤ) - (rowsHoles 7 G.flatten : ℤ) - 5 * ((G.length : ℤ) - 1))
    (hwt : rowsHoles 7 G.flatten + 6 * (G.length - 1) + ty.dw ≤ w) :
    ∃ e : A15.Ext, OK16 e ∧ e.v = v ∧ e.w = w ∧ e.own = own.map Subtype.val ∧ e.ty = ty := by
  obtain ⟨p, hl, hlen, hhol, hbl⟩ := A15.segSeq_spec hG hch hne
  refine ⟨⟨ty, A15.segSeq G, own.map Subtype.val, bor.map Subtype.val, v, w⟩, ?_, rfl, rfl, rfl, rfl⟩
  refine ⟨fun h => absurd h hty, fun _ => p, ?_, by simpa using hbor, ?_, ?_, ?_, hpos, by
    show PS.linksT (A15.segSeq G) ≤ 10
    omega⟩
  · show (KS.blocksT (A15.segSeq G)).Perm (own.map Subtype.val ++ bor.map Subtype.val)
    rw [hbl, ← List.map_append]
    exact (hperm.trans List.perm_append_comm).map _
  · intro h
    show bor.map Subtype.val = []
    rw [hborE h]
    rfl
  · show v + ty.dv ≤ KS.valT (A15.segSeq G)
    unfold KS.valT
    rw [hlen, hhol]
    have h1 : (PS.linksT (A15.segSeq G) : ℤ) = (G.length : ℤ) - 1 := by
      have h2 : ((PS.linksT (A15.segSeq G) + 1 : ℕ) : ℤ) = (G.length : ℤ) := by rw [hl]
      push_cast at h2
      linarith
    rw [h1]
    exact hval
  · show KS.wtT (A15.segSeq G) + ty.dw ≤ w
    unfold KS.wtT
    rw [hhol]
    have h1 : PS.linksT (A15.segSeq G) = G.length - 1 := by omega
    rw [h1]
    exact hwt

/-! ### Groups of trails -/

/-- The value of a group of trails joined by links of weight 4. -/
def valG (g : List (List (NRow 7))) : ℤ :=
  (g.flatten.length : ℤ) - (rowsHoles 7 g.flatten : ℤ) - 5 * ((g.length : ℤ) - 1)

/-- The weight of a group of trails joined by links of weight 4. -/
noncomputable def wtG (g : List (List (NRow 7))) : ℕ := rowsHoles 7 g.flatten + 6 * (g.length - 1)

theorem sum_valG : ∀ G : List (List (List (NRow 7))),
    (G.map valG).sum = (G.flatten.flatten.length : ℤ) - (rowsHoles 7 G.flatten.flatten : ℤ) -
      5 * ((G.flatten.length : ℤ) - (G.length : ℤ))
  | [] => by simp [rowsHoles_nil]
  | g :: G => by
      rw [List.map_cons, List.sum_cons, sum_valG G, List.flatten_cons, List.flatten_append,
        List.length_append, List.length_append, rowsHoles_append, List.length_cons]
      unfold valG
      push_cast
      ring

theorem sum_wtG : ∀ G : List (List (List (NRow 7))), (∀ g ∈ G, g ≠ []) →
    (G.map wtG).sum + 6 * G.length = rowsHoles 7 G.flatten.flatten + 6 * G.flatten.length
  | [], _ => by simp [rowsHoles_nil]
  | g :: G, h => by
      have ih := sum_wtG G (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
      have hg : 1 ≤ g.length := List.length_pos_iff.mpr (h g List.mem_cons_self)
      rw [List.map_cons, List.sum_cons, List.flatten_cons, List.flatten_append,
        List.length_append, rowsHoles_append, List.length_cons]
      have e : wtG g = rowsHoles 7 g.flatten + 6 * (g.length - 1) := rfl
      omega

theorem length_le_of_mem {α : Type} {g : List α} {G : List (List α)} (h : g ∈ G) :
    g.length ≤ G.flatten.length := (List.sublist_flatten_of_mem h).length_le

/-- **Groups as items `E`**: every group of positive value less 10 gives an item that borrows
nothing. -/
theorem groups_ext : ∀ gs : List (List (List (NRow 7))), TrailFam 7 gs.flatten →
    (∀ g ∈ gs, g ≠ [] ∧ g.IsChain (RowLink 7 4) ∧ g.length ≤ 11) →
    ∃ es : List A15.Ext, (∀ e ∈ es, OK16 e) ∧ (∀ e ∈ es, e.ty = .E) ∧ es.length ≤ gs.length ∧
      (es.flatMap A15.Ext.own).Sublist ((rowsEntries gs.flatten.flatten).map Subtype.val) ∧
      (gs.map valG).sum - 10 * (gs.length : ℤ) ≤ (es.map A15.Ext.v).sum ∧
      (es.map A15.Ext.w).sum ≤ (gs.map wtG).sum + 12 * gs.length
  | [], _, _ => ⟨[], by simp, by simp, by simp, by simp, by simp, by simp⟩
  | g :: gs, hF, hg => by
      rw [List.flatten_cons] at hF
      obtain ⟨es, ok, tE, len, sub, sv, sw⟩ := groups_ext gs (A15.trailFam_right hF)
        (fun g' h' => hg g' (List.mem_cons_of_mem _ h'))
      obtain ⟨gne, gch, g11⟩ := hg g List.mem_cons_self
      have hsplit : (rowsEntries (g :: gs).flatten.flatten).map Subtype.val =
          (rowsEntries g.flatten).map Subtype.val ++ (rowsEntries gs.flatten.flatten).map Subtype.val := by
        rw [List.flatten_cons, List.flatten_append, rowsEntries_append, List.map_append]
      by_cases hp : 1 ≤ valG g - 10
      · obtain ⟨e, eok, ev, ew, eown, ety⟩ := mk_seq_ext16 .E (fun h => A15.Ty.noConfusion h)
          (A15.trailFam_left hF) gch gne g11 (own := rowsEntries g.flatten) (bor := [])
          (List.Perm.refl _) (by simp) (fun _ => rfl) (v := valG g - 10) (w := wtG g + 12) hp
          (by show valG g - 10 + 10 ≤ _; unfold valG; linarith)
          (by show rowsHoles 7 g.flatten + 6 * (g.length - 1) + 12 ≤ _; unfold wtG; omega)
        refine ⟨e :: es, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro e' he'
          rcases List.mem_cons.mp he' with rfl | he'
          · exact eok
          · exact ok e' he'
        · intro e' he'
          rcases List.mem_cons.mp he' with rfl | he'
          · exact ety
          · exact tE e' he'
        · simp only [List.length_cons]
          omega
        · rw [List.flatMap_cons, eown, hsplit]
          exact (List.Sublist.refl _).append sub
        · simp only [List.map_cons, List.sum_cons, List.length_cons, ev]
          push_cast
          linarith
        · simp only [List.map_cons, List.sum_cons, List.length_cons, ew]
          omega
      · refine ⟨es, ok, tE, by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
        · rw [hsplit]
          exact sub.trans (List.sublist_append_right _ _)
        · simp only [List.map_cons, List.sum_cons, List.length_cons]
          push_cast
          linarith
        · simp only [List.map_cons, List.sum_cons, List.length_cons]
          omega

/-! ### The kernel (case (lin)) -/

/-- **The kernel as pieces.**  Cut at its dear seams: the first group is the kernel piece, every other
group gives an item `E` (left out if its value is not positive). -/
theorem kernel_pieces16 {R : List (NRow 7)} (hok : RowsOK R) (h11 : (cutRows R).length ≤ 11) :
    ∃ (L0 : List PS.TRow) (es : List A15.Ext), KS.IsPiece (.seq (PS.linksT L0)) L0 ∧
      PS.linksT L0 ≤ 10 ∧ (∀ e ∈ es, OK16 e) ∧
      es.countP (fun e => decide (e.ty = .E)) ≤ epsR R ∧
      (KS.blocksT L0 ++ es.flatMap A15.Ext.own).Sublist ((rowsEntries R).map Subtype.val) ∧
      valR R (rX R) ≤ KS.valT L0 + (es.map A15.Ext.v).sum ∧
      KS.wtT L0 + (es.map A15.Ext.w).sum ≤ wtR R (rX R) := by
  have hadd := hok.eps_add
  have inv := hok.inv
  obtain ⟨G, hG, hGc, hG1, hGl⟩ := cutG R hok.seams hok.ne
  obtain ⟨g0, gs, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hG1)
  have hfam := hok.fam
  rw [hG, List.flatten_cons] at hfam
  have hlenG : ∀ g ∈ g0 :: gs, g.length ≤ 11 := fun g hg => by
    have := length_le_of_mem hg
    rw [← hG] at this
    omega
  obtain ⟨gne, gch⟩ := hGc g0 List.mem_cons_self
  obtain ⟨p, hl, hlen, hhol, hbl⟩ := A15.segSeq_spec (A15.trailFam_left hfam) gch gne
  obtain ⟨es, ok, tE, elen, sub, sv, sw⟩ := groups_ext gs (A15.trailFam_right hfam)
    (fun g hg => ⟨(hGc g (List.mem_cons_of_mem _ hg)).1, (hGc g (List.mem_cons_of_mem _ hg)).2,
      hlenG g (List.mem_cons_of_mem _ hg)⟩)
  have hR : R = g0.flatten ++ gs.flatten.flatten := by
    rw [← inv.flat, hG, List.flatten_cons, List.flatten_append]
  have sv0 := sum_valG gs
  have sw0 := sum_wtG gs (fun g hg => (hGc g (List.mem_cons_of_mem _ hg)).1)
  have hcutlen : (cutRows R).length = g0.length + gs.flatten.length := by
    rw [hG, List.flatten_cons, List.length_append]
  have hg0 := hlenG g0 List.mem_cons_self
  rw [List.length_cons] at hGl
  have e1 : R.length = g0.flatten.length + gs.flatten.flatten.length := by
    rw [hR, List.length_append]
  have e2 : rowsHoles 7 R = rowsHoles 7 g0.flatten + rowsHoles 7 gs.flatten.flatten := by
    rw [hR, rowsHoles_append]
  refine ⟨A15.segSeq g0, es, p, by omega, ok, ?_, ?_, ?_, ?_⟩
  · have := List.countP_le_length (p := fun e : A15.Ext => decide (e.ty = .E)) (l := es)
    omega
  · rw [hbl]
    conv => rhs; rw [hR, rowsEntries_append, List.map_append]
    exact (List.Sublist.refl _).append sub
  · unfold valR KS.valT
    rw [hlen, hhol, e1, e2]
    have hl' : (PS.linksT (A15.segSeq g0) : ℤ) = (g0.length : ℤ) - 1 := by omega
    have hX : ((gs.length : ℕ) : ℤ) + 1 + ((g0.length : ℤ) + (gs.flatten.length : ℤ)) ≤
        (rX R : ℤ) + 2 := by
      have := hGl
      rw [hcutlen] at this
      omega
    push_cast
    rw [hl']
    linarith
  · unfold wtR KS.wtT
    rw [hhol, e2]
    have hl' : PS.linksT (A15.segSeq g0) = g0.length - 1 := by omega
    rw [hl']
    rw [hcutlen] at hGl
    omega

/-! ### Components read cyclically (case (cyc)) -/

/-- The trails of a component with at least two trails, as the first group `P`, the groups `Mg`
between dear seams and the last group `Q`; at most `epsR R` groups lie between. -/
theorem cyc_decomp {R : List (NRow 7)} (hok : RowsOK R) (h2 : 2 ≤ (cutRows R).length) :
    ∃ (P Q : List (List (NRow 7))) (Mg : List (List (List (NRow 7)))),
      cutRows R = P ++ Mg.flatten ++ Q ∧ P ≠ [] ∧ Q ≠ [] ∧ P.IsChain (RowLink 7 4) ∧
      Q.IsChain (RowLink 7 4) ∧ (∀ g ∈ Mg, g ≠ [] ∧ g.IsChain (RowLink 7 4)) ∧
      Mg.length ≤ epsR R := by
  have hadd := hok.eps_add
  obtain ⟨G, hG, hGc, hG1, hGl⟩ := cutG R hok.seams hok.ne
  obtain ⟨g0, G', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hG1)
  rcases G' with _ | ⟨g1, G''⟩
  · -- one group: the first trail and the rest
    obtain ⟨gne, gch⟩ := hGc g0 List.mem_cons_self
    have hg : cutRows R = g0 := by rw [hG]; simp
    obtain ⟨t, rest, rfl⟩ := List.exists_cons_of_ne_nil gne
    have hrest : rest ≠ [] := by
      intro h
      rw [hg, h] at h2
      simp at h2
    refine ⟨[t], rest, [], by rw [hg]; simp, by simp, hrest, List.isChain_singleton _, ?_,
      by simp, by simp⟩
    have := gch.tail
    rwa [List.tail_cons] at this
  · have hne : g1 :: G'' ≠ [] := List.cons_ne_nil _ _
    have hsp := (List.dropLast_concat_getLast hne).symm
    refine ⟨g0, (g1 :: G'').getLast hne, (g1 :: G'').dropLast, ?_, (hGc g0 List.mem_cons_self).1,
      (hGc _ (List.mem_cons_of_mem _ (List.getLast_mem hne))).1,
      (hGc g0 List.mem_cons_self).2,
      (hGc _ (List.mem_cons_of_mem _ (List.getLast_mem hne))).2, ?_, ?_⟩
    · rw [hG, List.flatten_cons]
      conv => lhs; rw [hsp]
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.append_assoc]
    · intro g hg
      exact hGc g (List.mem_cons_of_mem _ ((List.dropLast_sublist _).subset hg))
    · have h1 : ((g1 :: G'').dropLast).length + 1 = (g1 :: G'').length := by
        rw [List.length_dropLast, List.length_cons]
        omega
      simp only [List.length_cons] at hGl h1
      omega

/-- The first and the last group glued through the junction. -/
theorem cyc_glue {R J : List (NRow 7)} {r r₁ : NRow 7} {x : Vtx 7} (hok : RowsOK R)
    {P M Q : List (List (NRow 7))} (hcut : cutRows R = P ++ M ++ Q) (hP : P ≠ []) (hQ : Q ≠ [])
    (cP : P.IsChain (RowLink 7 4)) (cQ : Q.IsChain (RowLink 7 4))
    (hr : R.getLast? = some r) (hr₁ : R.head? = some r₁) (hJ : Junction 7 r r₁ x J)
    (hx : ∀ e ∈ rowsEntries R, NotRot x e) :
    ∃ T : List (List (NRow 7)), TrailFam 7 T ∧ T.IsChain (RowLink 7 4) ∧ T ≠ [] ∧
      T.length + 1 = P.length + Q.length ∧
      T.flatten.length + 2 = P.flatten.length + Q.flatten.length + J.length ∧
      rowsHoles 7 T.flatten + rowsHoles 7 [r, r₁] =
        rowsHoles 7 P.flatten + rowsHoles 7 Q.flatten + rowsHoles 7 J ∧
      (rowsEntries T.flatten).Perm (x :: (rowsEntries P.flatten ++ rowsEntries Q.flatten)) ∧
      (∀ j ∈ J, j.len ≤ 6) := by
  have inv := hok.inv
  obtain ⟨p, S₁, rfl⟩ := List.exists_cons_of_ne_nil hP
  obtain ⟨S₂, q, rfl⟩ : ∃ S₂ q, Q = S₂ ++ [q] :=
    ⟨Q.dropLast, Q.getLast hQ, (List.dropLast_concat_getLast hQ).symm⟩
  have hRf : R = p ++ (S₁.flatten ++ (M.flatten ++ (S₂.flatten ++ q))) := by
    rw [← inv.flat, hcut]
    simp
  have hpne : p ≠ [] := inv.ne p (by rw [hcut]; simp)
  have hqne : q ≠ [] := inv.ne q (by rw [hcut]; simp)
  obtain ⟨a, B, rfl⟩ := List.exists_cons_of_ne_nil hpne
  have ha : a = r₁ := by
    rw [hRf] at hr₁
    simpa using hr₁
  subst ha
  have hq := (List.dropLast_concat_getLast hqne).symm
  have hlast : q.getLast hqne = r := by
    have h1 : R.getLast? = some (q.getLast hqne) := by
      rw [hRf]
      conv => lhs; rw [hq]
      simp only [← List.append_assoc, ← List.cons_append, List.getLast?_concat]
    rw [hr] at h1
    exact (Option.some.inj h1).symm
  rw [hlast] at hq
  have hsub : ((a :: B) :: S₁ ++ (S₂ ++ [q])).Sublist (cutRows R) := by
    rw [hcut, List.append_assoc]
    exact (List.sublist_append_right M _).append_left _
  have hfam : TrailFam 7 (((a :: B) :: S₁) ++ (S₂ ++ [q])) := hok.fam.of_subperm hsub.subperm
  have hx' : ∀ e ∈ rowsEntries (((a :: B) :: S₁) ++ (S₂ ++ [q])).flatten, NotRot x e := by
    intro e he
    apply hx
    rw [← inv.flat]
    unfold rowsEntries at he ⊢
    obtain ⟨row, hrow, he'⟩ := List.mem_flatMap.mp he
    refine List.mem_flatMap.mpr ⟨row, ?_, he'⟩
    obtain ⟨t, ht, hrt⟩ := List.mem_flatten.mp hrow
    exact List.mem_flatten.mpr ⟨t, hsub.subset ht, hrt⟩
  obtain ⟨G0, Gch, Glen, Ghol, Gperm⟩ := A15.glue_split hfam cP cQ rfl hq hJ hx'
  have hJlen : ∀ j ∈ J, j.len ≤ 6 := by
    intro j hj
    refine len_le_of_rowsEntries_pairwise (by norm_num) G0.classes ?_
    refine List.mem_flatten.mpr ⟨glue q.dropLast J B, by simp, ?_⟩
    unfold glue
    exact List.mem_append_right _ (List.mem_append_left _ hj)
  refine ⟨_, G0, Gch, by simp, by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega, ?_, ?_, ?_, hJlen⟩
  · rw [Glen]
    simp only [List.flatten_append, List.length_append, List.flatten_cons, List.length_cons]
  · rw [Ghol]
    simp only [List.flatten_append, rowsHoles_append, List.flatten_cons]
  · have e : rowsEntries (((a :: B) :: S₁) ++ (S₂ ++ [q])).flatten =
        rowsEntries ((a :: B) :: S₁).flatten ++ rowsEntries (S₂ ++ [q]).flatten := by
      rw [List.flatten_append, rowsEntries_append]
    rw [e] at Gperm
    exact Gperm

/-- **The items of a component read cyclically.**  The glued first and last group give an item that
borrows the class of the junction, the groups between dear seams items `E`. -/
theorem cyc_ext {R J : List (NRow 7)} {r r₁ : NRow 7} {x : Vtx 7} (hok : RowsOK R)
    (h11 : (cutRows R).length ≤ 11) {P Q : List (List (NRow 7))} {Mg : List (List (List (NRow 7)))}
    (hcut : cutRows R = P ++ Mg.flatten ++ Q) (hP : P ≠ []) (hQ : Q ≠ [])
    (cP : P.IsChain (RowLink 7 4)) (cQ : Q.IsChain (RowLink 7 4))
    (hMg : ∀ g ∈ Mg, g ≠ [] ∧ g.IsChain (RowLink 7 4))
    (hr : R.getLast? = some r) (hr₁ : R.head? = some r₁) (hJ : Junction 7 r r₁ x J)
    (hx : ∀ e ∈ rowsEntries R, NotRot x e) {δ : ℕ}
    (hholes : (∀ j ∈ J, j.len ≤ 6) → rowsHoles 7 J + δ = rowsHoles 7 [r, r₁]) :
    ∃ es : List A15.Ext, (∀ e ∈ es, OK16 e) ∧
      es.countP (fun e => decide (e.ty = .E)) ≤ Mg.length ∧
      (es.flatMap A15.Ext.own).Subperm ((rowsEntries R).map Subtype.val) ∧
      (R.length : ℤ) + J.length + δ - rowsHoles 7 R - 5 * (cutRows R).length - 3 -
        5 * Mg.length ≤ (es.map A15.Ext.v).sum ∧
      (es.map A15.Ext.w).sum + δ ≤ rowsHoles 7 R + 6 * (cutRows R).length + 1 + 6 * Mg.length := by
  have inv := hok.inv
  obtain ⟨T, Tfam, Tch, Tne, Tl, Tfl, Thol, Tperm, hJlen⟩ :=
    cyc_glue hok hcut hP hQ cP cQ hr hr₁ hJ hx
  have hh := hholes hJlen
  have hRf : R = P.flatten ++ Mg.flatten.flatten ++ Q.flatten := by
    rw [← inv.flat, hcut, List.flatten_append, List.flatten_append]
  have hcl : (cutRows R).length = P.length + Mg.flatten.length + Q.length := by
    rw [hcut, List.length_append, List.length_append]
  have eR : R.length = P.flatten.length + Mg.flatten.flatten.length + Q.flatten.length := by
    rw [hRf, List.length_append, List.length_append]
  have eH : rowsHoles 7 R =
      rowsHoles 7 P.flatten + rowsHoles 7 Mg.flatten.flatten + rowsHoles 7 Q.flatten := by
    rw [hRf, rowsHoles_append, rowsHoles_append]
  have hMsub : Mg.flatten.Sublist (cutRows R) := by
    rw [hcut]
    exact (List.sublist_append_right P _).trans (List.sublist_append_left _ Q)
  obtain ⟨esE, okE, tE, lenE, subE, svE, swE⟩ := groups_ext Mg (hok.fam.of_subperm hMsub.subperm)
    (fun g hg => ⟨(hMg g hg).1, (hMg g hg).2, by
      have h1 := length_le_of_mem hg
      have h2 := hMsub.length_le
      omega⟩)
  have sv0 := sum_valG Mg
  have sw0 := sum_wtG Mg (fun g hg => (hMg g hg).1)
  have hTpos : 1 ≤ T.length := List.length_pos_iff.mpr Tne
  have cntE : esE.countP (fun e => decide (e.ty = .E)) ≤ Mg.length :=
    le_trans List.countP_le_length lenE
  have hperm0 : ((rowsEntries P.flatten ++ rowsEntries Q.flatten) ++ rowsEntries Mg.flatten.flatten).Perm
      (rowsEntries R) := by
    rw [hRf, rowsEntries_append, rowsEntries_append, List.append_assoc, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  have hperm : ((rowsEntries P.flatten ++ rowsEntries Q.flatten).map Subtype.val ++
      (rowsEntries Mg.flatten.flatten).map Subtype.val).Perm ((rowsEntries R).map Subtype.val) := by
    rw [← List.map_append]
    exact hperm0.map _
  -- the value of the glued sequence
  set a : ℤ := (T.flatten.length : ℤ) - (rowsHoles 7 T.flatten : ℤ) - 5 * ((T.length : ℤ) - 1) - 11
    with ha
  have hval_eq : a + ((Mg.map valG).sum - 10 * (Mg.length : ℤ)) =
      (R.length : ℤ) + J.length + δ - rowsHoles 7 R - 5 * (cutRows R).length - 3 -
        5 * Mg.length := by
    rw [ha, sv0, eR, eH, hcl]
    have t1 : ((T.flatten.length : ℕ) : ℤ) + 2 =
        (P.flatten.length : ℤ) + (Q.flatten.length : ℤ) + (J.length : ℤ) := by exact_mod_cast Tfl
    have t2 : ((rowsHoles 7 T.flatten : ℕ) : ℤ) + (δ : ℤ) =
        (rowsHoles 7 P.flatten : ℤ) + (rowsHoles 7 Q.flatten : ℤ) := by
      have : rowsHoles 7 T.flatten + δ = rowsHoles 7 P.flatten + rowsHoles 7 Q.flatten := by omega
      exact_mod_cast this
    have t3 : ((T.length : ℕ) : ℤ) + 1 = (P.length : ℤ) + (Q.length : ℤ) := by exact_mod_cast Tl
    push_cast
    linarith
  have hwt_eq : (rowsHoles 7 T.flatten + 6 * (T.length - 1) + 13) + ((Mg.map wtG).sum + 12 * Mg.length)
      + δ = rowsHoles 7 R + 6 * (cutRows R).length + 1 + 6 * Mg.length := by
    rw [eH, hcl]
    omega
  by_cases hp : 1 ≤ a
  · obtain ⟨e, eok, ev, ew, eown, ety⟩ := mk_seq_ext16 .AB (fun h => A15.Ty.noConfusion h) Tfam Tch
      Tne (by omega) (own := rowsEntries P.flatten ++ rowsEntries Q.flatten) (bor := [x]) Tperm
      (by simp) (fun h => A15.Ty.noConfusion h) (v := a)
      (w := rowsHoles 7 T.flatten + 6 * (T.length - 1) + 13) hp
      (by show a + 11 ≤ _; linarith [ha])
      (by show rowsHoles 7 T.flatten + 6 * (T.length - 1) + 13 ≤ _; omega)
    refine ⟨e :: esE, ?_, ?_, ?_, ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact eok
      · exact okE e' he'
    · rw [List.countP_cons, ety]
      simpa using cntE
    · rw [List.flatMap_cons, eown]
      exact (((List.Sublist.refl _).append subE).subperm).trans hperm.subperm
    · simp only [List.map_cons, List.sum_cons, ev]
      linarith
    · simp only [List.map_cons, List.sum_cons, ew]
      omega
  · refine ⟨esE, okE, cntE, ?_, ?_, ?_⟩
    · exact ((subE.trans (List.sublist_append_right _ _)).subperm).trans hperm.subperm
    · have : a ≤ 0 := by omega
      linarith
    · omega

/-! ### Hanging components -/

variable {c : NConfig 7} {H : NHanging 7}

/-- **Lemma ITEM16 with Lemma PIECE16** for a hanging component: its items. -/
theorem hanging_ext16 (hv : c.Valid) (hH : H ∈ c.hanging) (h11 : (cutRows H.rows).length ≤ 11) :
    ∃ es : List A15.Ext, (∀ e ∈ es, OK16 e) ∧
      (es.flatMap A15.Ext.own).Subperm ((rowsEntries H.rows).map Subtype.val) ∧
      vH H ≤ (es.map A15.Ext.v).sum ∧ (es.map A15.Ext.w).sum ≤ wH H ∧
      es.countP (fun e => decide (e.ty = .E)) ≤ epsH H := by
  by_cases hp : vH H ≤ 0
  · exact ⟨[], by simp, by simp, by simpa using hp, by simp, by simp⟩
  have hp1 : 1 ≤ vH H := by omega
  have hok := hanging_ok hv hH
  have inv := hok.inv
  have hadd := hok.eps_add
  have hpos := hok.pos
  obtain ⟨r₁, hr₁⟩ : ∃ r₁, H.rows.head? = some r₁ := by
    obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil hok.ne
    exact ⟨a, by rw [hl]; rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, H.rows.getLast? = some r :=
    ⟨H.rows.getLast hok.ne, List.getLast?_eq_some_getLast hok.ne⟩
  have single : ∀ e : A15.Ext, e.OK → e.own = (rowsEntries H.rows).map Subtype.val →
      e.v = vH H → e.w = wH H → e.ty = .R →
      ∃ es : List A15.Ext, (∀ e ∈ es, OK16 e) ∧
        (es.flatMap A15.Ext.own).Subperm ((rowsEntries H.rows).map Subtype.val) ∧
        vH H ≤ (es.map A15.Ext.v).sum ∧ (es.map A15.Ext.w).sum ≤ wH H ∧
        es.countP (fun e => decide (e.ty = .E)) ≤ epsH H := by
    intro e eok eown ev ew ety
    refine ⟨[e], fun e' he' => by rw [List.mem_singleton.mp he']; exact OK16.of_ok eok, ?_, ?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, eown]
      exact List.Subperm.refl _
    · simp [ev]
    · simp [ew]
    · simp [ety]
  by_cases hatt : H.att ≤ 1
  · have heps : epsH H = epsR H.rows := by unfold epsH; omega
    by_cases h2 : 2 ≤ (cutRows H.rows).length
    · -- (cyc)
      obtain ⟨P, Q, Mg, hcut, hP, hQ, cP, cQ, hMg, hMl⟩ := cyc_decomp hok h2
      have key : ∀ {x : Vtx 7} {J : List (NRow 7)} {δ : ℕ}, Junction 7 r r₁ x J →
          (∀ e ∈ rowsEntries H.rows, NotRot x e) →
          ((∀ j ∈ J, j.len ≤ 6) → rowsHoles 7 J + δ = rowsHoles 7 [r, r₁]) →
          (J.length : ℤ) + δ = 8 - 5 * H.att → δ + 6 * H.att = 7 →
          ∃ es : List A15.Ext, (∀ e ∈ es, OK16 e) ∧
            (es.flatMap A15.Ext.own).Subperm ((rowsEntries H.rows).map Subtype.val) ∧
            vH H ≤ (es.map A15.Ext.v).sum ∧ (es.map A15.Ext.w).sum ≤ wH H ∧
            es.countP (fun e => decide (e.ty = .E)) ≤ epsH H := by
        intro x J δ hJ hx hholes hJδ hδ
        obtain ⟨es, ok, cnt, sub, sv, sw⟩ := cyc_ext hok h11 hcut hP hQ cP cQ hMg hr hr₁ hJ hx hholes
        refine ⟨es, ok, sub, ?_, ?_, by omega⟩
        · unfold vH valR
          have e1 : ((rX H.rows : ℕ) : ℤ) + 1 =
              (epsR H.rows : ℤ) + ((cutRows H.rows).length : ℤ) := by exact_mod_cast hadd.symm
          have e2 : ((Mg.length : ℕ) : ℤ) ≤ (epsR H.rows : ℤ) := by exact_mod_cast hMl
          push_cast
          linarith
        · unfold wH wtR
          omega
      by_cases ha : H.att = 0
      · obtain ⟨hJ, _, hx⟩ := free_geom hv hH ha hr hr₁
        exact key hJ hx (fun hj => holes_merge (hj _ (List.mem_singleton_self _)))
          (by simp [ha]) (by omega)
      · have ha1 : H.att = 1 := by omega
        rcases cost_one_geom hv hH ha1 hr hr₁ with ⟨hJ, hx⟩ | ⟨y, hJ, hx⟩
        · exact key hJ hx (fun hj => holes_extLast (hj (extLast r) (by simp)))
            (by simp [ha1]) (by omega)
        · exact key hJ hx (fun hj => holes_extFirst (hj (extFirst y r₁) (by simp)))
            (by simp [ha1]) (by omega)
    · -- one trail: a ring
      have h1 : (cutRows H.rows).length = 1 := by omega
      obtain ⟨_, _, hX⟩ := hok.single h1
      by_cases ha : H.att = 0
      · obtain ⟨hJ, _, hx⟩ := free_geom hv hH ha hr hr₁
        have hholes : (∀ j ∈ [mergeRow r r₁], j.len ≤ 6) →
            rowsHoles 7 [mergeRow r r₁] + 7 = rowsHoles 7 [r, r₁] :=
          fun hj => holes_merge (hj _ (List.mem_singleton_self _))
        have hv0 : vH H = valR H.rows (rX H.rows) := by
          unfold vH
          rw [ha, Nat.add_zero]
        have hw0 : wH H = wtR H.rows (rX H.rows) := by
          unfold wH
          rw [ha, Nat.add_zero]
        by_cases h3 : 3 ≤ H.rows.length
        · obtain ⟨e, eok, ev, ew, eown, ety⟩ := A15.glued_ring_ext hok h1 (by omega) hr hr₁ hJ hx
            hholes (by simp only [List.length_singleton]; omega) (v := vH H) (w := wH H) hp1
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
          exact single e eok eown ev ew ety
        · have := free_small hv hH ha h1 (by omega)
          omega
      · have ha1 : H.att = 1 := by omega
        have hv1 : vH H = valR H.rows (rX H.rows + 1) := by
          unfold vH
          rw [ha1]
        have hw1 : wH H = wtR H.rows (rX H.rows + 1) := by
          unfold wH
          rw [ha1]
        have hp1' := hp1
        rw [hv1] at hp1'
        unfold valR at hp1'
        rw [hX] at hp1'
        have hm : 2 ≤ H.rows.length := by
          push_cast at hp1'
          omega
        have key : ∀ {x : Vtx 7} {J : List (NRow 7)}, Junction 7 r r₁ x J →
            (∀ e ∈ rowsEntries H.rows, NotRot x e) → J.length = 2 →
            ((∀ j ∈ J, j.len ≤ 6) → rowsHoles 7 J + 1 = rowsHoles 7 [r, r₁]) →
            ∃ es : List A15.Ext, (∀ e ∈ es, OK16 e) ∧
              (es.flatMap A15.Ext.own).Subperm ((rowsEntries H.rows).map Subtype.val) ∧
              vH H ≤ (es.map A15.Ext.v).sum ∧ (es.map A15.Ext.w).sum ≤ wH H ∧
              es.countP (fun e => decide (e.ty = .E)) ≤ epsH H := by
          intro x J hJ hx hJ2 hholes
          obtain ⟨e, eok, ev, ew, eown, ety⟩ := A15.glued_ring_ext hok h1 hm hr hr₁ hJ hx hholes
            (by omega) (v := vH H) (w := wH H) hp1
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
          exact single e eok eown ev ew ety
        rcases cost_one_geom hv hH ha1 hr hr₁ with ⟨hJ, hx⟩ | ⟨y, hJ, hx⟩
        · exact key hJ hx rfl (fun hj => holes_extLast (hj (extLast r) (by simp)))
        · exact key hJ hx rfl (fun hj => holes_extFirst (hj (extFirst y r₁) (by simp)))
  · -- (lin'): attachment cost at least 2, every group an item E
    have ha2 : 2 ≤ H.att := by omega
    obtain ⟨G, hG, hGc, hG1, hGl⟩ := cutG H.rows hok.seams hok.ne
    have hfam := hok.fam
    rw [hG] at hfam
    obtain ⟨es, ok, tE, elen, sub, sv, sw⟩ := groups_ext G hfam
      (fun g hg => ⟨(hGc g hg).1, (hGc g hg).2, by
        have := length_le_of_mem hg
        rw [← hG] at this
        omega⟩)
    have hR : H.rows = G.flatten.flatten := by rw [← inv.flat, hG]
    have sv0 := sum_valG G
    have sw0 := sum_wtG G (fun g hg => (hGc g hg).1)
    have eR : H.rows.length = G.flatten.flatten.length := by rw [hR]
    have eH : rowsHoles 7 H.rows = rowsHoles 7 G.flatten.flatten := by rw [hR]
    have hcl : (cutRows H.rows).length = G.flatten.length := by rw [hG]
    refine ⟨es, ok, ?_, ?_, ?_, ?_⟩
    · rw [hR]
      exact sub.subperm
    · unfold vH valR
      rw [eR, eH]
      have e1 : ((rX H.rows : ℕ) : ℤ) + 2 ≥ ((G.length : ℕ) : ℤ) + (G.flatten.length : ℤ) := by
        rw [hcl] at hGl
        exact_mod_cast hGl
      have e2 : (2 : ℤ) ≤ (H.att : ℤ) := by exact_mod_cast ha2
      push_cast
      linarith
    · unfold wH wtR
      rw [eH]
      rw [hcl] at hGl
      omega
    · have := List.countP_le_length (p := fun e : A15.Ext => decide (e.ty = .E)) (l := es)
      unfold epsH
      rw [hcl] at hGl hadd
      omega

theorem subperm_append {α : Type} {a b c d : List α} (h1 : a.Subperm b) (h2 : c.Subperm d) :
    (a ++ c).Subperm (b ++ d) := by
  obtain ⟨l1, p1, s1⟩ := h1
  obtain ⟨l2, p2, s2⟩ := h2
  exact ⟨l1 ++ l2, p1.append p2, s1.append s2⟩

/-- **The items of the hanging components.** -/
theorem hanging_exts16 (hv : c.Valid) (h11 : ∀ H ∈ c.hanging, (cutRows H.rows).length ≤ 11) :
    ∀ Hs : List (NHanging 7), (∀ H ∈ Hs, H ∈ c.hanging) →
      ∃ es : List A15.Ext, (∀ e ∈ es, OK16 e) ∧
        (es.flatMap A15.Ext.own).Subperm
          ((Hs.flatMap fun H => rowsEntries H.rows).map Subtype.val) ∧
        (Hs.map vH).sum ≤ (es.map A15.Ext.v).sum ∧ (es.map A15.Ext.w).sum ≤ (Hs.map wH).sum ∧
        es.countP (fun e => decide (e.ty = .E)) ≤ (Hs.map epsH).sum
  | [], _ => ⟨[], by simp, by simp, by simp, by simp, by simp⟩
  | H :: Hs, h => by
      obtain ⟨es, ok, sub, sv, sw, cnt⟩ :=
        hanging_exts16 hv h11 Hs (fun H' hH' => h H' (List.mem_cons_of_mem _ hH'))
      have hH := h H List.mem_cons_self
      obtain ⟨es1, ok1, sub1, sv1, sw1, cnt1⟩ := hanging_ext16 hv hH (h11 H hH)
      refine ⟨es1 ++ es, ?_, ?_, ?_, ?_, ?_⟩
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact ok1 e he
        · exact ok e he
      · rw [List.flatMap_append, List.flatMap_cons, List.map_append]
        exact subperm_append sub1 sub
      · rw [List.map_cons, List.sum_cons, List.map_append, List.sum_append]
        linarith
      · rw [List.map_cons, List.sum_cons, List.map_append, List.sum_append]
        omega
      · rw [List.map_cons, List.sum_cons, List.countP_append]
        omega

end A16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.A16.kernel_pieces16
#print axioms SuperpermLowerBounds.A16.hanging_exts16
