import LowerBounds.J15Sound

/-!
# A counterexample with the fewest rows is found (the written proof, section 5.4)

`JW k specs V W B`: there are no pieces of the kinds `specs` (a triple `(c, lo, hi)`: `c = 0` a
ring whose number of holes lies in `lo … hi`, `c = s + 1` a sequence with at most `s` links of
weight 4) with total weight at most `W`, total value at least `V` and at most `B` shared
classes.  The shared classes are counted as in `J15Sound.lean`: the blocks of all pieces are at
most `B` more than their classes (`Sh`).

`jw_of_parts`: if every part of the search answers `false`, `JW` holds, given the tables: `P t`
bounds the rows of a sequence with `t` links and `PR` those of a ring (`CapsOK`), and the three
tests of the engine answer `true` whenever the functions `bestF`, `fF` of `J15Search.lean` allow
it.

The proof is that of the written proof.  Take a counterexample with the fewest rows in which
every ring is read in the rotation of the cycle lemma (`Cyc`), and rename the symbols so that it
starts at `1 2 … k`.  Then the rule of the engine holds along its rows (`JAlong`):

* step 2, record: a proper prefix of a sequence piece has a smaller value, otherwise the prefix
  replaces the piece (`MinAt.rec_lt`);
* step 3, rest: the rest behind a cut has a smaller value than the piece, otherwise the rest
  replaces the piece (`MinAt.rest_lt`); this gives `val(A) ≥ 1`, or `val(A) - (k - 2) ≥ 1` at a
  link of weight 4;
* step 4, table bound: the rest of the piece and the later pieces are single objects, so their
  total value is at most `bestF` (`best_bound`);
* step 5: the rest of a ring is a chain, the ring obeys its cap, and the prefix has at most its
  share of the holes.
-/

namespace SuperpermLowerBounds
namespace J15

open S (PermW WLink DoorEq)
open PS (TRow IsSeq holesT linksT Closes SeqCapLt RingCapT LinkK relabSeq)
open KS (maxLe)

variable {k : ℕ}

/-! ### Values, weights, blocks -/

/-- The value of a list of rows: rows less holes less `k - 2` for every link of weight 4. -/
def valK (k : ℕ) (L : List TRow) : ℤ := vOf (k - 1) (linksT L) L.length (holesT k L)

/-- The weight of a list of rows: holes plus `k - 1` for every link of weight 4. -/
def wtK (k : ℕ) (L : List TRow) : ℕ := holesT k L + (k - 1) * linksT L

/-- `1` if the link before the row has weight 4. -/
def lk (x : TRow) : ℕ := if x.1 = 0 then 0 else 1

theorem valK_append (u : List TRow) (x : TRow) (w : List TRow) (hu : u ≠ []) :
    valK k (u ++ x :: w) = valK k u + valK k (x :: w) - (((k - 1 - 1) * lk x : ℕ) : ℤ) := by
  unfold valK vOf lk
  rw [PS.linksT_append u x w hu, PS.holesT_append, List.length_append]
  push_cast
  ring

theorem wtK_append (u : List TRow) (x : TRow) (w : List TRow) (hu : u ≠ []) :
    wtK k (u ++ x :: w) = wtK k u + (k - 1) * lk x + wtK k (x :: w) := by
  unfold wtK lk
  rw [PS.linksT_append u x w hu, PS.holesT_append]
  ring

theorem blocksR_append (A B : List TRow) : blocksR (A ++ B) = blocksR A ++ blocksR B := by
  simp [blocksR]

/-- The first block of a list of rows. -/
def firstB (L : List TRow) : List ℕ := (L.head?.bind fun x => x.2.head?).getD []

/-- The last block of a list of rows. -/
def lastB (L : List TRow) : List ℕ := (L.getLast?.bind fun x => x.2.getLast?).getD []

theorem lastB_eq {u : List TRow} (hu : u ≠ []) (ha : (u.getLast hu).2 ≠ []) :
    lastB u = (u.getLast hu).2.getLast ha := by
  unfold lastB
  rw [List.getLast?_eq_some_getLast hu]
  show ((u.getLast hu).2.getLast?).getD [] = _
  rw [List.getLast?_eq_some_getLast ha]
  rfl

theorem lastB_snoc (u : List TRow) (kd : ℕ) (v : List ℕ) (R : List (List ℕ)) :
    lastB (u ++ [(kd, v :: R)]) = (v :: R).getLast (List.cons_ne_nil v R) := by
  have h : (u ++ [(kd, v :: R)]).getLast? = some (kd, v :: R) := by simp
  unfold lastB
  rw [h]
  show ((v :: R).getLast?).getD [] = _
  rw [List.getLast?_eq_some_getLast (List.cons_ne_nil v R)]
  rfl

/-- The first row of a piece becomes a row that starts a piece. -/
def retag : List TRow → List TRow
  | [] => []
  | x :: L => (2, x.2) :: L

/-- The rows of a list of pieces, every piece after a jump. -/
def flatJ (Ls : List (List TRow)) : List TRow := (Ls.map retag).flatten

theorem blocksR_retag : ∀ L : List TRow, blocksR (retag L) = blocksR L
  | [] => rfl
  | _ :: _ => rfl

theorem blocksR_flatJ : ∀ Ls : List (List TRow), blocksR (flatJ Ls) = blocksR Ls.flatten
  | [] => rfl
  | L :: Ls => by
    show blocksR (retag L ++ flatJ Ls) = blocksR (L ++ Ls.flatten)
    rw [blocksR_append, blocksR_append, blocksR_retag, blocksR_flatJ Ls]

theorem le_maxLe (f : ℕ → ℤ) : ∀ n i : ℕ, i ≤ n → f i ≤ maxLe f n
  | 0, i, h => by
    have e : i = 0 := by omega
    subst e
    exact le_refl _
  | n + 1, i, h => by
    show f i ≤ max (maxLe f n) (f (n + 1))
    rcases Nat.lt_or_ge i (n + 1) with h1 | h1
    · exact le_trans (le_maxLe f n i (by omega)) (le_max_left _ _)
    · have e : i = n + 1 := by omega
      subst e
      exact le_max_right _ _

/-! ### Pieces and the statement -/

/-- A piece of the kind `p = (c, lo, hi)`. -/
def IsPieceW (k : ℕ) (p : ℕ × ℕ × ℕ) (L : List TRow) : Prop :=
  if p.1 = 0 then
    IsSeq k L ∧ (∀ x ∈ L, x.1 = 0) ∧ 2 ≤ L.length ∧ Closes k L ∧ p.2.1 ≤ holesT k L ∧
      holesT k L ≤ p.2.2
  else IsSeq k L ∧ L ≠ [] ∧ (∀ x ∈ L, x.1 ≤ 1) ∧ linksT L + 1 ≤ p.1

/-- The blocks of the pieces are at most `B` more than their classes. -/
def Sh (B : ℕ) (Ls : List (List TRow)) : Prop :=
  (blocksR Ls.flatten).length ≤ B + clsCount (blocksR Ls.flatten)

/-- J(specs; V, W; B). -/
def JW (k : ℕ) (specs : List (ℕ × ℕ × ℕ)) (V : ℤ) (W B : ℕ) : Prop :=
  ∀ Ls : List (List TRow), List.Forall₂ (IsPieceW k) specs Ls → Sh B Ls →
    (Ls.map (wtK k)).sum ≤ W → (Ls.map (valK k)).sum < V

theorem IsPieceW.isSeq {p : ℕ × ℕ × ℕ} {L : List TRow} (h : IsPieceW k p L) : IsSeq k L := by
  unfold IsPieceW at h
  split_ifs at h
  · exact h.1
  · exact h.1

theorem IsPieceW.ne_nil {p : ℕ × ℕ × ℕ} {L : List TRow} (h : IsPieceW k p L) : L ≠ [] := by
  unfold IsPieceW at h
  split_ifs at h
  · intro e
    rw [e] at h
    simp at h
  · exact h.2.1

theorem IsPieceW.le_one {p : ℕ × ℕ × ℕ} {L : List TRow} (h : IsPieceW k p L) :
    ∀ x ∈ L, x.1 ≤ 1 := by
  unfold IsPieceW at h
  split_ifs at h
  · intro x hx
    rw [h.2.1 x hx]
    omega
  · exact h.2.2.1

/-- The tables: `P t` for sequences with `t ≤ sm` links within weight `W`, `PR` for rings. -/
structure CapsOK (k : ℕ) (P : ℕ → ℕ → ℕ) (PR : ℕ → ℕ) (W sm : ℕ) : Prop where
  seq : ∀ t, t ≤ sm → SeqCapLt k t (P t) (W + 1 - (k - 1) * t)
  ring : RingCapT k PR W

section Bound

variable {P : ℕ → ℕ → ℕ} {PR : ℕ → ℕ} {W sm : ℕ}

/-- A single piece has at most its table value. -/
theorem piece_le (hc : CapsOK k P PR W sm) (p : ℕ × ℕ × ℕ) (L : List TRow)
    (h : IsPieceW k p L) (hp : p.1 ≤ sm + 1) (hw : wtK k L ≤ W) :
    valK k L ≤ pval P PR (k - 1) p (wtK k L) := by
  unfold IsPieceW at h
  by_cases h0 : p.1 = 0
  · rw [if_pos h0] at h
    obtain ⟨hL, hk0, h2, hcl, hlo, hhi⟩ := h
    have hl : linksT L = 0 := PS.linksT_zero hk0
    have hw' : wtK k L = holesT k L := by
      unfold wtK
      rw [hl]
      simp
    have hcap := hc.ring L hL hk0 h2 hcl (by rw [← hw']; exact hw)
    unfold pval
    rw [if_pos h0, hw', if_pos ⟨hlo, hhi⟩]
    unfold valK vOf
    rw [hl]
    have hcap' : (L.length : ℤ) ≤ (PR (holesT k L) : ℕ) := by exact_mod_cast hcap
    simp only [Nat.mul_zero, Nat.cast_zero, sub_zero]
    linarith
  · rw [if_neg h0] at h
    obtain ⟨hL, _, hk1, hlk⟩ := h
    have e1 : (k - 1) * linksT L ≤ wtK k L := by
      unfold wtK
      omega
    have e2 : wtK k L - (k - 1) * linksT L = holesT k L := by
      unfold wtK
      omega
    have hcap := hc.seq (linksT L) (by omega) L hL hk1 rfl (by unfold wtK at hw; omega)
    have hcap' : (L.length : ℤ) ≤ (P (linksT L) (holesT k L) : ℕ) := by exact_mod_cast hcap
    unfold pval
    rw [if_neg h0]
    refine le_trans ?_ (le_maxLe _ (p.1 - 1) (linksT L) (by omega))
    show valK k L ≤ if (k - 1) * linksT L ≤ wtK k L then
      sval P (k - 1) (linksT L) (wtK k L - (k - 1) * linksT L) else negInf
    rw [if_pos e1, e2]
    unfold valK vOf sval
    linarith

/-- **Table bound.**  Pieces of the kinds `sps` within weight `y` have total value at most
`bestF sps y`. -/
theorem best_bound (hc : CapsOK k P PR W sm) : ∀ (sps : List (ℕ × ℕ × ℕ))
    (Ps : List (List TRow)), List.Forall₂ (IsPieceW k) sps Ps → (∀ p ∈ sps, p.1 ≤ sm + 1) →
    ∀ y, (Ps.map (wtK k)).sum ≤ y → y ≤ W →
      (Ps.map (valK k)).sum ≤ bestF P PR (k - 1) sps y := by
  intro sps Ps h
  induction h with
  | nil =>
    intro _ y _ _
    exact le_refl _
  | @cons p L ps Ps' hpl _ ih =>
    intro hsm y hy hyW
    simp only [List.map_cons, List.sum_cons] at hy ⊢
    have h1 := piece_le hc p L hpl (hsm p List.mem_cons_self) (by omega)
    have h2 := ih (fun q hq => hsm q (List.mem_cons_of_mem _ hq)) (y - wtK k L) (by omega)
      (by omega)
    show _ ≤ maxLe (fun w => pval P PR (k - 1) p w + bestF P PR (k - 1) ps (y - w)) y
    exact le_trans (add_le_add h1 h2) (le_maxLe _ y (wtK k L) (by omega))

end Bound

/-! ### Counterexamples -/

/-- The prefixes of a ring have at most their share of the holes. -/
def Cyc (k : ℕ) (L : List TRow) : Prop :=
  ∀ u w, L = u ++ w → holesT k u * L.length ≤ u.length * holesT k L

/-- A piece, a ring being read in the rotation of the cycle lemma. -/
def IsPieceC (k : ℕ) (p : ℕ × ℕ × ℕ) (L : List TRow) : Prop :=
  IsPieceW k p L ∧ (p.1 = 0 → Cyc k L)

/-- A counterexample to J(specs; V, W; B). -/
def CE (k : ℕ) (specs : List (ℕ × ℕ × ℕ)) (V : ℤ) (W B : ℕ) (Ls : List (List TRow)) : Prop :=
  List.Forall₂ (IsPieceC k) specs Ls ∧ Sh B Ls ∧ (Ls.map (wtK k)).sum ≤ W ∧
    V ≤ (Ls.map (valK k)).sum

/-- A piece can be read so that it is a piece in the sense of `IsPieceC`. -/
theorem norm1 (p : ℕ × ℕ × ℕ) (L : List TRow) (h : IsPieceW k p L) :
    ∃ L', IsPieceC k p L' ∧ L'.Perm L ∧ wtK k L' = wtK k L ∧ valK k L' = valK k L := by
  by_cases h0 : p.1 = 0
  · have h' := h
    unfold IsPieceW at h'
    rw [if_pos h0] at h'
    obtain ⟨hL, hk0, h2, hcl, hlo, hhi⟩ := h'
    obtain ⟨A, B, hAB, hcyc⟩ := PS.cycle_lemma (fun x : TRow => k - 1 - x.2.length) L
    subst hAB
    obtain ⟨hL', hc'⟩ := PS.isSeq_rotate A B hL hk0 hcl
    have hk0' : ∀ x ∈ B ++ A, x.1 = 0 := by
      intro x hx
      apply hk0
      simp only [List.mem_append] at hx ⊢
      tauto
    have hlen : (B ++ A).length = (A ++ B).length := by
      simp only [List.length_append]
      omega
    have hhol : holesT k (B ++ A) = holesT k (A ++ B) := by
      rw [PS.holesT_append, PS.holesT_append]
      omega
    refine ⟨B ++ A, ⟨?_, fun _ => ?_⟩, List.perm_append_comm, ?_, ?_⟩
    · unfold IsPieceW
      rw [if_pos h0]
      exact ⟨hL', hk0', by omega, hc', by omega, by omega⟩
    · intro u w huw
      have := hcyc u w huw
      rw [hlen, hhol]
      exact this
    · unfold wtK
      rw [hhol, PS.linksT_zero hk0', PS.linksT_zero hk0]
    · unfold valK
      rw [hhol, hlen, PS.linksT_zero hk0', PS.linksT_zero hk0]
  · exact ⟨L, ⟨h, fun h' => absurd h' h0⟩, List.Perm.refl _, rfl, rfl⟩

theorem norm : ∀ (specs : List (ℕ × ℕ × ℕ)) (Ls : List (List TRow)),
    List.Forall₂ (IsPieceW k) specs Ls →
    ∃ Ls', List.Forall₂ (IsPieceC k) specs Ls' ∧
      (blocksR Ls'.flatten).Perm (blocksR Ls.flatten) ∧ Ls'.map (wtK k) = Ls.map (wtK k) ∧
      Ls'.map (valK k) = Ls.map (valK k) := by
  intro specs Ls h
  induction h with
  | nil => exact ⟨[], List.Forall₂.nil, List.Perm.refl _, rfl, rfl⟩
  | @cons p L ps Ps hpl _ ih =>
    obtain ⟨L', h1, h2, h3, h4⟩ := norm1 p L hpl
    obtain ⟨Ls', g1, g2, g3, g4⟩ := ih
    refine ⟨L' :: Ls', List.Forall₂.cons h1 g1, ?_, ?_, ?_⟩
    · show (blocksR (L' ++ Ls'.flatten)).Perm (blocksR (L ++ Ps.flatten))
      rw [blocksR_append, blocksR_append]
      exact ((h2.map Prod.snd).flatten).append g2
    · simp only [List.map_cons, h3, g3]
    · simp only [List.map_cons, h4, g4]

open Classical in
/-- A counterexample with the fewest rows. -/
theorem exists_min {specs : List (ℕ × ℕ × ℕ)} {V : ℤ} {W B : ℕ}
    (h : ∃ Ls, CE k specs V W B Ls) :
    ∃ Ls, CE k specs V W B Ls ∧
      ∀ Ls', CE k specs V W B Ls' → Ls.flatten.length ≤ Ls'.flatten.length := by
  have hex : ∃ n, ∃ Ls, CE k specs V W B Ls ∧ Ls.flatten.length = n := by
    obtain ⟨Ls, hLs⟩ := h
    exact ⟨_, Ls, hLs, rfl⟩
  obtain ⟨Ls, hce, hn⟩ := Nat.find_spec hex
  refine ⟨Ls, hce, fun Ls' h' => ?_⟩
  rw [hn]
  exact Nat.find_min' hex ⟨Ls', h', rfl⟩

/-! ### Renaming the symbols -/

theorem holesT_relab (e : List ℕ) (L : List TRow) : holesT k (relabSeq e L) = holesT k L := by
  simp [holesT, relabSeq, List.map_map, Function.comp_def]

theorem linksT_relab (e : List ℕ) (L : List TRow) : linksT (relabSeq e L) = linksT L := by
  cases L with
  | nil => rfl
  | cons x u =>
    show (List.map _ u).countP _ = u.countP _
    rw [List.countP_map]
    rfl

theorem length_relab (e : List ℕ) (L : List TRow) : (relabSeq e L).length = L.length := by
  simp [relabSeq]

theorem valK_relab (e : List ℕ) (L : List TRow) : valK k (relabSeq e L) = valK k L := by
  unfold valK
  rw [holesT_relab, linksT_relab, length_relab]

theorem wtK_relab (e : List ℕ) (L : List TRow) : wtK k (relabSeq e L) = wtK k L := by
  unfold wtK
  rw [holesT_relab, linksT_relab]

theorem blocksR_relab (e : List ℕ) (L : List TRow) :
    blocksR (relabSeq e L) = (blocksR L).map (List.map (S.relab e)) := by
  have e1 : (relabSeq e L).map Prod.snd = (L.map Prod.snd).map (List.map (List.map (S.relab e))) := by
    simp [relabSeq, List.map_map, Function.comp_def]
  unfold blocksR
  rw [e1, ← List.map_flatten]

theorem closes_relab (e : List ℕ) {L : List TRow} (h : Closes k L) :
    Closes k (relabSeq e L) := by
  intro u hu v hv
  unfold relabSeq at hu hv
  rw [List.getLast?_map] at hu
  rw [List.head?_map] at hv
  simp only [Option.mem_def, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hu hv
  obtain ⟨y, ⟨y0, hy0, rfl⟩, hyu⟩ := hu
  obtain ⟨z, ⟨z0, hz0, rfl⟩, hzv⟩ := hv
  rw [List.getLast?_map] at hyu
  rw [List.head?_map] at hzv
  simp only [Option.map_eq_some_iff] at hyu hzv
  obtain ⟨u0, hu0, rfl⟩ := hyu
  obtain ⟨w0, hw0, rfl⟩ := hzv
  exact (h u0 (by simp [hy0, hu0]) w0 (by simp [hz0, hw0])).map _

theorem pieceC_relab {e : List ℕ} (he : PermW k e) {p : ℕ × ℕ × ℕ} {L : List TRow}
    (h : IsPieceC k p L) : IsPieceC k p (relabSeq e L) := by
  obtain ⟨hw, hcy⟩ := h
  have hmem : ∀ x ∈ relabSeq e L, ∃ x0 ∈ L, x.1 = x0.1 := by
    intro x hx
    obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hx
    exact ⟨x0, hx0, rfl⟩
  refine ⟨?_, fun h0 u w huw => ?_⟩
  · unfold IsPieceW at hw ⊢
    by_cases h0 : p.1 = 0
    · rw [if_pos h0] at hw ⊢
      obtain ⟨hL, hk0, h2, hcl, hlo, hhi⟩ := hw
      refine ⟨hL.relabel he, ?_, by rw [length_relab]; exact h2, closes_relab e hcl,
        by rw [holesT_relab]; exact hlo, by rw [holesT_relab]; exact hhi⟩
      intro x hx
      obtain ⟨x0, hx0, e0⟩ := hmem x hx
      rw [e0]
      exact hk0 x0 hx0
    · rw [if_neg h0] at hw ⊢
      obtain ⟨hL, hne, hk1, hlk⟩ := hw
      refine ⟨hL.relabel he, ?_, ?_, by rw [linksT_relab]; exact hlk⟩
      · intro e0
        apply hne
        have := congrArg List.length e0
        rw [length_relab] at this
        exact List.length_eq_zero_iff.mp this
      · intro x hx
        obtain ⟨x0, hx0, e0⟩ := hmem x hx
        rw [e0]
        exact hk1 x0 hx0
  · obtain ⟨u0, w0, e0, hu0, _⟩ := List.map_eq_append_iff.mp huw
    have h1 := hcy h0 u0 w0 e0
    have e1 : holesT k u = holesT k u0 := by
      rw [← hu0]
      exact holesT_relab e u0
    have e2 : u.length = u0.length := by
      rw [← hu0]
      exact List.length_map _
    rw [e1, e2, length_relab, holesT_relab]
    exact h1

theorem forall₂_mem {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {u : List β},
    List.Forall₂ R l u → ∀ b ∈ u, ∃ a ∈ l, R a b
  | _, _, List.Forall₂.nil, _, hb => by cases hb
  | _, _, List.Forall₂.cons h hs, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨a, ha, hr⟩ := forall₂_mem hs b hb'
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-- The blocks of a counterexample are permutation words. -/
theorem CE.words {specs : List (ℕ × ℕ × ℕ)} {V : ℤ} {W B : ℕ} {Ls : List (List TRow)}
    (h : CE k specs V W B Ls) : ∀ w ∈ blocksR Ls.flatten, PermW k w := by
  intro w hw
  unfold blocksR at hw
  obtain ⟨Q, hQ, hwQ⟩ := List.mem_flatten.mp hw
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hQ
  obtain ⟨L, hL, hxL⟩ := List.mem_flatten.mp hx
  obtain ⟨p, _, hp⟩ := forall₂_mem h.1 L hL
  exact hp.1.isSeq.words x hxL w hwQ

theorem flatten_relab (e : List ℕ) (Ls : List (List TRow)) :
    (Ls.map (relabSeq e)).flatten = relabSeq e Ls.flatten := by
  unfold relabSeq
  rw [List.map_flatten]

/-- A renamed counterexample is a counterexample with the same number of rows. -/
theorem CE.relabel {specs : List (ℕ × ℕ × ℕ)} {V : ℤ} {W B : ℕ} {Ls : List (List TRow)}
    (h : CE k specs V W B Ls) {e : List ℕ} (he : PermW k e) :
    CE k specs V W B (Ls.map (relabSeq e)) ∧
      (Ls.map (relabSeq e)).flatten.length = Ls.flatten.length := by
  have hwords := h.words
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [List.forall₂_map_right_iff]
    exact h1.imp fun _ _ hp => pieceC_relab he hp
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

/-! ### The piece of a counterexample with the fewest rows -/

theorem forall₂_app {α β : Type} {R : α → β → Prop} : ∀ {a : List α} {b : List β} {c : List α}
    {d : List β}, List.Forall₂ R a b → List.Forall₂ R c d → List.Forall₂ R (a ++ c) (b ++ d)
  | _, _, _, _, List.Forall₂.nil, h => h
  | _, _, _, _, List.Forall₂.cons h hs, h' => List.Forall₂.cons h (forall₂_app hs h')

theorem getD_mid {α : Type} (a : List α) (x : α) (b : List α) (d : α) :
    (a ++ x :: b).getD a.length d = x := by
  induction a with
  | nil => rfl
  | cons y l ih => simp

theorem drop_mid {α : Type} (a : List α) (x : α) (b : List α) :
    (a ++ x :: b).drop (a.length + 1) = b := by
  induction a with
  | nil => rfl
  | cons y l ih => simp

/-- The piece `S` of a counterexample with the fewest rows, between the pieces `Pre` and
`Post`. -/
structure MinAt (k : ℕ) (specs : List (ℕ × ℕ × ℕ)) (V : ℤ) (W B : ℕ)
    (spre : List (ℕ × ℕ × ℕ)) (Pre : List (List TRow)) (sp : ℕ × ℕ × ℕ) (S : List TRow)
    (spost : List (ℕ × ℕ × ℕ)) (Post : List (List TRow)) : Prop where
  hspec : specs = spre ++ sp :: spost
  hPre : List.Forall₂ (IsPieceC k) spre Pre
  hS : IsPieceC k sp S
  hPost : List.Forall₂ (IsPieceC k) spost Post
  hSh : Sh B (Pre ++ S :: Post)
  hW : ((Pre ++ S :: Post).map (wtK k)).sum ≤ W
  hV : V ≤ ((Pre ++ S :: Post).map (valK k)).sum
  hmin : ∀ Ls', CE k specs V W B Ls' → (Pre ++ S :: Post).flatten.length ≤ Ls'.flatten.length

section Min

variable {specs : List (ℕ × ℕ × ℕ)} {V : ℤ} {W B : ℕ} {spre : List (ℕ × ℕ × ℕ)}
  {Pre : List (List TRow)} {sp : ℕ × ℕ × ℕ} {S : List TRow} {spost : List (ℕ × ℕ × ℕ)}
  {Post : List (List TRow)}

theorem MinAt.sumW (M : MinAt k specs V W B spre Pre sp S spost Post) :
    (Pre.map (wtK k)).sum + wtK k S + (Post.map (wtK k)).sum ≤ W := by
  have := M.hW
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at this
  omega

theorem MinAt.sumV (M : MinAt k specs V W B spre Pre sp S spost Post) :
    V ≤ (Pre.map (valK k)).sum + valK k S + (Post.map (valK k)).sum := by
  have := M.hV
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at this
  linarith

/-- The next piece. -/
theorem MinAt.next {sp' : ℕ × ℕ × ℕ} {S' : List TRow} {spost' : List (ℕ × ℕ × ℕ)}
    {Post' : List (List TRow)}
    (M : MinAt k specs V W B spre Pre sp S (sp' :: spost') (S' :: Post')) :
    MinAt k specs V W B (spre ++ [sp]) (Pre ++ [S]) sp' S' spost' Post' := by
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

/-- A piece that replaces `S` does not have fewer rows. -/
theorem MinAt.rep (M : MinAt k specs V W B spre Pre sp S spost Post) (S' : List TRow)
    (h1 : IsPieceC k sp S') (h2 : (blocksR S').Sublist (blocksR S)) (h3 : wtK k S' ≤ wtK k S)
    (h4 : valK k S ≤ valK k S') : S.length ≤ S'.length := by
  have hce : CE k specs V W B (Pre ++ S' :: Post) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [M.hspec]
      exact forall₂_app M.hPre (List.Forall₂.cons h1 M.hPost)
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

theorem piece_prefix {p : ℕ × ℕ × ℕ} {u : List TRow} {x : TRow} {w : List TRow}
    (h : IsPieceW k p (u ++ x :: w)) (h0 : p.1 ≠ 0) (hu : u ≠ []) : IsPieceW k p u := by
  unfold IsPieceW at h ⊢
  rw [if_neg h0] at h ⊢
  obtain ⟨hL, _, hk1, hlk⟩ := h
  rw [PS.linksT_append u x w hu] at hlk
  exact ⟨hL.infix (List.prefix_append u _).isInfix, hu,
    fun y hy => hk1 y (List.mem_append_left _ hy), by omega⟩

theorem piece_suffix {p : ℕ × ℕ × ℕ} {u : List TRow} {x : TRow} {w : List TRow}
    (h : IsPieceW k p (u ++ x :: w)) (h0 : p.1 ≠ 0) (hu : u ≠ []) :
    IsPieceW k (p.1 - linksT u - lk x, 0, 0) (x :: w) ∧ linksT u + lk x + 1 ≤ p.1 ∧
      IsPieceW k p (x :: w) := by
  unfold IsPieceW at h
  rw [if_neg h0] at h
  obtain ⟨hL, _, hk1, hlk⟩ := h
  rw [PS.linksT_append u x w hu] at hlk
  have hlk' : linksT u + lk x + linksT (x :: w) + 1 ≤ p.1 := hlk
  have hsq : IsSeq k (x :: w) := hL.infix (List.suffix_append u _).isInfix
  have hk1' : ∀ y ∈ x :: w, y.1 ≤ 1 := fun y hy => hk1 y (List.mem_append_right _ hy)
  refine ⟨?_, by omega, ?_⟩
  · unfold IsPieceW
    rw [if_neg (show ¬ (p.1 - linksT u - lk x, (0 : ℕ), (0 : ℕ)).1 = 0 from by
      show ¬ p.1 - linksT u - lk x = 0
      omega)]
    refine ⟨hsq, List.cons_ne_nil _ _, hk1', ?_⟩
    show linksT (x :: w) + 1 ≤ p.1 - linksT u - lk x
    omega
  · unfold IsPieceW
    rw [if_neg h0]
    exact ⟨hsq, List.cons_ne_nil _ _, hk1', by omega⟩

/-- Step 2: a proper prefix of a sequence piece has a smaller value. -/
theorem MinAt.rec_lt (M : MinAt k specs V W B spre Pre sp S spost Post) (h0 : sp.1 ≠ 0)
    {u : List TRow} {x : TRow} {w : List TRow} (hs : S = u ++ x :: w) (hu : u ≠ []) :
    valK k u < valK k S := by
  by_contra hcon
  have hw := M.hS.1
  rw [hs] at hw
  have h1 := piece_prefix hw h0 hu
  have h2 := M.rep u ⟨h1, fun h' => absurd h' h0⟩
    (by rw [hs, blocksR_append]; exact List.sublist_append_left _ _)
    (by rw [hs, wtK_append u x w hu]; omega) (not_lt.mp hcon)
  rw [hs, List.length_append, List.length_cons] at h2
  omega

/-- Step 3: the rest behind a cut of a sequence piece has a smaller value. -/
theorem MinAt.rest_lt (M : MinAt k specs V W B spre Pre sp S spost Post) (h0 : sp.1 ≠ 0)
    {u : List TRow} {x : TRow} {w : List TRow} (hs : S = u ++ x :: w) (hu : u ≠ []) :
    valK k (x :: w) < valK k S := by
  by_contra hcon
  have hw := M.hS.1
  rw [hs] at hw
  have h1 := (piece_suffix hw h0 hu).2.2
  have h2 := M.rep (x :: w) ⟨h1, fun h' => absurd h' h0⟩
    (by rw [hs, blocksR_append]; exact List.sublist_append_right _ _)
    (by rw [hs, wtK_append u x w hu]; omega) (not_lt.mp hcon)
  have hpos := List.length_pos_of_ne_nil hu
  rw [hs, List.length_append] at h2
  omega

end Min

/-! ### Rows of a sequence -/

/-- A row of a sequence is a row for the search, and its blocks are new. -/
theorem rowOk_of_split (hk : 3 ≤ k) {u : List TRow} {kdx : ℕ} {v : List ℕ} {R : List (List ℕ)}
    {w : List TRow} (hS : IsSeq k (u ++ (kdx, v :: R) :: w)) :
    RowOk k v R ∧ ∀ b' ∈ blocksR u, ∀ w' ∈ v :: R, ¬ b' ~r w' := by
  have hx : (kdx, v :: R) ∈ u ++ (kdx, v :: R) :: w := by simp
  have hcl : (blocksR (u ++ (kdx, v :: R) :: w)).Pairwise fun a b => ¬ a ~r b := hS.classes
  rw [blocksR_append, blocksR_cons] at hcl
  obtain ⟨_, h2, h3⟩ := List.pairwise_append.mp hcl
  have h4 := (List.pairwise_append.mp h2).1
  have hsz := hS.size_le _ hx
  have hwd := hS.words _ hx
  refine ⟨⟨?_, hwd, S.door_chain hk _ hwd (hS.doors _ hx) h4, h4⟩,
    fun b' hb w' hw => h3 b' hb w' (List.mem_append_left _ hw)⟩
  simp only [List.length_cons] at hsz
  omega

/-- The link before a row of a sequence. -/
theorem link_of_split {u : List TRow} {kdx : ℕ} {v : List ℕ} {R : List (List ℕ)}
    {w : List TRow} (hS : IsSeq k (u ++ (kdx, v :: R) :: w)) (hu : u ≠ []) :
    LinkK k kdx (lastB u) v := by
  have ha : (u.getLast hu).2 ≠ [] :=
    hS.pieces_ne _ (List.mem_append_left _ (List.getLast_mem hu))
  have h := (List.isChain_append.mp hS.links).2.2 (u.getLast hu)
    (by rw [List.getLast?_eq_some_getLast hu]; rfl) (kdx, v :: R) (by rfl) ha
    (List.cons_ne_nil v R)
  rw [lastB_eq hu ha]
  exact h

theorem closes_first_last {L : List TRow} (hL : IsSeq k L) (hne : L ≠ []) (hcl : Closes k L) :
    WLink k 3 (lastB L) (firstB L) := by
  have ha : (L.getLast hne).2 ≠ [] := hL.pieces_ne _ (List.getLast_mem hne)
  have e1 : L.getLast?.bind (fun x => x.2.getLast?) = some (lastB L) := by
    rw [lastB_eq hne ha, List.getLast?_eq_some_getLast hne]
    show (L.getLast hne).2.getLast? = _
    rw [List.getLast?_eq_some_getLast ha]
  obtain ⟨x0, L', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hb : x0.2 ≠ [] := hL.pieces_ne x0 List.mem_cons_self
  obtain ⟨v, R, hv⟩ := List.exists_cons_of_ne_nil hb
  have e2 : (x0 :: L').head?.bind (fun x => x.2.head?) = some (firstB (x0 :: L')) := by
    unfold firstB
    simp [hv]
  exact hcl _ (by rw [e1]; rfl) _ (by rw [e2]; rfl)

theorem valK_single_gt {kd : ℕ} {v : List ℕ} {R : List (List ℕ)} (hk : 2 ≤ k)
    (hR : R.length ≤ k - 2) : -((k - 1 : ℕ) : ℤ) < valK k [(kd, v :: R)] := by
  have e1 : holesT k [(kd, v :: R)] = k - 2 - R.length := by
    simp [holesT]
    omega
  have e2 : linksT [(kd, v :: R)] = 0 := rfl
  have hR' := hR
  unfold valK vOf
  rw [e1, e2]
  simp only [Nat.mul_zero, Nat.cast_zero, sub_zero, List.length_singleton]
  omega

/-! ### The rule along a counterexample with the fewest rows -/

section Along

variable {specs : List (ℕ × ℕ × ℕ)} {V : ℤ} {W B sm : ℕ} {P : ℕ → ℕ → ℕ} {PR : ℕ → ℕ}
  {enc : List ℕ → ℕ} {kd lo hi : ℕ → ℕ} {bestLe : ℕ → ℕ → ℤ → Bool}
  {gLe : ℕ → ℕ → ℕ → ℤ → Bool} {fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool} {gi gr : ℕ}

theorem finOk_piece {sp : ℕ × ℕ × ℕ} {S : List TRow} {i : ℕ} {m : ℤ} (hS : IsPieceC k sp S)
    (hkd : kd i = sp.1) (hlo : lo i = sp.2.1) (hhi : hi i = sp.2.2)
    (hm : sp.1 ≠ 0 → m < valK k S) :
    FinOk k kd lo hi i S.length (holesT k S) m (valK k S) (firstB S) (lastB S) := by
  unfold FinOk
  rw [hkd]
  by_cases h0 : sp.1 = 0
  · rw [if_pos h0]
    have hw := hS.1
    unfold IsPieceW at hw
    rw [if_pos h0] at hw
    obtain ⟨hL, _, h2, hcl, h3, h4⟩ := hw
    exact ⟨h2, by rw [hlo]; exact h3, by rw [hhi]; exact h4,
      closes_first_last hL hS.1.ne_nil hcl⟩
  · rw [if_neg h0]
    exact hm h0

/-- The rule holds along the rest of a piece of a counterexample with the fewest rows, if it
holds from the end of the piece on. -/
theorem inner_min (hk : 3 ≤ k) (hc : CapsOK k P PR W sm) (hsm : ∀ p ∈ specs, p.1 ≤ sm + 1)
    (hkd : ∀ i, i < specs.length →
      kd i = kdF specs i ∧ lo i = loF specs i ∧ hi i = hiF specs i)
    (hg : ∀ i u y x, i < specs.length → y ≤ W → u < kd i →
      x ≤ bestF P PR (k - 1) ((u + 1, 0, 0) :: specs.drop (i + 1)) y → gLe i u y x = true)
    (hf : ∀ i b r d x, i < specs.length → b ≤ W → kd i = 0 →
      x ≤ fF P PR (bestF P PR (k - 1) (specs.drop (i + 1))) (lo i) (hi i) b r d →
      fLe i b r d x = true)
    {spre : List (ℕ × ℕ × ℕ)} {Pre : List (List TRow)} {sp : ℕ × ℕ × ℕ} {S : List TRow}
    {spost : List (ℕ × ℕ × ℕ)} {Post : List (List TRow)}
    (M : MinAt k specs V W B spre Pre sp S spost Post)
    (hend : ∀ m : ℤ, (sp.1 ≠ 0 → m < valK k S) →
      JAlong k specs.length enc kd lo hi bestLe gLe fLe (Gate gi gr 1 0) (Early gi gr 1 0)
        spre.length (linksT S)
        S.length (holesT k S) (V - (Pre.map (valK k)).sum) (W - (Pre.map (wtK k)).sum) m
        (firstB S) (lastB S) (blocksR S) (flatJ Post)) :
    ∀ (rest u : List TRow) (m : ℤ), S = u ++ rest → u ≠ [] → (sp.1 ≠ 0 → m < valK k S) →
      JAlong k specs.length enc kd lo hi bestLe gLe fLe (Gate gi gr 1 0) (Early gi gr 1 0)
        spre.length (linksT u)
        u.length (holesT k u) (V - (Pre.map (valK k)).sum) (W - (Pre.map (wtK k)).sum) m
        (firstB S) (lastB u) (blocksR u) (rest ++ flatJ Post) := by
  have hi_lt : spre.length < specs.length := by
    rw [M.hspec]
    simp
  obtain ⟨hkdi, hloi, hhii⟩ := hkd _ hi_lt
  have hsp : specs.getD spre.length (0, 0, 0) = sp := by
    rw [M.hspec]
    exact getD_mid _ _ _ _
  have hkd' : kd spre.length = sp.1 := by
    rw [hkdi]
    unfold kdF
    rw [hsp]
  have hlo' : lo spre.length = sp.2.1 := by
    rw [hloi]
    unfold loF
    rw [hsp]
  have hhi' : hi spre.length = sp.2.2 := by
    rw [hhii]
    unfold hiF
    rw [hsp]
  have hdrop : specs.drop (spre.length + 1) = spost := by
    rw [M.hspec]
    exact drop_mid _ _ _
  have hseqS := M.hS.1.isSeq
  have hsW := M.sumW
  have hsV := M.sumV
  have hsmp : ∀ p ∈ spost, p.1 ≤ sm + 1 := fun p hp => hsm p (by rw [M.hspec]; simp [hp])
  have hsmsp : sp.1 ≤ sm + 1 := hsm sp (by rw [M.hspec]; simp)
  have hpostW : List.Forall₂ (IsPieceW k) spost Post := M.hPost.imp fun _ _ h => h.1
  intro rest
  induction rest with
  | nil =>
    intro u m hs hu hm
    rw [List.append_nil] at hs
    subst hs
    rw [List.nil_append]
    exact hend m hm
  | cons x w ih =>
    intro u m hs hu hm
    obtain ⟨kdx, Q⟩ := x
    have hSs : IsSeq k (u ++ (kdx, Q) :: w) := hs ▸ hseqS
    have hQ : Q ≠ [] := hSs.pieces_ne (kdx, Q) (by simp)
    obtain ⟨v, R, rfl⟩ := List.exists_cons_of_ne_nil hQ
    obtain ⟨hrow, hnew⟩ := rowOk_of_split hk hSs
    have hlink := link_of_split hSs hu
    -- the prefix with the row added
    have e1 : (u ++ [(kdx, v :: R)]).length = u.length + 1 := by simp
    have hh1 : holesT k [(kdx, v :: R)] = k - 2 - R.length := by
      simp [holesT]
      omega
    have e2 : holesT k (u ++ [(kdx, v :: R)]) = holesT k u + (k - 2 - R.length) := by
      rw [PS.holesT_append, hh1]
    have e3 : blocksR (u ++ [(kdx, v :: R)]) = blocksR u ++ v :: R := by
      rw [blocksR_append]
      simp [blocksR]
    have e4 := lastB_snoc u kdx v R
    have e5 : linksT (u ++ [(kdx, v :: R)]) = linksT u + lk (kdx, v :: R) := by
      have h := PS.linksT_append u (kdx, v :: R) [] hu
      have h0 : linksT [(kdx, v :: R)] = 0 := rfl
      rw [h, h0]
      rfl
    have hs' : S = (u ++ [(kdx, v :: R)]) ++ w := by
      rw [hs]
      simp
    have hIH := ih (u ++ [(kdx, v :: R)]) (max m (valK k u)) hs' (by simp)
      (fun h0 => max_lt (hm h0) (M.rec_lt h0 hs hu))
    rw [e1, e2, e3, e4, e5] at hIH
    -- the cut
    have hlenS : S.length = u.length + (w.length + 1) := by
      rw [hs]
      simp
    have hholx : holesT k ((kdx, v :: R) :: w) = (k - 2 - R.length) + holesT k w := by
      have h := PS.holesT_append (k := k) [(kdx, v :: R)] w
      rw [hh1] at h
      exact h
    have hholS : holesT k S = holesT k u + holesT k ((kdx, v :: R) :: w) := by
      rw [hs, PS.holesT_append]
    have hwtS := wtK_append (k := k) u (kdx, v :: R) w hu
    rw [← hs] at hwtS
    have hvalS := valK_append (k := k) u (kdx, v :: R) w hu
    rw [← hs] at hvalS
    have hwx : k - 2 - R.length ≤ wtK k ((kdx, v :: R) :: w) := by
      unfold wtK
      omega
    have hgate : Gate gi gr 1 0 spre.length u.length (enc (lastB u) + 8192 * holesT k u) :=
      Or.inr (Or.inr (Nat.mod_one _))
    rw [List.cons_append]
    by_cases h0 : sp.1 = 0
    · -- a ring
      have hc0 : (sp.1 == 0) = true := by simp [h0]
      have hw' := M.hS.1
      unfold IsPieceW at hw'
      rw [if_pos h0] at hw'
      obtain ⟨_, hk0, h2len, hcl, hlo, hhi⟩ := hw'
      have hcyc := M.hS.2 h0 u ((kdx, v :: R) :: w) hs
      have hkx : kdx = 0 := hk0 (kdx, v :: R) (by rw [hs]; simp)
      subst hkx
      have hlu : linksT u = 0 :=
        PS.linksT_zero fun y hy => hk0 y (by rw [hs]; exact List.mem_append_left _ hy)
      have hlS : linksT S = 0 := PS.linksT_zero hk0
      have hk0w : ∀ y ∈ ((0 : ℕ), v :: R) :: w, y.1 = 0 :=
        fun y hy => hk0 y (by rw [hs]; exact List.mem_append_right _ hy)
      have hwtSe : wtK k S = holesT k S := by
        unfold wtK
        rw [hlS]
        simp
      have hvS : valK k S = (S.length : ℤ) - (holesT k S : ℤ) := by
        unfold valK vOf
        rw [hlS]
        simp
      have hH : holesT k S ≤ W - (Pre.map (wtK k)).sum := by omega
      have hT1 : S.length ≤ PR (holesT k S) := hc.ring S hseqS hk0 h2len hcl (by omega)
      have hrestseq : IsSeq k (((0 : ℕ), v :: R) :: w) :=
        hSs.infix (List.suffix_append u _).isInfix
      have hT2 : w.length + 1 ≤ P 0 (holesT k (((0 : ℕ), v :: R) :: w)) := by
        have h := hc.seq 0 (Nat.zero_le _) (((0 : ℕ), v :: R) :: w) hrestseq
          (fun y hy => by rw [hk0w y hy]; omega) (PS.linksT_zero hk0w)
          (by rw [Nat.mul_zero, Nat.sub_zero]; omega)
        simpa using h
      have hT : S.length ≤ tmax P PR u.length (holesT k u) (holesT k S) := by
        have hd : holesT k S - holesT k u = holesT k (((0 : ℕ), v :: R) :: w) := by omega
        unfold tmax
        rw [hd]
        by_cases hd0 : holesT k u = 0
        · rw [if_pos hd0]
          exact le_min hT1 (by omega)
        · rw [if_neg hd0]
          refine le_min (le_min hT1 (by omega)) ?_
          rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
          exact hcyc
      have hp := best_bound hc spost Post hpostW hsmp
        (W - (Pre.map (wtK k)).sum - holesT k S) (by omega) (by omega)
      have hT' : (S.length : ℤ) ≤ ((tmax P PR u.length (holesT k u) (holesT k S) : ℕ) : ℤ) := by
        exact_mod_cast hT
      have hfle : fLe spre.length (W - (Pre.map (wtK k)).sum) u.length (holesT k u)
          (V - (Pre.map (valK k)).sum) = true := by
        apply hf _ _ _ _ _ hi_lt (Nat.sub_le _ _) (by rw [hkd']; exact h0)
        rw [hdrop, hlo', hhi']
        unfold fF
        refine le_trans ?_ (le_maxLe _ _ (holesT k S) hH)
        show _ ≤ if sp.2.1 ≤ holesT k S ∧ holesT k S ≤ sp.2.2 ∧ holesT k u ≤ holesT k S ∧
            u.length + 1 ≤ tmax P PR u.length (holesT k u) (holesT k S) then
          ((tmax P PR u.length (holesT k u) (holesT k S) : ℕ) : ℤ) - (holesT k S : ℤ) +
            bestF P PR (k - 1) spost (W - (Pre.map (wtK k)).sum - holesT k S)
          else negInf
        rw [if_pos ⟨hlo, hhi, by omega, by omega⟩]
        linarith
      rw [JAlong]
      refine ⟨hgate, hrow, ?_, hlink.1 rfl, hnew, ?_, ?_⟩
      · unfold k3Ok
        rw [hkd', if_pos hc0]
        exact hfle
      · rw [hlu]
        omega
      · have e6 : lk ((0 : ℕ), v :: R) = 0 := rfl
        rw [e6, Nat.add_zero] at hIH
        exact hIH
    · -- a sequence
      have hc0 : ¬ (sp.1 == 0) = true := by simp [h0]
      have hw' : IsPieceW k sp (u ++ (kdx, v :: R) :: w) := hs ▸ M.hS.1
      have hk1 := hw'.le_one (kdx, v :: R) (by simp)
      obtain ⟨hsuf, hlkS, _⟩ := piece_suffix hw' h0 hu
      have hrest := M.rest_lt h0 hs hu
      have hb := best_bound hc ((sp.1 - linksT u - lk (kdx, v :: R), 0, 0) :: spost)
        (((kdx, v :: R) :: w) :: Post) (List.Forall₂.cons hsuf hpostW)
        (by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · show sp.1 - linksT u - lk (kdx, v :: R) ≤ sm + 1
            omega
          · exact hsmp p hp')
        (W - (Pre.map (wtK k)).sum - wtK k u - (k - 1) * lk (kdx, v :: R))
        (by simp only [List.map_cons, List.sum_cons]; omega) (by omega)
      simp only [List.map_cons, List.sum_cons] at hb
      rcases (show kdx = 0 ∨ kdx = 1 by omega) with rfl | rfl
      · -- a link of weight 3
        have e6 : lk ((0 : ℕ), v :: R) = 0 := rfl
        rw [e6] at hb hwtS hvalS hlkS hIH
        simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.cast_zero, sub_zero] at hb hwtS hvalS hlkS hIH
        have hv1 : 1 ≤ valK k u := by linarith
        rw [JAlong]
        refine ⟨hgate, hrow, ?_, hlink.1 rfl, hnew, ?_, hIH⟩
        · unfold k3Ok
          rw [hkd', if_neg hc0, Bool.and_eq_true]
          refine ⟨decide_eq_true hv1, ?_⟩
          apply hg _ _ _ _ hi_lt (Nat.sub_le_of_le_add (by omega)) (by rw [hkd']; omega)
          rw [hdrop]
          have e7 : sp.1 - 1 - linksT u + 1 = sp.1 - linksT u := by omega
          rw [e7]
          show V - (Pre.map (valK k)).sum - valK k u ≤ bestF P PR (k - 1)
            ((sp.1 - linksT u, 0, 0) :: spost) (W - (Pre.map (wtK k)).sum - wtK k u)
          linarith
        · show wtK k u + (k - 2 - R.length) ≤ W - (Pre.map (wtK k)).sum
          omega
      · -- a link of weight 4
        have e6 : lk ((1 : ℕ), v :: R) = 1 := rfl
        rw [e6] at hb hwtS hvalS hlkS hIH
        simp only [Nat.mul_one] at hb hwtS hvalS
        have e8 : ((k - 1 - 1 : ℕ) : ℤ) + 1 = ((k - 1 : ℕ) : ℤ) := by
          have : k - 1 - 1 + 1 = k - 1 := by omega
          exact_mod_cast this
        rw [JAlong]
        refine ⟨hgate, hrow, ?_, hlink.2 rfl, hnew, ?_, hIH⟩
        · unfold k4Ok
          rw [hkd']
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨⟨by omega, ?_⟩, ?_⟩, ?_⟩
          · show ((k - 1 : ℕ) : ℤ) ≤ valK k u
            linarith
          · show k - 1 ≤ W - (Pre.map (wtK k)).sum - wtK k u
            omega
          · apply hg _ _ _ _ hi_lt
              (Nat.sub_le_of_le_add (Nat.sub_le_of_le_add (by omega))) (by rw [hkd']; omega)
            rw [hdrop]
            have e7 : sp.1 - 2 - linksT u + 1 = sp.1 - linksT u - 1 := by omega
            rw [e7]
            show V - (Pre.map (valK k)).sum - valK k u + ((k - 1 - 1 : ℕ) : ℤ) ≤
              bestF P PR (k - 1) ((sp.1 - linksT u - 1, 0, 0) :: spost)
                (W - (Pre.map (wtK k)).sum - wtK k u - (k - 1))
            linarith
        · show wtK k u + (k - 1) + (k - 2 - R.length) ≤ W - (Pre.map (wtK k)).sum
          omega

/-- The rule holds from the end of a piece of a counterexample with the fewest rows on. -/
theorem along_min (hk : 3 ≤ k) (hc : CapsOK k P PR W sm) (hsm : ∀ p ∈ specs, p.1 ≤ sm + 1)
    (hkd : ∀ i, i < specs.length →
      kd i = kdF specs i ∧ lo i = loF specs i ∧ hi i = hiF specs i)
    (hbest : ∀ i y x, i < specs.length → y ≤ W →
      x ≤ bestF P PR (k - 1) (specs.drop (i + 1)) y → bestLe i y x = true)
    (hg : ∀ i u y x, i < specs.length → y ≤ W → u < kd i →
      x ≤ bestF P PR (k - 1) ((u + 1, 0, 0) :: specs.drop (i + 1)) y → gLe i u y x = true)
    (hf : ∀ i b r d x, i < specs.length → b ≤ W → kd i = 0 →
      x ≤ fF P PR (bestF P PR (k - 1) (specs.drop (i + 1))) (lo i) (hi i) b r d →
      fLe i b r d x = true) :
    ∀ (Post : List (List TRow)) (spost spre : List (ℕ × ℕ × ℕ)) (Pre : List (List TRow))
      (sp : ℕ × ℕ × ℕ) (S : List TRow), MinAt k specs V W B spre Pre sp S spost Post →
      ∀ m : ℤ, (sp.1 ≠ 0 → m < valK k S) →
      JAlong k specs.length enc kd lo hi bestLe gLe fLe (Gate gi gr 1 0) (Early gi gr 1 0)
        spre.length (linksT S)
        S.length (holesT k S) (V - (Pre.map (valK k)).sum) (W - (Pre.map (wtK k)).sum) m
        (firstB S) (lastB S) (blocksR S) (flatJ Post) := by
  intro Post
  induction Post with
  | nil =>
    intro spost spre Pre sp S M m hm
    have hsp0 : spost = [] := by
      have := M.hPost
      cases this
      rfl
    subst hsp0
    have hi_lt : spre.length < specs.length := by
      rw [M.hspec]
      simp
    obtain ⟨hkdi, hloi, hhii⟩ := hkd _ hi_lt
    have hsp : specs.getD spre.length (0, 0, 0) = sp := by
      rw [M.hspec]
      exact getD_mid _ _ _ _
    have hsV := M.sumV
    simp only [List.map_nil, List.sum_nil, add_zero] at hsV
    show JAlong k specs.length enc kd lo hi bestLe gLe fLe (Gate gi gr 1 0) (Early gi gr 1 0)
        spre.length (linksT S)
        S.length (holesT k S) (V - (Pre.map (valK k)).sum) (W - (Pre.map (wtK k)).sum) m
        (firstB S) (lastB S) (blocksR S) []
    rw [JAlong]
    refine ⟨Or.inr (Or.inr (Nat.mod_one _)),
      finOk_piece M.hS (by rw [hkdi]; unfold kdF; rw [hsp]) (by rw [hloi]; unfold loF; rw [hsp])
        (by rw [hhii]; unfold hiF; rw [hsp]) hm, ?_, ?_⟩
    · rw [M.hspec]
      simp
    · show V - (Pre.map (valK k)).sum ≤ valK k S
      linarith
  | cons S' Post' ih =>
    intro spost spre Pre sp S M m hm
    obtain ⟨sp', spost', rfl⟩ : ∃ sp' spost', spost = sp' :: spost' := by
      have := M.hPost
      cases this
      exact ⟨_, _, rfl⟩
    have hi_lt : spre.length < specs.length := by
      rw [M.hspec]
      simp
    obtain ⟨hkdi, hloi, hhii⟩ := hkd _ hi_lt
    have hsp : specs.getD spre.length (0, 0, 0) = sp := by
      rw [M.hspec]
      exact getD_mid _ _ _ _
    have hdrop : specs.drop (spre.length + 1) = sp' :: spost' := by
      rw [M.hspec]
      exact drop_mid _ _ _
    have hsW := M.sumW
    have hsV := M.sumV
    have M' := M.next
    have hS' := M'.hS
    obtain ⟨x0, S'', rfl⟩ := List.exists_cons_of_ne_nil hS'.1.ne_nil
    obtain ⟨kd0, Q0⟩ := x0
    have hseq' := hS'.1.isSeq
    have hQ0 : Q0 ≠ [] := hseq'.pieces_ne (kd0, Q0) List.mem_cons_self
    obtain ⟨v, R, rfl⟩ := List.exists_cons_of_ne_nil hQ0
    obtain ⟨hrow, _⟩ := rowOk_of_split hk (u := []) hseq'
    have hend' := ih spost' (spre ++ [sp]) (Pre ++ [S]) sp' ((kd0, v :: R) :: S'') M'
    have hm0 : sp'.1 ≠ 0 → -((k - 1 : ℕ) : ℤ) < valK k ((kd0, v :: R) :: S'') := by
      intro h0
      have h1 := valK_single_gt (kd := kd0) (v := v) (by omega) hrow.1
      cases S'' with
      | nil => exact h1
      | cons y w'' =>
        have h2 := M'.rec_lt h0 (u := [(kd0, v :: R)]) (x := y) (w := w'') rfl (by simp)
        linarith
    have hinner := inner_min hk hc hsm hkd hg hf M' hend' S'' [(kd0, v :: R)]
      (-((k - 1 : ℕ) : ℤ)) rfl (by simp) hm0
    have f1 : (spre ++ [sp]).length = spre.length + 1 := by simp
    have f2 : linksT [(kd0, v :: R)] = 0 := rfl
    have f3 : [(kd0, v :: R)].length = 1 := rfl
    have f4 : holesT k [(kd0, v :: R)] = k - 2 - R.length := by
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
    have f7 : firstB ((kd0, v :: R) :: S'') = v := rfl
    have f8 := lastB_snoc [] kd0 v R
    have f9 : blocksR [(kd0, v :: R)] = v :: R := by simp [blocksR]
    rw [List.nil_append] at f8
    rw [f1, f2, f3, f4, f5, f6, f7, f8, f9] at hinner
    have hholx : holesT k ((kd0, v :: R) :: S'') = (k - 2 - R.length) + holesT k S'' := by
      have h := PS.holesT_append (k := k) [(kd0, v :: R)] S''
      rw [f4] at h
      exact h
    simp only [List.map_cons, List.sum_cons] at hsW hsV
    have hp := best_bound hc (sp' :: spost') (((kd0, v :: R) :: S'') :: Post')
      (M.hPost.imp fun _ _ h => h.1) (fun p hp => hsm p (by rw [M.hspec]; simp [hp]))
      (W - (Pre.map (wtK k)).sum - wtK k S)
      (by simp only [List.map_cons, List.sum_cons]; omega) (by omega)
    simp only [List.map_cons, List.sum_cons] at hp
    show JAlong k specs.length enc kd lo hi bestLe gLe fLe (Gate gi gr 1 0) (Early gi gr 1 0)
        spre.length (linksT S)
        S.length (holesT k S) (V - (Pre.map (valK k)).sum) (W - (Pre.map (wtK k)).sum) m
        (firstB S) (lastB S) (blocksR S) ((2, v :: R) :: (S'' ++ flatJ Post'))
    rw [JAlong]
    refine ⟨Or.inr (Or.inr (Nat.mod_one _)), hrow,
      finOk_piece M.hS (by rw [hkdi]; unfold kdF; rw [hsp]) (by rw [hloi]; unfold loF; rw [hsp])
        (by rw [hhii]; unfold hiF; rw [hsp]) hm, ?_, ?_, Or.inr (Or.inr (Nat.mod_one _)), ?_, hinner⟩
    · rw [M.hspec]
      simp only [List.length_append, List.length_cons]
      omega
    · apply hbest _ _ _ hi_lt (Nat.sub_le_of_le_add (by omega))
      rw [hdrop]
      show V - (Pre.map (valK k)).sum - valK k S ≤ bestF P PR (k - 1) (sp' :: spost')
        (W - (Pre.map (wtK k)).sum - wtK k S)
      linarith
    · show k - 2 - R.length ≤ W - (Pre.map (wtK k)).sum - wtK k S
      have : k - 2 - R.length ≤ wtK k ((kd0, v :: R) :: S'') := by
        unfold wtK
        omega
      omega

/-- **A search that finds nothing proves the statement.** -/
theorem jw_of_parts {ci nxt : ℕ → ℕ} {s3 s4 : ℕ → List ℕ} {jl : List ℕ} {st sz fuel : ℕ} {gs : List (ℕ × ℕ × ℕ)}
    (E : PS.Enc k enc ci nxt s3 s4 jl st) (hk : 3 ≤ k) (hne : specs ≠ [])
    (hnp : specs.length ≤ 255) (hgs : ∀ g ∈ gs, 0 < g.2.2) (hc : CapsOK k P PR W sm)
    (hsm : ∀ p ∈ specs, p.1 ≤ sm + 1)
    (hkd : ∀ i, i < specs.length →
      kd i = kdF specs i ∧ lo i = loF specs i ∧ hi i = hiF specs i)
    (hbest : ∀ i y x, i < specs.length → y ≤ W →
      x ≤ bestF P PR (k - 1) (specs.drop (i + 1)) y → bestLe i y x = true)
    (hg : ∀ i u y x, i < specs.length → y ≤ W → u < kd i →
      x ≤ bestF P PR (k - 1) ((u + 1, 0, 0) :: specs.drop (i + 1)) y → gLe i u y x = true)
    (hf : ∀ i b r d x, i < specs.length → b ≤ W → kd i = 0 →
      x ≤ fF P PR (bestF P PR (k - 1) (specs.drop (i + 1))) (lo i) (hi i) b r d →
      fLe i b r d x = true)
    (hs : ∀ tp, tp < gprod gs →
      searchPart ci nxt s3 s4 jl st (k - 1) specs.length B kd lo hi bestLe gLe fLe V W sz fuel
        (gateD (digs gs tp)) (earlyD (digs gs tp)) = false) :
    JW k specs V W B := by
  intro Ls hLs hSh hW
  by_contra hcon
  have hV : V ≤ (Ls.map (valK k)).sum := not_lt.mp hcon
  obtain ⟨Ls1, g1, g2, g3, g4⟩ := norm specs Ls hLs
  have hce1 : CE k specs V W B Ls1 := by
    refine ⟨g1, ?_, by rw [g3]; exact hW, by rw [g4]; exact hV⟩
    unfold Sh at hSh ⊢
    rw [g2.length_eq, clsCount_perm g2]
    exact hSh
  obtain ⟨Ls2, hce2, hmin2⟩ := exists_min ⟨Ls1, hce1⟩
  obtain ⟨sp0, spost, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨S0, Post, rfl⟩ : ∃ S0 Post, Ls2 = S0 :: Post := by
    have := hce2.1
    cases this
    exact ⟨_, _, rfl⟩
  have hS0 := (List.forall₂_cons.mp hce2.1).1
  obtain ⟨x0, S0', rfl⟩ := List.exists_cons_of_ne_nil hS0.1.ne_nil
  obtain ⟨kd0, Q0⟩ := x0
  have hQ0 := hS0.1.isSeq.pieces_ne (kd0, Q0) List.mem_cons_self
  obtain ⟨v0, R0, rfl⟩ := List.exists_cons_of_ne_nil hQ0
  have hv0 : PermW k v0 := hS0.1.isSeq.words _ List.mem_cons_self v0 List.mem_cons_self
  obtain ⟨hce3, hrows3⟩ := hce2.relabel hv0
  have hshape : (((kd0, v0 :: R0) :: S0') :: Post).map (relabSeq v0) =
      ((kd0, List.range' 1 k :: R0.map (List.map (S.relab v0))) :: relabSeq v0 S0') ::
        Post.map (relabSeq v0) := by
    simp [relabSeq, S.map_relab_self hv0.1, hv0.2.1]
  rw [hshape] at hce3 hrows3
  generalize R0.map (List.map (S.relab v0)) = R1 at hce3 hrows3
  generalize relabSeq v0 S0' = S1 at hce3 hrows3
  generalize Post.map (relabSeq v0) = Post1 at hce3 hrows3
  have hfa := List.forall₂_cons.mp hce3.1
  have M : MinAt k (sp0 :: spost) V W B [] [] sp0 ((kd0, List.range' 1 k :: R1) :: S1) spost
      Post1 :=
    ⟨rfl, List.Forall₂.nil, hfa.1, hfa.2, hce3.2.1, hce3.2.2.1, hce3.2.2.2,
      fun Ls' h' => by
        show (((kd0, List.range' 1 k :: R1) :: S1) :: Post1).flatten.length ≤ _
        rw [hrows3]
        exact hmin2 Ls' h'⟩
  have hseq := M.hS.1.isSeq
  obtain ⟨⟨hR1, hperm, hdoor, hpw⟩, _⟩ := rowOk_of_split hk (u := []) hseq
  have hend := along_min (enc := enc) (gi := 0) (gr := 0) hk hc hsm hkd hbest hg hf Post1 spost
    [] [] sp0 _ M
  have hm0 : sp0.1 ≠ 0 →
      -((k - 1 : ℕ) : ℤ) < valK k ((kd0, List.range' 1 k :: R1) :: S1) := by
    intro h0
    have h1 := valK_single_gt (kd := kd0) (v := List.range' 1 k) (by omega) hR1
    cases S1 with
    | nil => exact h1
    | cons y w'' =>
      have h2 := M.rec_lt h0 (u := [(kd0, List.range' 1 k :: R1)]) (x := y) (w := w'') rfl
        (by simp)
      linarith
  have hinner := inner_min hk hc hsm hkd hg hf M hend S1 [(kd0, List.range' 1 k :: R1)]
    (-((k - 1 : ℕ) : ℤ)) rfl (by simp) hm0
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
  refine not_along_of_parts (gi := 0) (gr := 0) E (by omega) hnp (PS.permW_range' k) hgs hs R1 (S1 ++ flatJ Post1)
    hR1 hperm hdoor hpw ?_ ?_ hinner
  · have : k - 2 - R1.length ≤ wtK k ((kd0, List.range' 1 k :: R1) :: S1) := by
      unfold wtK
      omega
    omega
  · have e : (List.range' 1 k :: R1) ++ blocksR (S1 ++ flatJ Post1)
        = blocksR ((((kd0, List.range' 1 k :: R1) :: S1) :: Post1).flatten) := by
      rw [blocksR_append, blocksR_flatJ]
      show _ = blocksR (((kd0, List.range' 1 k :: R1) :: S1) ++ Post1.flatten)
      rw [blocksR_append, blocksR_cons, List.append_assoc]
    have c0 : clsCount [] = 0 := by simp [clsCount]
    have hsh := hce3.2.1
    unfold Sh at hsh
    unfold Bud
    rw [e, c0, List.nil_append]
    omega

end Along

end J15
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.J15.jw_of_parts
