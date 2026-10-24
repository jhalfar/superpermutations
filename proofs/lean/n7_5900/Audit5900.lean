import LowerBounds.F5900Joint

/-!
# Audit of level 1 for 5,900: the theorem from the finite statements (no `native_decide`)

What is proved in the files `LowerBounds/A15*.lean` and `LowerBounds/F5900Joint.lean`, with the
statement about words written out and the hypotheses unfolded to the objects they speak about.

The hypotheses are finite statements of two kinds.  The statements of the proof of 5,899 (F0 to
F5, FR, FF) speak about chains of vertices and are unfolded in `Audit5899.lean`.  The statements
of the proof of 5,900 speak about rows on words and are unfolded here: table T' (`KS.TableT`),
Theorem K (`KS.TheoremK`) and the joint statements S1 .. S5 (`KS.Joint`).

`Audit5900Search.lean` replaces the finite statements by search equations and
`Audit5900Native.lean` is the statement with the equations evaluated.
-/

open SuperpermLowerBounds

section

/-! ### Rows on words -/

/-- A word: a list of the symbols `1 .. k` without repetition. -/
example (k : ℕ) (w : List ℕ) :
    S.PermW k w ↔ w.Nodup ∧ w.length = k ∧ ∀ a, a ∈ w ↔ 1 ≤ a ∧ a ≤ k :=
  Iff.rfl

/-- The link of weight `d` from the block entered at `u` to the block entered at `v`: the exit of
the first block (its entry rotated by `k - 1`) without its first `d` symbols is the beginning of
`v`. -/
example (k d : ℕ) (u v : List ℕ) :
    S.WLink k d u v ↔ (u.rotate (k - 1)).drop d = v.take (k - d) :=
  Iff.rfl

/-- A row with its kind: the kind of the link that enters it (0: weight 3, 1: weight 4) and the
entries of its blocks. -/
example : PS.TRow = (ℕ × List (List ℕ)) := rfl

/-- The link of a kind. -/
example (k kd : ℕ) (u v : List ℕ) :
    PS.LinkK k kd u v ↔ (kd = 0 → S.WLink k 3 u v) ∧ (kd = 1 → S.WLink k 4 u v) :=
  Iff.rfl

/-- A sequence of rows: every row has between 1 and `k - 1` blocks, entered at words and joined
by links of weight 2; consecutive rows are joined by the link of the kind of the second row; all
blocks lie in pairwise different rotation classes. -/
example (k : ℕ) (L : List PS.TRow) :
    PS.IsSeq k L ↔
      (∀ x ∈ L, ∀ w ∈ x.2, S.PermW k w) ∧ (∀ x ∈ L, x.2 ≠ []) ∧ (∀ x ∈ L, x.2.length ≤ k - 1) ∧
        (∀ x ∈ L, List.IsChain (S.WLink k 2) x.2) ∧
        List.IsChain (fun x y : PS.TRow => ∀ (hx : x.2 ≠ []) (hy : y.2 ≠ []),
          PS.LinkK k y.1 (x.2.getLast hx) (y.2.head hy)) L ∧
        List.Pairwise (fun u v : List ℕ => ¬ u ~r v) (L.map Prod.snd).flatten :=
  ⟨fun h => ⟨h.words, h.pieces_ne, h.size_le, h.doors, h.links, h.classes⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩⟩

/-- Holes: `k - 1` minus the number of blocks, summed over the rows. -/
example (k : ℕ) (L : List PS.TRow) : PS.holesT k L = (L.map fun x => k - 1 - x.2.length).sum := rfl

/-- Links: the rows after the first one that are entered by a link of weight 4. -/
example (L : List PS.TRow) : PS.linksT L = L.tail.countP fun x => x.1 != 0 := rfl

/-- A sequence closes: the link from its last block to its first block has weight 3. -/
example (k : ℕ) (L : List PS.TRow) :
    PS.Closes k L ↔
      ∀ u ∈ L.getLast?.bind (fun x => x.2.getLast?), ∀ v ∈ L.head?.bind (fun x => x.2.head?),
        S.WLink k 3 u v :=
  Iff.rfl

/-! ### The finite statements of 5,900 -/

/-- A sequence with exactly `s` links and fewer than `b` holes has at most `P holes` rows. -/
example (k s : ℕ) (P : ℕ → ℕ) (b : ℕ) :
    PS.SeqCapLt k s P b ↔
      ∀ L : List PS.TRow, PS.IsSeq k L → (∀ x ∈ L, x.1 ≤ 1) → PS.linksT L = s →
        PS.holesT k L < b → L.length ≤ P (PS.holesT k L) :=
  Iff.rfl

/-- A ring (a sequence of at least two rows without links of weight 4 that closes) with at most
`G` holes has at most `PR holes` rows. -/
example (k : ℕ) (PR : ℕ → ℕ) (G : ℕ) :
    PS.RingCapT k PR G ↔
      ∀ L : List PS.TRow, PS.IsSeq k L → (∀ x ∈ L, x.1 = 0) → 2 ≤ L.length → PS.Closes k L →
        PS.holesT k L ≤ G → L.length ≤ PR (PS.holesT k L) :=
  Iff.rfl

/-- The entries of a table. -/
example (caps : List (List ℕ)) (j x : ℕ) : PS.capF caps j x = (caps.getD j []).getD x 0 := rfl

/-- Table T' is valid: its rows for sequences with 0 to 8 links and its ring row to 84 holes. -/
example :
    KS.TableT ↔
      (∀ s, s ≤ 8 → PS.SeqCapLt 7 s (PS.capF T5900.Ttab s) ([85, 79, 73, 67, 61, 61, 55, 49, 43].getD s 0)) ∧
        PS.RingCapT 7 (fun x => T5900.TRtab.getD x 0) 84 :=
  Iff.rfl

/-- Theorem K: table D is valid for sequences with `s ≤ 8` links and `x ≤ 90 - 6 s` holes. -/
example : KS.TheoremK ↔ ∀ s, s ≤ 8 → PS.SeqCapLt 7 s (PS.capF T5900.Dtab s) (91 - 6 * s) := Iff.rfl

/-- A piece: a sequence with at most `s` links, or a ring. -/
example (s : ℕ) (L : List PS.TRow) :
    KS.IsPiece (.seq s) L ↔ PS.IsSeq 7 L ∧ L ≠ [] ∧ (∀ x ∈ L, x.1 ≤ 1) ∧ PS.linksT L ≤ s :=
  Iff.rfl

example (L : List PS.TRow) :
    KS.IsPiece .ring L ↔ PS.IsSeq 7 L ∧ (∀ x ∈ L, x.1 = 0) ∧ 2 ≤ L.length ∧ PS.Closes 7 L :=
  Iff.rfl

/-- Value and weight of a piece. -/
example (L : List PS.TRow) :
    KS.valT L = (L.length : ℤ) - PS.holesT 7 L - 5 * PS.linksT L := rfl

example (L : List PS.TRow) : KS.wtT L = PS.holesT 7 L + 6 * PS.linksT L := rfl

/-- At most `B` shared classes: after removing at most `B` blocks, the blocks of all pieces lie
in pairwise different rotation classes. -/
example (Ls : List (List PS.TRow)) (B : ℕ) :
    KS.SharedLe Ls B ↔
      ∃ keep rem : List (List ℕ),
        (Ls.flatMap fun L => (L.map Prod.snd).flatten).Perm (keep ++ rem) ∧ rem.length ≤ B ∧
          keep.Pairwise (fun u v => ¬ u ~r v) :=
  Iff.rfl

/-- The joint statement J(kinds; V, W; B). -/
example (kinds : List KS.Kind) (V : ℤ) (W B : ℕ) :
    KS.J kinds V W B ↔
      ∀ Ls : List (List PS.TRow), List.Forall₂ KS.IsPiece kinds Ls → KS.SharedLe Ls B →
        (Ls.map KS.wtT).sum ≤ W → (Ls.map KS.valT).sum < V :=
  Iff.rfl

/-- S1 .. S5. -/
example :
    KS.Joint ↔
      KS.J [.seq 4, .seq 4] 55 78 1 ∧ KS.J [.seq 5, .ring] 51 83 1 ∧
        KS.J [.seq 2, .ring, .ring] 57 76 2 ∧ KS.J [.seq 1, .seq 1, .ring] 61 71 1 ∧
        KS.J [.seq 0, .seq 0, .ring] 62 70 2 :=
  Iff.rfl

/-! ### Level 1: the theorem from the finite statements -/

/-- **Level 1.**  If the finite statements of the proof of 5,899 hold (the chain caps F0, the caps
F1 to F5 for sequences with 1 to 5 links of weight 4, the ring caps FR, the five profile
statements FF), table T' is valid, Theorem K holds and the joint statements S1 .. S5 hold, then
every word over 7 symbols that contains every permutation of the 7 symbols as a factor has at
least 5,900 letters. -/
example
    (hF0 : ChainCap T5899.Mf 84)
    (hF1 : PathCap 1 (T5899.Pf 1) 78) (hF2 : PathCap 2 (T5899.Pf 2) 72)
    (hF3 : PathCap 3 (T5899.Pf 3) 66) (hF4 : PathCap 4 (T5899.Pf 4) 60)
    (hF5 : PathCap 5 (T5899.Pf 5) 54)
    (hFR : RingCap T5899.PRf 77)
    (hP1 : NoProfile [(66, 36), (66, 36)]) (hP2 : NoProfile [(50, 26), (50, 26)])
    (hP3 : NoProfile [(63, 34), (34, 16)]) (hP4 : NoProfile [(66, 36), (31, 14)])
    (hP5 : NoProfile [(31, 14), (31, 14), (34, 16), (34, 16)])
    (hT : ∀ s, s ≤ 8 →
      PS.SeqCapLt 7 s (PS.capF T5900.Ttab s) ([85, 79, 73, 67, 61, 61, 55, 49, 43].getD s 0))
    (hTR : PS.RingCapT 7 (fun x => T5900.TRtab.getD x 0) 84)
    (hK : ∀ s, s ≤ 8 → PS.SeqCapLt 7 s (PS.capF T5900.Dtab s) (91 - 6 * s))
    (hS1 : KS.J [.seq 4, .seq 4] 55 78 1) (hS2 : KS.J [.seq 5, .ring] 51 83 1)
    (hS3 : KS.J [.seq 2, .ring, .ring] 57 76 2) (hS4 : KS.J [.seq 1, .seq 1, .ring] 61 71 1)
    (hS5 : KS.J [.seq 0, .seq 0, .ring] 62 70 2) :
    ∀ w : List (Fin 7),
      (∀ p : List (Fin 7), p.length = 7 → p.Nodup → ∃ u v : List (Fin 7), w = u ++ p ++ v) →
      5900 ≤ w.length := by
  refine covers_5900_of_caps ⟨hF0, ?_, hFR⟩ ⟨hP1, hP2, hP3, hP4, hP5⟩ ⟨hT, hTR⟩ hK
    ⟨hS1, hS2, hS3, hS4, hS5⟩
  intro s h1 h5
  have hs : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact hF1
  · exact hF2
  · exact hF3
  · exact hF4
  · exact hF5

/-- The same step without words: no valid standard configuration (`NConfig.Valid`, audited in
`AuditN.lean`) on 7 symbols has cost at most 135. -/
example (hC : Caps) (hF : Profiles) (hT : KS.TableT) (hK : KS.TheoremK) (hJ : KS.Joint)
    (c : NConfig 7) (hv : c.Valid) : ¬ c.cost ≤ 135 :=
  A15.no_config_135 hC hF hT hK hJ c hv

end

/-! ### Axioms -/

#print axioms SuperpermLowerBounds.covers_5900_of_caps
#print axioms SuperpermLowerBounds.A15.no_config_135
#print axioms SuperpermLowerBounds.A15.core
#print axioms SuperpermLowerBounds.A15.hanging_exts
#print axioms SuperpermLowerBounds.A15.hanging_ext
#print axioms SuperpermLowerBounds.A15.kernel_pieces
#print axioms SuperpermLowerBounds.A15.segSeq_spec
#print axioms SuperpermLowerBounds.A15.ringSeq_spec
#print axioms SuperpermLowerBounds.A15.glue_split
#print axioms SuperpermLowerBounds.A15.cut5
#print axioms SuperpermLowerBounds.A15.acc_value
#print axioms SuperpermLowerBounds.A15.acc_weight
#print axioms SuperpermLowerBounds.A15.eps_le_one
#print axioms SuperpermLowerBounds.A15.famC_length_le
#print axioms SuperpermLowerBounds.A15.sum_le_Hn
#print axioms SuperpermLowerBounds.A15.cHn
#print axioms SuperpermLowerBounds.A15.cK3
#print axioms SuperpermLowerBounds.A15.cRABa
#print axioms SuperpermLowerBounds.A15.Dv_le_SH
