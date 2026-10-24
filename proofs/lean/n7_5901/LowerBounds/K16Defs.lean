import LowerBounds.KDefs
import LowerBounds.K16Tables

/-!
# The statements of the proof of 5,901 on words

Definitions only (no proofs).  The parts of the proof meet here: the accounting at defect 16 (A16), the
kernel alone (B16), the joint statements (C16) and the final theorem (D16).  Sections refer to the written
proof `proofs/n7_5901/PROOF_5901.md`; the computations are those of `proofs/n7_5901/table/TABLE_C16.md`.  The objects on
words are those of the proof of 5,900 (`KDefs.lean`): `PS.IsSeq`, `PS.SeqCapLt`, `KS.Kind`, `KS.IsPiece`,
`KS.valT`, `KS.wtT`, `KS.SharedLe`, `KS.J`.

* `FRow P s LO G`: the statement F(s; LO, G) of section 3.1 on the table `P`: if the rows below `s` are
  valid to `G` holes and the row `s` to `LO` holes, the row `s` is valid to `G` holes.  `K0 .. K10`: the
  eleven kernel statements of Table C with the tables they read (section 3.4).
* `CL16`: the entries of the rows 9 and 10 of D16 below `LO = 35` (Lemma CL of the proof of 5,900; the
  only entries that the eleven statements take as given and that Theorem K of 5,900 does not give).
* `TheoremK16`: table D16 is valid (Theorem K16, section 3.1).
* `IsPieceP`, `JP`: a joint statement restricted to the objects whose ring pieces all satisfy a condition
  (a class of objects, section 4.1).  `T1 .. T9`: the joint statements as they were run (section 4.7, the
  list "what each run proves"), in the order of the kinds of the run.  `Joint16`: all of them.
-/

namespace SuperpermLowerBounds
namespace K16

open T5899 T5900 T5901

/-! ### The kernel alone -/

/-- F(s; LO, G) on the table `P` (section 3.1): given the rows `0 .. s - 1` of `P` to `G` holes and the
row `s` to `LO` holes, every sequence with exactly `s` links and at most `G` holes has at most `P_s(x)`
rows. -/
def FRow (P : List (List ℕ)) (s LO G : ℕ) : Prop :=
  (∀ j, j < s → PS.SeqCapLt 7 j (PS.capF P j) (G + 1)) → PS.SeqCapLt 7 s (PS.capF P s) (LO + 1) →
    PS.SeqCapLt 7 s (PS.capF P s) (G + 1)

/-- K10 .. K5: the tables `capD16u_s_k.txt` (rows below `s` from D, row `s` from D16). -/
def K10 : Prop := FRow Utab10 10 35 36
def K9 : Prop := FRow Utab9 9 35 42
def K8 : Prop := FRow Utab8 8 35 48
def K7 : Prop := FRow Utab7 7 35 54
def K6 : Prop := FRow Utab6 6 37 60
def K5 : Prop := FRow Utab5 5 37 66
/-- K4 .. K0: the table `capD16_k.txt` (D16). -/
def K4 : Prop := FRow D16tab 4 41 72
def K3 : Prop := FRow D16tab 3 48 78
def K2 : Prop := FRow D16tab 2 51 84
def K1 : Prop := FRow D16tab 1 55 90
def K0 : Prop := FRow D16tab 0 65 96

/-- The eleven kernel statements of Table C. -/
def Kernel16 : Prop := K0 ∧ K1 ∧ K2 ∧ K3 ∧ K4 ∧ K5 ∧ K6 ∧ K7 ∧ K8 ∧ K9 ∧ K10

/-- The closure entries that the kernel statements take as given: rows 9 and 10 of D16 (equal to D
there) to 35 holes. -/
def CL16 : Prop :=
  PS.SeqCapLt 7 9 (PS.capF D16tab 9) 36 ∧ PS.SeqCapLt 7 10 (PS.capF D16tab 10) 36

/-- **Theorem K16**: every sequence with `s ≤ 10` links and `x ≤ 96 - 6 s` holes has at most
`D16_s(x)` rows. -/
def TheoremK16 : Prop := ∀ s, s ≤ 10 → PS.SeqCapLt 7 s (PS.capF D16tab s) (97 - 6 * s)

/-! ### Joint statements on classes of objects -/

/-- A piece of a kind; a ring piece must in addition satisfy `P`. -/
def IsPieceP (P : List PS.TRow → Prop) : KS.Kind → List PS.TRow → Prop
  | .seq s, L => KS.IsPiece (.seq s) L
  | .ring, L => KS.IsPiece .ring L ∧ P L

/-- J(kinds; V, W; B) for the objects whose ring pieces all satisfy `P`. -/
def JP (P : List PS.TRow → Prop) (kinds : List KS.Kind) (V : ℤ) (W B : ℕ) : Prop :=
  ∀ Ls : List (List PS.TRow), List.Forall₂ (IsPieceP P) kinds Ls → KS.SharedLe Ls B →
    (Ls.map KS.wtT).sum ≤ W → (Ls.map KS.valT).sum < V

/-- Rings with `lo ≤ holes ≤ hi`. -/
def RIn (lo hi : ℕ) (L : List PS.TRow) : Prop := lo ≤ PS.holesT 7 L ∧ PS.holesT 7 L ≤ hi

/-- Rings with at least 8 holes (`RLO=8`). -/
def R8 (L : List PS.TRow) : Prop := 8 ≤ PS.holesT 7 L

/-- Rings of value at least 0 (the class of section 4.2: the cut at a ring with negative need). -/
def RNN (L : List PS.TRow) : Prop := 0 ≤ KS.valT L

/-- T1: J(S7 S7; 50, 84; 1). -/
def T1 : Prop := KS.J [.seq 7, .seq 7] 50 84 1

/-- A window of T2 run whole: J(R S7; 46, 89; 1) for rings with `lo ≤ holes ≤ hi`. -/
def T2win (lo hi : ℕ) : Prop := JP (RIn lo hi) [.ring, .seq 7] 46 89 1

/-- The upper half of a window of T2 (VS (hi)): rings in the window with value at least `a`. -/
def T2up (lo hi : ℕ) (a : ℤ) : Prop :=
  JP (fun L => RIn lo hi L ∧ a ≤ KS.valT L) [.ring, .seq 7] 46 89 1

/-- The lower half of a window of T2 (VS (lo), run kernel first): rings in the window with value at
most `a - 1`. -/
def T2lo (lo hi : ℕ) (a : ℤ) : Prop :=
  JP (fun L => RIn lo hi L ∧ KS.valT L ≤ a - 1) [.seq 7, .ring] 46 89 1

/-- T2: the ten runs of Table C (windows 8..15, 16..23, 24..31, 56..89 whole; 32..39, 40..47, 48..55
split at the ring value 17, 20, 23). -/
def T2 : Prop :=
  T2win 8 15 ∧ T2win 16 23 ∧ T2win 24 31 ∧ T2up 32 39 17 ∧ T2lo 32 39 17 ∧ T2up 40 47 20 ∧
    T2lo 40 47 20 ∧ T2up 48 55 23 ∧ T2lo 48 55 23 ∧ T2win 56 89

/-- T3': J(R S5 R; 52, 82; 2) for rings with at least 8 holes and value at least 0. -/
def T3 : Prop := JP (fun L => R8 L ∧ RNN L) [.ring, .seq 5, .ring] 52 82 2

/-- T4': J(R S4 S4; 56, 77; 2) for rings with at least 8 holes (the ring is piece 1, need 56 > 0). -/
def T4 : Prop := JP R8 [.ring, .seq 4, .seq 4] 56 77 2

/-- T5: J(S3 S3 S3; 60, 72; 2). -/
def T5 : Prop := KS.J [.seq 3, .seq 3, .seq 3] 60 72 2

/-- T6': J(S2 R R R; 58, 75; 3) for rings with at least 8 holes and value at least 0. -/
def T6 : Prop := JP (fun L => R8 L ∧ RNN L) [.seq 2, .ring, .ring, .ring] 58 75 3

/-- T7: J(S1 S1 R R; 62, 70; 3) for rings of value at least 0. -/
def T7 : Prop := JP RNN [.seq 1, .seq 1, .ring, .ring] 62 70 3

/-- T8: J(S0 S0 S0 R; 66, 65; 2) for rings of value at least 0. -/
def T8 : Prop := JP RNN [.seq 0, .seq 0, .seq 0, .ring] 66 65 2

/-- T9': J(S0 R R R R; 64, 68; 4) for rings with at least 8 holes and value at least 0. -/
def T9 : Prop := JP (fun L => R8 L ∧ RNN L) [.seq 0, .ring, .ring, .ring, .ring] 64 68 4

/-- The joint statements of Table C. -/
def Joint16 : Prop := T1 ∧ T2 ∧ T3 ∧ T4 ∧ T5 ∧ T6 ∧ T7 ∧ T8 ∧ T9

end K16
end SuperpermLowerBounds
