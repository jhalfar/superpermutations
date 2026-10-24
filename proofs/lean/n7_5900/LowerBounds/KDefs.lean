import LowerBounds.PLevels
import LowerBounds.PTables
import LowerBounds.KTables

/-!
# The statements of the proof of 5,900 on words

Definitions only.  The parts of the proof (the accounting at defect 15, the kernel alone, the joint
statements, the final theorem) meet at these statements; sections refer to the written proof.

* `SetB`: the tables of set B for sequences and rings on words (section 2.1).
* `TableT`: table T' is valid (sections 2.2, 2.3).
* `TheoremK`: every sequence with `s ≤ 8` links and `x ≤ 90 - 6 s` holes has at most `D_s(x)` rows
  (section 4.1).
* `J`, `Joint`: the joint statements S1 .. S5 (sections 5.1, 5.3).
-/

namespace SuperpermLowerBounds
namespace KS

open T5899 T5900

/-- Set B on words: chains to 84 holes, sequences with 1 to 5 links, rings to 77 holes. -/
def SetB : Prop :=
  PS.SeqCapLt 7 0 (PS.capF Ptabs 0) 85 ∧ PS.SeqCapLt 7 1 (PS.capF Ptabs 1) 79 ∧
    PS.SeqCapLt 7 2 (PS.capF Ptabs 2) 73 ∧ PS.SeqCapLt 7 3 (PS.capF Ptabs 3) 67 ∧
    PS.SeqCapLt 7 4 (PS.capF Ptabs 4) 61 ∧ PS.SeqCapLt 7 5 (PS.capF Ptabs 5) 55 ∧
    PS.RingCapT 7 (fun x => PRtab.getD x 0) 77

/-- The number of entries of the rows of T'. -/
def Tlen : List ℕ := [85, 79, 73, 67, 61, 61, 55, 49, 43]

/-- Table T' is valid: its rows for sequences with `s ≤ 8` links and its ring row to 84 holes. -/
def TableT : Prop :=
  (∀ s, s ≤ 8 → PS.SeqCapLt 7 s (PS.capF Ttab s) (Tlen.getD s 0)) ∧
    PS.RingCapT 7 (fun x => TRtab.getD x 0) 84

/-- Theorem K: table D is valid. -/
def TheoremK : Prop := ∀ s, s ≤ 8 → PS.SeqCapLt 7 s (PS.capF Dtab s) (91 - 6 * s)

/-- The kind of a piece: a sequence with at most `s` links, or a ring. -/
inductive Kind
  | seq (s : ℕ)
  | ring

/-- A piece of a kind. -/
def IsPiece : Kind → List PS.TRow → Prop
  | .seq s, L => PS.IsSeq 7 L ∧ L ≠ [] ∧ (∀ x ∈ L, x.1 ≤ 1) ∧ PS.linksT L ≤ s
  | .ring, L => PS.IsSeq 7 L ∧ (∀ x ∈ L, x.1 = 0) ∧ 2 ≤ L.length ∧ PS.Closes 7 L

/-- The value of a piece: rows less holes less 5 for every link. -/
def valT (L : List PS.TRow) : ℤ := (L.length : ℤ) - PS.holesT 7 L - 5 * PS.linksT L

/-- The weight of a piece: holes plus 6 for every link. -/
def wtT (L : List PS.TRow) : ℕ := PS.holesT 7 L + 6 * PS.linksT L

/-- The blocks (entries) of a piece. -/
def blocksT (L : List PS.TRow) : List (List ℕ) := (L.map Prod.snd).flatten

/-- The pieces have at most `B` shared classes: after removing at most `B` blocks, the classes of
the blocks of all pieces are pairwise different. -/
def SharedLe (Ls : List (List PS.TRow)) (B : ℕ) : Prop :=
  ∃ keep rem : List (List ℕ), (Ls.flatMap blocksT).Perm (keep ++ rem) ∧ rem.length ≤ B ∧
    keep.Pairwise (fun u v => ¬ u ~r v)

/-- J(kinds; V, W; B): pieces of the given kinds with at most `B` shared classes and total weight
at most `W` have total value less than `V`. -/
def J (kinds : List Kind) (V : ℤ) (W B : ℕ) : Prop :=
  ∀ Ls : List (List PS.TRow), List.Forall₂ IsPiece kinds Ls → SharedLe Ls B →
    (Ls.map wtT).sum ≤ W → (Ls.map valT).sum < V

/-- The five joint statements S1, S2, S3, S4, S5. -/
def Joint : Prop :=
  J [.seq 4, .seq 4] 55 78 1 ∧ J [.seq 5, .ring] 51 83 1 ∧ J [.seq 2, .ring, .ring] 57 76 2 ∧
    J [.seq 1, .seq 1, .ring] 61 71 1 ∧ J [.seq 0, .seq 0, .ring] 62 70 2

end KS
end SuperpermLowerBounds
