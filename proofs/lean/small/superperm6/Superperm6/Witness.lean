/-
NOTICE OF MODIFICATION.
This file is `formal-verification/Superperm6/Witness.lean` of github.com/BGray-wrl/superperm6, commit
d8a932d8f61d80b0bcfc737bd0e235a8300449c4 (MIT License, Copyright (c) 2026 Benjamin Grayzel), with changes
made 2026-10-25 by Jakub Halfar (github.com/jhalfar/superpermutations):
  * kernel-only version: `witness` written out as a list (the content of `data/superperm6_872_clean.txt`; `build.sh` compares them), `IsSuperpermutation witness` checked by the kernel in 30 parts, the pairwise distinctness of the 720 windows by sorting their codes (`windowCode`); the other checks by the kernel.
-/
import Superperm6.Basic

/-!
# The explicit length-872 witness

The canonical witness is read at elaboration time from the frozen ancillary
file.  `include_str` expands its contents into the Lean declaration.  The
subsequent finite propositions are discharged with Lean's trusted native
evaluator; `AxiomAudit.lean` exposes that trust explicitly.
-/

namespace Superperm6

def witnessText : String :=
  include_str ".." / "data" / "superperm6_872_clean.txt"

def digit? : Char → Option Symbol
  | '1' => some 0
  | '2' => some 1
  | '3' => some 2
  | '4' => some 3
  | '5' => some 4
  | '6' => some 5
  | _ => none

/-- The newline in the canonical text file is ignored; digits `1`--`6` are
represented internally by `Fin 6` values `0`--`5`.

Kernel-only version: the digits of `data/superperm6_872_clean.txt` (that is, `witnessText.toList.filterMap
digit?`), written out as a list, because the kernel decodes the string literal of `include_str` only at great
cost.  `build.sh` checks that this list is the content of the file. -/
def witness : Word :=
  [3, 2, 1, 4, 0, 5, 3, 2, 1, 4, 0, 3, 5, 2, 4, 1, 0, 3, 2, 5, 4, 1, 0, 3, 2, 4, 5, 1, 0, 3, 2, 4, 1, 5, 0, 2, 3, 4, 1, 0,
    5, 2, 3, 4, 1, 0, 2, 5, 3, 4, 1, 0, 2, 3, 5, 4, 1, 0, 2, 3, 4, 5, 1, 0, 2, 3, 4, 1, 5, 0, 2, 4, 3, 1, 0, 5, 2, 4, 3, 1,
    0, 2, 5, 4, 3, 1, 0, 2, 4, 5, 3, 1, 0, 2, 4, 3, 5, 1, 0, 2, 4, 3, 1, 5, 0, 2, 4, 1, 3, 5, 0, 4, 2, 1, 3, 5, 4, 0, 2, 1,
    3, 4, 5, 0, 2, 1, 3, 4, 0, 5, 2, 1, 3, 4, 0, 2, 5, 1, 3, 4, 0, 2, 1, 5, 3, 4, 0, 2, 1, 3, 5, 4, 2, 0, 1, 3, 4, 5, 2, 0,
    1, 3, 4, 2, 5, 0, 1, 3, 4, 2, 0, 5, 1, 3, 4, 2, 0, 1, 5, 3, 4, 2, 0, 1, 3, 5, 4, 2, 1, 0, 3, 4, 5, 2, 1, 0, 3, 4, 2, 5,
    1, 0, 3, 4, 2, 1, 5, 0, 3, 4, 2, 1, 0, 5, 3, 4, 2, 1, 0, 3, 5, 4, 2, 1, 3, 0, 5, 4, 1, 2, 3, 0, 5, 1, 4, 2, 3, 0, 1, 5,
    4, 2, 3, 0, 1, 4, 5, 2, 3, 0, 1, 4, 2, 5, 3, 1, 0, 4, 2, 3, 5, 1, 0, 4, 2, 3, 1, 5, 0, 4, 2, 3, 1, 0, 5, 4, 2, 3, 1, 0,
    4, 5, 2, 3, 1, 0, 4, 2, 5, 3, 1, 4, 0, 2, 3, 5, 1, 4, 0, 2, 3, 1, 5, 4, 0, 2, 3, 1, 4, 5, 0, 2, 3, 1, 4, 0, 5, 2, 3, 1,
    4, 0, 2, 5, 3, 1, 4, 2, 0, 5, 3, 1, 2, 4, 0, 5, 3, 1, 2, 0, 4, 5, 3, 1, 2, 0, 5, 4, 3, 1, 2, 0, 5, 3, 4, 1, 2, 0, 5, 3,
    1, 4, 2, 5, 0, 3, 1, 2, 4, 5, 0, 3, 1, 2, 5, 4, 0, 3, 1, 2, 5, 0, 4, 3, 1, 2, 5, 0, 3, 4, 1, 2, 5, 0, 3, 1, 4, 2, 5, 3,
    0, 1, 4, 2, 3, 5, 0, 1, 4, 2, 3, 0, 5, 1, 2, 4, 3, 0, 1, 5, 2, 4, 3, 0, 1, 2, 5, 4, 3, 0, 1, 2, 4, 5, 3, 0, 1, 2, 4, 3,
    5, 0, 1, 2, 4, 3, 0, 5, 1, 2, 3, 4, 0, 1, 5, 2, 3, 4, 0, 1, 2, 5, 3, 4, 0, 1, 2, 3, 5, 4, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3,
    4, 0, 5, 1, 2, 3, 0, 4, 5, 1, 3, 2, 0, 4, 5, 1, 3, 0, 2, 4, 5, 1, 3, 0, 4, 2, 5, 1, 3, 0, 4, 5, 2, 1, 3, 0, 4, 5, 1, 2,
    3, 0, 5, 4, 1, 3, 2, 0, 5, 4, 1, 3, 0, 2, 5, 4, 1, 3, 0, 5, 2, 4, 1, 3, 0, 5, 4, 2, 1, 3, 5, 0, 4, 1, 2, 3, 5, 0, 4, 1,
    3, 2, 5, 0, 4, 1, 3, 5, 2, 0, 4, 1, 3, 5, 0, 2, 4, 1, 5, 3, 0, 4, 2, 1, 5, 3, 0, 4, 1, 2, 5, 3, 0, 4, 1, 5, 2, 3, 0, 4,
    1, 5, 3, 2, 0, 4, 1, 5, 3, 0, 2, 4, 1, 5, 0, 3, 2, 4, 1, 0, 5, 3, 2, 4, 1, 0, 3, 5, 2, 4, 0, 1, 3, 2, 5, 4, 0, 1, 3, 2,
    4, 5, 0, 1, 3, 2, 4, 0, 5, 1, 3, 2, 4, 0, 1, 5, 3, 2, 4, 0, 1, 3, 5, 2, 4, 0, 3, 1, 5, 2, 0, 4, 3, 1, 5, 2, 0, 3, 4, 1,
    5, 2, 0, 3, 1, 4, 5, 2, 0, 3, 1, 5, 4, 2, 0, 3, 1, 5, 2, 4, 0, 3, 5, 1, 2, 0, 4, 3, 5, 1, 2, 0, 3, 4, 5, 1, 2, 0, 3, 5,
    4, 1, 2, 0, 3, 5, 1, 4, 2, 0, 3, 5, 1, 2, 4, 0, 3, 5, 2, 1, 4, 0, 3, 2, 5, 1, 4, 0, 3, 2, 1, 5, 4, 0, 3, 2, 1, 4, 5, 0,
    3, 2, 1, 4, 3, 0, 5, 2, 1, 4, 3, 0, 2, 5, 1, 4, 3, 0, 2, 1, 5, 4, 3, 0, 2, 1, 4, 5, 3, 0, 2, 1, 4, 3, 5, 0, 2, 1, 4, 3,
    2, 0, 5, 1, 4, 3, 2, 0, 1, 5, 4, 3, 2, 0, 1, 4, 5, 3, 2, 0, 1, 4, 3, 5, 2, 0, 1, 4, 3, 2, 5, 0, 1, 4, 3, 2, 1, 0, 5, 4,
    3, 2, 1, 0, 4, 5, 3, 2, 1, 0, 4, 3, 5, 2, 1, 0, 4, 3, 2, 5, 1, 0, 4, 3, 2, 1, 5, 0, 4, 3, 2, 1]

theorem witness_length : witness.length = 872 := by decide +kernel

/-! Kernel-only version: `IsSuperpermutation witness` is checked by the kernel in 30 parts of 24 permutations
each (`p 0 = a`, `p 1 = b`). -/

theorem witness_occurs_chunk_0_1 : ∀ p : Perm6, p 0 = 0 → p 1 = 1 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_0_2 : ∀ p : Perm6, p 0 = 0 → p 1 = 2 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_0_3 : ∀ p : Perm6, p 0 = 0 → p 1 = 3 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_0_4 : ∀ p : Perm6, p 0 = 0 → p 1 = 4 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_0_5 : ∀ p : Perm6, p 0 = 0 → p 1 = 5 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_1_0 : ∀ p : Perm6, p 0 = 1 → p 1 = 0 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_1_2 : ∀ p : Perm6, p 0 = 1 → p 1 = 2 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_1_3 : ∀ p : Perm6, p 0 = 1 → p 1 = 3 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_1_4 : ∀ p : Perm6, p 0 = 1 → p 1 = 4 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_1_5 : ∀ p : Perm6, p 0 = 1 → p 1 = 5 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_2_0 : ∀ p : Perm6, p 0 = 2 → p 1 = 0 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_2_1 : ∀ p : Perm6, p 0 = 2 → p 1 = 1 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_2_3 : ∀ p : Perm6, p 0 = 2 → p 1 = 3 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_2_4 : ∀ p : Perm6, p 0 = 2 → p 1 = 4 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_2_5 : ∀ p : Perm6, p 0 = 2 → p 1 = 5 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_3_0 : ∀ p : Perm6, p 0 = 3 → p 1 = 0 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_3_1 : ∀ p : Perm6, p 0 = 3 → p 1 = 1 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_3_2 : ∀ p : Perm6, p 0 = 3 → p 1 = 2 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_3_4 : ∀ p : Perm6, p 0 = 3 → p 1 = 4 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_3_5 : ∀ p : Perm6, p 0 = 3 → p 1 = 5 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_4_0 : ∀ p : Perm6, p 0 = 4 → p 1 = 0 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_4_1 : ∀ p : Perm6, p 0 = 4 → p 1 = 1 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_4_2 : ∀ p : Perm6, p 0 = 4 → p 1 = 2 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_4_3 : ∀ p : Perm6, p 0 = 4 → p 1 = 3 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_4_5 : ∀ p : Perm6, p 0 = 4 → p 1 = 5 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_5_0 : ∀ p : Perm6, p 0 = 5 → p 1 = 0 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_5_1 : ∀ p : Perm6, p 0 = 5 → p 1 = 1 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_5_2 : ∀ p : Perm6, p 0 = 5 → p 1 = 2 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_5_3 : ∀ p : Perm6, p 0 = 5 → p 1 = 3 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunk_5_4 : ∀ p : Perm6, p 0 = 5 → p 1 = 4 →
    Occurs witness p := by
  decide +kernel

theorem witness_occurs_chunked (p : Perm6) :
    Occurs witness p := by
  have key : ∀ a b : Fin 6, p 0 = a → p 1 = b →
      Occurs witness p := by
    intro a b
    fin_cases a <;> fin_cases b
    · intro h0 h1; exact absurd (p.injective (h0.trans h1.symm)) (by decide)
    · exact witness_occurs_chunk_0_1 p
    · exact witness_occurs_chunk_0_2 p
    · exact witness_occurs_chunk_0_3 p
    · exact witness_occurs_chunk_0_4 p
    · exact witness_occurs_chunk_0_5 p
    · exact witness_occurs_chunk_1_0 p
    · intro h0 h1; exact absurd (p.injective (h0.trans h1.symm)) (by decide)
    · exact witness_occurs_chunk_1_2 p
    · exact witness_occurs_chunk_1_3 p
    · exact witness_occurs_chunk_1_4 p
    · exact witness_occurs_chunk_1_5 p
    · exact witness_occurs_chunk_2_0 p
    · exact witness_occurs_chunk_2_1 p
    · intro h0 h1; exact absurd (p.injective (h0.trans h1.symm)) (by decide)
    · exact witness_occurs_chunk_2_3 p
    · exact witness_occurs_chunk_2_4 p
    · exact witness_occurs_chunk_2_5 p
    · exact witness_occurs_chunk_3_0 p
    · exact witness_occurs_chunk_3_1 p
    · exact witness_occurs_chunk_3_2 p
    · intro h0 h1; exact absurd (p.injective (h0.trans h1.symm)) (by decide)
    · exact witness_occurs_chunk_3_4 p
    · exact witness_occurs_chunk_3_5 p
    · exact witness_occurs_chunk_4_0 p
    · exact witness_occurs_chunk_4_1 p
    · exact witness_occurs_chunk_4_2 p
    · exact witness_occurs_chunk_4_3 p
    · intro h0 h1; exact absurd (p.injective (h0.trans h1.symm)) (by decide)
    · exact witness_occurs_chunk_4_5 p
    · exact witness_occurs_chunk_5_0 p
    · exact witness_occurs_chunk_5_1 p
    · exact witness_occurs_chunk_5_2 p
    · exact witness_occurs_chunk_5_3 p
    · exact witness_occurs_chunk_5_4 p
    · intro h0 h1; exact absurd (p.injective (h0.trans h1.symm)) (by decide)
  exact key _ _ rfl rfl

theorem witness_isSuperpermutation : IsSuperpermutation witness :=
  fun p => witness_occurs_chunked p


def windows (n : ℕ) (w : List α) : List (List α) :=
  (List.range (w.length + 1 - n)).map fun i => (w.drop i).take n

def IsPermutationWindow (w : Word) : Prop := w.length = 6 ∧ w.Nodup

instance (w : Word) : Decidable (IsPermutationWindow w) :=
  inferInstanceAs (Decidable (w.length = 6 ∧ w.Nodup))

def permutationWindows : List Word :=
  (windows 6 witness).filter IsPermutationWindow

/-- The witness has 867 six-symbol windows. -/
theorem witness_window_count : (windows 6 witness).length = 867 := by decide +kernel

/-- Exactly 720 windows are permutations. -/
theorem witness_permutation_window_count : permutationWindows.length = 720 := by
  decide +kernel

/-- A number for each word (its digits in base 6). -/
def windowCode (w : Word) : ℕ := w.foldl (fun a x => 6 * a + x.val) 0

/-- Kernel-only version: the codes of the windows, sorted, increase strictly (a linear check after a sort, instead
of comparing all pairs of windows). -/
theorem witness_window_codes_sorted :
    ((permutationWindows.map windowCode).insertionSort (· ≤ ·)).IsChain (· < ·) := by
  decide +kernel

/-- Those 720 permutation windows are pairwise distinct. -/
theorem witness_permutation_windows_nodup : permutationWindows.Nodup := by
  have hsorted := List.isChain_iff_pairwise.mp witness_window_codes_sorted
  have hnodup : ((permutationWindows.map windowCode).insertionSort (· ≤ ·)).Nodup :=
    hsorted.imp (fun h => Nat.ne_of_lt h)
  exact ((List.perm_insertionSort _ _).nodup_iff.mp hnodup).of_map windowCode

theorem verified_upper_bound :
    ∃ w : Word, IsSuperpermutation w ∧ w.length = 872 :=
  ⟨witness, witness_isSuperpermutation, witness_length⟩

end Superperm6
