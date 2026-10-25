import Challenge
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Perm.Subperm

/-!
# Superpermutations on 1 to 5 symbols, checked by the kernel

`check K w` asks, for every arrangement of `0, ..., K-1` in Mathlib's list `permutations'`, whether it occurs in
`w` as a contiguous part. `covers_of_check` proves that a word that passes is a superpermutation in the sense of
Pantone's `Covers`. The words are those of the recursive construction (each word on K symbols is built from the
word on K - 1 symbols); their lengths 1, 3, 9, 33, 153 are 1! + 2! + ... + K!. Every check is a kernel reduction
(`decide +kernel`); no `native_decide`.
-/

namespace SmallSuperperm

open SuperpermutationBounds

/-- `occurs p w`: the list `p` is a contiguous part of `w`. -/
def occurs {α : Type} [DecidableEq α] (p : List α) : List α → Bool
  | [] => p.isEmpty
  | x :: t => p.isPrefixOf (x :: t) || occurs p t

theorem infix_of_occurs {α : Type} [DecidableEq α] (p : List α) :
    ∀ w : List α, occurs p w = true → p <:+: w
  | [], h => by
    have : p = [] := List.isEmpty_iff.mp (by simpa [occurs] using h)
    subst this
    exact List.nil_infix
  | x :: t, h => by
    simp only [occurs, Bool.or_eq_true] at h
    rcases h with h | h
    · exact (List.isPrefixOf_iff_prefix.mp h).isInfix
    · exact (infix_of_occurs p t h).trans (List.suffix_cons x t).isInfix

/-- Every arrangement of `0, ..., K-1` occurs in `w`. -/
def check (K : ℕ) (w : List (Fin K)) : Bool :=
  (List.finRange K).permutations'.all (fun p => occurs p w)

/-- A word that passes `check` is a superpermutation. -/
theorem covers_of_check {K : ℕ} (w : List (Fin K)) (h : check K w = true) : Covers w := by
  intro p hl hn
  have hp : p.Perm (List.finRange K) :=
    (List.Nodup.subperm hn (fun x _ => List.mem_finRange x)).perm_of_length_le (by simp [hl])
  have hocc := List.all_eq_true.mp h p (List.mem_permutations'.mpr hp)
  obtain ⟨u, v, huv⟩ := infix_of_occurs p w hocc
  exact ⟨u, v, huv.symm⟩

def word1 : List (Fin 1) := [0]
def word2 : List (Fin 2) := [0, 1, 0]
def word3 : List (Fin 3) := [0, 1, 2, 0, 1, 0, 2, 1, 0]
def word4 : List (Fin 4) :=
  [0, 1, 2, 3, 0, 1, 2, 0, 3, 1, 2, 0, 1, 3, 2, 0, 1, 0, 2, 3, 1, 0, 2, 1, 3, 0, 2, 1, 0, 3, 2, 1, 0]
def word5 : List (Fin 5) :=
  [0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 4, 1, 2, 3, 0, 1, 4, 2, 3, 0, 1, 2, 4, 3, 0, 1, 2, 0, 3, 4, 1, 2, 0, 3, 1, 4,
   2, 0, 3, 1, 2, 4, 0, 3, 1, 2, 0, 4, 3, 1, 2, 0, 1, 3, 4, 2, 0, 1, 3, 2, 4, 0, 1, 3, 2, 0, 4, 1, 3, 2, 0, 1,
   4, 3, 2, 0, 1, 0, 2, 3, 4, 1, 0, 2, 3, 1, 4, 0, 2, 3, 1, 0, 4, 2, 3, 1, 0, 2, 4, 3, 1, 0, 2, 1, 3, 4, 0, 2,
   1, 3, 0, 4, 2, 1, 3, 0, 2, 4, 1, 3, 0, 2, 1, 4, 3, 0, 2, 1, 0, 3, 4, 2, 1, 0, 3, 2, 4, 1, 0, 3, 2, 1, 4, 0,
   3, 2, 1, 0, 4, 3, 2, 1, 0]

theorem check1 : check 1 word1 = true := by decide +kernel
theorem check2 : check 2 word2 = true := by decide +kernel
theorem check3 : check 3 word3 = true := by decide +kernel
theorem check4 : check 4 word4 = true := by decide +kernel
theorem check5 : check 5 word5 = true := by decide +kernel

theorem word1_length : word1.length = 1 := by decide +kernel
theorem word2_length : word2.length = 3 := by decide +kernel
theorem word3_length : word3.length = 9 := by decide +kernel
theorem word4_length : word4.length = 33 := by decide +kernel
theorem word5_length : word5.length = 153 := by decide +kernel

theorem upper_one : ∃ w : List (Fin 1), Covers w ∧ w.length = 1 :=
  ⟨word1, covers_of_check _ check1, word1_length⟩
theorem upper_two : ∃ w : List (Fin 2), Covers w ∧ w.length = 3 :=
  ⟨word2, covers_of_check _ check2, word2_length⟩
theorem upper_three : ∃ w : List (Fin 3), Covers w ∧ w.length = 9 :=
  ⟨word3, covers_of_check _ check3, word3_length⟩
theorem upper_four : ∃ w : List (Fin 4), Covers w ∧ w.length = 33 :=
  ⟨word4, covers_of_check _ check4, word4_length⟩
theorem upper_five : ∃ w : List (Fin 5), Covers w ∧ w.length = 153 :=
  ⟨word5, covers_of_check _ check5, word5_length⟩

/-- The lower bound for one symbol: the word contains `[0]`. -/
theorem lower_one : ∀ w : List (Fin 1), Covers w → 1 ≤ w.length := by
  intro w hw
  obtain ⟨u, v, rfl⟩ := hw [0] rfl (List.nodup_singleton 0)
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- The lower bound for two symbols: a word of at most two letters cannot contain both `[0, 1]` and `[1, 0]`. -/
theorem lower_two : ∀ w : List (Fin 2), Covers w → 3 ≤ w.length := by
  intro w hw
  obtain ⟨u, v, h1⟩ := hw [0, 1] rfl (by decide)
  obtain ⟨u', v', h2⟩ := hw [1, 0] rfl (by decide)
  by_contra hlt
  have l1 := congrArg List.length h1
  have l2 := congrArg List.length h2
  simp only [List.length_append, List.length_cons, List.length_nil] at l1 l2
  have hu : u = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hv : v = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hu' : u' = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hv' : v' = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hu hv hu' hv'
  rw [h1] at h2
  exact absurd h2 (by decide)

end SmallSuperperm

#print axioms SmallSuperperm.covers_of_check
#print axioms SmallSuperperm.check5
#print axioms SmallSuperperm.upper_five
#print axioms SmallSuperperm.lower_one
#print axioms SmallSuperperm.lower_two
