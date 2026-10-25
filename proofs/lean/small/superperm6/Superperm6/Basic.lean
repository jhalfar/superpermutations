/-
NOTICE OF MODIFICATION.
This file is `formal-verification/Superperm6/Basic.lean` of github.com/BGray-wrl/superperm6, commit
d8a932d8f61d80b0bcfc737bd0e235a8300449c4 (MIT License, Copyright (c) 2026 Benjamin Grayzel), with changes
made 2026-10-25 by Jakub Halfar (github.com/jhalfar/superpermutations):
  * kernel-only version: the inverse checks of the index permutations by `decide`; `R_order_six`, `F_order_five`, the orbit sizes, orbit membership, the orbit counts and the cost-one and cost-two successors proved symbolically (the proof follows the eight-symbol port (William Echols, superperm8-ge-46130, Apache License 2.0, after Justin Lebar's superperm7-ge-5898, Copyright 2026 Anthropic, PBC, Apache License 2.0), written back for six symbols; see NOTICE.echols); new relabelling lemmas (`d_mul_left`, `rClass_mul`, `fBlock_mul`, `forall_pair_of_one`); `cost_three_outdegree` from the kernel check at the start `1`.
-/
import Mathlib

/-!
# Basic definitions and the exact overlap metric

This file formalizes the non-computational definitions in Sections 1--2 of
the manuscript.  The overlap cost is defined as the least shift at which a
suffix of the first word agrees with a prefix of the second word.  The proof
that it is a directed metric is generic for equal-length lists.
-/

namespace Superperm6

abbrev Symbol := Fin 6
abbrev Perm6 := Equiv.Perm Symbol
abbrev Word := List Symbol

/-- The six-letter word associated with a permutation. -/
def permWord (p : Perm6) : Word := List.ofFn p

@[simp] theorem permWord_length (p : Perm6) : (permWord p).length = 6 := by
  simp [permWord]

theorem permWord_nodup (p : Perm6) : (permWord p).Nodup := by
  change (List.ofFn p).Nodup
  exact List.nodup_ofFn.mpr p.injective

theorem permWord_injective : Function.Injective permWord := by
  intro p q h
  apply Equiv.ext
  intro i
  exact congrFun (List.ofFn_injective h) i

theorem card_perm6 : Fintype.card Perm6 = 720 := by
  norm_num [Fintype.card_perm]

/-- A permutation occurs as a contiguous six-symbol factor of `w`. -/
def Occurs (w : Word) (p : Perm6) : Prop := permWord p <:+: w

instance (w : Word) (p : Perm6) : Decidable (Occurs w p) :=
  List.decidableInfix (permWord p) w

/-- A word containing all `6!` permutations. -/
def IsSuperpermutation (w : Word) : Prop := ∀ p : Perm6, Occurs w p

instance (w : Word) : Decidable (IsSuperpermutation w) :=
  Fintype.decidableForallFintype

/-- A formulation of `s(6) = n` that does not hide existence in `Nat.find`. -/
def IsMinimumLength (n : ℕ) : Prop :=
  (∃ w : Word, IsSuperpermutation w ∧ w.length = n) ∧
  (∀ w : Word, IsSuperpermutation w → n ≤ w.length)

section Overlap

variable {α : Type*} [DecidableEq α]

/-- A shift `k` is compatible when the suffix remaining after dropping `k`
symbols from `x` is the corresponding prefix of `y`. -/
def OverlapCompatible (x y : List α) (k : ℕ) : Prop :=
  x.drop k = y.take (x.length - k)

instance (x y : List α) (k : ℕ) : Decidable (OverlapCompatible x y k) :=
  inferInstanceAs (Decidable (x.drop k = y.take (x.length - k)))

omit [DecidableEq α] in
private theorem overlap_exists (x y : List α) :
    ∃ k, OverlapCompatible x y k := by
  refine ⟨x.length, ?_⟩
  simp [OverlapCompatible]

/-- Least number of symbols which must be appended to an equal-length word
`x` in order for the result to end in `y`. -/
def overlapCost (x y : List α) : ℕ := Nat.find (overlap_exists x y)

theorem overlapCost_spec (x y : List α) :
    OverlapCompatible x y (overlapCost x y) :=
  Nat.find_spec (overlap_exists x y)

theorem overlapCost_le_length (x y : List α) : overlapCost x y ≤ x.length :=
  Nat.find_min' (overlap_exists x y)
    (show OverlapCompatible x y x.length by simp [OverlapCompatible])

theorem overlapCost_le_of_compatible {x y : List α} {k : ℕ}
    (h : OverlapCompatible x y k) : overlapCost x y ≤ k :=
  Nat.find_min' (overlap_exists x y) h

omit [DecidableEq α] in
theorem suffix_of_compatible {x y : List α} {k : ℕ}
    (h : OverlapCompatible x y k) :
    y <:+ x ++ y.drop (x.length - k) := by
  refine ⟨x.take k, ?_⟩
  calc
    x.take k ++ y =
        x.take k ++ (y.take (x.length - k) ++ y.drop (x.length - k)) := by
          rw [List.take_append_drop]
    _ = (x.take k ++ x.drop k) ++ y.drop (x.length - k) := by
          rw [h]
          simp only [List.append_assoc]
    _ = x ++ y.drop (x.length - k) := by rw [List.take_append_drop]

omit [DecidableEq α] in
theorem compatible_of_suffix {x y t : List α} {k : ℕ}
    (hlen : y.length = x.length) (ht : t.length = k) (hk : k ≤ x.length)
    (h : y <:+ x ++ t) : OverlapCompatible x y k := by
  rcases h with ⟨pre, hpre⟩
  have hprelen : pre.length = k := by
    have hlen := congrArg List.length hpre
    simp only [List.length_append] at hlen
    omega
  have hy : y = x.drop k ++ t := by
    calc
      y = (pre ++ y).drop k := by simp [hprelen]
      _ = (x ++ t).drop k := by rw [hpre]
      _ = x.drop k ++ t := List.drop_append_of_le_length hk
  have hdrop : (x.drop k).length = x.length - k := by simp
  calc
    x.drop k = (x.drop k ++ t).take (x.length - k) := by simp [hdrop]
    _ = y.take (x.length - k) := by rw [hy]

/-- `overlapCost` is minimal among *all* appended words, not merely among
the canonical suffixes of `y`. -/
theorem overlapCost_min {x y t : List α} {k : ℕ}
    (hlen : y.length = x.length) (ht : t.length = k)
    (h : y <:+ x ++ t) : overlapCost x y ≤ k := by
  by_cases hk : x.length ≤ k
  · exact (overlapCost_le_length x y).trans hk
  · exact Nat.find_min' (overlap_exists x y)
      (compatible_of_suffix hlen ht (Nat.le_of_lt (Nat.lt_of_not_ge hk)) h)

/-- The canonical symbols appended by an optimal overlap. -/
def optimalAppend (x y : List α) : List α :=
  y.drop (x.length - overlapCost x y)

theorem optimalAppend_length {x y : List α} (hlen : y.length = x.length) :
    (optimalAppend x y).length = overlapCost x y := by
  simp only [optimalAppend, List.length_drop, hlen]
  have hle := overlapCost_le_length x y
  omega

theorem optimalAppend_suffix {x y : List α} :
    y <:+ x ++ optimalAppend x y := by
  exact suffix_of_compatible (overlapCost_spec x y)

theorem overlapCost_self (x : List α) : overlapCost x x = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.find_min' (overlap_exists x x)
    (show OverlapCompatible x x 0 by simp [OverlapCompatible])

theorem overlapCost_triangle {x y z : List α}
    (hxy : y.length = x.length) (hyz : z.length = y.length) :
    overlapCost x z ≤ overlapCost x y + overlapCost y z := by
  let u := optimalAppend x y
  let v := optimalAppend y z
  have hyS : y <:+ x ++ u := optimalAppend_suffix
  have hzS : z <:+ y ++ v := optimalAppend_suffix
  rcases hyS with ⟨a, ha⟩
  rcases hzS with ⟨b, hb⟩
  have hzFinal : z <:+ x ++ (u ++ v) := by
    refine ⟨a ++ b, ?_⟩
    calc
      (a ++ b) ++ z = a ++ (b ++ z) := by simp [List.append_assoc]
      _ = a ++ (y ++ v) := by rw [hb]
      _ = (a ++ y) ++ v := by simp [List.append_assoc]
      _ = (x ++ u) ++ v := by rw [ha]
      _ = x ++ (u ++ v) := by simp [List.append_assoc]
  apply overlapCost_min (hyz.trans hxy)
    (show (u ++ v).length = overlapCost x y + overlapCost y z by
      simp [u, v, optimalAppend_length hxy, optimalAppend_length hyz])
    hzFinal

theorem overlapCost_pos_of_ne {x y : List α} (hlen : y.length = x.length)
    (hne : x ≠ y) : 0 < overlapCost x y := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have h := overlapCost_spec x y
  rw [hzero] at h
  have hxy : x = y := by simpa [OverlapCompatible, ← hlen] using h
  exact hne hxy

end Overlap

/-- Directed append cost on six-symbol permutations. -/
def d (p q : Perm6) : ℕ := overlapCost (permWord p) (permWord q)

@[simp] theorem d_self (p : Perm6) : d p p = 0 := overlapCost_self _

theorem d_le_six (p q : Perm6) : d p q ≤ 6 := by
  simpa [d] using overlapCost_le_length (permWord p) (permWord q)

theorem d_pos_of_ne {p q : Perm6} (h : p ≠ q) : 0 < d p q := by
  apply overlapCost_pos_of_ne (by simp)
  exact fun hpq => h (permWord_injective hpq)

theorem d_triangle (p q r : Perm6) : d p r ≤ d p q + d q r := by
  exact overlapCost_triangle (by simp) (by simp)

/-! ## The rotation and insertion maps -/

private def rotIndexFn : Symbol → Symbol
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 5
  | ⟨_, _⟩ => 0

private def insertIndexFn : Symbol → Symbol
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 0
  | ⟨_, _⟩ => 5

private def nondecompTwoIndexFn : Symbol → Symbol
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 5
  | ⟨4, _⟩ => 1
  | ⟨_, _⟩ => 0

private def rotIndexInvFn : Symbol → Symbol
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 3
  | ⟨_, _⟩ => 4

private def insertIndexInvFn : Symbol → Symbol
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 3
  | ⟨_, _⟩ => 5

private def nondecompTwoIndexInvFn : Symbol → Symbol
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 2
  | ⟨_, _⟩ => 3

def rotIndex : Equiv.Perm Symbol where
  toFun := rotIndexFn
  invFun := rotIndexInvFn
  left_inv := by decide
  right_inv := by decide

def insertIndex : Equiv.Perm Symbol where
  toFun := insertIndexFn
  invFun := insertIndexInvFn
  left_inv := by decide
  right_inv := by decide

def nondecompTwoIndex : Equiv.Perm Symbol where
  toFun := nondecompTwoIndexFn
  invFun := nondecompTwoIndexInvFn
  left_inv := by decide
  right_inv := by decide

/-- `R(abcdef) = bcdefa`. -/
def R (p : Perm6) : Perm6 := rotIndex.trans p

/-- `F(abcdef) = bcdeaf`. -/
def F (p : Perm6) : Perm6 := insertIndex.trans p

/-- The nondecomposable cost-two successor `abcdef ↦ cdefba`. -/
def N₂ (p : Perm6) : Perm6 := nondecompTwoIndex.trans p

def finiteOrbit [Fintype α] [DecidableEq α] (f : α → α) (n : ℕ) (x : α) : Finset α :=
  (Finset.range n).image fun i => (f^[i]) x

def rClass (p : Perm6) : Finset Perm6 := finiteOrbit R 6 p
def fBlock (p : Perm6) : Finset Perm6 := finiteOrbit F 5 p

def allRClasses : Finset (Finset Perm6) := Finset.univ.image rClass
def allFBlocks : Finset (Finset Perm6) := Finset.univ.image fBlock

/-! ## The finite facts of this section, proved without `native_decide`

Kernel-only version.  The statements are the original ones; the proofs below replace evaluations over all
permutations (or all pairs of permutations).  Orbit sizes, orbit membership, the orbit count and the cost-one and
cost-two successors follow the symbolic proofs of the eight-symbol port (William Echols, superperm8-ge-46130,
`Superperm8/BasicOrbits.lean`, `BasicCount.lean`, `Basic.lean`, after Justin Lebar's superperm7-ge-5898),
written back for six symbols.  The cost-three out-degree uses relabelling: `d (σ * p) (σ * q) = d p q`. -/

theorem R_order_six : ∀ p : Perm6, (R^[6]) p = p := by
  intro p; apply Equiv.ext; intro i; fin_cases i <;> rfl

theorem F_order_five : ∀ p : Perm6, (F^[5]) p = p := by
  intro p; apply Equiv.ext; intro i; fin_cases i <;> rfl

theorem rClass_card (p : Perm6) : (rClass p).card = 6 := by
  have hcoord (i : Fin 6) : ((R^[i.val]) p) 0 = p i := by fin_cases i <;> rfl
  have hinj : Set.InjOn (fun i => (R^[i]) p) (Finset.range 6 : Set Nat) := by
    intro i hi j hj h
    have hi' : i < 6 := Finset.mem_range.mp hi
    have hj' : j < 6 := Finset.mem_range.mp hj
    have he := congrArg (fun q : Perm6 => q 0) h
    dsimp only at he
    rw [hcoord ⟨i, hi'⟩, hcoord ⟨j, hj'⟩] at he
    exact congrArg Fin.val (p.injective he)
  unfold rClass finiteOrbit
  rw [Finset.card_image_iff.mpr hinj, Finset.card_range]

theorem fBlock_card (p : Perm6) : (fBlock p).card = 5 := by
  have hcoord (i : Fin 5) : ((F^[i.val]) p) 0 = p i.castSucc := by fin_cases i <;> rfl
  have hinj : Set.InjOn (fun i => (F^[i]) p) (Finset.range 5 : Set Nat) := by
    intro i hi j hj h
    have hi' : i < 5 := Finset.mem_range.mp hi
    have hj' : j < 5 := Finset.mem_range.mp hj
    have he := congrArg (fun q : Perm6 => q 0) h
    dsimp only at he
    rw [hcoord ⟨i, hi'⟩, hcoord ⟨j, hj'⟩] at he
    exact congrArg Fin.val (p.injective he)
  unfold fBlock finiteOrbit
  rw [Finset.card_image_iff.mpr hinj, Finset.card_range]

theorem rClass_R_base (p : Perm6) : rClass (R p) = rClass p := by
  ext q
  simp only [rClass, finiteOrbit, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h : i < 5
    · exact ⟨i + 1, by omega, by rw [Function.iterate_succ_apply]⟩
    · have he : i = 5 := by omega
      subst i
      refine ⟨0, by omega, ?_⟩
      have ho := R_order_six p
      rw [show (6 : Nat) = 5 + 1 from rfl, Function.iterate_succ_apply] at ho
      exact ho.symm
  · rintro ⟨i, hi, rfl⟩
    by_cases h : i = 0
    · subst i
      refine ⟨5, by omega, ?_⟩
      have ho := R_order_six p
      rw [show (6 : Nat) = 5 + 1 from rfl, Function.iterate_succ_apply] at ho
      exact ho
    · refine ⟨i - 1, by omega, ?_⟩
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, show i - 1 + 1 = i by omega]

theorem rClass_iterate_base (p : Perm6) (i : Nat) : rClass ((R^[i]) p) = rClass p := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', rClass_R_base, ih]

theorem rClass_mem_base (p q : Perm6) (h : q ∈ rClass p) : rClass q = rClass p := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
  exact rClass_iterate_base p i

theorem fBlock_F_base (p : Perm6) : fBlock (F p) = fBlock p := by
  ext q
  simp only [fBlock, finiteOrbit, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h : i < 4
    · exact ⟨i + 1, by omega, by rw [Function.iterate_succ_apply]⟩
    · have he : i = 4 := by omega
      subst i
      refine ⟨0, by omega, ?_⟩
      have ho := F_order_five p
      rw [show (5 : Nat) = 4 + 1 from rfl, Function.iterate_succ_apply] at ho
      exact ho.symm
  · rintro ⟨i, hi, rfl⟩
    by_cases h : i = 0
    · subst i
      refine ⟨4, by omega, ?_⟩
      have ho := F_order_five p
      rw [show (5 : Nat) = 4 + 1 from rfl, Function.iterate_succ_apply] at ho
      exact ho
    · refine ⟨i - 1, by omega, ?_⟩
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, show i - 1 + 1 = i by omega]

theorem fBlock_iterate_base (p : Perm6) (i : Nat) : fBlock ((F^[i]) p) = fBlock p := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', fBlock_F_base, ih]

theorem fBlock_mem_base (p q : Perm6) (h : q ∈ fBlock p) : fBlock q = fBlock p := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
  exact fBlock_iterate_base p i

open scoped BigOperators in
private theorem partition_card {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset (Finset α)) (k : Nat)
    (hdis : (s : Set (Finset α)).PairwiseDisjoint id)
    (hcover : s.biUnion id = Finset.univ)
    (hsize : ∀ A ∈ s, A.card = k) : s.card * k = Fintype.card α := by
  have h := Finset.card_biUnion hdis
  rw [hcover, Finset.card_univ] at h
  calc
    s.card * k = ∑ _A ∈ s, k := by simp
    _ = ∑ A ∈ s, (id A).card := by
      apply Finset.sum_congr rfl
      intro A hA
      exact (hsize A hA).symm
    _ = Fintype.card α := h.symm

theorem number_of_rClasses : allRClasses.card = 120 := by
  have hself (p : Perm6) : p ∈ rClass p := Finset.mem_image.mpr ⟨0, by simp, rfl⟩
  have hunion : allRClasses.biUnion id = (Finset.univ : Finset Perm6) := by
    ext p
    simp only [Finset.mem_univ, iff_true, Finset.mem_biUnion]
    exact ⟨rClass p, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩, hself p⟩
  have hdis : (allRClasses : Set (Finset Perm6)).PairwiseDisjoint id := by
    intro A hA B hB hne
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hB
    change Disjoint (rClass p) (rClass q)
    rw [Finset.disjoint_left]
    intro x hxp hxq
    exact hne ((rClass_mem_base p x hxp).symm.trans (rClass_mem_base q x hxq))
  have hc := partition_card allRClasses 6 hdis hunion (by
    intro A hA
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hA
    exact rClass_card p)
  have hn : allRClasses.card * 6 = 720 := hc.trans card_perm6
  omega

theorem number_of_fBlocks : allFBlocks.card = 144 := by
  have hself (p : Perm6) : p ∈ fBlock p := Finset.mem_image.mpr ⟨0, by simp, rfl⟩
  have hunion : allFBlocks.biUnion id = (Finset.univ : Finset Perm6) := by
    ext p
    simp only [Finset.mem_univ, iff_true, Finset.mem_biUnion]
    exact ⟨fBlock p, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩, hself p⟩
  have hdis : (allFBlocks : Set (Finset Perm6)).PairwiseDisjoint id := by
    intro A hA B hB hne
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hB
    change Disjoint (fBlock p) (fBlock q)
    rw [Finset.disjoint_left]
    intro x hxp hxq
    exact hne ((fBlock_mem_base p x hxp).symm.trans (fBlock_mem_base q x hxq))
  have hc := partition_card allFBlocks 5 hdis hunion (by
    intro A hA
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hA
    exact fBlock_card p)
  have hn : allFBlocks.card * 5 = 720 := hc.trans card_perm6
  omega

theorem permWord_getElem? (p : Perm6) (i : ℕ) (hi : i < 6) :
    (permWord p)[i]? = some (p ⟨i, hi⟩) := by
  rw [permWord, List.getElem?_ofFn]
  simp [hi]

/-- Compatibility at shift `k` pins the first `6 - k` values of `q`. -/
theorem agree_of_compatible {p q : Perm6} {k : ℕ} (hk : k < 6)
    (h : OverlapCompatible (permWord p) (permWord q) k)
    (i : Fin 6) (hi : i.val + k < 6) : q i = p ⟨i.val + k, hi⟩ := by
  unfold OverlapCompatible at h
  have := congrArg (fun l => l[i.val]?) h
  simp only [List.getElem?_drop, List.getElem?_take, permWord_length] at this
  rw [if_pos (by omega), permWord_getElem? p (k + i.val) (by omega),
    permWord_getElem? q i.val i.isLt] at this
  simp only [Option.some.injEq] at this
  rw [← this]
  congr 1; ext; simp; omega

theorem overlapCompatible_perm_unique {p q : Perm6} {j k : ℕ} (hj : j < 6) (hk : k < 6)
    (h1 : OverlapCompatible (permWord p) (permWord q) j)
    (h2 : OverlapCompatible (permWord p) (permWord q) k) : j = k := by
  have a := agree_of_compatible hj h1 ⟨0, by omega⟩ (by simp; omega)
  have b := agree_of_compatible hk h2 ⟨0, by omega⟩ (by simp; omega)
  rw [a] at b
  have := congrArg Fin.val (p.injective b)
  simpa using this

theorem d_eq_iff_compatible {p q : Perm6} {k : ℕ} (hk : k < 6) :
    d p q = k ↔ OverlapCompatible (permWord p) (permWord q) k := by
  constructor
  · intro h
    have := overlapCost_spec (permWord p) (permWord q)
    unfold d at h
    rwa [h] at this
  · intro h
    have hle : d p q ≤ k := overlapCost_le_of_compatible h
    have hspec := overlapCost_spec (permWord p) (permWord q)
    exact overlapCompatible_perm_unique (lt_of_le_of_lt hle hk) hk hspec h

/-- Two permutations of `Fin 6` that agree on the first five positions are equal. -/
theorem perm_eq_of_agree_five {q q' : Perm6} (h : ∀ i : Fin 6, i.val < 5 → q i = q' i) :
    q = q' := by
  apply Equiv.ext
  intro i
  by_cases hi : i.val < 5
  · exact h i hi
  · obtain ⟨j, hj⟩ := q'.surjective (q i)
    by_cases hj5 : j.val < 5
    · have e := h j hj5
      rw [hj] at e
      have := congrArg Fin.val (q.injective e.symm)
      omega
    · have : j = i := Fin.ext (by omega)
      rw [this] at hj; exact hj.symm

/-- Positions swap `4 ↔ 5`. -/
def swapLastTwo : Equiv.Perm Symbol := Equiv.swap ⟨4, by omega⟩ ⟨5, by omega⟩

theorem perm_eq_or_swap_of_agree_four {q q' : Perm6}
    (h : ∀ i : Fin 6, i.val < 4 → q i = q' i) :
    q = q' ∨ q = swapLastTwo.trans q' := by
  by_cases h4 : q ⟨4, by omega⟩ = q' ⟨4, by omega⟩
  · left
    apply perm_eq_of_agree_five
    intro i hi
    by_cases hi4 : i.val < 4
    · exact h i hi4
    · have : i = ⟨4, by omega⟩ := Fin.ext (by simp; omega)
      rw [this]; exact h4
  · right
    obtain ⟨j, hj⟩ := q'.surjective (q ⟨4, by omega⟩)
    have hj5 : j.val = 5 := by
      by_contra hne
      by_cases hj4 : j.val < 4
      · have e := h j hj4
        rw [hj] at e
        have := congrArg Fin.val (q.injective e.symm); simp at this; omega
      · have : j = ⟨4, by omega⟩ := Fin.ext (by simp; omega)
        rw [this] at hj; exact h4 hj.symm
    apply perm_eq_of_agree_five
    intro i hi
    simp only [Equiv.trans_apply, swapLastTwo]
    by_cases hi4 : i.val < 4
    · rw [Equiv.swap_apply_of_ne_of_ne]
      · exact h i hi4
      · intro he; have := congrArg Fin.val he; simp at this; omega
      · intro he; have := congrArg Fin.val he; simp at this; omega
    · have hi' : i = ⟨4, by omega⟩ := Fin.ext (by simp; omega)
      have hj' : j = ⟨5, by omega⟩ := Fin.ext hj5
      rw [hi', Equiv.swap_apply_left, ← hj', hj]

theorem permWord_R_compat (p : Perm6) :
    OverlapCompatible (permWord p) (permWord (R p)) 1 := rfl

theorem permWord_RR_compat (p : Perm6) :
    OverlapCompatible (permWord p) (permWord (R (R p))) 2 := rfl

theorem permWord_N₂_compat (p : Perm6) :
    OverlapCompatible (permWord p) (permWord (N₂ p)) 2 := rfl

theorem N₂_eq_swap_RR (p : Perm6) : N₂ p = swapLastTwo.trans (R (R p)) := by
  apply Equiv.ext; intro i; fin_cases i <;> rfl

theorem cost_one_successor : ∀ p q : Perm6, d p q = 1 ↔ q = R p := by
  intro p q
  rw [d_eq_iff_compatible (by omega)]
  constructor
  · intro h
    apply perm_eq_of_agree_five
    intro i hi
    rw [agree_of_compatible (by omega) h i (by omega),
      agree_of_compatible (by omega) (permWord_R_compat p) i (by omega)]
  · rintro rfl; exact permWord_R_compat p

theorem cost_two_successors : ∀ p q : Perm6,
    d p q = 2 ↔ q = R (R p) ∨ q = N₂ p := by
  intro p q
  rw [d_eq_iff_compatible (by omega)]
  constructor
  · intro h
    have : ∀ i : Fin 6, i.val < 4 → q i = (R (R p)) i := by
      intro i hi
      rw [agree_of_compatible (by omega) h i (by omega),
        agree_of_compatible (by omega) (permWord_RR_compat p) i (by omega)]
    rcases perm_eq_or_swap_of_agree_four this with h | h
    · exact Or.inl h
    · right; rw [N₂_eq_swap_RR]; exact h
  · rintro (rfl | rfl)
    · exact permWord_RR_compat p
    · exact permWord_N₂_compat p

/-! ### Relabelling: the overlap cost does not change when the same permutation is applied to both words -/

theorem permWord_mul (σ p : Perm6) : permWord (σ * p) = (permWord p).map σ := by
  unfold permWord; rw [List.map_ofFn]; rfl

theorem overlapCompatible_map_iff {f : Symbol → Symbol} (hf : Function.Injective f)
    (x y : Word) (k : ℕ) :
    OverlapCompatible (x.map f) (y.map f) k ↔ OverlapCompatible x y k := by
  unfold OverlapCompatible
  rw [List.length_map, ← List.map_drop, ← List.map_take]
  exact (List.map_injective_iff.mpr hf).eq_iff

theorem overlapCost_map {f : Symbol → Symbol} (hf : Function.Injective f) (x y : Word) :
    overlapCost (x.map f) (y.map f) = overlapCost x y := by
  apply le_antisymm
  · exact overlapCost_le_of_compatible
      ((overlapCompatible_map_iff hf x y _).mpr (overlapCost_spec x y))
  · exact overlapCost_le_of_compatible
      ((overlapCompatible_map_iff hf x y _).mp (overlapCost_spec _ _))

theorem d_mul_left (σ p q : Perm6) : d (σ * p) (σ * q) = d p q := by
  unfold d; rw [permWord_mul, permWord_mul]; exact overlapCost_map σ.injective _ _

/-- The kernel evaluates this one over the 720 permutations. -/
theorem cost_three_outdegree_one :
    ((Finset.univ : Finset Perm6).filter fun q => d 1 q = 3).card = 6 := by
  decide +kernel

theorem cost_three_outdegree (p : Perm6) :
    ((Finset.univ : Finset Perm6).filter fun q => d p q = 3).card = 6 := by
  refine Eq.trans ?_ cost_three_outdegree_one
  apply Finset.card_bij (fun q _ => p⁻¹ * q)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [← d_mul_left p⁻¹ p q] at hq
    simpa using hq
  · intro a _ b _ h
    exact mul_left_cancel h
  · intro r hr
    refine ⟨p * r, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    rw [← d_mul_left p 1 r] at hr
    simpa using hr

/-! ### Relabelling of the maps and orbits -/

theorem R_mul (σ p : Perm6) : R (σ * p) = σ * R p := by
  apply Equiv.ext; intro i; rfl

theorem F_mul (σ p : Perm6) : F (σ * p) = σ * F p := by
  apply Equiv.ext; intro i; rfl

theorem R_iterate_mul (σ p : Perm6) (i : ℕ) : (R^[i]) (σ * p) = σ * (R^[i]) p := by
  induction i generalizing p with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, R_mul, ih]

theorem F_iterate_mul (σ p : Perm6) (i : ℕ) : (F^[i]) (σ * p) = σ * (F^[i]) p := by
  induction i generalizing p with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, F_mul, ih]

theorem rClass_mul (σ p : Perm6) : rClass (σ * p) = (rClass p).image (σ * ·) := by
  unfold rClass finiteOrbit
  rw [Finset.image_image]
  congr 1
  funext i
  simp [Function.comp, R_iterate_mul]

theorem fBlock_mul (σ p : Perm6) : fBlock (σ * p) = (fBlock p).image (σ * ·) := by
  unfold fBlock finiteOrbit
  rw [Finset.image_image]
  congr 1
  funext i
  simp [Function.comp, F_iterate_mul]

/-- A statement about pairs that is unchanged by relabelling holds for all pairs once it holds for the pairs
whose first member is the identity: `p, q` is the relabelling by `p` of `1, p⁻¹ * q`. -/
theorem forall_pair_of_one {P : Perm6 → Perm6 → Prop}
    (hinv : ∀ σ p q, P p q → P (σ * p) (σ * q)) (h : ∀ q, P 1 q) : ∀ p q, P p q := by
  intro p q
  have := hinv p 1 (p⁻¹ * q) (h _)
  simpa using this

end Superperm6
