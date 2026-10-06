/-
Codes of permutations as natural numbers, for a search that the Lean kernel can evaluate.
New file (not in williamechols/superperm8-ge-46130).  Apache-2.0, as the project.
-/
import Superperm8.Coarsen
import Superperm8.KSearch

/-!
# Permutations of eight symbols as octal numbers

`code p` reads the word of `p` as eight octal digits, first symbol first.  The kernel computes with
natural numbers quickly, so the search of `KSearch.lean` works on codes; the arithmetic it uses
(`rotF`, `cidx`, `bidx`, `sixCodes`, …) is defined there.  This file proves what the search needs
to know about it:

* `code_F`, `code_R`: the maps `F` and `R` are digit rotations (`rotF`, `rotR`);
* `walk_perm`: a test `f : Nat → Bool` that the walk `walk f 8 [0, …, 7] 0` accepts holds for the
  code of every permutation (the walk visits all 40,320 codes);
* `cidx`, `bidx`: numbers below `2 ^ 16` computed from a code, with
  `rClass_eq_of_cidx_eq` and `fBlock_eq_of_bidx_eq`: equal numbers mean the same rotation class,
  respectively the same insertion block;
* `code_mem_sixCodes`: the start of a row that follows a row is one of six codes computed from
  the code of the last state of that row.

The definitions that the kernel evaluates are written with `Nat.add`, `Nat.land` and so on,
without notation, to save unfolding steps; lemmas here restate them with notation.
-/

namespace Superperm8
namespace K

/-- The word of `p` as an octal number, first symbol first. -/
def code (p : Perm8) : Nat :=
  (((((((p 0).val * 8 + (p 1).val) * 8 + (p 2).val) * 8 + (p 3).val) * 8 + (p 4).val) * 8
    + (p 5).val) * 8 + (p 6).val) * 8 + (p 7).val

theorem rotF_eq (c : Nat) : rotF c = (c / 8 % 262144 * 8 + c / 2097152) * 8 + c % 8 := rfl
theorem rotR_eq (c : Nat) : rotR c = c % 2097152 * 8 + c / 2097152 := rfl

theorem code_F (p : Perm8) : code (F p) = rotF (code p) := by
  show (((((((p 1).val * 8 + (p 2).val) * 8 + (p 3).val) * 8 + (p 4).val) * 8 + (p 5).val) * 8
    + (p 6).val) * 8 + (p 0).val) * 8 + (p 7).val = rotF (code p)
  rw [rotF_eq]
  unfold code
  omega

theorem code_R (p : Perm8) : code (R p) = rotR (code p) := by
  show (((((((p 1).val * 8 + (p 2).val) * 8 + (p 3).val) * 8 + (p 4).val) * 8 + (p 5).val) * 8
    + (p 6).val) * 8 + (p 7).val) * 8 + (p 0).val = rotR (code p)
  rw [rotR_eq]
  unfold code
  omega

theorem code_F_iterate (p : Perm8) : ∀ i : Nat, code ((F^[i]) p) = (rotF^[i]) (code p)
  | 0 => rfl
  | i + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', code_F, code_F_iterate p i]

theorem code_R_iterate (p : Perm8) : ∀ i : Nat, code ((R^[i]) p) = (rotR^[i]) (code p)
  | 0 => rfl
  | i + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', code_R, code_R_iterate p i]

/-! ### Digits of a code -/

theorem code_lt (p : Perm8) : code p < 16777216 := by unfold code; omega

theorem code_d0 (p : Perm8) : code p / 2097152 = (p 0).val := by unfold code; omega

theorem code_d7 (p : Perm8) : code p % 8 = (p 7).val := by unfold code; omega

theorem code_div8 (p : Perm8) : code p / 8 =
    (((((((p 0).val * 8 + (p 1).val) * 8 + (p 2).val) * 8 + (p 3).val) * 8 + (p 4).val) * 8
      + (p 5).val) * 8 + (p 6).val) := by unfold code; omega

theorem code_div64 (p : Perm8) : code p / 64 =
    ((((((p 0).val * 8 + (p 1).val) * 8 + (p 2).val) * 8 + (p 3).val) * 8 + (p 4).val) * 8
      + (p 5).val) := by unfold code; omega

theorem code_div512 (p : Perm8) : code p / 512 =
    (((((p 0).val * 8 + (p 1).val) * 8 + (p 2).val) * 8 + (p 3).val) * 8 + (p 4).val) := by
  unfold code; omega

theorem code_div262144 (p : Perm8) : code p / 262144 = (p 0).val * 8 + (p 1).val := by
  unfold code; omega

theorem code_d6 (p : Perm8) : code p / 8 % 8 = (p 6).val := by rw [code_div8]; omega

theorem code_d5 (p : Perm8) : code p / 64 % 8 = (p 5).val := by rw [code_div64]; omega

theorem code_d1 (p : Perm8) : code p / 262144 % 8 = (p 1).val := by rw [code_div262144]; omega

theorem code_mid15 (p : Perm8) : code p / 64 % 32768 =
    ((((p 1).val * 8 + (p 2).val) * 8 + (p 3).val) * 8 + (p 4).val) * 8 + (p 5).val := by
  rw [code_div64]; omega

theorem code_mid14 (p : Perm8) : code p / 512 % 4096 =
    (((p 1).val * 8 + (p 2).val) * 8 + (p 3).val) * 8 + (p 4).val := by
  rw [code_div512]; omega

theorem code_mid26 (p : Perm8) : code p / 8 % 32768 =
    ((((p 2).val * 8 + (p 3).val) * 8 + (p 4).val) * 8 + (p 5).val) * 8 + (p 6).val := by
  rw [code_div8]; omega

theorem digits4_inj {a1 a2 a3 a4 b1 b2 b3 b4 : Nat} (ha2 : a2 < 8) (ha3 : a3 < 8)
    (ha4 : a4 < 8) (hb2 : b2 < 8) (hb3 : b3 < 8) (hb4 : b4 < 8)
    (h : ((a1 * 8 + a2) * 8 + a3) * 8 + a4 = ((b1 * 8 + b2) * 8 + b3) * 8 + b4) :
    a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem digits5_inj {a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 : Nat} (ha2 : a2 < 8)
    (ha3 : a3 < 8) (ha4 : a4 < 8) (ha5 : a5 < 8) (hb2 : b2 < 8) (hb3 : b3 < 8)
    (hb4 : b4 < 8) (hb5 : b5 < 8)
    (h : (((a1 * 8 + a2) * 8 + a3) * 8 + a4) * 8 + a5 =
      (((b1 * 8 + b2) * 8 + b3) * 8 + b4) * 8 + b5) :
    a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-! ### Rotations by several digits -/

/-- Rotation of the eight digits to the left by `k` digits, where `P = 8 ^ k`, `Q = 8 ^ (8 - k)`. -/
def rotL (P Q c : Nat) : Nat := c % Q * P + c / Q

theorem rotR_iter (c : Nat) (hc : c < 16777216) :
    (rotR^[1]) c = rotL 8 2097152 c ∧ (rotR^[2]) c = rotL 64 262144 c ∧
    (rotR^[3]) c = rotL 512 32768 c ∧ (rotR^[4]) c = rotL 4096 4096 c ∧
    (rotR^[5]) c = rotL 32768 512 c ∧ (rotR^[6]) c = rotL 262144 64 c ∧
    (rotR^[7]) c = rotL 2097152 8 c := by
  have s1 : (rotR^[1]) c = rotL 8 2097152 c := rfl
  have s2 : (rotR^[2]) c = rotL 64 262144 c := by
    rw [Function.iterate_succ_apply', s1, rotR_eq]; unfold rotL; omega
  have s3 : (rotR^[3]) c = rotL 512 32768 c := by
    rw [Function.iterate_succ_apply', s2, rotR_eq]; unfold rotL; omega
  have s4 : (rotR^[4]) c = rotL 4096 4096 c := by
    rw [Function.iterate_succ_apply', s3, rotR_eq]; unfold rotL; omega
  have s5 : (rotR^[5]) c = rotL 32768 512 c := by
    rw [Function.iterate_succ_apply', s4, rotR_eq]; unfold rotL; omega
  have s6 : (rotR^[6]) c = rotL 262144 64 c := by
    rw [Function.iterate_succ_apply', s5, rotR_eq]; unfold rotL; omega
  have s7 : (rotR^[7]) c = rotL 2097152 8 c := by
    rw [Function.iterate_succ_apply', s6, rotR_eq]; unfold rotL; omega
  exact ⟨s1, s2, s3, s4, s5, s6, s7⟩

/-- Rotation of seven digits to the left by `k` digits, where `P = 8 ^ k`, `Q = 8 ^ (7 - k)`. -/
def rot7 (P Q t : Nat) : Nat := t % Q * P + t / Q

/-- Rotation of the first seven digits; the last digit stays. -/
def rotFL (P Q c : Nat) : Nat := rot7 P Q (c / 8) * 8 + c % 8

theorem rotF_mk (T l : Nat) (hl : l < 8) :
    rotF (T * 8 + l) = (T % 262144 * 8 + T / 262144) * 8 + l := by
  rw [rotF_eq]; omega

theorem rotF_rotFL (P Q P' Q' c : Nat) (hc : c < 16777216)
    (hstep : ∀ t, t < 2097152 →
      rot7 P Q t % 262144 * 8 + rot7 P Q t / 262144 = rot7 P' Q' t) :
    rotF (rotFL P Q c) = rotFL P' Q' c := by
  have ht : c / 8 < 2097152 := by omega
  have hl : c % 8 < 8 := by omega
  unfold rotFL
  rw [rotF_mk _ _ hl, hstep _ ht]

theorem rotF_iter (c : Nat) (hc : c < 16777216) :
    (rotF^[1]) c = rotFL 8 262144 c ∧ (rotF^[2]) c = rotFL 64 32768 c ∧
    (rotF^[3]) c = rotFL 512 4096 c ∧ (rotF^[4]) c = rotFL 4096 512 c ∧
    (rotF^[5]) c = rotFL 32768 64 c ∧ (rotF^[6]) c = rotFL 262144 8 c := by
  have s1 : (rotF^[1]) c = rotFL 8 262144 c := by
    show rotF c = _
    rw [rotF_eq]; unfold rotFL rot7; omega
  have s2 : (rotF^[2]) c = rotFL 64 32768 c := by
    rw [Function.iterate_succ_apply', s1]
    exact rotF_rotFL _ _ _ _ c hc (by intro t ht; unfold rot7; omega)
  have s3 : (rotF^[3]) c = rotFL 512 4096 c := by
    rw [Function.iterate_succ_apply', s2]
    exact rotF_rotFL _ _ _ _ c hc (by intro t ht; unfold rot7; omega)
  have s4 : (rotF^[4]) c = rotFL 4096 512 c := by
    rw [Function.iterate_succ_apply', s3]
    exact rotF_rotFL _ _ _ _ c hc (by intro t ht; unfold rot7; omega)
  have s5 : (rotF^[5]) c = rotFL 32768 64 c := by
    rw [Function.iterate_succ_apply', s4]
    exact rotF_rotFL _ _ _ _ c hc (by intro t ht; unfold rot7; omega)
  have s6 : (rotF^[6]) c = rotFL 262144 8 c := by
    rw [Function.iterate_succ_apply', s5]
    exact rotF_rotFL _ _ _ _ c hc (by intro t ht; unfold rot7; omega)
  exact ⟨s1, s2, s3, s4, s5, s6⟩

/-! ### All permutations by a walk -/

/-- Remove the first occurrence of `a`. -/
def erase1 : List Nat → Nat → List Nat
  | [], _ => []
  | b :: t, a => bif Nat.beq b a then t else b :: erase1 t a

/-- `walk f n rem c`: `f` holds for every code obtained from `c` by appending `n` distinct digits
taken from `rem`. -/
def walk (f : Nat → Bool) : Nat → List Nat → Nat → Bool
  | 0, _, c => f c
  | n + 1, rem, c => rem.all fun a => walk f n (erase1 rem a) (c * 8 + a)

theorem mem_erase1 {l : List Nat} {a b : Nat} (hb : b ∈ l) (hne : b ≠ a) : b ∈ erase1 l a := by
  induction l with
  | nil => cases hb
  | cons x t ih =>
    cases hx : Nat.beq x a with
    | true =>
      have hxa : x = a := Nat.eq_of_beq_eq_true hx
      have he : erase1 (x :: t) a = t := by simp [erase1, hx]
      rw [he]
      rcases List.mem_cons.mp hb with h | h
      · exact absurd (h.trans hxa) hne
      · exact h
    | false =>
      have he : erase1 (x :: t) a = x :: erase1 t a := by simp [erase1, hx]
      rw [he]
      rcases List.mem_cons.mp hb with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

theorem walk_sound (f : Nat → Bool) : ∀ (n : Nat) (rem : List Nat) (c : Nat) (w : List Nat),
    w.length = n → w.Nodup → (∀ a ∈ w, a ∈ rem) → walk f n rem c = true →
    f (w.foldl (fun acc a => acc * 8 + a) c) = true := by
  intro n
  induction n with
  | zero =>
    intro rem c w hlen _ _ h
    cases w with
    | nil => exact h
    | cons a t => simp at hlen
  | succ n ih =>
    intro rem c w hlen hnd hmem h
    cases w with
    | nil => simp at hlen
    | cons a t =>
      have ha : a ∈ rem := hmem a List.mem_cons_self
      have h' : (rem.all fun a => walk f n (erase1 rem a) (c * 8 + a)) = true := h
      have hall := List.all_eq_true.mp h' a ha
      have hnd' := List.nodup_cons.mp hnd
      simp only [List.foldl_cons]
      apply ih (erase1 rem a) (c * 8 + a) t (by simpa using hlen) hnd'.2
      · intro b hb
        refine mem_erase1 (hmem b (List.mem_cons_of_mem _ hb)) ?_
        intro hba
        exact hnd'.1 (hba ▸ hb)
      · exact hall

/-- The walk over all arrangements of eight symbols, in eight parts by the first symbol (so that
the kernel evaluates 5,040 codes at a time). -/
theorem walk8_of_parts (f : Nat → Bool)
    (h0 : walk f 7 [1, 2, 3, 4, 5, 6, 7] 0 = true) (h1 : walk f 7 [0, 2, 3, 4, 5, 6, 7] 1 = true)
    (h2 : walk f 7 [0, 1, 3, 4, 5, 6, 7] 2 = true) (h3 : walk f 7 [0, 1, 2, 4, 5, 6, 7] 3 = true)
    (h4 : walk f 7 [0, 1, 2, 3, 5, 6, 7] 4 = true) (h5 : walk f 7 [0, 1, 2, 3, 4, 6, 7] 5 = true)
    (h6 : walk f 7 [0, 1, 2, 3, 4, 5, 7] 6 = true) (h7 : walk f 7 [0, 1, 2, 3, 4, 5, 6] 7 = true) :
    walk f 8 [0, 1, 2, 3, 4, 5, 6, 7] 0 = true := by
  show ([0, 1, 2, 3, 4, 5, 6, 7].all fun a =>
    walk f 7 (erase1 [0, 1, 2, 3, 4, 5, 6, 7] a) (0 * 8 + a)) = true
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

/-- A test accepted by the walk over all arrangements of eight symbols holds for the code of
every permutation. -/
theorem walk_perm (f : Nat → Bool) (h : walk f 8 [0, 1, 2, 3, 4, 5, 6, 7] 0 = true) (p : Perm8) :
    f (code p) = true := by
  have hinj : Function.Injective (fun i : Fin 8 => (p i).val) :=
    fun i j hij => p.injective (Fin.ext hij)
  have hnd : (List.ofFn fun i : Fin 8 => (p i).val).Nodup := List.nodup_ofFn.mpr hinj
  have hlist : (List.ofFn fun i : Fin 8 => (p i).val) =
      [(p 0).val, (p 1).val, (p 2).val, (p 3).val, (p 4).val, (p 5).val, (p 6).val, (p 7).val] :=
    rfl
  rw [hlist] at hnd
  have hw := walk_sound f 8 [0, 1, 2, 3, 4, 5, 6, 7] 0 _ rfl hnd (by
    intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha ⊢
    omega) h
  have hc : List.foldl (fun acc a => acc * 8 + a) 0
      [(p 0).val, (p 1).val, (p 2).val, (p 3).val, (p 4).val, (p 5).val, (p 6).val, (p 7).val] =
      code p := by
    simp only [List.foldl_cons, List.foldl_nil, code]
    omega
  rw [hc] at hw
  exact hw

/-! ### Two permutations that agree outside two positions -/

theorem perm_eq_of_agree_off_two {a b : Perm8} (i j : Fin 8)
    (h : ∀ k : Fin 8, k ≠ i → k ≠ j → a k = b k)
    (hord : ((a i).val < (a j).val ↔ (b i).val < (b j).val)) : a = b := by
  have key : ∀ t : Fin 8, (t = i ∨ t = j) → (b t = a i ∨ b t = a j) := by
    intro t ht
    by_contra hcon
    have hc1 : a.symm (b t) ≠ i := fun e => hcon (Or.inl ((Equiv.symm_apply_eq a).mp e))
    have hc2 : a.symm (b t) ≠ j := fun e => hcon (Or.inr ((Equiv.symm_apply_eq a).mp e))
    have h1 := h (a.symm (b t)) hc1 hc2
    rw [Equiv.apply_symm_apply] at h1
    have h2 : t = a.symm (b t) := b.injective h1
    rcases ht with ht | ht
    · exact hc1 (h2.symm.trans ht)
    · exact hc2 (h2.symm.trans ht)
  have hij : a i = b i ∧ a j = b j := by
    rcases key i (Or.inl rfl) with h1 | h1 <;> rcases key j (Or.inr rfl) with h2 | h2
    · have e : i = j := b.injective (h1.trans h2.symm)
      subst e
      exact ⟨h1.symm, h1.symm⟩
    · exact ⟨h1.symm, h2.symm⟩
    · have hv1 : (b i).val = (a j).val := congrArg Fin.val h1
      have hv2 : (b j).val = (a i).val := congrArg Fin.val h2
      have hv : (a i).val = (a j).val := by
        by_cases hlt : (a i).val < (a j).val
        · have := hord.mp hlt
          omega
        · have : ¬ (b i).val < (b j).val := fun hh => hlt (hord.mpr hh)
          omega
      have e : i = j := a.injective (Fin.ext hv)
      subst e
      exact ⟨h1.symm, h1.symm⟩
    · have e : i = j := b.injective (h1.trans h2.symm)
      subst e
      exact ⟨h1.symm, h1.symm⟩
  apply Equiv.ext
  intro k
  by_cases hk : k = i
  · rw [hk]; exact hij.1
  · by_cases hk' : k = j
    · rw [hk']; exact hij.2
    · exact h k hk hk'

theorem fin8_cases_67 : ∀ k : Fin 8, k ≠ 6 → k ≠ 7 →
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by decide

theorem fin8_cases_56 : ∀ k : Fin 8, k ≠ 5 → k ≠ 6 →
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 7 := by decide

/-! ### The index of a rotation class -/

/-- `m` is one of `8 ^ 0, …, 8 ^ 7`. -/
def pow8 (m : Nat) : Bool :=
  Nat.beq m 1 || (Nat.beq m 8 || (Nat.beq m 64 || (Nat.beq m 512 || (Nat.beq m 4096 ||
    (Nat.beq m 32768 || (Nat.beq m 262144 || Nat.beq m 2097152))))))

theorem pow8_spec {m : Nat} (h : pow8 m = true) :
    m = 1 ∨ m = 8 ∨ m = 64 ∨ m = 512 ∨ m = 4096 ∨ m = 32768 ∨ m = 262144 ∨ m = 2097152 := by
  unfold pow8 at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h | h | h | h | h | h | h <;>
    (have e := Nat.eq_of_beq_eq_true h; subst e; decide)

theorem ccanonM_eq (c m : Nat) : ccanonM c m = c * (2097152 / m) % 16777216 + c / (8 * m) := rfl

/-- With a mask that is a power of eight, `ccanonM` is a rotation. -/
theorem ccanonM_rot (c m : Nat) (hc : c < 16777216)
    (hm : m = 1 ∨ m = 8 ∨ m = 64 ∨ m = 512 ∨ m = 4096 ∨ m = 32768 ∨ m = 262144 ∨ m = 2097152) :
    ∃ i, ccanonM c m = (rotR^[i]) c := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := rotR_iter c hc
  rw [ccanonM_eq]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨7, by rw [s7]; unfold rotL; omega⟩
  · exact ⟨6, by rw [s6]; unfold rotL; omega⟩
  · exact ⟨5, by rw [s5]; unfold rotL; omega⟩
  · exact ⟨4, by rw [s4]; unfold rotL; omega⟩
  · exact ⟨3, by rw [s3]; unfold rotL; omega⟩
  · exact ⟨2, by rw [s2]; unfold rotL; omega⟩
  · exact ⟨1, by rw [s1]; unfold rotL; omega⟩
  · exact ⟨0, by show _ = c; omega⟩

/-- The test for one code: the mask is a power of eight and `ccanon c` begins with `7`. -/
def cTest (c : Nat) : Bool :=
  pow8 (cmask c) && Nat.beq (Nat.div (ccanon c) 2097152) 7

theorem cTest_all : walk cTest 8 [0, 1, 2, 3, 4, 5, 6, 7] 0 = true :=
  walk8_of_parts cTest (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem ccanon_spec (p : Perm8) :
    ∃ a : Perm8, rClass a = rClass p ∧ ccanon (code p) = code a ∧ (a 0).val = 7 := by
  have h := walk_perm cTest cTest_all p
  have h' : (pow8 (cmask (code p)) && Nat.beq (Nat.div (ccanon (code p)) 2097152) 7) = true := h
  rw [Bool.and_eq_true] at h'
  obtain ⟨i, hi⟩ := ccanonM_rot (code p) (cmask (code p)) (code_lt p) (pow8_spec h'.1)
  have hi' : ccanon (code p) = code ((R^[i]) p) := by rw [code_R_iterate]; exact hi
  refine ⟨(R^[i]) p, rClass_iterate_base p i, hi', ?_⟩
  have h7 : ccanon (code p) / 2097152 = 7 := Nat.eq_of_beq_eq_true h'.2
  rw [hi', code_d0] at h7
  exact h7

theorem cidxV_eq (v : Nat) :
    cidxV v = v / 64 % 32768 * 2 + (if v / 8 % 8 < v % 8 then 1 else 0) := by
  show v / 64 % 32768 * 2 + (bif Nat.blt (v / 8 % 8) (v % 8) then 1 else 0) = _
  by_cases h : v / 8 % 8 < v % 8
  · have hb : Nat.blt (v / 8 % 8) (v % 8) = true := by simpa [Nat.blt_eq] using h
    rw [hb, if_pos h, cond_true]
  · have hb : Nat.blt (v / 8 % 8) (v % 8) = false := by
      rw [← Bool.not_eq_true]; simpa [Nat.blt_eq] using h
    rw [hb, if_neg h, cond_false]

/-- Equal class indices: the same rotation class. -/
theorem rClass_eq_of_cidx_eq {p q : Perm8} (h : cidx (code p) = cidx (code q)) :
    rClass p = rClass q := by
  obtain ⟨a, ha, hca, ha0⟩ := ccanon_spec p
  obtain ⟨b, hb, hcb, hb0⟩ := ccanon_spec q
  have h' : cidxV (code a) = cidxV (code b) := by
    rw [← hca, ← hcb]; exact h
  rw [cidxV_eq, cidxV_eq, code_mid15, code_mid15, code_d6, code_d6, code_d7, code_d7] at h'
  have hmid : ((((a 1).val * 8 + (a 2).val) * 8 + (a 3).val) * 8 + (a 4).val) * 8 + (a 5).val =
        ((((b 1).val * 8 + (b 2).val) * 8 + (b 3).val) * 8 + (b 4).val) * 8 + (b 5).val ∧
      ((a 6).val < (a 7).val ↔ (b 6).val < (b 7).val) := by
    by_cases h1 : (a 6).val < (a 7).val <;> by_cases h2 : (b 6).val < (b 7).val <;>
      simp only [h1, h2, if_true, if_false] at h'
    · exact ⟨by omega, iff_of_true h1 h2⟩
    · exfalso; omega
    · exfalso; omega
    · exact ⟨by omega, iff_of_false h1 h2⟩
  have hab : a = b := by
    obtain ⟨e1, e2, e3, e4, e5⟩ := digits5_inj (a 2).isLt (a 3).isLt (a 4).isLt
      (a 5).isLt (b 2).isLt (b 3).isLt (b 4).isLt (b 5).isLt hmid.1
    have e0 : (a 0).val = (b 0).val := by rw [ha0, hb0]
    apply perm_eq_of_agree_off_two 6 7 _ hmid.2
    intro k hk6 hk7
    apply Fin.ext
    rcases fin8_cases_67 k hk6 hk7 with rfl | rfl | rfl | rfl | rfl | rfl
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
  rw [← ha, ← hb, hab]

/-! ### The index of an insertion block -/

/-- `m` is one of `8 ^ 0, …, 8 ^ 6`. -/
def pow8b (m : Nat) : Bool :=
  Nat.beq m 1 || (Nat.beq m 8 || (Nat.beq m 64 || (Nat.beq m 512 || (Nat.beq m 4096 ||
    (Nat.beq m 32768 || Nat.beq m 262144)))))

theorem pow8b_spec {m : Nat} (h : pow8b m = true) :
    m = 1 ∨ m = 8 ∨ m = 64 ∨ m = 512 ∨ m = 4096 ∨ m = 32768 ∨ m = 262144 := by
  unfold pow8b at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h | h | h | h | h | h <;>
    (have e := Nat.eq_of_beq_eq_true h; subst e; decide)

theorem bcanonM_eq (c m : Nat) :
    bcanonM (c / 8) (c % 8) m = (c / 8 * (262144 / m) % 2097152 + c / 8 / (8 * m)) * 8 + c % 8 :=
  rfl

/-- With a mask that is a power of eight, `bcanonM` is an `F`-rotation. -/
theorem bcanonM_rot (c m : Nat) (hc : c < 16777216)
    (hm : m = 1 ∨ m = 8 ∨ m = 64 ∨ m = 512 ∨ m = 4096 ∨ m = 32768 ∨ m = 262144) :
    ∃ i, bcanonM (c / 8) (c % 8) m = (rotF^[i]) c := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := rotF_iter c hc
  have ht : c / 8 < 2097152 := by omega
  have hc8 : c / 8 * 8 + c % 8 = c := by omega
  rw [bcanonM_eq]
  have key : ∀ (P Q m' : Nat), (∀ t, t < 2097152 →
      t * (262144 / m') % 2097152 + t / (8 * m') = rot7 P Q t) →
      (c / 8 * (262144 / m') % 2097152 + c / 8 / (8 * m')) * 8 + c % 8 = rotFL P Q c := by
    intro P Q m' h
    unfold rotFL
    rw [h _ ht]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨6, by rw [s6]; exact key _ _ _ (by intro t ht; unfold rot7; omega)⟩
  · exact ⟨5, by rw [s5]; exact key _ _ _ (by intro t ht; unfold rot7; omega)⟩
  · exact ⟨4, by rw [s4]; exact key _ _ _ (by intro t ht; unfold rot7; omega)⟩
  · exact ⟨3, by rw [s3]; exact key _ _ _ (by intro t ht; unfold rot7; omega)⟩
  · exact ⟨2, by rw [s2]; exact key _ _ _ (by intro t ht; unfold rot7; omega)⟩
  · exact ⟨1, by rw [s1]; exact key _ _ _ (by intro t ht; unfold rot7; omega)⟩
  · exact ⟨0, by show _ = c; omega⟩

/-- The test for one code: the mask is a power of eight and `bcanon c` begins with `btarget`. -/
def bTest (c : Nat) : Bool :=
  pow8b (bm c) && Nat.beq (Nat.div (bcanon c) 2097152) (btarget (Nat.mod c 8))

theorem bTest_all : walk bTest 8 [0, 1, 2, 3, 4, 5, 6, 7] 0 = true :=
  walk8_of_parts bTest (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem btarget_eq (l : Nat) : btarget l = if l = 7 then 6 else 7 := by
  unfold btarget
  by_cases h : l = 7
  · subst h; rfl
  · have hb : Nat.beq l 7 = false := by
      rw [← Bool.not_eq_true]; exact fun e => h (Nat.eq_of_beq_eq_true e)
    rw [hb, if_neg h, cond_false]

theorem bcanon_spec (p : Perm8) :
    ∃ a : Perm8, fBlock a = fBlock p ∧ bcanon (code p) = code a ∧ a 7 = p 7 ∧
      (a 0).val = btarget (p 7).val := by
  have h := walk_perm bTest bTest_all p
  have h' : (pow8b (bm (code p)) &&
      Nat.beq (Nat.div (bcanon (code p)) 2097152) (btarget (Nat.mod (code p) 8))) = true := h
  rw [Bool.and_eq_true] at h'
  obtain ⟨i, hi⟩ := bcanonM_rot (code p) (bm (code p)) (code_lt p) (pow8b_spec h'.1)
  have hi' : bcanon (code p) = code ((F^[i]) p) := by rw [code_F_iterate]; exact hi
  have h7 : ∀ i : Nat, ((F^[i]) p) 7 = p 7 := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply']; exact ih
  refine ⟨(F^[i]) p, fBlock_iterate_base p i, hi', h7 i, ?_⟩
  have ht : bcanon (code p) / 2097152 = btarget (code p % 8) := Nat.eq_of_beq_eq_true h'.2
  rw [hi', code_d0, code_d7] at ht
  exact ht

theorem bidxV_eq (v : Nat) :
    bidxV v = v / 512 % 4096 * 16 + (if v / 64 % 8 < v / 8 % 8 then 8 else 0) + v % 8 := by
  show v / 512 % 4096 * 16 + (bif Nat.blt (v / 64 % 8) (v / 8 % 8) then 8 else 0) + v % 8 = _
  by_cases h : v / 64 % 8 < v / 8 % 8
  · have hb : Nat.blt (v / 64 % 8) (v / 8 % 8) = true := by simpa [Nat.blt_eq] using h
    rw [hb, if_pos h, cond_true]
  · have hb : Nat.blt (v / 64 % 8) (v / 8 % 8) = false := by
      rw [← Bool.not_eq_true]; simpa [Nat.blt_eq] using h
    rw [hb, if_neg h, cond_false]

/-- Equal block indices: the same insertion block. -/
theorem fBlock_eq_of_bidx_eq {p q : Perm8} (h : bidx (code p) = bidx (code q)) :
    fBlock p = fBlock q := by
  obtain ⟨a, ha, hca, ha7, ha0⟩ := bcanon_spec p
  obtain ⟨b, hb, hcb, hb7, hb0⟩ := bcanon_spec q
  have h' : bidxV (code a) = bidxV (code b) := by
    rw [← hca, ← hcb]; exact h
  rw [bidxV_eq, bidxV_eq, code_mid14, code_mid14, code_d5, code_d5, code_d6, code_d6, code_d7,
    code_d7] at h'
  have hmid : (((a 1).val * 8 + (a 2).val) * 8 + (a 3).val) * 8 + (a 4).val =
        (((b 1).val * 8 + (b 2).val) * 8 + (b 3).val) * 8 + (b 4).val ∧ (a 7).val = (b 7).val ∧
      ((a 5).val < (a 6).val ↔ (b 5).val < (b 6).val) := by
    have la := (a 7).isLt
    have lb := (b 7).isLt
    by_cases h1 : (a 5).val < (a 6).val <;> by_cases h2 : (b 5).val < (b 6).val <;>
      simp only [h1, h2, if_true, if_false] at h'
    · exact ⟨by omega, by omega, iff_of_true h1 h2⟩
    · exfalso; omega
    · exfalso; omega
    · exact ⟨by omega, by omega, iff_of_false h1 h2⟩
  have hab : a = b := by
    obtain ⟨e1, e2, e3, e4⟩ := digits4_inj (a 2).isLt (a 3).isLt (a 4).isLt
      (b 2).isLt (b 3).isLt (b 4).isLt hmid.1
    have e7 := hmid.2.1
    have e0 : (a 0).val = (b 0).val := by
      rw [ha0, hb0, ← ha7, ← hb7, e7]
    apply perm_eq_of_agree_off_two 5 6 _ hmid.2.2
    intro k hk5 hk6
    apply Fin.ext
    rcases fin8_cases_56 k hk5 hk6 with rfl | rfl | rfl | rfl | rfl | rfl
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e7
  rw [← ha, ← hb, hab]

/-! ### The six starts after a row -/

theorem sixCodes_eq (c : Nat) :
    sixCodes c = six (c / 8 % 32768 * 512) (c / 2097152) (c / 262144 % 8) (c % 8) := rfl

theorem mem_six {v base x y z : Nat}
    (h : v = base + (x * 64 + y * 8 + z) ∨ v = base + (x * 64 + z * 8 + y) ∨
      v = base + (y * 64 + x * 8 + z) ∨ v = base + (y * 64 + z * 8 + x) ∨
      v = base + (z * 64 + x * 8 + y) ∨ v = base + (z * 64 + y * 8 + x)) :
    v ∈ six base x y z := by
  show v ∈ [base + (x * 64 + y * 8 + z), base + (x * 64 + z * 8 + y),
    base + (y * 64 + x * 8 + z), base + (y * 64 + z * 8 + x),
    base + (z * 64 + x * 8 + y), base + (z * 64 + y * 8 + x)]
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  exact h

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem not_mid : ∀ a : Fin 8, a ≠ 2 → a ≠ 3 → a ≠ 4 → a ≠ 5 → a ≠ 6 → a = 0 ∨ a = 1 ∨ a = 7 := by
  decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem three_left : ∀ a b c : Fin 8, (a = 0 ∨ a = 1 ∨ a = 7) → (b = 0 ∨ b = 1 ∨ b = 7) →
    (c = 0 ∨ c = 1 ∨ c = 7) → a ≠ b → a ≠ c → b ≠ c →
    (a = 0 ∧ b = 1 ∧ c = 7) ∨ (a = 0 ∧ b = 7 ∧ c = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 7) ∨
    (a = 1 ∧ b = 7 ∧ c = 0) ∨ (a = 7 ∧ b = 0 ∧ c = 1) ∨ (a = 7 ∧ b = 1 ∧ c = 0) := by
  decide

theorem rowCompatible_iff (x y : Row) :
    RowCompatible x y ↔
      [x.lastState 2, x.lastState 3, x.lastState 4, x.lastState 5, x.lastState 6] =
        [y.start 0, y.start 1, y.start 2, y.start 3, y.start 4] := Iff.rfl

/-- The start of a row that follows `x` is one of the six codes computed from the last state
of `x`. -/
theorem code_mem_sixCodes {x y : Row} (h : RowCompatible x y) :
    code y.start ∈ sixCodes (code x.lastState) := by
  rw [rowCompatible_iff] at h
  generalize x.lastState = u at h ⊢
  generalize y.start = q at h ⊢
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have hu : ∀ t : Fin 8, u (u.symm (q t)) = q t := fun t => Equiv.apply_symm_apply u (q t)
  have ne : ∀ (t k s : Fin 8), u k = q s → s ≠ t → u.symm (q t) ≠ k := by
    intro t k s hks hst e
    have : q t = q s := by rw [← hu t, e, hks]
    exact hst (q.injective this).symm
  have dist : ∀ (t s : Fin 8), s ≠ t → u.symm (q t) ≠ u.symm (q s) := by
    intro t s hst e
    exact hst (q.injective (u.symm.injective e)).symm
  have hcase := three_left (u.symm (q 5)) (u.symm (q 6)) (u.symm (q 7))
    (not_mid _ (ne 5 2 0 h0 (by decide)) (ne 5 3 1 h1 (by decide)) (ne 5 4 2 h2 (by decide))
      (ne 5 5 3 h3 (by decide)) (ne 5 6 4 h4 (by decide)))
    (not_mid _ (ne 6 2 0 h0 (by decide)) (ne 6 3 1 h1 (by decide)) (ne 6 4 2 h2 (by decide))
      (ne 6 5 3 h3 (by decide)) (ne 6 6 4 h4 (by decide)))
    (not_mid _ (ne 7 2 0 h0 (by decide)) (ne 7 3 1 h1 (by decide)) (ne 7 4 2 h2 (by decide))
      (ne 7 5 3 h3 (by decide)) (ne 7 6 4 h4 (by decide)))
    (dist 5 6 (by decide)) (dist 5 7 (by decide)) (dist 6 7 (by decide))
  have e0 : (q 0).val = (u 2).val := by rw [h0]
  have e1 : (q 1).val = (u 3).val := by rw [h1]
  have e2 : (q 2).val = (u 4).val := by rw [h2]
  have e3 : (q 3).val = (u 5).val := by rw [h3]
  have e4 : (q 4).val = (u 6).val := by rw [h4]
  have val : ∀ (t k : Fin 8), u.symm (q t) = k → (q t).val = (u k).val := by
    intro t k e
    rw [← e, hu t]
  rw [sixCodes_eq, code_mid26, code_d0, code_d1, code_d7]
  apply mem_six
  unfold code
  rw [e0, e1, e2, e3, e4]
  rcases hcase with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · rw [val 5 _ a, val 6 _ b, val 7 _ c]
    exact Or.inl (by omega)
  · rw [val 5 _ a, val 6 _ b, val 7 _ c]
    exact Or.inr (Or.inl (by omega))
  · rw [val 5 _ a, val 6 _ b, val 7 _ c]
    exact Or.inr (Or.inr (Or.inl (by omega)))
  · rw [val 5 _ a, val 6 _ b, val 7 _ c]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · rw [val 5 _ a, val 6 _ b, val 7 _ c]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
  · rw [val 5 _ a, val 6 _ b, val 7 _ c]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))

end K
end Superperm8
