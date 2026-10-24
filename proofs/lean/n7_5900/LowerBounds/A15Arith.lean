import LowerBounds.PTables
import LowerBounds.KTables
import LowerBounds.A15Tables

/-!
# The arithmetic of the accounting at defect 15 (the written proof, sections 3.3 and 3.7)

Everything here is about tables and numbers; no rows, no words, no Mathlib.  The closed statements
are Boolean functions evaluated by the kernel (`decide +kernel`); there is no `native_decide`.

Values and weights are those of the pieces of the written proof, section 5.1: a sequence with `t`
links and `x` holes has weight `y = x + 6 t` and value at most `Dv t y = D_t(x) - x - 5 t`; a ring
with `y` holes has value at most `Rv y = TR'(y) - y`.  `SH lo W` is the largest `Dv t y` over
`lo ≤ t ≤ 8` and `y ≤ W`, `RH W` the largest `Rv y` over `y ≤ W` (`Dv_le_SH`, `Rv_le_RH`).

The finite statement KN of the written proof (which profiles survive) is used in this form: a
kernel piece together with the pieces of the hanging items, with the shifts of Lemma PIECE,

* cannot have three or more hanging items (`cHn`, `cK3`), nor none (`cK`);
* with one ring has at most 5 links (`c1R`); with one sequence, both have at most 4 links (`c1S`);
* with two rings has at most 2 links (`cRR`); with a ring and a sequence that borrows no class,
  both sequences have at most 1 link (`cRE`); with a ring and a sequence that borrows a class, both
  sequences have no link (`cRAB`); with two sequences it does not exist (`cSSS`).

`M_lin` is the arithmetic of Lemma NCH for the excess 0.
-/

namespace SuperpermLowerBounds
namespace A15

open T5900

/-- Entry of table D. -/
def Dc (t x : Nat) : Nat := (Dtab.getD t []).getD x 0

/-- The largest value of a sequence with `t` links and weight `y`, from table D. -/
def Dv (t y : Nat) : Nat := if 6 * t ≤ y then Dc t (y - 6 * t) - (y - 6 * t) - 5 * t else 0

/-- Entry of the ring row of table T'. -/
def Rc (y : Nat) : Nat := TRtab.getD y 0

/-- The largest value of a ring with `y` holes. -/
def Rv (y : Nat) : Nat := Rc y - y

def SH (lo W : Nat) : Nat := (SHtab.getD lo []).getD W 0

def RH (W : Nat) : Nat := RHtab.getD W 0

def HV (W : Nat) : Nat := HVtab.getD W 0

def Hn (n W : Nat) : Nat := (Hntab.getD n []).getD W 0

/-- `p a` for all `a < n`. -/
def allLt (n : Nat) (p : Nat → Bool) : Bool := (List.range n).all p

theorem allLt_spec {n : Nat} {p : Nat → Bool} (h : allLt n p = true) (a : Nat) (ha : a < n) :
    p a = true := by
  unfold allLt at h
  rw [List.all_eq_true] at h
  exact h a (List.mem_range.mpr ha)

theorem mono_of_step (f : Nat → Nat) (N : Nat) (h : ∀ a, a < N → f a ≤ f (a + 1)) :
    ∀ b, b ≤ N → ∀ a, a ≤ b → f a ≤ f b := by
  intro b
  induction b with
  | zero =>
    intro _ a ha
    have h0 : a = 0 := by omega
    subst h0
    exact Nat.le_refl _
  | succ b ih =>
    intro hb a ha
    by_cases h1 : a = b + 1
    · subst h1
      exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega) a (by omega)) (h b (by omega))

theorem anti_of_step (f : Nat → Nat) (N : Nat) (h : ∀ a, a < N → f (a + 1) ≤ f a) :
    ∀ b, b ≤ N → ∀ a, a ≤ b → f b ≤ f a := by
  intro b
  induction b with
  | zero =>
    intro _ a ha
    have h0 : a = 0 := by omega
    subst h0
    exact Nat.le_refl _
  | succ b ih =>
    intro hb a ha
    by_cases h1 : a = b + 1
    · subst h1
      exact Nat.le_refl _
    · exact Nat.le_trans (h b (by omega)) (ih (by omega) a (by omega))

/-! ### The certificates are upper bounds and monotone -/

theorem tDv_b : allLt 9 (fun t => allLt 91 (fun y => Nat.ble (Dv t y) (SH t y))) = true := by
  decide +kernel

theorem tSHmono_b : allLt 9 (fun lo => allLt 90 (fun W => Nat.ble (SH lo W) (SH lo (W + 1)))) = true := by
  decide +kernel

theorem tSHanti_b : allLt 8 (fun lo => allLt 91 (fun W => Nat.ble (SH (lo + 1) W) (SH lo W))) = true := by
  decide +kernel

theorem tRv_b : allLt 85 (fun y => Nat.ble (Rv y) (RH y)) = true := by decide +kernel

theorem tRHmono_b : allLt 84 (fun W => Nat.ble (RH W) (RH (W + 1))) = true := by decide +kernel

theorem tHn3mono_b : allLt 90 (fun W => Nat.ble (Hn 3 W) (Hn 3 (W + 1))) = true := by decide +kernel

/-- `SH lo W` bounds the value of every sequence with `lo ≤ t ≤ 8` links and weight `y ≤ W ≤ 90`. -/
theorem Dv_le_SH {lo t y W : Nat} (h1 : lo ≤ t) (h2 : t ≤ 8) (h3 : y ≤ W) (h4 : W ≤ 90) :
    Dv t y ≤ SH lo W := by
  have a1 : Dv t y ≤ SH t y :=
    Nat.le_of_ble_eq_true (allLt_spec (allLt_spec tDv_b t (by omega)) y (by omega))
  have a2 : SH t y ≤ SH t W :=
    mono_of_step (SH t) 90
      (fun a ha => Nat.le_of_ble_eq_true (allLt_spec (allLt_spec tSHmono_b t (by omega)) a ha))
      W h4 y h3
  have a3 : SH t W ≤ SH lo W :=
    anti_of_step (fun i => SH i W) 8
      (fun a ha => Nat.le_of_ble_eq_true (allLt_spec (allLt_spec tSHanti_b a ha) W (by omega)))
      t h2 lo h1
  exact Nat.le_trans a1 (Nat.le_trans a2 a3)

/-- `RH W` bounds the value of every ring with `y ≤ W ≤ 84` holes. -/
theorem Rv_le_RH {y W : Nat} (h3 : y ≤ W) (h4 : W ≤ 84) : Rv y ≤ RH W := by
  have a1 : Rv y ≤ RH y := Nat.le_of_ble_eq_true (allLt_spec tRv_b y (by omega))
  have a2 : RH y ≤ RH W :=
    mono_of_step RH 84 (fun a ha => Nat.le_of_ble_eq_true (allLt_spec tRHmono_b a ha)) W h4 y h3
  exact Nat.le_trans a1 a2

theorem Hn3_mono {a b : Nat} (h3 : a ≤ b) (h4 : b ≤ 90) : Hn 3 a ≤ Hn 3 b :=
  mono_of_step (Hn 3) 90 (fun a ha => Nat.le_of_ble_eq_true (allLt_spec tHn3mono_b a ha)) b h4 a h3

/-! ### The knapsack -/

theorem c1R_b : allLt 84 (fun a => Nat.ble (SH 6 a + RH (83 - a)) 50) = true := by decide +kernel

/-- A sequence with at least 6 links and a ring, within the weight 83, have value at most 50. -/
theorem c1R (a : Nat) (ha : a ≤ 83) : SH 6 a + RH (83 - a) ≤ 50 :=
  Nat.le_of_ble_eq_true (allLt_spec c1R_b a (by omega))

theorem c1S_b : allLt 79 (fun a => Nat.ble (SH 5 a + SH 0 (78 - a)) 54) = true := by decide +kernel

/-- A sequence with at least 5 links and a sequence, within the weight 78, have value at most 54. -/
theorem c1S (a : Nat) (ha : a ≤ 78) : SH 5 a + SH 0 (78 - a) ≤ 54 :=
  Nat.le_of_ble_eq_true (allLt_spec c1S_b a (by omega))

theorem cRR_b : allLt 77 (fun a => allLt (77 - a) (fun b =>
    Nat.ble (SH 3 a + RH b + RH (76 - a - b)) 56)) = true := by decide +kernel

/-- A sequence with at least 3 links and two rings, within the weight 76, have value at most 56. -/
theorem cRR (a b : Nat) (h : a + b ≤ 76) : SH 3 a + RH b + RH (76 - a - b) ≤ 56 :=
  Nat.le_of_ble_eq_true (allLt_spec (allLt_spec cRR_b a (by omega)) b (by omega))

theorem cRE_b : allLt 72 (fun a => allLt (72 - a) (fun b =>
    Nat.ble (SH 2 a + SH 0 b + RH (71 - a - b)) 60)) = true := by decide +kernel

/-- A sequence with at least 2 links, a sequence and a ring, within the weight 71, have value at
most 60. -/
theorem cRE (a b : Nat) (h : a + b ≤ 71) : SH 2 a + SH 0 b + RH (71 - a - b) ≤ 60 :=
  Nat.le_of_ble_eq_true (allLt_spec (allLt_spec cRE_b a (by omega)) b (by omega))

theorem cRABa_b : allLt 71 (fun a => allLt (71 - a) (fun b =>
    decide (12 ≤ SH 0 b → 7 ≤ RH (70 - a - b) → SH 1 a + SH 0 b + RH (70 - a - b) ≤ 61))) = true := by
  decide +kernel

/-- A sequence with at least 1 link, a sequence of value at least 12 and a ring of value at least
7, within the weight 70, have value at most 61. -/
theorem cRABa (a b : Nat) (h : a + b ≤ 70) (h1 : 12 ≤ SH 0 b) (h2 : 7 ≤ RH (70 - a - b)) :
    SH 1 a + SH 0 b + RH (70 - a - b) ≤ 61 :=
  of_decide_eq_true (allLt_spec (allLt_spec cRABa_b a (by omega)) b (by omega)) h1 h2

theorem cRABb_b : allLt 71 (fun a => allLt (71 - a) (fun b =>
    decide (12 ≤ SH 1 b → 7 ≤ RH (70 - a - b) → SH 0 a + SH 1 b + RH (70 - a - b) ≤ 61))) = true := by
  decide +kernel

/-- A sequence, a sequence with at least 1 link of value at least 12 and a ring of value at least
7, within the weight 70, have value at most 61. -/
theorem cRABb (a b : Nat) (h : a + b ≤ 70) (h1 : 12 ≤ SH 1 b) (h2 : 7 ≤ RH (70 - a - b)) :
    SH 0 a + SH 1 b + RH (70 - a - b) ≤ 61 :=
  of_decide_eq_true (allLt_spec (allLt_spec cRABb_b a (by omega)) b (by omega)) h1 h2

theorem cSSS_b : allLt 66 (fun a => allLt (66 - a) (fun b =>
    Nat.ble (SH 0 a + SH 0 b + SH 0 (65 - a - b)) 65)) = true := by decide +kernel

/-- Three sequences within the weight 65 have value at most 65. -/
theorem cSSS (a b : Nat) (h : a + b ≤ 65) : SH 0 a + SH 0 b + SH 0 (65 - a - b) ≤ 65 :=
  Nat.le_of_ble_eq_true (allLt_spec (allLt_spec cSSS_b a (by omega)) b (by omega))

/-- A sequence with at most 8 links and weight at most 90 has value at most 44. -/
theorem cK : SH 0 90 ≤ 44 := by decide +kernel

theorem cHV_b : allLt 91 (fun W => decide ((7 ≤ W → RH (W - 7) ≤ HV W + 6) ∧
    (12 ≤ W → SH 0 (W - 12) ≤ HV W + 10) ∧ (13 ≤ W → SH 0 (W - 13) ≤ HV W + 11))) = true := by
  decide +kernel

/-- `HV W` bounds the value of a hanging item of weight at most `W`: a ring (shifts 6 and 7), a
sequence that borrows no class (10 and 12), a sequence that borrows a class (11 and 13). -/
theorem cHV (W : Nat) (h : W ≤ 90) : (7 ≤ W → RH (W - 7) ≤ HV W + 6) ∧
    (12 ≤ W → SH 0 (W - 12) ≤ HV W + 10) ∧ (13 ≤ W → SH 0 (W - 13) ≤ HV W + 11) :=
  of_decide_eq_true (allLt_spec cHV_b W (by omega))

theorem cHn_b : allLt 4 (fun n => allLt 91 (fun w => allLt (91 - w) (fun W =>
    decide (1 ≤ HV w → (n = 0 ∨ 1 ≤ Hn n W) → HV w + Hn n W ≤ Hn (min (n + 1) 3) (w + W))))) = true := by
  decide +kernel

/-- One more hanging item: `Hn n` is closed. -/
theorem cHn (n w W : Nat) (hn : n ≤ 3) (h : w + W ≤ 90) (h1 : 1 ≤ HV w) (h2 : n = 0 ∨ 1 ≤ Hn n W) :
    HV w + Hn n W ≤ Hn (min (n + 1) 3) (w + W) :=
  of_decide_eq_true (allLt_spec (allLt_spec (allLt_spec cHn_b n (by omega)) w (by omega)) W
    (by omega)) h1 h2

theorem cK3_b : allLt 91 (fun a => decide (1 ≤ Hn 3 (90 - a) → SH 0 a + Hn 3 (90 - a) ≤ 44)) = true := by
  decide +kernel

/-- A sequence and at least three hanging items, within the weight 90, have value at most 44. -/
theorem cK3 (a : Nat) (h : a ≤ 90) (h1 : 1 ≤ Hn 3 (90 - a)) : SH 0 a + Hn 3 (90 - a) ≤ 44 :=
  of_decide_eq_true (allLt_spec cK3_b a (by omega)) h1

/-! ### Lemma NCH -/

theorem M_lin_b : allLt 85 (fun x => Nat.ble (T5899.Mtab.getD x 0) (2 * x + 5)) = true := by
  decide +kernel

/-- A chain with `x ≤ 84` holes has at most `2 x + 5` rows. -/
theorem M_lin (x : Nat) (h : x ≤ 84) : T5899.Mtab.getD x 0 ≤ 2 * x + 5 :=
  Nat.le_of_ble_eq_true (allLt_spec M_lin_b x (by omega))

end A15
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.A15.Dv_le_SH
#print axioms SuperpermLowerBounds.A15.Rv_le_RH
#print axioms SuperpermLowerBounds.A15.c1R
#print axioms SuperpermLowerBounds.A15.c1S
#print axioms SuperpermLowerBounds.A15.cRR
#print axioms SuperpermLowerBounds.A15.cRE
#print axioms SuperpermLowerBounds.A15.cRABa
#print axioms SuperpermLowerBounds.A15.cRABb
#print axioms SuperpermLowerBounds.A15.cSSS
#print axioms SuperpermLowerBounds.A15.cK
#print axioms SuperpermLowerBounds.A15.cHV
#print axioms SuperpermLowerBounds.A15.cHn
#print axioms SuperpermLowerBounds.A15.cK3
#print axioms SuperpermLowerBounds.A15.Hn3_mono
#print axioms SuperpermLowerBounds.A15.M_lin
