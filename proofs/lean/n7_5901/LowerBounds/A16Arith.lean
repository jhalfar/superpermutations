import LowerBounds.A15Arith
import LowerBounds.K16Tables
import LowerBounds.A16Tables

/-!
# The arithmetic of the accounting at defect 16 (the written proof `proofs/n7_5901/PROOF_5901.md`, 2.8)

Tables and numbers only; no rows, no Mathlib.  The closed statements are Boolean functions evaluated by the
kernel (`decide +kernel`); no `native_decide`.

A sequence with `t ≤ 10` links and weight `y ≤ 96` has value at most `Dv t y` (table D16); a ring with
`y ≤ 96` holes has value at most `Rv y` (the ring row of T' to 84 holes and the chain row of D16).  `SK lo W`
and `RH W` are the hulls (`Dv_le_SK`, `Rv_le_RH`).  The items of the accounting, in the units of the
components, have the values at most `IR w` (a ring, shifts 6 and 7), `IS lo w` (a sequence with at least
`lo` links that borrows nothing, shifts 10 and 12; a sequence that borrows a class has larger shifts, so the
bound holds for it too), `IA w` (a sequence that borrows a class, shifts 11 and 13) at the item weight `w`.
`NR n`, `NS n`, `NX n` bound `n` items of positive value of one kind, `NA2` two items `IA`, `NS1` an item
`IS 1` and an item `IS 0` (`cNR`, `cNS`, `cNX`, `cNA2`, `cNS1`).

The knapsack of the written proof (KN16) is used in this form: with the kernel piece and the items,

* the kernel alone has value at most 39 (`fK`); five or more items do not fit (`kX`);
* the shapes with one to four items whose numbers of links fit a joint statement: if a sequence piece
  has more links than the statement allows, the value is at most 39 (`fT1a` .. `fT9`);
* the other shapes do not fit (`k31`, `k22`, `k13`, `k04`, `k03`, `k1AA`).
-/

namespace SuperpermLowerBounds
namespace A16

open T5900 T5901

/-- Entry of table D16. -/
def Dc (t x : Nat) : Nat := (D16tab.getD t []).getD x 0

/-- The largest value of a sequence with `t` links and weight `y`, from table D16. -/
def Dv (t y : Nat) : Nat := if 6 * t ≤ y then Dc t (y - 6 * t) - (y - 6 * t) - 5 * t else 0

/-- The ring row: T' to 84 holes, and the chain row of D16. -/
def Rc (y : Nat) : Nat := if y ≤ 84 then min (TRtab.getD y 0) (Dc 0 y) else Dc 0 y

/-- The largest value of a ring with `y` holes. -/
def Rv (y : Nat) : Nat := Rc y - y

def SK (lo W : Nat) : Nat := (SKtab.getD lo []).getD W 0
def RH (W : Nat) : Nat := RHtab.getD W 0
def IR (w : Nat) : Nat := if 7 ≤ w then RH (w - 7) - 6 else 0
def IS (lo w : Nat) : Nat := if 12 ≤ w then SK lo (w - 12) - 10 else 0
def IA (w : Nat) : Nat := if 13 ≤ w then SK 0 (w - 13) - 11 else 0
def IX (w : Nat) : Nat := max (IR w) (IS 0 w)
def NR (n W : Nat) : Nat := (NRtab.getD n []).getD W 0
def NS (n W : Nat) : Nat := (NStab.getD n []).getD W 0
def NX (n W : Nat) : Nat := (NXtab.getD n []).getD W 0
def NA2 (W : Nat) : Nat := NA2tab.getD W 0
def NS1 (W : Nat) : Nat := NS1tab.getD W 0

theorem ble_of {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

/-! ### Hulls -/

theorem tDv_b : A15.allLt 11 (fun t => A15.allLt 97 (fun y => Nat.ble (Dv t y) (SK t y))) = true := by
  decide +kernel
theorem tSKmono_b : A15.allLt 11 (fun lo => A15.allLt 96 (fun W => Nat.ble (SK lo W) (SK lo (W + 1)))) = true := by
  decide +kernel
theorem tSKanti_b : A15.allLt 10 (fun lo => A15.allLt 97 (fun W => Nat.ble (SK (lo + 1) W) (SK lo W))) = true := by
  decide +kernel
theorem tRv_b : A15.allLt 97 (fun y => Nat.ble (Rv y) (RH y)) = true := by decide +kernel
theorem tRHmono_b : A15.allLt 96 (fun W => Nat.ble (RH W) (RH (W + 1))) = true := by decide +kernel
theorem tRsmall_b : A15.allLt 8 (fun y => Nat.ble (Rv y) 5) = true := by decide +kernel
theorem tISmono_b : A15.allLt 11 (fun lo => A15.allLt 96 (fun w => Nat.ble (IS lo w) (IS lo (w + 1)))) = true := by
  decide +kernel
theorem tIRmono_b : A15.allLt 96 (fun w => Nat.ble (IR w) (IR (w + 1))) = true := by decide +kernel
theorem tNRmono_b : A15.allLt 5 (fun n => A15.allLt 96 (fun w => Nat.ble (NR n w) (NR n (w + 1)))) = true := by
  decide +kernel
theorem tNSmono_b : A15.allLt 5 (fun n => A15.allLt 96 (fun w => Nat.ble (NS n w) (NS n (w + 1)))) = true := by
  decide +kernel
theorem tNXmono_b : A15.allLt 6 (fun n => A15.allLt 96 (fun w => Nat.ble (NX n w) (NX n (w + 1)))) = true := by
  decide +kernel
theorem tNA2mono_b : A15.allLt 96 (fun w => Nat.ble (NA2 w) (NA2 (w + 1))) = true := by decide +kernel
theorem tNS1mono_b : A15.allLt 96 (fun w => Nat.ble (NS1 w) (NS1 (w + 1))) = true := by decide +kernel

/-- `SK lo W` bounds every sequence with `lo ≤ t ≤ 10` links and weight `y ≤ W ≤ 96`. -/
theorem Dv_le_SK {lo t y W : Nat} (h1 : lo ≤ t) (h2 : t ≤ 10) (h3 : y ≤ W) (h4 : W ≤ 96) :
    Dv t y ≤ SK lo W := by
  have a1 : Dv t y ≤ SK t y := ble_of (A15.allLt_spec (A15.allLt_spec tDv_b t (by omega)) y (by omega))
  have a2 : SK t y ≤ SK t W :=
    A15.mono_of_step (SK t) 96 (fun a ha => ble_of (A15.allLt_spec (A15.allLt_spec tSKmono_b t (by omega)) a ha))
      W h4 y h3
  have a3 : SK t W ≤ SK lo W :=
    A15.anti_of_step (fun i => SK i W) 10
      (fun a ha => ble_of (A15.allLt_spec (A15.allLt_spec tSKanti_b a ha) W (by omega))) t h2 lo h1
  omega

theorem SK_mono {lo a b : Nat} (hlo : lo ≤ 10) (h : a ≤ b) (hb : b ≤ 96) : SK lo a ≤ SK lo b :=
  A15.mono_of_step (SK lo) 96 (fun x hx => ble_of (A15.allLt_spec (A15.allLt_spec tSKmono_b lo (by omega)) x hx))
    b hb a h

theorem SK_anti {lo hi W : Nat} (h : lo ≤ hi) (hhi : hi ≤ 10) (hW : W ≤ 96) : SK hi W ≤ SK lo W :=
  A15.anti_of_step (fun i => SK i W) 10
    (fun a ha => ble_of (A15.allLt_spec (A15.allLt_spec tSKanti_b a ha) W (by omega))) hi hhi lo h

/-- `RH W` bounds every ring with `y ≤ W ≤ 96` holes. -/
theorem Rv_le_RH {y W : Nat} (h3 : y ≤ W) (h4 : W ≤ 96) : Rv y ≤ RH W := by
  have a1 : Rv y ≤ RH y := ble_of (A15.allLt_spec tRv_b y (by omega))
  have a2 : RH y ≤ RH W :=
    A15.mono_of_step RH 96 (fun a ha => ble_of (A15.allLt_spec tRHmono_b a ha)) W h4 y h3
  omega

/-- A ring with at most 7 holes has value at most 5. -/
theorem Rv_small {y : Nat} (h : y ≤ 7) : Rv y ≤ 5 := ble_of (A15.allLt_spec tRsmall_b y (by omega))

theorem IS_mono {lo a b : Nat} (hlo : lo ≤ 10) (h : a ≤ b) (hb : b ≤ 96) : IS lo a ≤ IS lo b :=
  A15.mono_of_step (IS lo) 96 (fun x hx => ble_of (A15.allLt_spec (A15.allLt_spec tISmono_b lo (by omega)) x hx))
    b hb a h

theorem IR_mono {a b : Nat} (h : a ≤ b) (hb : b ≤ 96) : IR a ≤ IR b :=
  A15.mono_of_step IR 96 (fun x hx => ble_of (A15.allLt_spec tIRmono_b x hx)) b hb a h

theorem NR_mono {n a b : Nat} (hn : n ≤ 4) (h : a ≤ b) (hb : b ≤ 96) : NR n a ≤ NR n b :=
  A15.mono_of_step (NR n) 96 (fun x hx => ble_of (A15.allLt_spec (A15.allLt_spec tNRmono_b n (by omega)) x hx))
    b hb a h

theorem NS_mono {n a b : Nat} (hn : n ≤ 4) (h : a ≤ b) (hb : b ≤ 96) : NS n a ≤ NS n b :=
  A15.mono_of_step (NS n) 96 (fun x hx => ble_of (A15.allLt_spec (A15.allLt_spec tNSmono_b n (by omega)) x hx))
    b hb a h

theorem NX_mono {n a b : Nat} (hn : n ≤ 5) (h : a ≤ b) (hb : b ≤ 96) : NX n a ≤ NX n b :=
  A15.mono_of_step (NX n) 96 (fun x hx => ble_of (A15.allLt_spec (A15.allLt_spec tNXmono_b n (by omega)) x hx))
    b hb a h

theorem NA2_mono {a b : Nat} (h : a ≤ b) (hb : b ≤ 96) : NA2 a ≤ NA2 b :=
  A15.mono_of_step NA2 96 (fun x hx => ble_of (A15.allLt_spec tNA2mono_b x hx)) b hb a h

theorem NS1_mono {a b : Nat} (h : a ≤ b) (hb : b ≤ 96) : NS1 a ≤ NS1 b :=
  A15.mono_of_step NS1 96 (fun x hx => ble_of (A15.allLt_spec tNS1mono_b x hx)) b hb a h

/-! ### Several items of one kind -/

theorem cNR_b : A15.allLt 4 (fun n => A15.allLt 97 (fun w => A15.allLt (97 - w) (fun W =>
    decide (1 ≤ IR w → (n = 0 ∨ 1 ≤ NR n W) → IR w + NR n W ≤ NR (n + 1) (w + W))))) = true := by
  decide +kernel

theorem cNR {n w W : Nat} (hn : n < 4) (h : w + W ≤ 96) (h1 : 1 ≤ IR w) (h2 : n = 0 ∨ 1 ≤ NR n W) :
    IR w + NR n W ≤ NR (n + 1) (w + W) :=
  of_decide_eq_true (A15.allLt_spec (A15.allLt_spec (A15.allLt_spec cNR_b n hn) w (by omega)) W (by omega)) h1 h2

theorem cNS_b : A15.allLt 4 (fun n => A15.allLt 97 (fun w => A15.allLt (97 - w) (fun W =>
    decide (1 ≤ IS 0 w → (n = 0 ∨ 1 ≤ NS n W) → IS 0 w + NS n W ≤ NS (n + 1) (w + W))))) = true := by
  decide +kernel

theorem cNS {n w W : Nat} (hn : n < 4) (h : w + W ≤ 96) (h1 : 1 ≤ IS 0 w) (h2 : n = 0 ∨ 1 ≤ NS n W) :
    IS 0 w + NS n W ≤ NS (n + 1) (w + W) :=
  of_decide_eq_true (A15.allLt_spec (A15.allLt_spec (A15.allLt_spec cNS_b n hn) w (by omega)) W (by omega)) h1 h2

theorem cNX_b : A15.allLt 6 (fun n => A15.allLt 97 (fun w => A15.allLt (97 - w) (fun W =>
    decide (1 ≤ IX w → (n = 0 ∨ 1 ≤ NX n W) → IX w + NX n W ≤ NX (min (n + 1) 5) (w + W))))) = true := by
  decide +kernel

theorem cNX {n w W : Nat} (hn : n ≤ 5) (h : w + W ≤ 96) (h1 : 1 ≤ IX w) (h2 : n = 0 ∨ 1 ≤ NX n W) :
    IX w + NX n W ≤ NX (min (n + 1) 5) (w + W) :=
  of_decide_eq_true (A15.allLt_spec (A15.allLt_spec (A15.allLt_spec cNX_b n (by omega)) w (by omega)) W (by omega))
    h1 h2

theorem cNA2_b : A15.allLt 97 (fun w => A15.allLt (97 - w) (fun W =>
    decide (1 ≤ IA w → 1 ≤ IA W → IA w + IA W ≤ NA2 (w + W)))) = true := by
  decide +kernel

theorem cNA2 {w W : Nat} (h : w + W ≤ 96) (h1 : 1 ≤ IA w) (h2 : 1 ≤ IA W) : IA w + IA W ≤ NA2 (w + W) :=
  of_decide_eq_true (A15.allLt_spec (A15.allLt_spec cNA2_b w (by omega)) W (by omega)) h1 h2

theorem cNS1_b : A15.allLt 97 (fun w => A15.allLt (97 - w) (fun W =>
    decide (1 ≤ IS 1 w → 1 ≤ IS 0 W → IS 1 w + IS 0 W ≤ NS1 (w + W)))) = true := by
  decide +kernel

theorem cNS1 {w W : Nat} (h : w + W ≤ 96) (h1 : 1 ≤ IS 1 w) (h2 : 1 ≤ IS 0 W) :
    IS 1 w + IS 0 W ≤ NS1 (w + W) :=
  of_decide_eq_true (A15.allLt_spec (A15.allLt_spec cNS1_b w (by omega)) W (by omega)) h1 h2

/-! ### The final checks -/

/-- One item: `SK lo a + F (96 - a) ≤ 39` for `6 lo ≤ a ≤ 96` where `F (96 - a)` is positive. -/
def chk1 (lo : Nat) (F : Nat → Nat) : Bool :=
  A15.allLt 97 (fun a => decide (6 * lo ≤ a → 1 ≤ F (96 - a) → SK lo a + F (96 - a) ≤ 39))

/-- Two items: `SK lo a + F b + G (96 - a - b) ≤ 39`. -/
def chk2 (lo : Nat) (F G : Nat → Nat) : Bool :=
  A15.allLt 97 (fun a => A15.allLt (97 - a) (fun b =>
    decide (6 * lo ≤ a → 1 ≤ F b → 1 ≤ G (96 - a - b) → SK lo a + F b + G (96 - a - b) ≤ 39)))

theorem chk1_spec {lo : Nat} {F : Nat → Nat} (h : chk1 lo F = true) {a : Nat} (ha : a ≤ 96)
    (h6 : 6 * lo ≤ a) (h1 : 1 ≤ F (96 - a)) : SK lo a + F (96 - a) ≤ 39 :=
  of_decide_eq_true (A15.allLt_spec h a (by omega)) h6 h1

theorem chk2_spec {lo : Nat} {F G : Nat → Nat} (h : chk2 lo F G = true) {a b : Nat} (hab : a + b ≤ 96)
    (h6 : 6 * lo ≤ a) (h1 : 1 ≤ F b) (h2 : 1 ≤ G (96 - a - b)) : SK lo a + F b + G (96 - a - b) ≤ 39 :=
  of_decide_eq_true (A15.allLt_spec (A15.allLt_spec h a (by omega)) b (by omega)) h6 h1 h2

theorem fK : SK 0 96 ≤ 39 := by decide +kernel
theorem fT1a : chk1 8 (IS 0) = true := by decide +kernel
theorem fT1b : chk1 0 (IS 8) = true := by decide +kernel
theorem fT2 : chk1 8 IR = true := by decide +kernel
theorem fT3 : chk1 6 (NR 2) = true := by decide +kernel
theorem fT4a : chk2 5 IR (IS 0) = true := by decide +kernel
theorem fT4b : chk2 0 IR (IS 5) = true := by decide +kernel
theorem fT5a : chk1 4 (NS 2) = true := by decide +kernel
theorem fT5b : chk2 0 (IS 4) (IS 0) = true := by decide +kernel
theorem fT6 : chk1 3 (NR 3) = true := by decide +kernel
theorem fT7a : chk2 2 (NR 2) (IS 0) = true := by decide +kernel
theorem fT7b : chk2 0 (NR 2) (IS 2) = true := by decide +kernel
theorem fT8a : chk2 1 IR (NS 2) = true := by decide +kernel
theorem fT8b : chk2 0 IR NS1 = true := by decide +kernel
theorem fT9 : chk1 1 (NR 4) = true := by decide +kernel
theorem kX : chk1 0 (NX 5) = true := by decide +kernel
theorem k31 : chk2 0 (NR 3) (IS 0) = true := by decide +kernel
theorem k22 : chk2 0 (NR 2) (NS 2) = true := by decide +kernel
theorem k13 : chk2 0 IR (NS 3) = true := by decide +kernel
theorem k04 : chk1 0 (NS 4) = true := by decide +kernel
theorem k03 : chk2 0 IA (NS 2) = true := by decide +kernel
theorem k1AA : chk2 0 IR NA2 = true := by decide +kernel

end A16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.A16.Dv_le_SK
#print axioms SuperpermLowerBounds.A16.cNX
#print axioms SuperpermLowerBounds.A16.fT8b
#print axioms SuperpermLowerBounds.A16.k1AA
