import LowerBounds.A15Arith

/-!
# Tests of the arithmetic of the accounting at defect 15

Evaluated by the kernel, no Mathlib, no `native_decide`.  They show that the checks of
`A15Arith.lean` compute what they say and that their thresholds are the ones that matter:

* the entries of the certificates at a few places against the tables D and T';
* every bound of the knapsack fails when it is lowered by 1 (`c1S`, `cRR`, `cRABa`, `cK`, `cK3`),
  so the pieces of the shapes of the written proof (section 5.3) pass the tables and the joint
  statements are needed;
* `cRABa` fails without its two conditions on the values, so the positivity of the items is used.
-/

namespace SuperpermLowerBounds
namespace A15

/-- D_0(76) = 120, so a chain of weight 76 has value at most 44; the same with 8 links. -/
example : Dc 0 76 = 120 ∧ Dv 0 76 = 44 ∧ Dc 8 42 = 126 ∧ Dv 8 90 = 44 := by decide +kernel

/-- A ring with 0 holes has at most 5 rows; rings with 70 holes at most 112. -/
example : Rv 0 = 5 ∧ Rc 70 = 112 ∧ Rv 70 = 42 := by decide +kernel

/-- The best sequence within weight 90 has value 44 (Theorem K), not less. -/
example : SH 0 90 = 44 ∧ SH 8 90 = 44 ∧ SH 0 0 = 5 := by decide +kernel

/-- No three hanging items fit into weight 44; three fit into 45 with total value 6. -/
example : Hn 3 44 = 0 ∧ Hn 3 45 = 6 ∧ Hn 1 15 = 2 ∧ Hn 1 14 = 0 := by decide +kernel

/-- `c1S` is tight: two sequences, one with at least 5 links, reach the value 54 within 78. -/
example : allLt 79 (fun a => Nat.ble (SH 5 a + SH 0 (78 - a)) 53) = false := by decide +kernel

/-- Two sequences with at most 4 links pass the tables at (55, 78): S1 is needed. -/
example : allLt 79 (fun a => Nat.ble (SH 0 a + SH 0 (78 - a)) 54) = false := by decide +kernel

/-- A sequence and a ring pass the tables at (51, 83): S2 is needed. -/
example : allLt 84 (fun a => Nat.ble (SH 0 a + RH (83 - a)) 50) = false := by decide +kernel

/-- A sequence and two rings pass the tables at (57, 76): S3 is needed. -/
example : allLt 77 (fun a => allLt (77 - a) (fun b =>
    Nat.ble (SH 0 a + RH b + RH (76 - a - b)) 56)) = false := by decide +kernel

/-- Two sequences and a ring pass the tables at (61, 71) and at (62, 70): S4, S5 are needed. -/
example : allLt 72 (fun a => allLt (72 - a) (fun b =>
    Nat.ble (SH 0 a + SH 0 b + RH (71 - a - b)) 60)) = false := by decide +kernel

example : allLt 71 (fun a => allLt (71 - a) (fun b =>
    decide (12 ≤ SH 0 b → 7 ≤ RH (70 - a - b) → SH 0 a + SH 0 b + RH (70 - a - b) ≤ 61))) = false := by
  decide +kernel

/-- `cRABa` without the conditions on the values of the items is false. -/
example : allLt 71 (fun a => allLt (71 - a) (fun b =>
    Nat.ble (SH 1 a + SH 0 b + RH (70 - a - b)) 61)) = false := by decide +kernel

/-- `cRR` and `cK3` are tight. -/
example : allLt 77 (fun a => allLt (77 - a) (fun b =>
    Nat.ble (SH 3 a + RH b + RH (76 - a - b)) 55)) = false := by decide +kernel

example : allLt 91 (fun a => decide (1 ≤ Hn 3 (90 - a) → SH 0 a + Hn 3 (90 - a) ≤ 43)) = false := by
  decide +kernel

/-- A kernel piece with two hanging items passes the tables of the knapsack. -/
example : allLt 91 (fun a => decide (1 ≤ Hn 2 (90 - a) → SH 0 a + Hn 2 (90 - a) ≤ 44)) = false := by
  decide +kernel

end A15
end SuperpermLowerBounds
