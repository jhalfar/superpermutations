import LowerBounds.J16Search
import Audit5901.J16Count
/-! Sanity check of the counting copy: the twelve statements of `J16Test.lean` on 5 symbols.
Expected answers `[false, true, false, true, true, true, false, true, true, false, true, false]`;
the counting copy must report found = 0 exactly where jSearch answers false. -/
open SuperpermLowerBounds J16
def C5 : List (List Nat) := [[3, 3, 5, 5, 6], [6, 0, 0, 0, 0]]
def R5 : List Nat := [3, 0, 2, 0, 6]
def nc : Int × Int := (J15.negInf, 1000000000)
def rPlain : Rules := ⟨[nc, nc], false, 9, 10, 15, 25, 9⟩
def rPrev0 : Rules := ⟨[nc, nc], false, 0, 10, 15, 25, 9⟩
def rOrd : Rules := ⟨[nc, nc], false, 9, 10, 15, 25, 0⟩
def rBoth : Rules := ⟨[nc, nc], false, 0, 10, 15, 25, 0⟩
def rPrev1 : Rules := ⟨[nc, nc], false, 1, 10, 15, 25, 9⟩
def rRing (a : Int) : Rules := ⟨[(a, 1000000000), nc], true, 9, 10, 15, 25, 9⟩
def cases : List (List (Nat × Nat × Nat) × Rules × Nat × Nat × Nat × List (Nat × Nat × Nat) × Nat) :=
  [([(1, 0, 0), (1, 0, 0)], rPlain, 7, 2, 0, [], 1), ([(1, 0, 0), (1, 0, 0)], rPlain, 6, 2, 0, [], 1),
   ([(1, 0, 0), (1, 0, 0)], rPrev0, 7, 2, 0, [], 1), ([(1, 0, 0), (1, 0, 0)], rPrev0, 6, 2, 0, [], 1),
   ([(1, 0, 0), (1, 0, 0)], rOrd, 6, 2, 0, [], 1), ([(1, 0, 0), (1, 0, 0)], rBoth, 6, 2, 0, [], 1),
   ([(1, 0, 0), (1, 0, 0)], rBoth, 7, 2, 0, [(0, 2, 3)], 3), ([(0, 0, 3), (1, 0, 0)], rPlain, 6, 3, 1, [], 1),
   ([(0, 0, 3), (1, 0, 0)], rPrev1, 6, 3, 1, [], 1), ([(0, 0, 3), (1, 0, 0)], rPrev1, 7, 3, 1, [], 1),
   ([(0, 0, 3), (1, 0, 0)], rRing 3, 6, 3, 1, [], 1), ([(0, 0, 3), (1, 0, 0)], rRing 4, 6, 3, 1, [], 1)]
#eval cases.map fun (sp, R, V, W, B, gs, n) => jSearch 5 C5 R5 sp R V W B 40 gs 0 n
#eval cases.map fun (sp, R, V, W, B, gs, n) => J16C.jCount 5 C5 R5 sp R V W B 40 gs 0 n
