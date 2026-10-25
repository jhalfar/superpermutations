import Mathlib.Tactic.IntervalCases
import K6.TE.T1P0Q0
import K6.TE.T1P1Q0
import K6.TE.T1P2Q0
import K6.TE.T1P3Q0
import K6.TE.T1P4Q0
import K6.TE.T1P5Q0
import K6.TE.T1P6Q0
import K6.TE.T1P7Q0
import K6.TE.T2P0Q0
import K6.TE.T2P0Q1
import K6.TE.T2P0Q2
import K6.TE.T2P0Q3
import K6.TE.T2P0Q4
import K6.TE.T2P0Q5
import K6.TE.T2P0Q6
import K6.TE.T2P0Q7
import K6.TE.T2P1Q0
import K6.TE.T2P1Q1
import K6.TE.T2P1Q2
import K6.TE.T2P1Q3
import K6.TE.T2P1Q4
import K6.TE.T2P1Q5
import K6.TE.T2P1Q6
import K6.TE.T2P1Q7
import K6.TE.T2P2Q0
import K6.TE.T2P2Q1
import K6.TE.T2P2Q2
import K6.TE.T2P2Q3
import K6.TE.T2P2Q4
import K6.TE.T2P2Q5
import K6.TE.T2P2Q6
import K6.TE.T2P2Q7
import K6.TE.T2P3Q0
import K6.TE.T2P3Q1
import K6.TE.T2P3Q2
import K6.TE.T2P3Q3
import K6.TE.T2P3Q4
import K6.TE.T2P3Q5
import K6.TE.T2P3Q6
import K6.TE.T2P3Q7
import K6.TE.T3P0Q0
import K6.TE.T3P0Q1
import K6.TE.T3P0Q2
import K6.TE.T3P0Q3
import K6.TE.T3P0Q4
import K6.TE.T3P0Q5
import K6.TE.T3P0Q6
import K6.TE.T3P0Q7
import K6.TE.T3P0Q8
import K6.TE.T3P0Q9
import K6.TE.T3P0Q10
import K6.TE.T3P0Q11
import K6.TE.T3P0Q12
import K6.TE.T3P0Q13
import K6.TE.T3P0Q14
import K6.TE.T3P0Q15
import K6.TE.T3P0Q16
import K6.TE.T3P0Q17
import K6.TE.T3P0Q18
import K6.TE.T3P0Q19
import K6.TE.T3P0Q20
import K6.TE.T3P0Q21
import K6.TE.T3P0Q22
import K6.TE.T3P0Q23
import K6.TE.T3P0Q24
import K6.TE.T3P0Q25
import K6.TE.T3P0Q26
import K6.TE.T3P0Q27
import K6.TE.T3P0Q28
import K6.TE.T3P0Q29
import K6.TE.T3P0Q30
import K6.TE.T3P0Q31

/-!
# All parts of the search of the tight case

`tightAll T`: for `T = 1, 2, 3` trails, every part of the search answers `false`.
-/

namespace K6

/-- The parts of the search with `T` trails: `(g0, n0, n1)`. -/
def tparts : Nat → Nat × Nat × Nat
  | 1 => (6, 8, 1)
  | 2 => (4, 4, 8)
  | _ => (30, 1, 32)

theorem tightAll1 : ∀ p0, p0 < 8 → ∀ p1, p1 < 1 →
    part (famRules 1 6 8 p0 1 p1) 40 = false := by
  intro p0 h0 p1 h1
  interval_cases p0 <;> interval_cases p1
  · exact te_T1P0Q0
  · exact te_T1P1Q0
  · exact te_T1P2Q0
  · exact te_T1P3Q0
  · exact te_T1P4Q0
  · exact te_T1P5Q0
  · exact te_T1P6Q0
  · exact te_T1P7Q0

theorem tightAll2 : ∀ p0, p0 < 4 → ∀ p1, p1 < 8 →
    part (famRules 2 4 4 p0 8 p1) 40 = false := by
  intro p0 h0 p1 h1
  interval_cases p0 <;> interval_cases p1
  · exact te_T2P0Q0
  · exact te_T2P0Q1
  · exact te_T2P0Q2
  · exact te_T2P0Q3
  · exact te_T2P0Q4
  · exact te_T2P0Q5
  · exact te_T2P0Q6
  · exact te_T2P0Q7
  · exact te_T2P1Q0
  · exact te_T2P1Q1
  · exact te_T2P1Q2
  · exact te_T2P1Q3
  · exact te_T2P1Q4
  · exact te_T2P1Q5
  · exact te_T2P1Q6
  · exact te_T2P1Q7
  · exact te_T2P2Q0
  · exact te_T2P2Q1
  · exact te_T2P2Q2
  · exact te_T2P2Q3
  · exact te_T2P2Q4
  · exact te_T2P2Q5
  · exact te_T2P2Q6
  · exact te_T2P2Q7
  · exact te_T2P3Q0
  · exact te_T2P3Q1
  · exact te_T2P3Q2
  · exact te_T2P3Q3
  · exact te_T2P3Q4
  · exact te_T2P3Q5
  · exact te_T2P3Q6
  · exact te_T2P3Q7

theorem tightAll3 : ∀ p0, p0 < 1 → ∀ p1, p1 < 32 →
    part (famRules 3 30 1 p0 32 p1) 40 = false := by
  intro p0 h0 p1 h1
  interval_cases p0 <;> interval_cases p1
  · exact te_T3P0Q0
  · exact te_T3P0Q1
  · exact te_T3P0Q2
  · exact te_T3P0Q3
  · exact te_T3P0Q4
  · exact te_T3P0Q5
  · exact te_T3P0Q6
  · exact te_T3P0Q7
  · exact te_T3P0Q8
  · exact te_T3P0Q9
  · exact te_T3P0Q10
  · exact te_T3P0Q11
  · exact te_T3P0Q12
  · exact te_T3P0Q13
  · exact te_T3P0Q14
  · exact te_T3P0Q15
  · exact te_T3P0Q16
  · exact te_T3P0Q17
  · exact te_T3P0Q18
  · exact te_T3P0Q19
  · exact te_T3P0Q20
  · exact te_T3P0Q21
  · exact te_T3P0Q22
  · exact te_T3P0Q23
  · exact te_T3P0Q24
  · exact te_T3P0Q25
  · exact te_T3P0Q26
  · exact te_T3P0Q27
  · exact te_T3P0Q28
  · exact te_T3P0Q29
  · exact te_T3P0Q30
  · exact te_T3P0Q31

end K6
