import LowerBounds.J15Search

/-!
# Small joint searches, evaluated by the kernel (5 symbols)

The search of `J15Search.lean` with arithmetic tables and the rule evaluated (`jSearchA`) on 5
symbols, by `decide +kernel` (no `native_decide`).  This file imports `J15Search.lean` only, so
that the evaluation runs in a small process; `J15TestNative.lean` repeats the equations with the
compiled search.

The tables are the true caps on 5 symbols: chains `3 3 5 5 6` (0 to 4 holes), sequences with one
link of weight 4 `6` (0 holes), rings `3 - 2 - 6`.  On 5 symbols a link of weight 4 costs 3 in
the value and 4 in the weight.  The arguments after the pieces are `V W B`, the fuel, the gates
`(piece, rows, classes)` and the range of parts.

The kernel evaluates the rule (`bestF`, `fF`) at every prefix, and its cost grows with the number
of start vertices tried (about a quarter of a second and 15 MB each; with three pieces more).  So
every statement here has few of them: the largest takes half a minute and 3 GB.  A statement is
evaluated at a value for which objects exist (answer `true`), one above it (answer `false`), or
with a table that is raised by one (`R5a`, `C5b`), so that the bound of the table does not
decide and the search walks the pieces before it answers `false`.  The answers and the numbers
of kept prefixes are those of the compiled search and of the reference program.
-/

namespace SuperpermLowerBounds
namespace J15
namespace Small

/-- Caps on 5 symbols: chains with 0 to 4 holes, sequences with one link and 0 holes. -/
def C5 : List (List Nat) := [[3, 3, 5, 5, 6], [6, 0, 0, 0, 0]]

/-- Ring caps on 5 symbols for 0 to 4 holes. -/
def R5 : List Nat := [3, 0, 2, 0, 6]

/-- Ring caps with the entry for 0 holes raised by one. -/
def R5a : List Nat := [4, 0, 2, 0, 6]

/-- Caps with the entries for one link raised (7 rows with 0 and with 1 hole). -/
def C5b : List (List Nat) := [[3, 3, 5, 5, 6], [7, 7, 0, 0, 0]]

/-! ### Two chains -/

/-- J(S0 S0; 7, 2; 0): two disjoint chains within weight 2 have total value at most 6 (9 kept
prefixes, 46 start vertices tried). -/
theorem chains5 : jSearchA 5 C5 R5 [(1, 0, 0), (1, 0, 0)] 7 2 0 40 [] 0 1 = false := by
  decide +kernel

/-- Two disjoint chains with total value 6 are found. -/
theorem chains5_low : jSearchA 5 C5 R5 [(1, 0, 0), (1, 0, 0)] 6 2 0 40 [] 0 1 = true := by
  decide +kernel

/-- The same statement in 3 parts, with a gate at the prefixes with 2 rows of the first piece. -/
theorem chains5_parts :
    jSearchA 5 C5 R5 [(1, 0, 0), (1, 0, 0)] 7 2 0 40 [(0, 2, 3)] 0 3 = false := by
  decide +kernel

/-- The same statement in 6 parts of two gates, at 2 and at 3 rows of the first piece. -/
theorem chains5_gates :
    jSearchA 5 C5 R5 [(1, 0, 0), (1, 0, 0)] 7 2 0 40 [(0, 2, 3), (0, 3, 2)] 0 6 = false := by
  decide +kernel

/-! ### A ring -/

/-- J(R S0; 7, 3; 1): the bound of the table alone. -/
theorem ring5 : jSearchA 5 C5 R5 [(0, 0, 3), (1, 0, 0)] 7 3 1 40 [] 0 1 = false := by
  decide +kernel

/-- A ring and a chain with total value 6 and at most one shared class are found. -/
theorem ring5_low : jSearchA 5 C5 R5 [(0, 0, 3), (1, 0, 0)] 6 3 1 40 [] 0 1 = true := by
  decide +kernel

/-- With the ring restricted to 1 to 3 holes there is no such pair with value 4. -/
theorem ring5_window : jSearchA 5 C5 R5 [(0, 1, 3), (1, 0, 0)] 4 3 1 40 [] 0 1 = false := by
  decide +kernel

/-- With the ring cap raised to 4 the search walks the rings without holes and finds none with
4 rows. -/
theorem ring5_walk : jSearchA 5 C5 R5a [(0, 0, 0)] 4 0 0 40 [] 0 1 = false := by
  decide +kernel

/-- A ring with 6 rows and 4 holes is found. -/
theorem ring5_single : jSearchA 5 C5 R5 [(0, 0, 4)] 2 4 0 40 [] 0 1 = true := by
  decide +kernel

/-! ### A link of weight 4 -/

/-- J(S1 S0; 7, 2; 1): a sequence with at most one link of weight 4 and a chain. -/
theorem link5 : jSearchA 5 C5 R5 [(2, 0, 0), (1, 0, 0)] 7 2 1 40 [] 0 1 = false := by
  decide +kernel

/-- With value 6 such a pair is found. -/
theorem link5_low : jSearchA 5 C5 R5 [(2, 0, 0), (1, 0, 0)] 6 2 1 40 [] 0 1 = true := by
  decide +kernel

/-- With the caps for one link raised to 7 the search walks the sequences with a link of weight
4 within weight 4 and finds none with value 4 (25 kept prefixes, 126 start vertices tried). -/
theorem link5_walk : jSearchA 5 C5b R5 [(2, 0, 0)] 4 4 0 40 [] 0 1 = false := by
  decide +kernel

/-! ### Three pieces and shared classes -/

/-- Two chains and a ring with total value 6 and at most two shared classes are found. -/
theorem three5_low :
    jSearchA 5 C5 R5 [(1, 0, 0), (1, 0, 0), (0, 0, 0)] 6 0 2 40 [] 0 1 = true := by
  decide +kernel

/-- J(S1 S0 R; 10, 0; 2): above the bound of the table, which is 9. -/
theorem three5_top :
    jSearchA 5 C5 R5 [(2, 0, 0), (1, 0, 0), (0, 0, 0)] 10 0 2 40 [] 0 1 = false := by
  decide +kernel

end Small
end J15
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.J15.Small.chains5
#print axioms SuperpermLowerBounds.J15.Small.chains5_gates
#print axioms SuperpermLowerBounds.J15.Small.ring5_low
#print axioms SuperpermLowerBounds.J15.Small.link5_walk
#print axioms SuperpermLowerBounds.J15.Small.three5_low
