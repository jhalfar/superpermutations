import LowerBounds.J15SmallSearch
import LowerBounds.KTables

/-!
# Tests of the compiled joint search (not part of any proof)

Every equation of this file is proved by `native_decide`, so it shows what the compiled code
answers; nothing imports this file.

* On 5 symbols: the equations of `J15SmallSearch.lean` (evaluated there by the kernel), repeated
  with the search whose rule is read from tables (`jSearch`), and further cases that are too
  large for the kernel: three pieces at the values 9, 8 and 7, in one part, in 7 parts with a
  gate in the second piece and in 12 parts of three gates in three pieces; two rings.
* On 7 symbols, with table T': J(S0 S0; 60, 72; 0) (two disjoint chains within weight 72 have
  total value at most 59; 635,179 kept prefixes) in one part, in 7 parts and in 35 parts of two
  gates; J(S0 S0; 30, 24; 0), for which a pair of chains with 27 rows and 12 holes each is found;
  and S5 = J(S0 S0 R; 62, 70; 2) in one part (43,171,554 kept prefixes, about a minute).

A table that is lowered makes this search cut more, never find more, so there is no test "found
after lowering an entry"; the tests with answer `true` lower the value `V` instead, and
`ring5_walk`, `link5_walk` raise an entry, so that the search has to walk before it answers
`false`.
-/

namespace SuperpermLowerBounds
namespace J15
namespace Small

open T5900

theorem chains5_t : jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0)] 7 2 0 40 [] 0 1 = false := by
  native_decide
theorem chains5_low_t : jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0)] 6 2 0 40 [] 0 1 = true := by
  native_decide
theorem chains5_parts_t : jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0)] 7 2 0 40 [(0, 2, 3)] 0 3 = false := by
  native_decide
theorem ring5_t : jSearch 5 C5 R5 [(0, 0, 3), (1, 0, 0)] 7 3 1 40 [] 0 1 = false := by
  native_decide
theorem ring5_low_t : jSearch 5 C5 R5 [(0, 0, 3), (1, 0, 0)] 6 3 1 40 [] 0 1 = true := by
  native_decide
theorem ring5_window_t : jSearch 5 C5 R5 [(0, 1, 3), (1, 0, 0)] 4 3 1 40 [] 0 1 = false := by
  native_decide
theorem ring5_window_low_t : jSearch 5 C5 R5 [(0, 2, 2), (1, 0, 0)] 3 3 0 40 [] 0 1 = true := by
  native_decide
theorem link5_t : jSearch 5 C5 R5 [(2, 0, 0), (1, 0, 0)] 7 2 1 40 [] 0 1 = false := by
  native_decide
theorem link5_low_t : jSearch 5 C5 R5 [(2, 0, 0), (1, 0, 0)] 6 2 1 40 [] 0 1 = true := by
  native_decide
theorem three5_t : jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0), (0, 0, 2)] 9 2 2 40 [] 0 1 = false := by
  native_decide
theorem three5_8 : jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0), (0, 0, 2)] 8 2 2 40 [] 0 1 = false := by
  native_decide
theorem three5_7 : jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0), (0, 0, 2)] 7 2 2 40 [] 0 1 = false := by
  native_decide
theorem three5_7_parts :
    jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0), (0, 0, 2)] 7 2 2 40 [(1, 2, 7)] 0 7 = false := by
  native_decide
theorem three5_7_A :
    jSearchA 5 C5 R5 [(1, 0, 0), (1, 0, 0), (0, 0, 2)] 7 2 2 40 [(1, 2, 7)] 0 7 = false := by
  native_decide
theorem three5_7_gates :
    jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0), (0, 0, 2)] 7 2 2 40 [(0, 2, 2), (1, 2, 3), (2, 1, 2)] 0 12
      = false := by
  native_decide
theorem three5_7_gates_A :
    jSearchA 5 C5 R5 [(1, 0, 0), (1, 0, 0), (0, 0, 2)] 7 2 2 40 [(0, 2, 2), (1, 2, 3), (2, 1, 2)] 0 12
      = false := by
  native_decide
theorem chains5_gates_t :
    jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0)] 7 2 0 40 [(0, 2, 3), (0, 3, 2)] 0 6 = false := by
  native_decide
theorem ring5_walk_t : jSearch 5 C5 R5a [(0, 0, 0)] 4 0 0 40 [] 0 1 = false := by
  native_decide
theorem ring5_single_t : jSearch 5 C5 R5 [(0, 0, 4)] 2 4 0 40 [] 0 1 = true := by
  native_decide
theorem link5_walk_t : jSearch 5 C5b R5 [(2, 0, 0)] 4 4 0 40 [] 0 1 = false := by
  native_decide
theorem three5_low_t :
    jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0), (0, 0, 0)] 6 0 2 40 [] 0 1 = true := by
  native_decide
theorem three5_top_t :
    jSearch 5 C5 R5 [(2, 0, 0), (1, 0, 0), (0, 0, 0)] 10 0 2 40 [] 0 1 = false := by
  native_decide
theorem three5_6 : jSearch 5 C5 R5 [(1, 0, 0), (1, 0, 0), (0, 0, 2)] 6 2 2 40 [] 0 1 = true := by
  native_decide
theorem rings5 : jSearch 5 C5 R5 [(0, 0, 4), (0, 0, 4)] 5 4 0 40 [] 0 1 = true := by
  native_decide

/-- Two disjoint chains on 7 symbols within weight 72 have total value at most 59. -/
theorem pair7 : jSearch 7 Ttab TRtab [(1, 0, 0), (1, 0, 0)] 60 72 0 400 [] 0 1 = false := by
  native_decide
theorem pair7_parts : jSearch 7 Ttab TRtab [(1, 0, 0), (1, 0, 0)] 60 72 0 400 [(0, 8, 7)] 0 7 = false := by
  native_decide
theorem pair7_gates :
    jSearch 7 Ttab TRtab [(1, 0, 0), (1, 0, 0)] 60 72 0 400 [(0, 6, 5), (0, 10, 7)] 0 35 = false := by
  native_decide
/-- S5 = J(S0 S0 R; 62, 70; 2) in one part. -/
theorem s5_whole :
    jSearch 7 Ttab TRtab [(1, 0, 0), (1, 0, 0), (0, 0, 70)] 62 70 2 400 [] 0 1 = false := by
  native_decide
/-- Two disjoint chains with total value 30 within weight 24 are found. -/
theorem pair7_low : jSearch 7 Ttab TRtab [(1, 0, 0), (1, 0, 0)] 30 24 0 400 [] 0 1 = true := by
  native_decide

end Small
end J15
end SuperpermLowerBounds
