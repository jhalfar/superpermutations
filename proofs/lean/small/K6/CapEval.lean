import K6.CapRules

/-!
# Evaluation by the kernel: the chain search on 6 symbols with the caps `W6` (0 to 20 holes)

One part, 52,386 calls of `go` (counted by a copy of the search in Python).  No Mathlib is loaded.
-/

namespace K6

theorem capEval : part (capRules [W6] 0 20 TB_0_20 TK_0_20) 130 = false := by decide +kernel

end K6

#print axioms K6.capEval
