import K6.TightRules

/-! Evaluation by the kernel: the tight case with 1 trails, part (2, 0) of 8 x 1. -/

namespace K6

theorem te_T1P2Q0 : part (famRules 1 6 8 2 1 0) 40 = false := by decide +kernel

end K6
