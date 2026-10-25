import K6.TightRules

/-! Evaluation by the kernel: the tight case with 1 trails, part (0, 0) of 8 x 1. -/

namespace K6

theorem te_T1P0Q0 : part (famRules 1 6 8 0 1 0) 40 = false := by decide +kernel

end K6
