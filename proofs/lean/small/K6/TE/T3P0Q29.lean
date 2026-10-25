import K6.TightRules

/-! Evaluation by the kernel: the tight case with 3 trails, part (0, 29) of 1 x 32. -/

namespace K6

theorem te_T3P0Q29 : part (famRules 3 30 1 0 32 29) 40 = false := by decide +kernel

end K6
