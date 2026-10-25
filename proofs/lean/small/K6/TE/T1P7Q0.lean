import K6.TightRules

/-! Evaluation by the kernel: the tight case with 1 trails, part (7, 0) of 8 x 1. -/

namespace K6

theorem te_T1P7Q0 : part (famRules 1 6 8 7 1 0) 40 = false := by decide +kernel

end K6
