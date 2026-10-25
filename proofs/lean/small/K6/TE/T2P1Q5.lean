import K6.TightRules

/-! Evaluation by the kernel: the tight case with 2 trails, part (1, 5) of 4 x 8. -/

namespace K6

theorem te_T2P1Q5 : part (famRules 2 4 4 1 8 5) 40 = false := by decide +kernel

end K6
