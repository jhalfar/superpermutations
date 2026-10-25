import K6.TightRules

/-! Evaluation by the kernel: the tight case with 2 trails, part (0, 6) of 4 x 8. -/

namespace K6

theorem te_T2P0Q6 : part (famRules 2 4 4 0 8 6) 40 = false := by decide +kernel

end K6
