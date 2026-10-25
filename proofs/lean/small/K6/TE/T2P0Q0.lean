import K6.TightRules

/-! Evaluation by the kernel: the tight case with 2 trails, part (0, 0) of 4 x 8. -/

namespace K6

theorem te_T2P0Q0 : part (famRules 2 4 4 0 8 0) 40 = false := by decide +kernel

end K6
