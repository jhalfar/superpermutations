import K6.TightRules

/-! Evaluation by the kernel: the tight case with 2 trails, part (2, 4) of 4 x 8. -/

namespace K6

theorem te_T2P2Q4 : part (famRules 2 4 4 2 8 4) 40 = false := by decide +kernel

end K6
