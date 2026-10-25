import K6.TightRules

/-! Evaluation by the kernel: the tight case with 2 trails, part (3, 5) of 4 x 8. -/

namespace K6

theorem te_T2P3Q5 : part (famRules 2 4 4 3 8 5) 40 = false := by decide +kernel

end K6
