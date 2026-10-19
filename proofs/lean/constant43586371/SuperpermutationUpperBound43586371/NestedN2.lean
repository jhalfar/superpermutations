import SuperpermutationUpperBound43586371.Nested2c
import SuperpermutationUpperBound43586371.Certificate.BlockD73
import SuperpermutationUpperBound43586371.Certificate.BlockS133U
import SuperpermutationUpperBound43586371.NoSeed

/-!
# No seed, three block levels: 3853/8736 from 19 symbols on

No selection on 9 symbols: all 6! loops on `[1, ..., 7]` pending (`Stage.noSeed` with letter 0 added), then the
(7,3) block D73 (`data/`, 315 rows of charge 126, 189 loops without a row, 3 cycles on
13 symbols from `data/`; tokens 0, 8, 11 so that the letters one
level up are `alph10`), W103 with its 20 cycles on 16 symbols, S133 with 11 cycles on 19 symbols
(`data/`), and charts.  The closed level on 18 symbols has `16!` rows of
total charge 7,896,994,560,000 = 465/1232 · 16! and 83,185,704,000 = 6113/96096 · 15! cycles: coefficient
3853/8736 = 0.4410485.
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open Certificate

set_option maxRecDepth 100000 in
theorem closed18n : ∃ comps circles, Closed alph18 16 comps circles (Nat.factorial 16)
    7896994560000 83185704000 := by
  have S0 := Stage.noSeed (a := 1) (z := 0) (rest := [2, 3, 4, 5, 6, 7]) (by decide) (by decide) (by decide) (by decide)
  have S12 := S0.advance d73Cert.fam (List.Perm.refl _) rfl
  have S15 := S12.advance w103uCert.fam (List.Perm.refl _) rfl
  have S := S15.advance s133uCert.fam (List.Perm.refl _) rfl
  exact ⟨_, _, S.close.congr (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

set_option maxHeartbeats 4000000 in
/-- The finite bound on `k + 19` symbols in natural numbers: `q` is the total charge and `c`
the number of connector cycles. -/
theorem word_ledgerI (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 17) :
    ∃ q c : Nat, ∃ w : Word (k + 19), IsSuperpermutation w ∧
      1232 * q = 465 * (k + 16).factorial ∧ 96096 * c = 6113 * (k + 15).factorial ∧
      w.length ≤ F3 (k + 19) + q + (k + 16) * c + (a - 2) * c +
        (k + 17 - a) * min c ((k + 18).descFactorial (k + 17 - a)) := by
  obtain ⟨comps, circles, C⟩ := closed18n
  obtain ⟨Q', c', Ck, hq, hc⟩ := C.all alph18_full 465 1232 6113 96096
    (by decide +kernel) (by decide +kernel) k
  obtain ⟨w, hw, hl⟩ := Ck.word (K := k + 19) (by omega) (alphG_full alph18_full k) a ha
    (by omega)
  refine ⟨Q', c', w, hw, hq, ?_, ?_⟩
  · rw [show k + 15 = k + 16 - 1 by omega]
    exact hc
  · rw [show k + 18 = k + 19 - 1 by omega, show k + 17 - a = k + 16 + 1 - a by omega]
    exact hl

end SuperpermutationUpperBound43586371
