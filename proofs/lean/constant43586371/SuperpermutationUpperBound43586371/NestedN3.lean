import SuperpermutationUpperBound43586371.Nested3b
import SuperpermutationUpperBound43586371.Certificate.BlockB73
import SuperpermutationUpperBound43586371.Certificate.BlockW133U
import SuperpermutationUpperBound43586371.Certificate.BlockS163U
import SuperpermutationUpperBound43586371.NoSeed

/-!
# No seed, four block levels: 11117297/27675648 from 22 symbols on

No selection on 9 symbols (`Stage.noSeed`), then the (7,3) block B73 (`data/`, one
walk of 147 rows of charge 42, 357 loops without a row, 6 cycles on 13 symbols), X103 with its 20 cycles on 16
symbols, W133 with 7 cycles on 19 symbols, S163 with 45 cycles on 22 symbols (`data/cyc_up_*_alph.txt`),
and charts.  The closed level on 21 symbols has `19!` rows of total charge 37,976,061,499,084,800 =
51923/166320 · 19! and 573,090,939,892,800 = 1769507/19768320 · 18! cycles: coefficient 11117297/27675648 = 0.4016996.
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open Certificate

set_option maxRecDepth 100000 in
theorem closed21n3 : ∃ comps circles, Closed alph21 19 comps circles (Nat.factorial 19)
    37976061499084800 573090939892800 := by
  have S0 := Stage.noSeed (a := 1) (z := 0) (rest := [2, 3, 4, 5, 6, 7]) (by decide) (by decide) (by decide) (by decide)
  have S12 := S0.advance b73Cert.fam (List.Perm.refl _) rfl
  have S15 := S12.advance x103uCert.fam (List.Perm.refl _) rfl
  have S18 := S15.advance w133uCert.fam (List.Perm.refl _) rfl
  have S := S18.advance s163uCert.fam (List.Perm.refl _) rfl
  exact ⟨_, _, S.close.congr (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

set_option maxHeartbeats 4000000 in
/-- The finite bound on `k + 22` symbols in natural numbers: `q` is the total charge and `c`
the number of connector cycles. -/
theorem word_ledgerJ (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 20) :
    ∃ q c : Nat, ∃ w : Word (k + 22), IsSuperpermutation w ∧
      166320 * q = 51923 * (k + 19).factorial ∧ 19768320 * c = 1769507 * (k + 18).factorial ∧
      w.length ≤ F3 (k + 22) + q + (k + 19) * c + (a - 2) * c +
        (k + 20 - a) * min c ((k + 21).descFactorial (k + 20 - a)) := by
  obtain ⟨comps, circles, C⟩ := closed21n3
  obtain ⟨Q', c', Ck, hq, hc⟩ := C.all alph21_full 51923 166320 1769507 19768320
    (by decide +kernel) (by decide +kernel) k
  obtain ⟨w, hw, hl⟩ := Ck.word (K := k + 22) (by omega) (alphG_full alph21_full k) a ha
    (by omega)
  refine ⟨Q', c', w, hw, hq, ?_, ?_⟩
  · rw [show k + 18 = k + 19 - 1 by omega]
    exact hc
  · rw [show k + 21 = k + 22 - 1 by omega, show k + 20 - a = k + 19 + 1 - a by omega]
    exact hl

end SuperpermutationUpperBound43586371
