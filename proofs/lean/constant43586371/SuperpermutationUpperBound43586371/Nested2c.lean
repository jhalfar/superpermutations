import SuperpermutationUpperBound43586371.Nested2
import SuperpermutationUpperBound43586371.Certificate.BlockW103U

/-!
# Two block levels, first-level cycles one level up: 8711159/17297280 from 19 symbols on

As `Nested2.lean` (blocks W103 = `w103_0.6245_1`, then S133 = `s133_0`), but the cycles of W103 are
chosen on 16 symbols, for its walks transported once (`BlockCertUp`): 20 cycles
(`this directory/cyc16/cyc_t_w103_0.6245_1_n16.txt`, `blockcyc.py`, Gurobi optimal) in place of the 4 cycles on
15 symbols, which count as 48 there.

The closed level on 18 symbols has `16!` rows of total charge 10,386,167,500,800 = 41281/83160 · 16!
and 9,428,151,600 = 124711/17297280 · 15! cycles (`ledgerC.py`, chain `w103_0.6245_1@16 + s133_0`):
coefficient 8711159/17297280 = 0.5036144.
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open Certificate

set_option maxRecDepth 100000 in
theorem closed18c : ∃ comps circles, Closed alph18 16 comps circles (Nat.factorial 16)
    10386167500800 9428151600 := by
  have S15 := cert.stage12.advance w103uCert.fam (List.Perm.refl _) rfl
  have S18 := S15.advance s133Cert.fam (List.Perm.refl _) rfl
  exact ⟨_, _, S18.close.congr (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

set_option maxHeartbeats 4000000 in
/-- The finite bound on `k + 19` symbols in natural numbers: `q` is the total charge and `c`
the number of connector cycles. -/
theorem word_ledgerF (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 17) :
    ∃ q c : Nat, ∃ w : Word (k + 19), IsSuperpermutation w ∧
      83160 * q = 41281 * (k + 16).factorial ∧ 17297280 * c = 124711 * (k + 15).factorial ∧
      w.length ≤ F3 (k + 19) + q + (k + 16) * c + (a - 2) * c +
        (k + 17 - a) * min c ((k + 18).descFactorial (k + 17 - a)) := by
  obtain ⟨comps, circles, C⟩ := closed18c
  obtain ⟨Q', c', Ck, hq, hc⟩ := C.all alph18_full 41281 83160 124711 17297280
    (by decide +kernel) (by decide +kernel) k
  obtain ⟨w, hw, hl⟩ := Ck.word (K := k + 19) (by omega) (alphG_full alph18_full k) a ha
    (by omega)
  refine ⟨Q', c', w, hw, hq, ?_, ?_⟩
  · rw [show k + 15 = k + 16 - 1 by omega]
    exact hc
  · rw [show k + 18 = k + 19 - 1 by omega, show k + 17 - a = k + 16 + 1 - a by omega]
    exact hl

end SuperpermutationUpperBound43586371
