import SuperpermutationUpperBound43586371.Nested3
import SuperpermutationUpperBound43586371.Certificate.BlockX103U

/-!
# Three block levels, first-level cycles one level up: 21736511/43243200 from 22 symbols on

As `Nested3.lean` (X103 = `w103_0.4795_0`, W133 = `w133_0`, S163 = `s163_old2_0`), but the cycles of
X103 are chosen on 16 symbols, for its walks transported once (`BlockCertUp`): 20 cycles
(`this directory/cyc16/cyc_t_w103_0.4795_0_n16.txt`, `blockcyc.py`, Gurobi optimal) in place of the 4 cycles on
15 symbols.

The closed level on 21 symbols has `19!` rows of total charge 60,351,241,265,602,560 = 22921/46200 · 19!
and 41,818,886,323,200 = 56491/8648640 · 18! cycles (`ledgerC.py`, chain
`w103_0.4795_0@16 + w133_0 + s163_old2_0`): coefficient 21736511/43243200 = 0.5026573.
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open Certificate

set_option maxRecDepth 100000 in
theorem closed21b : ∃ comps circles, Closed alph21 19 comps circles (Nat.factorial 19)
    60351241265602560 41818886323200 := by
  have S15 := cert.stage12.advance x103uCert.fam (List.Perm.refl _) rfl
  have S18 := S15.advance w133Cert.fam (List.Perm.refl _) rfl
  have S21 := S18.advance s163Cert.fam (List.Perm.refl _) rfl
  exact ⟨_, _, S21.close.congr (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

set_option maxHeartbeats 4000000 in
/-- The finite bound on `k + 22` symbols in natural numbers: `q` is the total charge and `c`
the number of connector cycles. -/
theorem word_ledgerG (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 20) :
    ∃ q c : Nat, ∃ w : Word (k + 22), IsSuperpermutation w ∧
      46200 * q = 22921 * (k + 19).factorial ∧ 8648640 * c = 56491 * (k + 18).factorial ∧
      w.length ≤ F3 (k + 22) + q + (k + 19) * c + (a - 2) * c +
        (k + 20 - a) * min c ((k + 21).descFactorial (k + 20 - a)) := by
  obtain ⟨comps, circles, C⟩ := closed21b
  obtain ⟨Q', c', Ck, hq, hc⟩ := C.all alph21_full 22921 46200 56491 8648640
    (by decide +kernel) (by decide +kernel) k
  obtain ⟨w, hw, hl⟩ := Ck.word (K := k + 22) (by omega) (alphG_full alph21_full k) a ha
    (by omega)
  refine ⟨Q', c', w, hw, hq, ?_, ?_⟩
  · rw [show k + 18 = k + 19 - 1 by omega]
    exact hc
  · rw [show k + 21 = k + 22 - 1 by omega, show k + 20 - a = k + 19 + 1 - a by omega]
    exact hl

end SuperpermutationUpperBound43586371
