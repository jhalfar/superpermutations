import SuperpermutationUpperBound43586371.AllSizesG
import SuperpermutationUpperBound43586371.Certificate.Cert
import SuperpermutationUpperBound43586371.Certificate.BlockX103
import SuperpermutationUpperBound43586371.Certificate.BlockW133
import SuperpermutationUpperBound43586371.Certificate.BlockS163

/-!
# Three block levels: the coefficient 21751799/43243200 from 22 symbols on

* 12 symbols: the selection of step (A), its 6,048 loops of `d11` pending (`Cert.stage12`);
* 15 symbols: the (10,3) block X103 (`data/`: 660 rows of charge 240,
  660 loops without a row, 4 cycles on the completion of 14 symbols) above every pending loop;
* 18 symbols: the (13,3) block W133 (`data/`: 1,625 rows of charge 598, 1,105 loops
  without a row, 1 cycle on the completion of 17 symbols) above each of the 3,991,680 pending loops;
* 21 symbols: the (16,3) block S163 (`data/`: 2,688 rows of charge 768,
  2,208 loops without a row, 6 cycles on the completion of 20 symbols,
  `data/`) above each of the 4,410,806,400 pending loops;
* closed on 21 symbols: the 9,739,060,531,200 loops without a row become full charts.

The closed level has `19!` rows of total charge 60,351,241,265,602,560 = 22921/46200 · 19! and
44,082,351,774,720 = 297743/43243200 · 18! cycles (`ledgerC.py`).  `word_ledgerD` is the finite
bound on `k + 22` symbols in natural numbers.
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open Certificate

/-- The letters of the closed level on 21 symbols. -/
def alph21 : List Nat := 21 :: 20 :: 19 :: 18 :: 17 :: 16 :: 15 :: 14 :: 13 :: 12 :: alph10

set_option maxRecDepth 100000 in
theorem closed21 : ∃ comps circles, Closed alph21 19 comps circles (Nat.factorial 19)
    60351241265602560 44082351774720 := by
  have S15 := cert.stage12.advance x103Cert.fam (List.Perm.refl _) rfl
  have S18 := S15.advance w133Cert.fam (List.Perm.refl _) rfl
  have S21 := S18.advance s163Cert.fam (List.Perm.refl _) rfl
  exact ⟨_, _, S21.close.congr (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem alph21_full : (10 :: (alph21 ++ [9])).Perm (List.range 22) := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- The finite bound on `k + 22` symbols in natural numbers: `q` is the total charge and `c`
the number of connector cycles. -/
theorem word_ledgerD (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 20) :
    ∃ q c : Nat, ∃ w : Word (k + 22), IsSuperpermutation w ∧
      46200 * q = 22921 * (k + 19).factorial ∧ 43243200 * c = 297743 * (k + 18).factorial ∧
      w.length ≤ F3 (k + 22) + q + (k + 19) * c + (a - 2) * c +
        (k + 20 - a) * min c ((k + 21).descFactorial (k + 20 - a)) := by
  obtain ⟨comps, circles, C⟩ := closed21
  obtain ⟨Q', c', Ck, hq, hc⟩ := C.all alph21_full 22921 46200 297743 43243200
    (by decide +kernel) (by decide +kernel) k
  obtain ⟨w, hw, hl⟩ := Ck.word (K := k + 22) (by omega) (alphG_full alph21_full k) a ha
    (by omega)
  refine ⟨Q', c', w, hw, hq, ?_, ?_⟩
  · rw [show k + 18 = k + 19 - 1 by omega]
    exact hc
  · rw [show k + 21 = k + 22 - 1 by omega, show k + 20 - a = k + 19 + 1 - a by omega]
    exact hl

end SuperpermutationUpperBound43586371
