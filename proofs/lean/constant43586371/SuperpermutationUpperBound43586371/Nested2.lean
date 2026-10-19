import SuperpermutationUpperBound43586371.AllSizesG
import SuperpermutationUpperBound43586371.Certificate.Cert
import SuperpermutationUpperBound43586371.Certificate.BlockW103
import SuperpermutationUpperBound43586371.Certificate.BlockS133

/-!
# Two block levels: the coefficient 43586371/86486400 from 19 symbols on

* 12 symbols: the selection of step (A) (`Certificate.cert`), its 6,048 loops of `d11` pending
  (`Cert.stage12`);
* 15 symbols: above every pending loop the (10,3) block W103 (`data/`,
  820 rows of charge 320, 500 loops without a row, 4 cycles on the completion of 14 symbols);
  pending: 6,048 · 500 = 3,024,000 loops on 14 symbols;
* 18 symbols: above every pending loop the (13,3) block S133 (`data/`, 1,742 rows
  of charge 702, 988 loops without a row, 1 cycle on the completion of 17 symbols);
* closed on 18 symbols: the 2,987,712,000 loops without a row become full charts, met by their own
  words.

The closed level has `16!` rows of total charge 10,386,167,500,800 = 41281/83160 · 16! and
9,890,460,720 = 654131/86486400 · 15! cycles (`ledgerC.py`, which writes out every
part).  `word_ledgerC` is the finite bound on `k + 19` symbols in natural numbers, in the shape of
step (B)'s `Cert.word_ledgerB`.
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open Certificate

/-- The letters of the closed level on 18 symbols. -/
def alph18 : List Nat := 18 :: 17 :: 16 :: 15 :: 14 :: 13 :: 12 :: alph10

set_option maxRecDepth 100000 in
theorem closed18 : ∃ comps circles, Closed alph18 16 comps circles (Nat.factorial 16)
    10386167500800 9890460720 := by
  have S15 := cert.stage12.advance w103Cert.fam (List.Perm.refl _) rfl
  have S18 := S15.advance s133Cert.fam (List.Perm.refl _) rfl
  exact ⟨_, _, S18.close.congr (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem alph18_full : (10 :: (alph18 ++ [9])).Perm (List.range 19) := by decide +kernel

/-- The finite bound on `k + 19` symbols in natural numbers: `q` is the total charge and `c`
the number of connector cycles. -/
theorem word_ledgerC (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 17) :
    ∃ q c : Nat, ∃ w : Word (k + 19), IsSuperpermutation w ∧
      83160 * q = 41281 * (k + 16).factorial ∧ 86486400 * c = 654131 * (k + 15).factorial ∧
      w.length ≤ F3 (k + 19) + q + (k + 16) * c + (a - 2) * c +
        (k + 17 - a) * min c ((k + 18).descFactorial (k + 17 - a)) := by
  obtain ⟨comps, circles, C⟩ := closed18
  obtain ⟨Q', c', Ck, hq, hc⟩ := C.all alph18_full 41281 83160 654131 86486400
    (by decide +kernel) (by decide +kernel) k
  obtain ⟨w, hw, hl⟩ := Ck.word (K := k + 19) (by omega) (alphG_full alph18_full k) a ha
    (by omega)
  refine ⟨Q', c', w, hw, hq, ?_, ?_⟩
  · rw [show k + 15 = k + 16 - 1 by omega]
    exact hc
  · rw [show k + 18 = k + 19 - 1 by omega, show k + 17 - a = k + 16 + 1 - a by omega]
    exact hl

end SuperpermutationUpperBound43586371
