import SuperpermutationUpperBound43586371.Nested2
import SuperpermutationUpperBound43586371.Certificate.BlockS103

/-!
# Two block levels with step (B)'s block: the coefficient 3961457/7862400 from 19 symbols on

As `Nested2.lean`, with step (B)'s (10,3) block S103 (`data/`: 880 rows of charge
370, 440 loops without a row) at the first level, its cycles chosen one level up: the 26 cycles on
16 symbols of `data/` (`BlockCertUp`); the second level is S133 as
before.  Pending after the first level: 6,048 · 440 = 2,661,120 loops on 14 symbols; charts at the
end: 2,629,186,560.

The closed level on 18 symbols has `16!` rows of total charge 10,395,300,464,640 = 413173/831600 · 16!
and 9,163,249,200 = 121207/17297280 · 15! cycles (`ledgerC.py`, chain `s103_old2_0@16 + s133_0`):
coefficient 413173/831600 + 121207/17297280 = 3961457/7862400 = 0.5038483, below the
43586371/86486400 = 0.5039679 of `Nested2.lean`.
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open Certificate

set_option maxRecDepth 100000 in
theorem closed18b : ∃ comps circles, Closed alph18 16 comps circles (Nat.factorial 16)
    10395300464640 9163249200 := by
  have S15 := cert.stage12.advance s103Cert.fam (List.Perm.refl _) rfl
  have S18 := S15.advance s133Cert.fam (List.Perm.refl _) rfl
  exact ⟨_, _, S18.close.congr (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

set_option maxHeartbeats 4000000 in
/-- The finite bound on `k + 19` symbols in natural numbers: `q` is the total charge and `c`
the number of connector cycles. -/
theorem word_ledgerE (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 17) :
    ∃ q c : Nat, ∃ w : Word (k + 19), IsSuperpermutation w ∧
      831600 * q = 413173 * (k + 16).factorial ∧ 17297280 * c = 121207 * (k + 15).factorial ∧
      w.length ≤ F3 (k + 19) + q + (k + 16) * c + (a - 2) * c +
        (k + 17 - a) * min c ((k + 18).descFactorial (k + 17 - a)) := by
  obtain ⟨comps, circles, C⟩ := closed18b
  obtain ⟨Q', c', Ck, hq, hc⟩ := C.all alph18_full 413173 831600 121207 17297280
    (by decide +kernel) (by decide +kernel) k
  obtain ⟨w, hw, hl⟩ := Ck.word (K := k + 19) (by omega) (alphG_full alph18_full k) a ha
    (by omega)
  refine ⟨Q', c', w, hw, hq, ?_, ?_⟩
  · rw [show k + 15 = k + 16 - 1 by omega]
    exact hc
  · rw [show k + 18 = k + 19 - 1 by omega, show k + 17 - a = k + 16 + 1 - a by omega]
    exact hl

end SuperpermutationUpperBound43586371
