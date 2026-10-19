import SuperpermutationUpperBound43586371.Nested3b
import SuperpermutationUpperBound43586371.NoSeed

/-!
# No seed, three block levels: 629507/1441440 from 22 symbols on

The construction of `the no-seed construction` (referee: my referee notes): no selection at all on 12 symbols,
all 9! loops on `alph10` pending (`Stage.noSeed`), then the blocks of `Nested3b.lean`: X103 with its 20 cycles
on 16 symbols, W133, S163, and charts.  The closed level on 21 symbols has `19!` rows of total charge
39,302,075,009,433,600 = 2239/6930 · 19! and 727,520,258,304,000 = 32759/288288 · 18! cycles
(`ledgerC.py` `ledger_ns`; the referee's `ref/ledger_ns.py` gives the same): coefficient 629507/1441440 = 0.4367209.
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open Certificate

set_option maxRecDepth 100000 in
theorem closed21n : ∃ comps circles, Closed alph21 19 comps circles (Nat.factorial 19)
    39302075009433600 727520258304000 := by
  have S0 := Stage.noSeed (a := 11) (z := 12) (rest := alph9) (by decide) (by decide) (by decide) (by decide)
  have S15 := S0.advance x103uCert.fam (List.Perm.refl _) rfl
  have S18 := S15.advance w133Cert.fam (List.Perm.refl _) rfl
  have S := S18.advance s163Cert.fam (List.Perm.refl _) rfl
  exact ⟨_, _, S.close.congr (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

set_option maxHeartbeats 4000000 in
/-- The finite bound on `k + 22` symbols in natural numbers: `q` is the total charge and `c`
the number of connector cycles. -/
theorem word_ledgerH (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 20) :
    ∃ q c : Nat, ∃ w : Word (k + 22), IsSuperpermutation w ∧
      6930 * q = 2239 * (k + 19).factorial ∧ 288288 * c = 32759 * (k + 18).factorial ∧
      w.length ≤ F3 (k + 22) + q + (k + 19) * c + (a - 2) * c +
        (k + 20 - a) * min c ((k + 21).descFactorial (k + 20 - a)) := by
  obtain ⟨comps, circles, C⟩ := closed21n
  obtain ⟨Q', c', Ck, hq, hc⟩ := C.all alph21_full 2239 6930 32759 288288
    (by decide +kernel) (by decide +kernel) k
  obtain ⟨w, hw, hl⟩ := Ck.word (K := k + 22) (by omega) (alphG_full alph21_full k) a ha
    (by omega)
  refine ⟨Q', c', w, hw, hq, ?_, ?_⟩
  · rw [show k + 18 = k + 19 - 1 by omega]
    exact hc
  · rw [show k + 21 = k + 22 - 1 by omega, show k + 20 - a = k + 19 + 1 - a by omega]
    exact hl

end SuperpermutationUpperBound43586371
