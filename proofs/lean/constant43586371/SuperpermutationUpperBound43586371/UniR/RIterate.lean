import SuperpermutationUpperBound43586371.UniR.RBlock
import SuperpermutationUpperBound43586371.Uniform.Iterate

/-!
# The stage iteration with R'(m) at every level, and the exact counts (`PROOF_R.md`, section 7)

No seed on `m0 + 1` letters, then the block R'(a) above every pending loop at `a = m0, m0 + 3, …`.
`cntR m0 K = (R, Q, c, P)` is the exact recursion that `Stage.advance` performs; `stagesR` gives the stage
after `K` levels with these counts, `closedR` the closed level (`R + P a = a!` rows, charge `Q`, `c + P` cycles).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SuperpermutationUpperBound43586371.UniR

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound43586371.Uniform

/-- The counts `(R, Q, c, P)` after `K` levels, starting with no seed at `m0`. -/
def cntR (m0 : Nat) : Nat → Nat × Nat × Nat × Nat
  | 0 => (0, 0, 0, (m0 - 1).factorial)
  | K + 1 =>
    let a := m0 + 3 * K
    let x := cntR m0 K
    ((a + 3) * ((a + 2) * ((a + 1) * x.1)) + x.2.2.2 * ((a + 3) * rowsR a),
     (a + 3) * ((a + 2) * ((a + 1) * x.2.1)) + x.2.2.2 * ((a + 3) * chargeR a),
     (a + 2) * ((a + 1) * (a * x.2.2.1)) + x.2.2.2 * ((a + 2) * ncycR a),
     x.2.2.2 * (a * ((a + 1) * (a + 2)) - rowsR a))

/-- The rows of R'(a) are at most the loops above a pending loop. -/
theorem rows_le (F : Frame) (hF : F.OK) (hm : 7 ≤ F.d0.length) :
    rowsR F.d0.length ≤ F.d0.length * ((F.d0.length + 1) * (F.d0.length + 2)) := by
  have S := setting_of F hF hm
  have h9 : 9 ∉ F.t3 :: F.t2 :: F.t1 :: F.d0 := hF.nine
  have hb : ∀ r ∈ blockRows F.d0 F.t1 F.t2 F.t3, r.base.Perm (F.t3 :: F.t2 :: F.t1 :: F.d0) := by
    intro r hr
    obtain ⟨d, hd, hrd⟩ := List.mem_flatMap.mp hr
    exact ((walkD_basedOn S h9 hd) r hrd).2.1
  have hc := count_covered (above3T F.t1 F.t2 F.t3 F.d0) (blockRows F.d0 F.t1 F.t2 F.t3) F.t3
    (above3T_nodup S.nd) (fun t ht => canon_ent ht) (fun r hr => (hb r hr).nodup_iff.mpr S.nd)
    (fun r hr => ⟨block_canon_mem S hr, canon_cyc_self ((hb r hr).mem_iff.mpr List.mem_cons_self)⟩)
    (block_canon_nodup S)
  have hle := List.length_filter_le (Uniform.coveredB (blockRows F.d0 F.t1 F.t2 F.t3)) (above3T F.t1 F.t2 F.t3 F.d0)
  rw [hc, above3T_length, blockRows_length S] at hle
  exact hle

theorem stagesR (m0 : Nat) (h11 : 11 ≤ m0) :
    ∀ K, ∃ A0 z comps circles pending, Stage A0 z comps circles pending (cntR m0 K).1 (cntR m0 K).2.1
      (cntR m0 K).2.2.1 (cntR m0 K).2.2.2 ∧ LetOK A0 z ∧ A0.length = m0 + 3 * K ∧
      (cntR m0 K).1 + (cntR m0 K).2.2.2 * A0.length = A0.length.factorial := by
  intro K
  induction K with
  | zero =>
    have hL := letOK0 m0 h11
    have hlen : (1 :: rest0 m0).length = m0 := by simp [rest0]; omega
    have S := Stage.noSeed (a := 1) (z := 0) (rest := rest0 m0) hL.nodup hL.nine hL.ten
      (by rw [rest0_length]; omega)
    have hPc : (rest0 m0).length.factorial = (cntR m0 0).2.2.2 := by
      simp only [cntR]; rw [show (rest0 m0).length = m0 - 1 by rw [rest0_length]; omega]
    refine ⟨_, _, _, _, _, S.congr rfl rfl rfl hPc, hL, hlen, ?_⟩
    simp only [cntR]
    rw [hlen, fact_pred m0 (by omega)]; ring
  | succ K ih =>
    obtain ⟨A0, z, comps, circles, pending, S, hL, hlen, hI1⟩ := ih
    have hF := frameAt_ok hL (by omega)
    have hm7 : 7 ≤ (frameAt A0 z).d0.length := by simp [frameAt]; omega
    have S1 := S.advance (rFam (frameAt A0 z) hF hm7) (List.Perm.refl _) rfl
    have hrl := rows_le (frameAt A0 z) hF hm7
    simp only [frameAt] at hrl
    refine ⟨_, _, _, _, _, S1.congr ?_ ?_ ?_ ?_, hL.next, by simp; omega, ?_⟩
    · simp only [cntR, rFam, famS, rData, frameAt, hlen]
    · simp only [cntR, rFam, famS, rData, frameAt, hlen]
    · simp only [cntR, rFam, famS, rData, frameAt, Frame.h, hlen]
    · simp only [cntR, rFam, famS, rData, frameAt, hlen]
    · simp only [List.length_cons, hlen]
      simp only [cntR]
      rw [hlen] at hI1 hrl
      set a := m0 + 3 * K
      set x := cntR m0 K
      obtain ⟨D, hD⟩ : ∃ D, a * ((a + 1) * (a + 2)) = D + rowsR a := ⟨_, (Nat.sub_add_cancel hrl).symm⟩
      rw [hD, Nat.add_sub_cancel, show a + 1 + 1 + 1 = a + 3 by omega, fact3, ← hI1]
      have : D = a * ((a + 1) * (a + 2)) - rowsR a := by omega
      nlinarith [hD]

/-- The closed level after `K` levels. -/
theorem closedR (m0 : Nat) (h11 : 11 ≤ m0) (K : Nat) :
    ∃ A comps circles, Closed A (m0 + 3 * K) comps circles (m0 + 3 * K).factorial (cntR m0 K).2.1
      ((cntR m0 K).2.2.1 + (cntR m0 K).2.2.2) ∧
      (10 :: (A ++ [9])).Perm (List.range (m0 + 3 * K + 3)) := by
  obtain ⟨A0, z, comps, circles, pending, S, hL, hlen, hI1⟩ := stagesR m0 h11 K
  have C := S.close
  rw [hlen] at C hI1
  rw [hI1] at C
  refine ⟨z :: A0, _, _, C, ?_⟩
  have := hL; unfold LetOK at this; rwa [hlen] at this

end SuperpermutationUpperBound43586371.UniR
