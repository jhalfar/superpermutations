import LowerBounds.K16Defs

/-!
# Theorem K16 from the eleven kernel statements (the written proof, sections 1.2, 1.4, 3.4)

* `cl16_of`: **Lemma CL for the rows 9 and 10 of D16 below 36 holes** (`CL16`), from Theorem K of
  5,900 alone.  A sequence with `s ≥ 1` links is cut at its first link of weight 4 (bound (cl2) of the
  closure): the first part is a chain, the second has `s - 1` links, and rows and holes add.  So
  `D16_9(x) ≥ D_0(d) + D_8(x - d)` and `D16_10(x) ≥ D_0(d) + D16_9(x - d)` for `d ≤ x < 36` suffice;
  both are kernel checks.
* `theoremK16_of`: Theorem K16 from Theorem K of 5,900, the statements `K0 .. K10` and `CL16`, as in
  section 3.4: below `LO_s` the row `D16_s` is at least `D_s`; `K0` first, then `K1 .. K4` read the rows
  of D16 before them; `K5 .. K8` read rows of D within weight 90; `K9`, `K10` read the rows 0 to 8 of D,
  `K10` the row 9 of D16 (proved by `K9`), and `CL16` gives the rows 9, 10 below `LO = 35`.
-/

namespace SuperpermLowerBounds
namespace K16

open T5899 T5900 T5901
open PS (TRow IsSeq holesT linksT SeqCapLt capF)

/-- A cap valid below `b` gives every larger cap below `b' ≤ b`. -/
theorem capWeaken {k s b b' : ℕ} {P Q : ℕ → ℕ} (h : SeqCapLt k s P b) (hb : b' ≤ b)
    (hPQ : ∀ x, x < b' → P x ≤ Q x) : SeqCapLt k s Q b' :=
  fun L h1 h2 h3 h4 => le_trans (h L h1 h2 h3 (by omega)) (hPQ _ h4)

/-! ### Lemma CL, bound (cl2), cut at the first link -/

/-- The first element of a list with a property. -/
theorem split_first {α : Type} (p : α → Bool) :
    ∀ (L : List α), 0 < L.countP p → ∃ u y w, L = u ++ y :: w ∧ p y = true ∧ u.countP p = 0 ∧
      L.countP p = w.countP p + 1
  | [], h => by simp at h
  | a :: L, h => by
    by_cases ha : p a = true
    · exact ⟨[], a, L, rfl, ha, rfl, by simp [ha]⟩
    · have ha' : p a = false := by simpa using ha
      have h' : 0 < L.countP p := by
        rw [List.countP_cons, ha'] at h
        simpa using h
      obtain ⟨u, y, w, rfl, hy, hu, hc⟩ := split_first p L h'
      refine ⟨a :: u, y, w, rfl, hy, ?_, ?_⟩
      · rw [List.countP_cons, ha']
        simpa using hu
      · rw [List.countP_cons, ha']
        simpa using hc

/-- **Bound (cl2)**: a sequence with `s + 1` links, cut at its first link of weight 4, is a chain and
a sequence with `s` links. -/
theorem cl2_first {k s b : ℕ} {P0 PB PS' : ℕ → ℕ} (h0 : SeqCapLt k 0 P0 b)
    (hB : SeqCapLt k s PB b) (hchk : ∀ x, x < b → ∀ d, d ≤ x → P0 d + PB (x - d) ≤ PS' x) :
    SeqCapLt k (s + 1) PS' b := by
  intro L hL htag hlinks hholes
  cases L with
  | nil => simp [linksT] at hlinks
  | cons x0 rest =>
    have hc : rest.countP (fun x : TRow => x.1 != 0) = s + 1 := hlinks
    obtain ⟨u, y, w, rfl, hy, hu, hcnt⟩ := split_first (fun x : TRow => x.1 != 0) rest (by omega)
    have hsplit : x0 :: (u ++ y :: w) = (x0 :: u) ++ (y :: w) := rfl
    rw [hsplit] at hL htag hholes ⊢
    have hA : IsSeq k (x0 :: u) := hL.infix ⟨[], y :: w, by simp⟩
    have hBs : IsSeq k (y :: w) := hL.infix ⟨x0 :: u, [], by simp⟩
    have htA : ∀ z ∈ x0 :: u, z.1 ≤ 1 := fun z hz => htag z (List.mem_append_left _ hz)
    have htB : ∀ z ∈ y :: w, z.1 ≤ 1 := fun z hz => htag z (List.mem_append_right _ hz)
    have hh := PS.holesT_append (k := k) (x0 :: u) (y :: w)
    have hlA : linksT (x0 :: u) = 0 := hu
    have hlB : linksT (y :: w) = s := by
      show w.countP _ = s
      omega
    have c0 := h0 (x0 :: u) hA htA hlA (by omega)
    have cB := hB (y :: w) hBs htB hlB (by omega)
    have hx := hchk _ hholes (holesT k (x0 :: u)) (by omega)
    rw [hh] at hx ⊢
    rw [show holesT k (x0 :: u) + holesT k (y :: w) - holesT k (x0 :: u) = holesT k (y :: w)
      from by omega] at hx
    rw [List.length_append]
    omega

/-- **CL16** (Lemma CL on the rows 9 and 10 of D16 below 36 holes), from Theorem K of 5,900. -/
theorem cl16_of (hK : KS.TheoremK) : CL16 := by
  have d0 : SeqCapLt 7 0 (capF Dtab 0) 36 :=
    capWeaken (hK 0 (by norm_num)) (by norm_num) (fun _ _ => le_refl _)
  have d8 : SeqCapLt 7 8 (capF Dtab 8) 36 :=
    capWeaken (hK 8 (by norm_num)) (by norm_num) (fun _ _ => le_refl _)
  have r9 : SeqCapLt 7 9 (capF D16tab 9) 36 := cl2_first d0 d8 (by decide +kernel)
  exact ⟨r9, cl2_first d0 r9 (by decide +kernel)⟩

/-! ### Theorem K16 -/

/-- The rows below `s ≤ 9` of a table `P` to `G` holes, from the rows of D (`G + 6 s ≤ 96`) where `P`
is at least D. -/
theorem lowD (hK : KS.TheoremK) (P : List (List ℕ)) (s G : ℕ) (hs : s ≤ 9) (hG : G + 6 * s ≤ 96)
    (hchk : ∀ j, j < s → ∀ x, x < G + 1 → capF Dtab j x ≤ capF P j x) :
    ∀ j, j < s → SeqCapLt 7 j (capF P j) (G + 1) :=
  fun j hj => capWeaken (hK j (by omega)) (by omega) (hchk j hj)

/-- The rows below `s` of D16 to `G` holes, from the rows of D16 already proved. -/
theorem lowE (s G : ℕ) (hE : ∀ j, j < s → SeqCapLt 7 j (capF D16tab j) (97 - 6 * j))
    (hG : G + 6 * s ≤ 96) : ∀ j, j < s → SeqCapLt 7 j (capF D16tab j) (G + 1) :=
  fun j hj => capWeaken (hE j hj) (by omega) (fun _ _ => le_refl _)

/-- The row `s` below `LO + 1` from D (`s ≤ 8`, `LO + 6 s ≤ 90`), where `P` is at least D. -/
theorem prevD (hK : KS.TheoremK) (P : List (List ℕ)) (s LO : ℕ) (hs : s ≤ 8) (hLO : LO + 6 * s ≤ 90)
    (hchk : ∀ x, x < LO + 1 → capF Dtab s x ≤ capF P s x) : SeqCapLt 7 s (capF P s) (LO + 1) :=
  capWeaken (hK s hs) (by omega) hchk

/-- **Theorem K16** from Theorem K of 5,900, the eleven kernel statements and `CL16`. -/
theorem theoremK16_of (hK : KS.TheoremK) (hR : Kernel16) (hCL : CL16) : TheoremK16 := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩ := hR
  -- K0 .. K4 on D16: the rows before `s` are those of D16 already proved
  have e0 : SeqCapLt 7 0 (capF D16tab 0) 97 :=
    k0 (fun j hj => absurd hj (Nat.not_lt_zero j))
      (prevD hK D16tab 0 65 (by norm_num) (by norm_num) (by decide +kernel))
  have E1 : ∀ j, j < 1 → SeqCapLt 7 j (capF D16tab j) (97 - 6 * j) := by
    intro j hj
    obtain rfl : j = 0 := by omega
    exact e0
  have e1 : SeqCapLt 7 1 (capF D16tab 1) 91 :=
    k1 (lowE 1 90 E1 (by norm_num))
      (prevD hK D16tab 1 55 (by norm_num) (by norm_num) (by decide +kernel))
  have E2 : ∀ j, j < 2 → SeqCapLt 7 j (capF D16tab j) (97 - 6 * j) := by
    intro j hj
    by_cases h : j < 1
    · exact E1 j h
    · obtain rfl : j = 1 := by omega
      exact e1
  have e2 : SeqCapLt 7 2 (capF D16tab 2) 85 :=
    k2 (lowE 2 84 E2 (by norm_num))
      (prevD hK D16tab 2 51 (by norm_num) (by norm_num) (by decide +kernel))
  have E3 : ∀ j, j < 3 → SeqCapLt 7 j (capF D16tab j) (97 - 6 * j) := by
    intro j hj
    by_cases h : j < 2
    · exact E2 j h
    · obtain rfl : j = 2 := by omega
      exact e2
  have e3 : SeqCapLt 7 3 (capF D16tab 3) 79 :=
    k3 (lowE 3 78 E3 (by norm_num))
      (prevD hK D16tab 3 48 (by norm_num) (by norm_num) (by decide +kernel))
  have E4 : ∀ j, j < 4 → SeqCapLt 7 j (capF D16tab j) (97 - 6 * j) := by
    intro j hj
    by_cases h : j < 3
    · exact E3 j h
    · obtain rfl : j = 3 := by omega
      exact e3
  have e4 : SeqCapLt 7 4 (capF D16tab 4) 73 :=
    k4 (lowE 4 72 E4 (by norm_num))
      (prevD hK D16tab 4 41 (by norm_num) (by norm_num) (by decide +kernel))
  -- K5 .. K8: the rows below `s` are rows of D within weight 90; the row `s` of `Utab s` is D16
  have e5 : SeqCapLt 7 5 (capF D16tab 5) 67 :=
    capWeaken (k5 (lowD hK Utab5 5 66 (by norm_num) (by norm_num) (by decide +kernel))
      (prevD hK Utab5 5 37 (by norm_num) (by norm_num) (by decide +kernel))) (by norm_num)
      (by decide +kernel)
  have e6 : SeqCapLt 7 6 (capF D16tab 6) 61 :=
    capWeaken (k6 (lowD hK Utab6 6 60 (by norm_num) (by norm_num) (by decide +kernel))
      (prevD hK Utab6 6 37 (by norm_num) (by norm_num) (by decide +kernel))) (by norm_num)
      (by decide +kernel)
  have e7 : SeqCapLt 7 7 (capF D16tab 7) 55 :=
    capWeaken (k7 (lowD hK Utab7 7 54 (by norm_num) (by norm_num) (by decide +kernel))
      (prevD hK Utab7 7 35 (by norm_num) (by norm_num) (by decide +kernel))) (by norm_num)
      (by decide +kernel)
  have e8 : SeqCapLt 7 8 (capF D16tab 8) 49 :=
    capWeaken (k8 (lowD hK Utab8 8 48 (by norm_num) (by norm_num) (by decide +kernel))
      (prevD hK Utab8 8 35 (by norm_num) (by norm_num) (by decide +kernel))) (by norm_num)
      (by decide +kernel)
  -- K9: the rows 0 to 8 of D, the row 9 below 36 holes from CL16
  have e9 : SeqCapLt 7 9 (capF D16tab 9) 43 :=
    capWeaken (k9 (lowD hK Utab9 9 42 (by norm_num) (by norm_num) (by decide +kernel))
      (capWeaken hCL.1 (by norm_num) (by decide +kernel))) (by norm_num) (by decide +kernel)
  -- K10: the rows 0 to 8 of D, the row 9 of D16 (K9), the row 10 below 36 holes from CL16
  have l10 : ∀ j, j < 10 → SeqCapLt 7 j (capF Utab10 j) (36 + 1) := by
    intro j hj
    by_cases h : j < 9
    · exact lowD hK Utab10 9 36 (by norm_num) (by norm_num) (by decide +kernel) j h
    · obtain rfl : j = 9 := by omega
      exact capWeaken e9 (by norm_num) (by decide +kernel)
  have e10 : SeqCapLt 7 10 (capF D16tab 10) 37 :=
    capWeaken (k10 l10 (capWeaken hCL.2 (by norm_num) (by decide +kernel))) (by norm_num)
      (by decide +kernel)
  intro s hs
  match s, hs with
  | 0, _ => exact e0
  | 1, _ => exact e1
  | 2, _ => exact e2
  | 3, _ => exact e3
  | 4, _ => exact e4
  | 5, _ => exact e5
  | 6, _ => exact e6
  | 7, _ => exact e7
  | 8, _ => exact e8
  | 9, _ => exact e9
  | 10, _ => exact e10
  | n + 11, h => exact absurd h (by omega)

/-- Theorem K16 from Theorem K of 5,900 and the eleven kernel statements (`CL16` by `cl16_of`). -/
theorem theoremK16_of_kernel (hK : KS.TheoremK) (hR : Kernel16) : TheoremK16 :=
  theoremK16_of hK hR (cl16_of hK)

end K16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K16.cl16_of
#print axioms SuperpermLowerBounds.K16.theoremK16_of
#print axioms SuperpermLowerBounds.K16.theoremK16_of_kernel
