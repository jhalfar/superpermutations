import LowerBounds.K16Sound

/-!
# Theorem JS: the statement by levels with Rule JS (the written proof, section 3.3)

`seqCap_levelK16` is `KS.seqCap_levelK` of 5,900 with the statement `KStmt16` of the search with Rule
JS.  The proof takes a counterexample with the fewest rows (all its parts obey the caps), chooses it or
its reversal by (4.1) (`KS.good_or_rev`), and then, among the good counterexamples with the same number
of rows, links and holes, one with the largest `psi` (an induction on the bound of `psi` less `psi`).  If
it had a shiftable junction, the shift (`shift_of_not_noJS`) would give a good counterexample with `psi`
one larger.  So it has none, the rule holds along it (`KS.ruleK_of_good`, Lemma CUT) and the search
finds it.  The potentials are natural numbers, so `b ≥ 0` holds and the shift keeps (4.1).
-/

namespace SuperpermLowerBounds
namespace K16

open PS (TRow IsSeq holesT linksT SeqCapLt)
open KS (codeF potN potS cutF a1F a2F uF segF Good)

variable {k : ℕ}

/-- **Theorem JS, by levels.**  F(s; lo - 1, hi) holds if the rule of the search holds along no
sequence without shiftable junction (with Rule JS) or along no sequence (without), given the rows of
fewer links up to `hi` holes and the row of `s` links below `lo`. -/
theorem seqCap_levelK16 {P : ℕ → ℕ → ℕ} {s lo hi a b h : ℕ} {js : Bool} (hk : 5 ≤ k)
    (hlow : ∀ j, j < s → SeqCapLt k j (P j) (hi + 1))
    (hprev : SeqCapLt k s (P s) lo)
    (hst : KStmt16 k js (codeF P s lo hi) (potN a b h) (potS a b h)
      (cutF (a1F P s lo hi a b h) (a2F (uF P s a b h) (segF P s a b h) P s lo hi a b h))) :
    SeqCapLt k s (P s) (hi + 1) := by
  suffices hmain : ∀ n : ℕ, ∀ L : List TRow, L.length = n → IsSeq k L → (∀ x ∈ L, x.1 ≤ 1) →
      linksT L = s → holesT k L < hi + 1 → L.length ≤ P s (holesT k L) from
    fun L h1 h2 h3 h4 => hmain L.length L rfl h1 h2 h3 h4
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L hlen hL htag hlinks hholes
    by_cases hlo : holesT k L < lo
    · exact hprev L hL htag hlinks hlo
    by_cases hne : L = []
    · subst hne
      simp
    by_contra hnb
    -- every proper part of a sequence with `n` rows obeys its cap
    have hparts : ∀ L' : List TRow, L'.length = n → IsSeq k L' → (∀ x ∈ L', x.1 ≤ 1) →
        linksT L' = s → holesT k L' < hi + 1 → ∀ U X W, L' = U ++ X ++ W → X ≠ [] →
        X.length < L'.length → X.length ≤ P (linksT X) (holesT k X) := by
      intro L' hlen' hL' htag' hlinks' hholes' U X W hUXW _ hXlen
      have hX : IsSeq k X := hL'.infix ⟨U, W, hUXW.symm⟩
      have hXtag : ∀ y ∈ X, y.1 ≤ 1 := fun y hy => htag' y (by rw [hUXW]; simp [hy])
      have hXholes : holesT k X ≤ holesT k L' := by
        rw [hUXW, PS.holesT_append, PS.holesT_append]
        omega
      have hXlinks : linksT X ≤ s := by
        rw [← hlinks', hUXW]
        exact le_trans (KS.linksT_le_left U X) (KS.linksT_le_right (U ++ X) W)
      by_cases hsX : linksT X < s
      · exact hlow _ hsX X hX hXtag rfl (by omega)
      · have hs : linksT X = s := by omega
        rw [hs]
        by_cases hloX : holesT k X < lo
        · exact hprev X hX hXtag hs hloX
        · exact ih X.length (by omega) X rfl hX hXtag hs (by omega)
    -- a good counterexample with `n` rows: by the largest `psi`, one without shiftable junction
    have hrev : ∀ L' : List TRow, L'.length = n → IsSeq k L' → (∀ x ∈ L', x.1 ≤ 1) →
        linksT L' = s → holesT k L' = holesT k L → Good k a b h L' → False := by
      suffices hmeas : ∀ D : ℕ, ∀ L' : List TRow, (k - 1) * n * n - psi L' = D →
          L'.length = n → IsSeq k L' → (∀ x ∈ L', x.1 ≤ 1) → linksT L' = s →
          holesT k L' = holesT k L → Good k a b h L' → False from
        fun L' h1 h2 h3 h4 h5 h6 => hmeas _ L' rfl h1 h2 h3 h4 h5 h6
      intro D
      induction D using Nat.strong_induction_on with
      | h D ihD =>
        intro L' hD hlen' hL' htag' hlinks' hholes' hgood
        by_cases hno : js = true → NoJS k L'
        · have hne' : L' ≠ [] := by
            intro h0
            rw [h0] at hlen'
            rw [← hlen] at hlen'
            exact hne (List.length_eq_zero_iff.mp hlen'.symm)
          obtain ⟨x0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne'
          have hrule := KS.ruleK_of_good (P := P) (s := s) (lo := lo) (hi := hi) (a := a)
            (b := b) (h := h) htag' hlinks' (by rw [hholes']; omega) (by rw [hholes']; omega)
            (by rw [hholes', hlen', ← hlen]; omega)
            (hparts _ hlen' hL' htag' hlinks' (by omega)) hgood rest [x0] 0 0 rfl (by simp)
            ⟨[], [x0], rfl, by simp, KS.phiAt_nil a b h _⟩
            (by
              intro A1 A2 hA12 hA2
              have hA1 : A1 = [] := by
                have hl := congrArg List.length hA12
                rw [List.length_append] at hl
                have : 0 < A2.length := List.length_pos_iff.mpr hA2
                simp only [List.length_cons, List.length_nil] at hl
                exact List.length_eq_zero_iff.mp (by omega)
              rw [hA1, KS.phiAt_nil])
          have e1 : linksT [x0] = 0 := rfl
          have e2 : ([x0] : List TRow).length = 1 := rfl
          have e3 : holesT k [x0] = k - 1 - x0.2.length := by simp [holesT]
          rw [e1, e2, e3] at hrule
          exact hst x0 rest hL' hno hrule
        · have hno' : js = true ∧ ¬ NoJS k L' := by
            by_cases hj : js = true
            · exact ⟨hj, fun h' => hno (fun _ => h')⟩
            · exact absurd (fun h' => absurd h' hj) hno
          obtain ⟨N, hN, htagN, hlenN, hlinksN, hholesN, hpsiN, hgoodN⟩ :=
            shift_of_not_noJS hk hL' htag' hno'.2
          have hb := psi_le N (fun x hx => hN.size_le x hx)
          rw [hlenN, hlen'] at hb
          exact ihD _ (by omega) N rfl (by omega) hN htagN (by omega) (by omega)
            (hgoodN a b h hgood)
    rcases KS.good_or_rev (k := k) a b h hne htag with hg | hg
    · exact hrev L hlen hL htag hlinks rfl hg
    · exact hrev (KS.revA k 0 L) (by rw [KS.length_revA, hlen]) (KS.isSeq_revA (by omega) 0 hL)
        (KS.kinds_revA (Nat.zero_le 1) htag) (by rw [KS.linksT_revA, hlinks])
        (KS.holesT_revA 0 L) hg

end K16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K16.seqCap_levelK16
