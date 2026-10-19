import SuperpermutationUpperBound43586371.Uniform.WalkLoops

/-!
# The arithmetic of Lemma 3 (`PROOF_R.md`, section 4)

The real keys of a row with offset `o`, parameter `g`, role order `σ` and family `f` are `o + 2 + K1` (token
`t1`) and `o + 2 + K2` (token `t2`) mod `m`.  Their difference is `Dv ∈ {g, g+1, g+2}` (`σ = 0`) or
`m - Dv` (`σ = 1`); equal keys force equal differences, hence `g = g'`, `σ = σ'` and the same family up to
`a1/a2`, and then the offsets agree mod `m` (or differ by one for `a1/a2`).
-/

namespace SuperpermutationUpperBound43586371.UniR

open SuperpermutationUpperBound43586371.Uniform

/-- `κ_A` relative to `o + 2`. -/
def cAf (m g f : Nat) : Nat := (m - 2 - g) + (if f ≤ 1 then 0 else f - 1)

/-- `κ_B` relative to `o + 2`. -/
def cBf (m f : Nat) : Nat := if f = 0 then m - 1 else 0

/-- The key of `t1` (relative to `o + 2`). -/
def K1 (m g σ f : Nat) : Nat := if σ = 0 then cAf m g f else cBf m f

/-- The key of `t2` (relative to `o + 2`). -/
def K2 (m g σ f : Nat) : Nat := if σ = 0 then cBf m f else cAf m g f

/-- `κ_B - κ_A` of the family (`PROOF_R.md`, section 3). -/
def dfam (g f : Nat) : Nat := if f = 1 then g + 2 else if f = 3 then g else g + 1

/-- The difference of the real keys, `κ_{t2} - κ_{t1}` (mod `m`). -/
def Dv (m g σ f : Nat) : Nat := if σ = 0 then dfam g f else m - dfam g f

theorem K1_le (m g σ f : Nat) (hf : f < 4) (hg : 1 ≤ g) (hm : g + 4 ≤ m) : K1 m g σ f ≤ m - 1 := by
  unfold K1 cAf cBf; split_ifs <;> omega

theorem K2_le (m g σ f : Nat) (hf : f < 4) (hg : 1 ≤ g) (hm : g + 4 ≤ m) : K2 m g σ f ≤ m - 1 := by
  unfold K2 cAf cBf; split_ifs <;> omega

theorem K2_mod (x m g σ f : Nat) (hσ : σ < 2) (hf : f < 4) (hg : 1 ≤ g) (hm : g + 4 ≤ m) :
    (x + K2 m g σ f) % m = (x + K1 m g σ f + Dv m g σ f) % m := by
  interval_cases σ <;> interval_cases f <;> simp only [K1, K2, Dv, dfam, cAf, cBf] <;> simp
  · congr 1; omega
  · rw [show x + (m - 2 - g) + (g + 2) = x + m by omega]; simp
  · rw [show x + (m - 2 - g + 1) + (g + 1) = x + m by omega]; simp
  · rw [show x + (m - 2 - g + 2) + g = x + m by omega]; simp
  · rw [show x + (m - 1) + (m - (g + 1)) = (x + (m - 2 - g)) + m by omega]; simp
  · rw [show x + (m - (g + 2)) = x + (m - 2 - g) by omega]
  · rw [show x + (m - (g + 1)) = x + (m - 2 - g + 1) by omega]
  · rw [show x + (m - g) = x + (m - 2 - g + 2) by omega]

theorem Dv_lt (m g σ f : Nat) (hσ : σ < 2) (hf : f < 4) (hg : 1 ≤ g) (hm : g + 4 ≤ m) : Dv m g σ f < m := by
  unfold Dv dfam; split_ifs <;> omega

theorem Dv_inj (m g g' σ σ' f f' : Nat) (hg : g % 3 = 1) (hg5 : 2 * g + 5 ≤ m)
    (hg' : g' % 3 = 1) (hg5' : 2 * g' + 5 ≤ m) (hσ : σ < 2) (hσ' : σ' < 2) (hf : f < 4) (hf' : f' < 4)
    (h : Dv m g σ f = Dv m g' σ' f') :
    g = g' ∧ σ = σ' ∧ (f = f' ∨ (f = 0 ∧ f' = 2) ∨ (f = 2 ∧ f' = 0)) := by
  interval_cases σ <;> interval_cases σ' <;> interval_cases f <;> interval_cases f' <;>
    simp only [Dv, dfam, if_true, if_false] at h <;> simp at h ⊢ <;> omega

theorem arithR (m g g' σ σ' f f' o o' : Nat) (hg : g % 3 = 1) (hg5 : 2 * g + 5 ≤ m)
    (hg' : g' % 3 = 1) (hg5' : 2 * g' + 5 ≤ m) (hσ : σ < 2) (hσ' : σ' < 2) (hf : f < 4) (hf' : f' < 4)
    (ho : o + 2 ≤ 2 * m) (ho' : o' + 2 ≤ 2 * m)
    (h1 : (o + 2 + K1 m g σ f) % m = (o' + 2 + K1 m g' σ' f') % m)
    (h2 : (o + 2 + K2 m g σ f) % m = (o' + 2 + K2 m g' σ' f') % m) :
    g = g' ∧ σ = σ' ∧ ((f = f' ∧ (o = o' ∨ o = o' + m ∨ o' = o + m)) ∨
      (f = 0 ∧ f' = 2 ∧ (o = o' + 1 ∨ o + m = o' + 1 ∨ o = o' + 1 + m ∨ o + 2 * m = o' + 1)) ∨
      (f = 2 ∧ f' = 0 ∧ (o' = o + 1 ∨ o' + m = o + 1 ∨ o' = o + 1 + m ∨ o' + 2 * m = o + 1))) := by
  have hg1 : 1 ≤ g := by omega
  have hg1' : 1 ≤ g' := by omega
  rw [K2_mod _ _ _ _ _ hσ hf hg1 (by omega), K2_mod _ _ _ _ _ hσ' hf' hg1' (by omega)] at h2
  have hD : Dv m g σ f % m = Dv m g' σ' f' % m := Nat.ModEq.add_left_cancel h1 h2
  rw [Nat.mod_eq_of_lt (Dv_lt m g σ f hσ hf hg1 (by omega)),
    Nat.mod_eq_of_lt (Dv_lt m g' σ' f' hσ' hf' hg1' (by omega))] at hD
  obtain ⟨rfl, rfl, hff⟩ := Dv_inj m g g' σ σ' f f' hg hg5 hg' hg5' hσ hσ' hf hf' hD
  refine ⟨rfl, rfl, ?_⟩
  have c1 := mod_eq_cases _ _ m (by omega) h1 (by have := K1_le m g σ f hf hg1 (by omega); omega)
    (by have := K1_le m g σ f' hf' hg1 (by omega); omega)
  rcases hff with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; refine ⟨rfl, ?_⟩; omega
  · right; left; refine ⟨rfl, rfl, ?_⟩
    interval_cases σ <;> simp only [K1, cAf, cBf] at c1 <;> simp at c1 <;> omega
  · right; right; refine ⟨rfl, rfl, ?_⟩
    interval_cases σ <;> simp only [K1, cAf, cBf] at c1 <;> simp at c1 <;> omega

end SuperpermutationUpperBound43586371.UniR
