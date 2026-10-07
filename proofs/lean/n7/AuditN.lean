import LowerBounds.NUpper

/-!
Audit file for the exact model of the paper `MODEL.md` (not in this package): Theorems W and N
(lower direction), Lemma T4, Theorems U and S (upper direction).  In the style of `AuditD.lean`: every definition that the final statement
uses is written out and Lean is asked to accept that it is the definition of the development
(`rfl`), and then the theorems of the development are accepted as proofs of the statements
written here.  Nothing here is a new proof.

Both directions are stated, so the model is exact: the least length of a superpermutation is
`HPV(k)` plus the least defect of a valid standard configuration.

Lower direction: for `k ≥ 5`, every Hamiltonian path `P` in the graph of permutations gives a
valid standard configuration `c` (a kernel and hanging components, as in section 4 of
`MODEL.md`) with `HPV(k) + cost(c) ≤ (k-2)! + wt(P) + k`; the defect of the paper is
`cost(c) - (k-2)!`.  Hence: if no valid standard configuration has cost at most `(k-2)! + D`,
every word over `k` symbols that contains all permutations has at least `HPV(k) + D + 1`
letters.

The same with Lemma T4: the configuration can be taken without seams of type T4 (no row starts
at `σ (τ₂ g)`, `g` the last block entry of the row before), so a search may leave that seam
type out.

Upper direction: for `k ≥ 3`, a valid standard configuration of cost `(k-2)! + D` gives a word
that contains all permutations and has exactly `HPV(k) + D` letters.

No `native_decide`; the axioms are `propext`, `Classical.choice`, `Quot.sound`.
-/

open SuperpermutationBounds Hunter PreimageChain SuperpermLowerBounds

section

variable {k : ℕ}

/-! ### Vocabulary -/

/-- A word covers: it contains every arrangement of the `k` symbols. -/
example (w : List (Fin k)) :
    Covers w =
      ∀ p : List (Fin k), p.length = k → p.Nodup → ∃ u v : List (Fin k), w = u ++ p ++ v := rfl

/-- Vertices: words without repetition whose symbols are exactly `1, …, k`. -/
example : Vtx k = {w : List ℕ // w.Nodup ∧ w.toFinset = Finset.Icc 1 k} := rfl

/-- The overlap weight: the least `d` in `[1, k]` such that `u` without its first `d` letters
is the beginning of `v`. -/
example (u v : Vtx k) :
    ew k u v =
      sInf {d | 1 ≤ d ∧ d ≤ k ∧ (u : List ℕ).drop d = (v : List ℕ).take (k - d)} := rfl

/-- `σ`: rotation by one letter; `σ⁻¹`. -/
example (v : Vtx k) : ((sigma v : Vtx k) : List ℕ) = (v : List ℕ).rotate 1 := rfl

example (v : Vtx k) : ((sigmaInv v : Vtx k) : List ℕ) = (v : List ℕ).rotate (k - 1) := rfl

/-- `τ₂`: `x M m ↦ M x m` (rotate the first `k - 1` letters, keep the marker `m`). -/
example (hk : 2 ≤ k) (v : Vtx k) (x : ℕ) (M : List ℕ) (m : ℕ)
    (hv : (v : List ℕ) = x :: (M ++ [m])) : ((tau2V v : Vtx k) : List ℕ) = M ++ [x, m] :=
  tau2V_cons_append hk v x M m hv

example : hpv k = k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3 := rfl

/-- A Hamiltonian path: a list without repetition that contains every vertex; its weight. -/
example (P : HPath k) : P.IsHamiltonian = ∀ v : Vtx k, v ∈ P.verts := rfl

example (P : HPath k) : P.wtP = (P.verts.zipWith (ew k) P.verts.tail).sum := rfl

/-! ### The model (`MODEL.md`, section 4) -/

/-- A row `(e, ℓ)` has the block entries `e, τ₂ e, …, τ₂^(ℓ-1) e`; its exit is `σ⁻¹` of the
last of them. -/
example (r : NRow k) : r.entries = (List.range r.len).map (fun i => tau2V^[i] r.entry) := rfl

example (r : NRow k) : r.exit = sigmaInv (tau2V^[r.len - 1] r.entry) := rfl

example (rows : List (NRow k)) : rowsEntries rows = rows.flatMap NRow.entries := rfl

/-- Seams: from the exit of a row to the entry of the next row. -/
example : seamWeights ([] : List (NRow k)) = [] := rfl

example (r : NRow k) : seamWeights [r] = [] := rfl

example (r r' : NRow k) (rest : List (NRow k)) :
    seamWeights (r :: r' :: rest) = ew k r.exit r'.entry :: seamWeights (r' :: rest) := rfl

example (rows : List (NRow k)) :
    rowsCost rows = rows.length + ((seamWeights rows).map (fun w => w - 3)).sum := rfl

/-- The attachment of a hanging component `H` at `v`: `w₀ = ew (head H) (σ v)`,
`w₁ = ew v (tail H)`, cost `w₀ + w₁ - 4`. -/
example (rows : List (NRow k)) (r : NRow k) (v : Vtx k) :
    NHanging.w0 ⟨rows ++ [r], v⟩ = ew k r.exit (sigma v) := by
  simp only [NHanging.w0, List.getLast?_concat]

example (rows : List (NRow k)) (r : NRow k) (v : Vtx k) :
    NHanging.w1 ⟨r :: rows, v⟩ = ew k v r.entry := rfl

example (H : NHanging k) : H.cost = rowsCost H.rows + (H.w0 + H.w1 - 4) := rfl

example (c : NConfig k) :
    c.entries = rowsEntries c.kernel ++ c.hanging.flatMap (fun H => rowsEntries H.rows) := rfl

/-- `cost = rows + Σ_seams (w - 3) + Σ_H (w₀ + w₁ - 4)`; the defect is `cost - (k-2)!`. -/
example (c : NConfig k) : c.cost = rowsCost c.kernel + (c.hanging.map NHanging.cost).sum := rfl

/-- "The component with rows `R` hangs on the component with rows `R'`." -/
example (c : NConfig k) (R R' : List (NRow k)) :
    c.HangsOn R R' ↔
      ∃ H ∈ c.hanging, H.rows = R ∧
        ∃ e ∈ rowsEntries R', ((H.slot : Vtx k) : List ℕ) ~r (e : List ℕ) := Iff.rfl

/-- A valid standard configuration, all conditions written out. -/
example (c : NConfig k) :
    c.Valid ↔
      (c.kernel ≠ [] ∧
        (∀ H ∈ c.hanging, H.rows ≠ []) ∧
        (∀ r ∈ c.kernel, 1 ≤ r.len) ∧
        (∀ H ∈ c.hanging, ∀ r ∈ H.rows, 1 ≤ r.len) ∧
        -- seams have weight at least 3
        (∀ w ∈ seamWeights c.kernel, 3 ≤ w) ∧
        (∀ H ∈ c.hanging, ∀ w ∈ seamWeights H.rows, 3 ≤ w) ∧
        -- (R1) the blocks are pairwise different rotation classes and all of them
        c.entries.Pairwise (fun a b : Vtx k => ¬ ((a : List ℕ) ~r (b : List ℕ))) ∧
        (∀ v : Vtx k, ∃ e ∈ c.entries, (v : List ℕ) ~r (e : List ℕ)) ∧
        -- (R2) the vertex of an attachment is not the exit of its block
        (∀ H ∈ c.hanging, sigma H.slot ∉ c.entries) ∧
        -- (V3) different hanging components are attached at different vertices
        (c.hanging.map NHanging.slot).Nodup ∧
        (∀ H ∈ c.hanging, 2 ≤ H.w0) ∧
        (∀ H ∈ c.hanging, 2 ≤ H.w1) ∧
        -- (R3) every hanging component reaches the kernel
        (∀ H ∈ c.hanging, Relation.TransGen c.HangsOn H.rows c.kernel)) :=
  ⟨fun h => ⟨h.kernel_ne, h.hanging_ne, h.kernel_len, h.hanging_len, h.kernel_seams,
      h.hanging_seams, h.distinct, h.cover, h.slot, h.slots_nodup, h.w0_ge, h.w1_ge, h.forest⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩⟩

/-- No seam of type T4: no row starts at `σ (τ₂ g)`, `g` the last block entry of the row
before it. -/
example (rows : List (NRow k)) :
    RowsNoT4 rows =
      rows.IsChain (fun r r' => r'.entry ≠ sigma (tau2V (tau2V^[r.len - 1] r.entry))) := rfl

example (c : NConfig k) :
    c.NoT4 = (RowsNoT4 c.kernel ∧ ∀ H ∈ c.hanging, RowsNoT4 H.rows) := rfl

/-! ### The statements -/

/-- **Theorems W and N.**  Every Hamiltonian path gives a valid standard configuration of
defect at most `wt(P) + k - HPV(k)`. -/
example (hk : 5 ≤ k) (P : HPath k) (hP : ∀ v : Vtx k, v ∈ P.verts) :
    ∃ c : NConfig k, c.Valid ∧
      k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3 + c.cost ≤
        (k - 2).factorial + ((P.verts.zipWith (ew k) P.verts.tail).sum + k) :=
  exists_stdConfig hk hP

/-- **The lower direction, for the searches.**  If no valid standard configuration has cost at
most `(k-2)! + D` (defect at most `D`), every covering word has at least `HPV(k) + D + 1`
letters. -/
example (hk : 5 ≤ k) (D : ℕ)
    (h : ∀ c : NConfig k, c.Valid → ¬ c.cost ≤ (k - 2).factorial + D) :
    ∀ w : List (Fin k),
      (∀ p : List (Fin k), p.length = k → p.Nodup → ∃ u v : List (Fin k), w = u ++ p ++ v) →
      k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3 + D + 1 ≤ w.length :=
  covers_length_gt_of_no_stdConfig hk D h

/-- The same as an existence statement. -/
example (hk : 5 ≤ k) (w : List (Fin k))
    (hw : ∀ p : List (Fin k), p.length = k → p.Nodup → ∃ u v : List (Fin k), w = u ++ p ++ v) :
    ∃ c : NConfig k, c.Valid ∧
      k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3 + c.cost ≤
        (k - 2).factorial + w.length :=
  exists_stdConfig_of_covers hk hw

/-- **Lemma T4.**  A valid standard configuration can be changed into one without seams of
type T4 and of no larger cost. -/
example (hk : 3 ≤ k) (c : NConfig k) (hv : c.Valid) :
    ∃ c' : NConfig k, c'.Valid ∧ c'.NoT4 ∧ c'.cost ≤ c.cost :=
  hv.exists_noT4 hk

/-- **The lower direction with Lemma T4.**  It is enough to exclude the valid standard
configurations without seams of type T4. -/
example (hk : 5 ≤ k) (D : ℕ)
    (h : ∀ c : NConfig k, c.Valid → c.NoT4 → ¬ c.cost ≤ (k - 2).factorial + D) :
    ∀ w : List (Fin k),
      (∀ p : List (Fin k), p.length = k → p.Nodup → ∃ u v : List (Fin k), w = u ++ p ++ v) →
      k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3 + D + 1 ≤ w.length :=
  covers_length_gt_of_no_stdConfig_noT4 hk D h

/-- **Theorems U and S (the upper direction).**  A valid standard configuration of cost
`(k-2)! + D` is a covering word of exactly `HPV(k) + D` letters. -/
example (hk : 3 ≤ k) (c : NConfig k) (hv : c.Valid) :
    ∃ w : List (Fin k),
      (∀ p : List (Fin k), p.length = k → p.Nodup → ∃ u v : List (Fin k), w = u ++ p ++ v) ∧
      k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3 + c.cost =
        (k - 2).factorial + w.length :=
  hv.exists_word hk

/-- **The model is exact.**  No valid standard configuration of defect at most `D` exists if and
only if every covering word has at least `HPV(k) + D + 1` letters. -/
example (hk : 5 ≤ k) (D : ℕ) :
    (∀ c : NConfig k, c.Valid → ¬ c.cost ≤ (k - 2).factorial + D) ↔
      ∀ w : List (Fin k),
        (∀ p : List (Fin k), p.length = k → p.Nodup → ∃ u v : List (Fin k), w = u ++ p ++ v) →
        k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3 + D + 1 ≤ w.length :=
  no_stdConfig_iff hk D

/-- The same with the configurations without seams of type T4 only. -/
example (hk : 5 ≤ k) (D : ℕ) :
    (∀ c : NConfig k, c.Valid → c.NoT4 → ¬ c.cost ≤ (k - 2).factorial + D) ↔
      ∀ w : List (Fin k),
        (∀ p : List (Fin k), p.length = k → p.Nodup → ∃ u v : List (Fin k), w = u ++ p ++ v) →
        k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3 + D + 1 ≤ w.length :=
  no_stdConfig_noT4_iff hk D

/-- The least length of a superpermutation, in the encoding of the Hunter–Raudvere library
(words over the symbols `1, …, k`). -/
example : Ssuper k = sInf {m | ∃ w : List ℕ,
    (∀ v : List ℕ, v.Nodup ∧ v.toFinset = Finset.Icc 1 k → v <:+: w) ∧ w.length = m} := rfl

/-- **`L(k) = HPV(k) + min D`.**  A valid standard configuration of least cost exists, and its
defect is the least length of a superpermutation minus `HPV(k)`. -/
example (hk : 5 ≤ k) :
    ∃ c : NConfig k, c.Valid ∧
      k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3 + c.cost =
        (k - 2).factorial + Ssuper k ∧
      ∀ c' : NConfig k, c'.Valid → c.cost ≤ c'.cost :=
  exists_optimal_stdConfig hk

/-- The defect of a valid standard configuration is not negative. -/
example (hk : 5 ≤ k) (c : NConfig k) (hv : c.Valid) : (k - 2).factorial ≤ c.cost :=
  hv.factorial_le_cost hk

/-- For seven symbols and defect 14: there is no valid standard configuration of cost at most
`5! + 14 = 134` if and only if every covering word has at least 5899 letters. -/
example :
    (∀ c : NConfig 7, c.Valid → ¬ c.cost ≤ 134) ↔
      ∀ w : List (Fin 7),
        (∀ p : List (Fin 7), p.length = 7 → p.Nodup → ∃ u v : List (Fin 7), w = u ++ p ++ v) →
        5899 ≤ w.length := by
  have h := no_stdConfig_iff (k := 7) (by norm_num) 14
  have e1 : (7 - 2).factorial + 14 = 134 := by decide
  have e2 : hpv 7 + 14 + 1 = 5899 := by decide
  rw [e1, e2] at h
  exact h

end

/-! ### Axioms -/

#print axioms SuperpermLowerBounds.stdConfig_valid
#print axioms SuperpermLowerBounds.stdConfig_cost_le
#print axioms SuperpermLowerBounds.mem_stdConfig_entries
#print axioms SuperpermLowerBounds.exists_stdConfig
#print axioms SuperpermLowerBounds.covers_length_gt_of_no_stdConfig
#print axioms SuperpermLowerBounds.exists_stdConfig_of_covers
#print axioms SuperpermLowerBounds.exists_stdConfig_noT4
#print axioms SuperpermLowerBounds.covers_length_gt_of_no_stdConfig_noT4
#print axioms SuperpermLowerBounds.NConfig.Valid.exists_noT4
#print axioms SuperpermLowerBounds.NConfig.Valid.exists_word
#print axioms SuperpermLowerBounds.no_stdConfig_iff
#print axioms SuperpermLowerBounds.no_stdConfig_noT4_iff
#print axioms SuperpermLowerBounds.exists_optimal_stdConfig
#print axioms SuperpermLowerBounds.NConfig.Valid.factorial_le_cost
