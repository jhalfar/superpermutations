import Mathlib.Data.Finset.Card
import LowerBounds.KDefs
import LowerBounds.J15Search

/-!
# The search of `J15Search.lean` is complete

`JAlong … i t r d a b m z last usedC rest`: the rule holds along the rows `rest` that continue a
prefix of piece `i` with counters `t`, `r`, `d`, needed value `a`, weight `b`, record `m`, first
entry `z`, last entry `last` and blocks `usedC`.  A row of kind `0` or `1` continues the piece by a
link of weight 3 or 4; a row of any other kind starts the next piece, and then the prefix is the
whole piece.  At the end of `rest` the prefix is the whole last piece and has the needed value.
The conditions are those that the engine tests, on words.

`not_along_of_parts`: if every part of the search answers `false`, the rule holds along no list
of rows that starts at the word `1 2 … k` and whose blocks obey the bound on shared classes
(`Bud`).

The marks.  A walk restores the table of marks exactly (`Id1`: a result is "found" or the table
that was given), so the table at a prefix has exactly the marks of the blocks on the way.  The
proof keeps three facts: every mark is the class of a block so far (`MInv`), every mark of the
current piece is the class of a block of the piece (`MC`), and no mark is larger than the number
of the current piece (`MB`).

Shared classes.  `clsCount l` is the number of classes of the words `l`.  `Bud bm du used rest`
says `du + |rest| + clsCount used ≤ bm + clsCount (used ++ rest)`: of the blocks `rest` still to
come, at most `bm - du` lie in a class that was seen before them.  A block whose class is marked
is such a block, so the engine's count `du` stays below `bm` when it meets one.
-/

namespace SuperpermLowerBounds
namespace J15

open S (PermW WLink DoorEq)
open PS (TRow Enc MInv all marks0)

/-! ### The table of marks -/

theorem ba_ext {A B : ByteArray} (h : A.data = B.data) : A = B := by
  cases A
  cases B
  simp_all

/-- Writing a mark and writing the old mark back gives the table back. -/
theorem set!_restore (M : ByteArray) (j : ℕ) (v : UInt8) :
    (M.set! j v).set! j (M.get! j) = M := by
  have h : ((M.set! j v).set! j (M.get! j)).data = M.data := by
    rw [S.data_set!, S.data_set!, S.get!_eq]
    apply Array.ext_getElem?
    intro i
    rw [Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
    by_cases hji : j = i
    · subst hji
      by_cases h2 : j < M.data.size
      · have h3 : j < M.size := by rw [← ByteArray.size_data]; exact h2
        simp [h3]
      · have h3 : ¬ j < M.size := by rw [← ByteArray.size_data]; exact h2
        simp [h3]
    · simp [hji]
  exact ba_ext h

/-- A result of a part of the search: found, or the table that was given. -/
def Id1 (M' M : ByteArray) : Prop := M'.size = 0 ∨ M' = M

theorem Id1.trans {A B C : ByteArray} (h1 : Id1 A B) (h2 : Id1 B C) : Id1 A C := by
  rcases h1 with h | h
  · exact Or.inl h
  · rw [h]
    exact h2

/-- Every mark of the current piece is the class index of one of the words of `usedC`. -/
def MC (enc : List ℕ → ℕ) (ci : ℕ → ℕ) (M : ByteArray) (pm : UInt8) (usedC : List (List ℕ)) :
    Prop :=
  ∀ j, M.get! j = pm → ∃ u ∈ usedC, j = ci (enc u)

/-- No mark is larger than `p`. -/
def MB (M : ByteArray) (p : ℕ) : Prop := ∀ j, (M.get! j).toNat ≤ p

theorem minv_setv {enc : List ℕ → ℕ} {ci : ℕ → ℕ} {M : ByteArray} {used : List (List ℕ)}
    (h : MInv enc ci M used) (v : List ℕ) (x : UInt8) :
    MInv enc ci (M.set! (ci (enc v)) x) (used ++ [v]) := by
  intro j hj
  rcases S.marked_set M _ j x hj with h1 | h1
  · exact ⟨v, by simp, h1⟩
  · obtain ⟨u, hu, he⟩ := h j h1
    exact ⟨u, List.mem_append_left _ hu, he⟩

theorem mc_set {enc : List ℕ → ℕ} {ci : ℕ → ℕ} {M : ByteArray} {pm : UInt8}
    {usedC : List (List ℕ)} (h : MC enc ci M pm usedC) (v : List ℕ) :
    MC enc ci (M.set! (ci (enc v)) pm) pm (usedC ++ [v]) := by
  intro j hj
  rw [S.get!_set!] at hj
  by_cases hij : ci (enc v) = j
  · exact ⟨v, by simp, hij.symm⟩
  · rw [if_neg hij] at hj
    obtain ⟨u, hu, he⟩ := h j hj
    exact ⟨u, List.mem_append_left _ hu, he⟩

theorem mb_set {M : ByteArray} {p : ℕ} (h : MB M p) (i : ℕ) {pm : UInt8} (hpm : pm.toNat ≤ p) :
    MB (M.set! i pm) p := by
  intro j
  rw [S.get!_set!]
  split_ifs
  · exact hpm
  · exact Nat.zero_le _
  · exact h j

theorem toNat_ofNat8 {n : ℕ} (h : n ≤ 255) : (UInt8.ofNat n).toNat = n := by
  rw [UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

/-- A table without a mark above `p` has no mark of the piece after `p`. -/
theorem mc_of_mb {enc : List ℕ → ℕ} {ci : ℕ → ℕ} {M : ByteArray} {p : ℕ} (h : MB M p)
    (hp : p + 1 ≤ 255) : MC enc ci M (UInt8.ofNat (p + 1)) [] := by
  intro j hj
  have h1 := h j
  rw [hj, toNat_ofNat8 hp] at h1
  omega

/-! ### Classes and the bound on shared classes -/

/-- The class of a word. -/
def cls (w : List ℕ) : Quotient (List.IsRotated.setoid ℕ) := Quotient.mk _ w

theorem cls_eq {u v : List ℕ} : cls u = cls v ↔ u ~r v := Quotient.eq

open Classical in
/-- The number of classes of the words of a list. -/
noncomputable def clsCount (l : List (List ℕ)) : ℕ := (l.map cls).toFinset.card

open Classical in
theorem clsCount_append_le (l l' : List (List ℕ)) : clsCount (l ++ l') ≤ clsCount l + l'.length := by
  unfold clsCount
  rw [List.map_append, List.toFinset_append]
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left ?_ _)
  exact le_trans (List.toFinset_card_le _) (by simp)

open Classical in
theorem clsCount_le_append (l l' : List (List ℕ)) : clsCount l ≤ clsCount (l ++ l') := by
  unfold clsCount
  rw [List.map_append, List.toFinset_append]
  exact Finset.card_le_card Finset.subset_union_left

open Classical in
theorem clsCount_snoc_of_mem {l : List (List ℕ)} {w : List ℕ} (h : ∃ u ∈ l, u ~r w) :
    clsCount (l ++ [w]) = clsCount l := by
  obtain ⟨u, hu, huw⟩ := h
  unfold clsCount
  rw [List.map_append, List.toFinset_append]
  congr 1
  apply Finset.union_eq_left.mpr
  intro x hx
  simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
    insert_empty_eq, Finset.mem_singleton] at hx
  rw [hx, List.mem_toFinset, List.mem_map]
  exact ⟨u, hu, cls_eq.mpr huw⟩

open Classical in
theorem clsCount_of_pairwise {l : List (List ℕ)} (h : l.Pairwise fun a b => ¬ a ~r b) :
    clsCount l = l.length := by
  unfold clsCount
  rw [List.toFinset_card_of_nodup, List.length_map]
  rw [List.Nodup, List.pairwise_map]
  exact h.imp fun hab he => hab (cls_eq.mp he)

open Classical in
theorem clsCount_perm {l l' : List (List ℕ)} (h : l.Perm l') : clsCount l = clsCount l' := by
  unfold clsCount
  rw [List.toFinset_eq_of_perm _ _ (h.map cls)]

open Classical in
theorem clsCount_cons (a : List ℕ) (l : List (List ℕ)) :
    clsCount (a :: l) = clsCount l + (if ∃ u ∈ l, u ~r a then 0 else 1) := by
  unfold clsCount
  rw [List.map_cons, List.toFinset_cons]
  by_cases h : ∃ u ∈ l, u ~r a
  · rw [if_pos h, Finset.card_insert_of_mem]
    · rfl
    · rw [List.mem_toFinset, List.mem_map]
      obtain ⟨u, hu, hr⟩ := h
      exact ⟨u, hu, cls_eq.mpr hr⟩
  · rw [if_neg h, Finset.card_insert_of_notMem]
    intro hm
    rw [List.mem_toFinset, List.mem_map] at hm
    obtain ⟨u, hu, he⟩ := hm
    exact h ⟨u, hu, cls_eq.mp he⟩

/-- Removing words does not make more repetitions of classes. -/
theorem clsCount_sublist {l₁ l₂ : List (List ℕ)} (h : l₁.Sublist l₂) :
    l₁.length + clsCount l₂ ≤ l₂.length + clsCount l₁ := by
  induction h with
  | slnil => simp
  | cons a _ ih =>
    rw [clsCount_cons]
    simp only [List.length_cons]
    split_ifs <;> omega
  | @cons_cons l₁ l₂ a hs ih =>
    rw [clsCount_cons, clsCount_cons]
    simp only [List.length_cons]
    by_cases h1 : ∃ u ∈ l₁, u ~r a
    · obtain ⟨u, hu, hr⟩ := h1
      have h2 : ∃ u ∈ l₂, u ~r a := ⟨u, hs.subset hu, hr⟩
      have h1' : ∃ u ∈ l₁, u ~r a := ⟨u, hu, hr⟩
      rw [if_pos h2, if_pos h1']
      omega
    · rw [if_neg h1]
      split_ifs <;> omega

/-- A map that keeps the classes of the words of the list apart keeps their number. -/
theorem clsCount_map (f : List ℕ → List ℕ) : ∀ (l : List (List ℕ)),
    (∀ u ∈ l, ∀ v ∈ l, u ~r v → f u ~r f v) → (∀ u ∈ l, ∀ v ∈ l, f u ~r f v → u ~r v) →
    clsCount (l.map f) = clsCount l
  | [], _, _ => rfl
  | a :: l, h1, h2 => by
    have ih := clsCount_map f l
      (fun u hu v hv => h1 u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv))
      (fun u hu v hv => h2 u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv))
    have e : (∃ u ∈ l.map f, u ~r f a) ↔ ∃ u ∈ l, u ~r a := by
      constructor
      · rintro ⟨u', hu', hr⟩
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hu'
        exact ⟨u, hu, h2 u (List.mem_cons_of_mem _ hu) a List.mem_cons_self hr⟩
      · rintro ⟨u, hu, hr⟩
        exact ⟨f u, List.mem_map_of_mem hu,
          h1 u (List.mem_cons_of_mem _ hu) a List.mem_cons_self hr⟩
    rw [List.map_cons, clsCount_cons, clsCount_cons, ih]
    by_cases h : ∃ u ∈ l, u ~r a
    · rw [if_pos h, if_pos (e.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (e.mp h'))]

/-- The bound on shared classes, for a search that has counted `du` shared blocks among the blocks
`used` and has the blocks `rest` to come. -/
def Bud (bm du : ℕ) (used rest : List (List ℕ)) : Prop :=
  du + rest.length + clsCount used ≤ bm + clsCount (used ++ rest)

/-- A block of a class that was seen is counted, and the count was below the bound. -/
theorem Bud.old {bm du : ℕ} {used rest : List (List ℕ)} {w : List ℕ}
    (h : Bud bm du used (w :: rest)) (hw : ∃ u ∈ used, u ~r w) :
    du < bm ∧ Bud bm (du + 1) (used ++ [w]) rest := by
  unfold Bud at h ⊢
  have e : used ++ w :: rest = (used ++ [w]) ++ rest := by simp
  have h1 := clsCount_append_le (used ++ [w]) rest
  have h2 := clsCount_snoc_of_mem hw
  rw [e] at h
  simp only [List.length_cons] at h
  constructor <;> omega

/-- A block that is not counted. -/
theorem Bud.new {bm du : ℕ} {used rest : List (List ℕ)} {w : List ℕ}
    (h : Bud bm du used (w :: rest)) : Bud bm du (used ++ [w]) rest := by
  unfold Bud at h ⊢
  have e : used ++ w :: rest = (used ++ [w]) ++ rest := by simp
  have h1 := clsCount_append_le used [w]
  rw [e] at h
  simp only [List.length_cons, List.length_nil] at h h1
  omega

/-! ### The equations of the search -/

section Engine

variable {k : ℕ} {enc : List ℕ → ℕ} {ci nxt : ℕ → ℕ} {s3 s4 : ℕ → List ℕ} {jl : List ℕ} {st : ℕ}

theorem walkJ_zero (visit : ℕ → ℕ → ℕ → ByteArray → ByteArray) (pm : UInt8) (bm mk du D : ℕ)
    (M : ByteArray) : walkJ ci nxt visit pm bm 0 mk du D M = M := rfl

theorem walkJ_succ (visit : ℕ → ℕ → ℕ → ByteArray → ByteArray) (pm : UInt8)
    (bm n mk du D : ℕ) (M : ByteArray) :
    walkJ ci nxt visit pm bm (n + 1) mk du D M =
      if (mk == 0) = true then M
      else if (M.get! (ci D) == pm) = true then M
      else if (M.get! (ci D) != 0 && decide (bm ≤ du)) = true then M
      else if ((if (mk % 2 == 1) = true then
          visit n D (if (M.get! (ci D) != 0) = true then du + 1 else du) (M.set! (ci D) pm)
          else M.set! (ci D) pm).size == 0) = true then
        (if (mk % 2 == 1) = true then
          visit n D (if (M.get! (ci D) != 0) = true then du + 1 else du) (M.set! (ci D) pm)
          else M.set! (ci D) pm)
      else (walkJ ci nxt visit pm bm n (mk / 2)
        (if (M.get! (ci D) != 0) = true then du + 1 else du) (nxt D)
        (if (mk % 2 == 1) = true then
          visit n D (if (M.get! (ci D) != 0) = true then du + 1 else du) (M.set! (ci D) pm)
          else M.set! (ci D) pm)).set! (ci D) (M.get! (ci D)) := rfl

theorem scanJ_succ (M : ByteArray) (pm : UInt8) (bm n mk du D : ℕ) :
    scanJ ci nxt M pm bm (n + 1) mk du D =
      if (mk == 0) = true then false
      else if (M.get! (ci D) == pm) = true then false
      else if (M.get! (ci D) != 0 && decide (bm ≤ du)) = true then false
      else if (mk % 2 == 1) = true then true
      else scanJ ci nxt M pm bm n (mk / 2)
        (if (M.get! (ci D) != 0) = true then du + 1 else du) (nxt D) := rfl

/-- A walk gives "found" or the table back, if the search below a row does. -/
theorem walkJ_id (visit : ℕ → ℕ → ℕ → ByteArray → ByteArray)
    (hv : ∀ n e du M, Id1 (visit n e du M) M) (pm : UInt8) (bm : ℕ) :
    ∀ (n mk du D : ℕ) (M : ByteArray), Id1 (walkJ ci nxt visit pm bm n mk du D M) M := by
  intro n
  induction n with
  | zero =>
    intro mk du D M
    exact Or.inr rfl
  | succ n ih =>
    intro mk du D M
    rw [walkJ_succ]
    by_cases h1 : (mk == 0) = true
    · rw [if_pos h1]
      exact Or.inr rfl
    rw [if_neg h1]
    by_cases h2 : (M.get! (ci D) == pm) = true
    · rw [if_pos h2]
      exact Or.inr rfl
    rw [if_neg h2]
    by_cases h3 : (M.get! (ci D) != 0 && decide (bm ≤ du)) = true
    · rw [if_pos h3]
      exact Or.inr rfl
    rw [if_neg h3]
    have hvis : Id1 (if (mk % 2 == 1) = true then
          visit n D (if (M.get! (ci D) != 0) = true then du + 1 else du) (M.set! (ci D) pm)
          else M.set! (ci D) pm) (M.set! (ci D) pm) := by
      by_cases hb : (mk % 2 == 1) = true
      · rw [if_pos hb]
        exact hv _ _ _ _
      · rw [if_neg hb]
        exact Or.inr rfl
    generalize (if (mk % 2 == 1) = true then
          visit n D (if (M.get! (ci D) != 0) = true then du + 1 else du) (M.set! (ci D) pm)
          else M.set! (ci D) pm) = vis at hvis
    by_cases hz : (vis.size == 0) = true
    · rw [if_pos hz]
      exact Or.inl (by simpa using hz)
    · rw [if_neg hz]
      rcases ih (mk / 2) (if (M.get! (ci D) != 0) = true then du + 1 else du) (nxt D) vis
        with h | h
      · left
        rw [ByteArray.size_set!]
        exact h
      · rw [h]
        rcases hvis with h' | h'
        · exact absurd (by simp [h']) hz
        · right
          rw [h']
          exact set!_restore M _ _

theorem walkG_id (visit : ℕ → ℕ → ℕ → ByteArray → ByteArray)
    (hv : ∀ n e du M, Id1 (visit n e du M) M) (pm : UInt8) (bm n mk du D : ℕ) (M : ByteArray) :
    Id1 (walkG ci nxt visit pm bm n mk du D M) M := by
  unfold walkG
  split_ifs
  · exact walkJ_id visit hv pm bm n mk du D M
  · exact Or.inr rfl

theorem all_id (w : ℕ → ByteArray → ByteArray) (hw : ∀ D M, Id1 (w D M) M) :
    ∀ (Ds : List ℕ) (M : ByteArray), Id1 (all w Ds M) M
  | [], _ => Or.inr rfl
  | D :: Ds, M => by
    rw [PS.all_cons]
    by_cases hz : (w D M).size = 0
    · rw [if_pos hz]
      exact Or.inl hz
    · rw [if_neg hz]
      rcases hw D M with h | h
      · exact absurd h hz
      · rw [h]
        exact all_id w hw Ds M

/-- One of the calls of `all` is found: then `all` is found. -/
theorem all_found (w : ℕ → ByteArray → ByteArray) (hw : ∀ D M, Id1 (w D M) M) (D : ℕ)
    (M : ByteArray) (hD : (w D M).size = 0) :
    ∀ (Ds : List ℕ), D ∈ Ds → (all w Ds M).size = 0
  | [], h => by cases h
  | D0 :: Ds, h => by
    rw [PS.all_cons]
    by_cases hz : (w D0 M).size = 0
    · rw [if_pos hz]
      exact hz
    · rw [if_neg hz]
      rcases hw D0 M with h1 | h1
      · exact absurd h1 hz
      · rw [h1]
        rcases List.mem_cons.mp h with h' | h'
        · rw [h'] at hD
          exact absurd hD hz
        · exact all_found w hw D M hD Ds h'

/-! ### The search follows a row -/

/-- What the walk does at the block `v` of a row: the block is not in the piece, the bound on
shared blocks lets it pass, and the new count keeps the bound. -/
theorem block_ok (E : Enc k enc ci nxt s3 s4 jl st) {pm : UInt8} {bm du : ℕ} {M : ByteArray}
    {usedA usedX usedC rest : List (List ℕ)} {v : List ℕ} (hv : PermW k v)
    (hM : MInv enc ci M usedA) (hC : MC enc ci M pm usedC) (hsub : ∀ u ∈ usedA, u ∈ usedX)
    (husedA : ∀ u ∈ usedA, PermW k u) (husedC : ∀ u ∈ usedC, PermW k u)
    (hnew : ∀ u ∈ usedC, ¬ u ~r v) (hbud : Bud bm du usedX (v :: rest)) :
    ¬ (M.get! (ci (enc v)) == pm) = true ∧
      ¬ (M.get! (ci (enc v)) != 0 && decide (bm ≤ du)) = true ∧
      Bud bm (if (M.get! (ci (enc v)) != 0) = true then du + 1 else du) (usedX ++ [v]) rest := by
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨u, hu, he⟩ := hC _ (by simpa using h)
    exact hnew u hu (E.ci_inj u v (husedC u hu) hv he.symm)
  · by_cases h0 : M.get! (ci (enc v)) = 0
    · have e : (if (M.get! (ci (enc v)) != 0) = true then du + 1 else du) = du := by simp [h0]
      refine ⟨by simp [h0], ?_⟩
      rw [e]
      exact hbud.new
    · obtain ⟨u, hu, he⟩ := hM _ h0
      have hold := hbud.old ⟨u, hsub u hu, E.ci_inj u v (husedA u hu) hv he.symm⟩
      refine ⟨?_, ?_⟩
      · have := hold.1
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_le]
        intro _
        exact this
      · have e : (if (M.get! (ci (enc v)) != 0) = true then du + 1 else du) = du + 1 := by
          simp [h0]
        rw [e]
        exact hold.2

/-- The look at the marks sees a row `v :: R`, if the mask has the bit of this row. -/
theorem scanJ_true (E : Enc k enc ci nxt s3 s4 jl st) (pm : UInt8) (bm : ℕ) (M : ByteArray)
    (usedA usedC : List (List ℕ)) (hM : MInv enc ci M usedA) (hC : MC enc ci M pm usedC)
    (husedA : ∀ u ∈ usedA, PermW k u) (husedC : ∀ u ∈ usedC, PermW k u) :
    ∀ (R : List (List ℕ)) (n mk du : ℕ) (v : List ℕ) (usedX later : List (List ℕ)),
      R.length ≤ n → (mk / 2 ^ R.length) % 2 = 1 → (∀ w ∈ v :: R, PermW k w) →
      List.IsChain (DoorEq k) (v :: R) → (∀ u ∈ usedA, u ∈ usedX) →
      (∀ u ∈ usedC, ∀ w ∈ v :: R, ¬ u ~r w) → Bud bm du usedX ((v :: R) ++ later) →
      scanJ ci nxt M pm bm (n + 1) mk du (enc v) = true := by
  intro R
  induction R with
  | nil =>
    intro n mk du v usedX later _ hbit hperm _ hsub hnew hbud
    have hv := hperm v List.mem_cons_self
    obtain ⟨b1, b2, _⟩ := block_ok E hv hM hC hsub husedA husedC
      (fun u hu => hnew u hu v List.mem_cons_self) hbud
    have hb : (mk % 2 == 1) = true := by simpa using hbit
    have hmk : ¬ (mk == 0) = true := by
      simp only [beq_iff_eq] at hb ⊢
      omega
    rw [scanJ_succ, if_neg hmk, if_neg b1, if_neg b2, if_pos hb]
  | cons v' R' ih =>
    intro n mk du v usedX later hn hbit hperm hdoor hsub hnew hbud
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
    have hv := hperm v List.mem_cons_self
    have hdc := List.isChain_cons_cons.mp hdoor
    obtain ⟨b1, b2, b3⟩ := block_ok E hv hM hC hsub husedA husedC
      (fun u hu => hnew u hu v List.mem_cons_self) hbud
    have hmk : ¬ (mk == 0) = true := by
      intro h
      rw [beq_iff_eq.mp h] at hbit
      simp at hbit
    have hbit' : (mk / 2 / 2 ^ R'.length) % 2 = 1 := by
      have e : mk / 2 / 2 ^ R'.length = mk / 2 ^ (v' :: R').length := by
        rw [Nat.div_div_eq_div_mul, List.length_cons, Nat.pow_succ, Nat.mul_comm]
      rw [e]
      exact hbit
    rw [scanJ_succ, if_neg hmk, if_neg b1, if_neg b2]
    by_cases hb : (mk % 2 == 1) = true
    · rw [if_pos hb]
    · rw [if_neg hb, E.nxt_eq v v' hv hdc.1]
      exact ih m (mk / 2) _ v' (usedX ++ [v]) later
        (by simp only [List.length_cons] at hn; omega) hbit'
        (fun w hw => hperm w (List.mem_cons_of_mem _ hw)) hdc.2
        (fun u hu => List.mem_append_left _ (hsub u hu))
        (fun u hu w hw => hnew u hu w (List.mem_cons_of_mem _ hw)) b3

/-- The walk that starts at the first block of a row `v :: R` finds what the search below the
piece extended by that row finds, if the mask has the bit of this row. -/
theorem walkJ_complete (E : Enc k enc ci nxt s3 s4 jl st)
    (visit : ℕ → ℕ → ℕ → ByteArray → ByteArray) (hvid : ∀ n e du M, Id1 (visit n e du M) M)
    (pm : UInt8) (p : ℕ) (hpm : pm.toNat ≤ p) (bm : ℕ) :
    ∀ (R : List (List ℕ)) (n mk du : ℕ) (v : List ℕ) (M : ByteArray)
      (usedA usedC later : List (List ℕ)),
      R.length ≤ n → (mk / 2 ^ R.length) % 2 = 1 → (∀ w ∈ v :: R, PermW k w) →
      List.IsChain (DoorEq k) (v :: R) → MInv enc ci M usedA → MC enc ci M pm usedC → MB M p →
      (∀ u ∈ usedA, PermW k u) → (∀ u ∈ usedC, PermW k u) →
      (∀ u ∈ usedC, ∀ w ∈ v :: R, ¬ u ~r w) → List.Pairwise (fun a b => ¬ a ~r b) (v :: R) →
      Bud bm du usedA ((v :: R) ++ later) →
      (∀ M' du', MInv enc ci M' (usedA ++ v :: R) → MC enc ci M' pm (usedC ++ v :: R) →
        MB M' p → Bud bm du' (usedA ++ v :: R) later →
        (visit (n - R.length) (enc ((v :: R).getLast (List.cons_ne_nil v R))) du' M').size = 0) →
      (walkJ ci nxt visit pm bm (n + 1) mk du (enc v) M).size = 0 := by
  intro R
  induction R with
  | nil =>
    intro n mk du v M usedA usedC later _ hbit hperm _ hM hC hB husedA husedC hnew _ hbud hfin
    have hv := hperm v List.mem_cons_self
    obtain ⟨b1, b2, b3⟩ := block_ok E hv hM hC (fun u hu => hu) husedA husedC
      (fun u hu => hnew u hu v List.mem_cons_self) hbud
    have hb : (mk % 2 == 1) = true := by simpa using hbit
    have hmk : ¬ (mk == 0) = true := by
      simp only [beq_iff_eq] at hb ⊢
      omega
    have hf := hfin _ _ (minv_setv hM v pm) (mc_set hC v) (mb_set hB _ hpm) b3
    have hf' : ((visit n (enc v) (if (M.get! (ci (enc v)) != 0) = true then du + 1 else du)
        (M.set! (ci (enc v)) pm)).size == 0) = true := by
      simpa using hf
    rw [walkJ_succ, if_neg hmk, if_neg b1, if_neg b2, if_pos hb, if_pos hf']
    exact hf
  | cons v' R' ih =>
    intro n mk du v M usedA usedC later hn hbit hperm hdoor hM hC hB husedA husedC hnew hpw hbud
      hfin
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
    have hv := hperm v List.mem_cons_self
    have hdc := List.isChain_cons_cons.mp hdoor
    have hpc := List.pairwise_cons.mp hpw
    obtain ⟨b1, b2, b3⟩ := block_ok E hv hM hC (fun u hu => hu) husedA husedC
      (fun u hu => hnew u hu v List.mem_cons_self) hbud
    have hmk : ¬ (mk == 0) = true := by
      intro h
      rw [beq_iff_eq.mp h] at hbit
      simp at hbit
    have hbit' : (mk / 2 / 2 ^ R'.length) % 2 = 1 := by
      have e : mk / 2 / 2 ^ R'.length = mk / 2 ^ (v' :: R').length := by
        rw [Nat.div_div_eq_div_mul, List.length_cons, Nat.pow_succ, Nat.mul_comm]
      rw [e]
      exact hbit
    have hvis : Id1 (if (mk % 2 == 1) = true then
          visit (m + 1) (enc v) (if (M.get! (ci (enc v)) != 0) = true then du + 1 else du)
            (M.set! (ci (enc v)) pm)
          else M.set! (ci (enc v)) pm) (M.set! (ci (enc v)) pm) := by
      by_cases hb : (mk % 2 == 1) = true
      · rw [if_pos hb]
        exact hvid _ _ _ _
      · rw [if_neg hb]
        exact Or.inr rfl
    rw [walkJ_succ, if_neg hmk, if_neg b1, if_neg b2]
    generalize (if (mk % 2 == 1) = true then
          visit (m + 1) (enc v) (if (M.get! (ci (enc v)) != 0) = true then du + 1 else du)
            (M.set! (ci (enc v)) pm)
          else M.set! (ci (enc v)) pm) = vis at hvis
    by_cases hz : (vis.size == 0) = true
    · rw [if_pos hz]
      simpa using hz
    · rw [if_neg hz, ByteArray.size_set!, E.nxt_eq v v' hv hdc.1]
      have hvis' : vis = M.set! (ci (enc v)) pm := by
        rcases hvis with h | h
        · exact absurd (by simp [h]) hz
        · exact h
      rw [hvis']
      have hA' : ∀ u ∈ usedA ++ [v], PermW k u := by
        intro u hu
        rcases List.mem_append.mp hu with h | h
        · exact husedA u h
        · rw [List.mem_singleton.mp h]
          exact hv
      have hC' : ∀ u ∈ usedC ++ [v], PermW k u := by
        intro u hu
        rcases List.mem_append.mp hu with h | h
        · exact husedC u h
        · rw [List.mem_singleton.mp h]
          exact hv
      apply ih m (mk / 2) _ v' _ (usedA ++ [v]) (usedC ++ [v]) later
        (by simp only [List.length_cons] at hn; omega) hbit'
        (fun w hw => hperm w (List.mem_cons_of_mem _ hw)) hdc.2 (minv_setv hM v pm) (mc_set hC v)
        (mb_set hB _ hpm) hA' hC'
        (by
          intro u hu w hw
          rcases List.mem_append.mp hu with h | h
          · exact hnew u h w (List.mem_cons_of_mem _ hw)
          · rw [List.mem_singleton.mp h]
            exact hpc.1 w hw)
        hpc.2 b3
      intro M' du' hM' hC'' hB' hbud'
      have e : usedA ++ [v] ++ v' :: R' = usedA ++ v :: v' :: R' := by simp
      have e' : usedC ++ [v] ++ v' :: R' = usedC ++ v :: v' :: R' := by simp
      rw [e] at hM' hbud'
      rw [e'] at hC''
      have h := hfin M' du' hM' hC'' hB' hbud'
      rw [List.getLast_cons (List.cons_ne_nil v' R')] at h
      have e2 : m + 1 - (v' :: R').length = m - R'.length := by
        simp only [List.length_cons]
        omega
      rw [e2] at h
      exact h

/-- The walk that is entered only after the look at the marks finds what the walk finds. -/
theorem walkG_complete (E : Enc k enc ci nxt s3 s4 jl st) (hk : 2 ≤ k)
    (visit : ℕ → ℕ → ℕ → ByteArray → ByteArray) (hvid : ∀ n e du M, Id1 (visit n e du M) M)
    (pm : UInt8) (p : ℕ) (hpm : pm.toNat ≤ p)
    (bm mk du : ℕ) (M : ByteArray) (v : List ℕ) (R usedA usedC later : List (List ℕ))
    (hR : R.length ≤ k - 2) (hbit : (mk / 2 ^ R.length) % 2 = 1)
    (hperm : ∀ w ∈ v :: R, PermW k w) (hdoor : List.IsChain (DoorEq k) (v :: R))
    (hM : MInv enc ci M usedA) (hC : MC enc ci M pm usedC) (hB : MB M p)
    (husedA : ∀ u ∈ usedA, PermW k u) (husedC : ∀ u ∈ usedC, PermW k u)
    (hnew : ∀ u ∈ usedC, ∀ w ∈ v :: R, ¬ u ~r w)
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) (v :: R))
    (hbud : Bud bm du usedA ((v :: R) ++ later))
    (hfin : ∀ M' du', MInv enc ci M' (usedA ++ v :: R) → MC enc ci M' pm (usedC ++ v :: R) →
      MB M' p → Bud bm du' (usedA ++ v :: R) later →
      (visit (k - 2 - R.length) (enc ((v :: R).getLast (List.cons_ne_nil v R))) du' M').size = 0) :
    (walkG ci nxt visit pm bm (k - 1) mk du (enc v) M).size = 0 := by
  have e : k - 1 = k - 2 + 1 := by omega
  unfold walkG
  rw [e, if_pos (scanJ_true E pm bm M usedA usedC hM hC husedA husedC R (k - 2) mk du v usedA later
    hR hbit hperm hdoor (fun u hu => hu) hnew hbud)]
  exact walkJ_complete E visit hvid pm p hpm bm R (k - 2) mk du v M usedA usedC
    later hR hbit hperm hdoor hM hC hB husedA husedC hnew hpw hbud hfin

/-- The calls for one list of successors find the row `v :: R`, if `v` is in the list. -/
theorem step_found (E : Enc k enc ci nxt s3 s4 jl st) (hk : 2 ≤ k)
    (visit : ℕ → ℕ → ℕ → ℕ → ByteArray → ByteArray)
    (hvid : ∀ D n e du M, Id1 (visit D n e du M) M) (pm : UInt8) (p : ℕ) (hpm : pm.toNat ≤ p)
    (bm mk du : ℕ) (l : List ℕ) (M : ByteArray) (v : List ℕ) (R usedA usedC later : List (List ℕ))
    (hl : enc v ∈ l) (hR : R.length ≤ k - 2) (hbit : (mk / 2 ^ R.length) % 2 = 1)
    (hperm : ∀ w ∈ v :: R, PermW k w) (hdoor : List.IsChain (DoorEq k) (v :: R))
    (hM : MInv enc ci M usedA) (hC : MC enc ci M pm usedC) (hB : MB M p)
    (husedA : ∀ u ∈ usedA, PermW k u) (husedC : ∀ u ∈ usedC, PermW k u)
    (hnew : ∀ u ∈ usedC, ∀ w ∈ v :: R, ¬ u ~r w)
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) (v :: R))
    (hbud : Bud bm du usedA ((v :: R) ++ later))
    (hfin : ∀ M' du', MInv enc ci M' (usedA ++ v :: R) → MC enc ci M' pm (usedC ++ v :: R) →
      MB M' p → Bud bm du' (usedA ++ v :: R) later →
      (visit (enc v) (k - 2 - R.length) (enc ((v :: R).getLast (List.cons_ne_nil v R))) du'
        M').size = 0) :
    (all (fun D M' => walkG ci nxt (visit D) pm bm (k - 1) mk du D M') l M).size = 0 :=
  all_found _ (fun D M' => walkG_id (visit D) (hvid D) pm bm (k - 1) mk du D M') (enc v) M
    (walkG_complete E hk (visit (enc v)) (hvid (enc v)) pm p hpm bm mk du M v R usedA usedC later
      hR hbit hperm hdoor hM hC hB husedA husedC hnew hpw hbud hfin) l hl

/-- Bit `j` of the mask is the answer for the row with `j + 1` blocks. -/
theorem mkMask_bit (p : ℕ → Bool) : ∀ (n j : ℕ), j < n → p (n - 1 - j) = true →
    (mkMask p n / 2 ^ j) % 2 = 1
  | 0, j, hj, _ => absurd hj (Nat.not_lt_zero _)
  | n + 1, 0, _, h => by
    have e : n + 1 - 1 - 0 = n := by omega
    rw [e] at h
    simp only [mkMask, pow_zero, Nat.div_one, h, if_true]
    omega
  | n + 1, j + 1, hj, h => by
    have e0 : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
    rw [e0] at h
    have ih := mkMask_bit p n j (by omega) h
    have e : (2 * mkMask p n + (if p n = true then 1 else 0)) / 2 ^ (j + 1)
        = mkMask p n / 2 ^ j := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, ← Nat.div_div_eq_div_mul]
      congr 1
      split_ifs <;> omega
    simp only [mkMask]
    rw [e]
    exact ih

/-! ### The search below a prefix, in three steps -/

variable {np bm : ℕ} {kd lo hi : ℕ → ℕ} {bestLe : ℕ → ℕ → ℤ → Bool}
  {gLe : ℕ → ℕ → ℕ → ℤ → Bool} {fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool} {gi gr nt tp : ℕ}
  {gate early : ℕ → ℕ → ℕ → Bool} {ea : ℕ → ℕ → Bool} {GP EP : ℕ → ℕ → ℕ → Prop}

/-- `M1` if it is "found", otherwise `f M1`. -/
def seqB (M1 : ByteArray) (f : ByteArray → ByteArray) : ByteArray :=
  if M1.size == 0 then M1 else f M1

/-- The prefix may be the whole piece. -/
def compCond (s3 : ℕ → List ℕ) (kb np : ℕ) (kd lo hi : ℕ → ℕ) (bestLe : ℕ → ℕ → ℤ → Bool)
    (early : ℕ → ℕ → ℕ → Bool) (i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ) (z q : ℕ) : Bool :=
  compOk np bestLe (fun i' r' => early i' r' (q + 8192 * d)) i r a (b - (d + kb * t)) (vOf kb t r d) &&
    (if kd i == 0 then
      decide (2 ≤ r) && decide (lo i ≤ d) && decide (d ≤ hi i) && (s3 q).contains z
    else decide (m < vOf kb t r d))

/-- The prefix as the whole piece. -/
def compPart (ci nxt : ℕ → ℕ) (s3 : ℕ → List ℕ) (jl : List ℕ) (kb np bm : ℕ)
    (kd lo hi : ℕ → ℕ) (bestLe : ℕ → ℕ → ℤ → Bool) (gLe : ℕ → ℕ → ℕ → ℤ → Bool)
    (fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool) (early : ℕ → ℕ → ℕ → Bool)
    (rec : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℕ → ℕ → ℕ → ByteArray → ByteArray)
    (i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ) (z q du : ℕ) (M : ByteArray) : ByteArray :=
  if compCond s3 kb np kd lo hi bestLe early i t r d a b m z q then
    if i + 1 == np then ByteArray.empty
    else
      all (fun D M' => walkG ci nxt
        (fun n e du' M'' =>
          rec (i + 1) 0 1 n (a - vOf kb t r d) (b - (d + kb * t)) (-(kb : ℤ)) D e du' M'')
        (UInt8.ofNat (i + 2)) bm kb
        (mkMask (fun n => decide (n ≤ b - (d + kb * t)) &&
          live kb np kd bestLe gLe fLe (fun _ _ => true) (i + 1) 0 1 n (a - vOf kb t r d)
            (b - (d + kb * t)) (-(kb : ℤ))) kb) du D M') jl M
  else M

/-- The prefix continued with links of weight 3. -/
def k3Part (ci nxt : ℕ → ℕ) (s3 : ℕ → List ℕ) (kb np bm : ℕ)
    (kd : ℕ → ℕ) (bestLe : ℕ → ℕ → ℤ → Bool) (gLe : ℕ → ℕ → ℕ → ℤ → Bool)
    (fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool)
    (rec : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℕ → ℕ → ℕ → ByteArray → ByteArray)
    (i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ) (z q du : ℕ) (M : ByteArray) : ByteArray :=
  if k3Ok gLe fLe i (kd i) t r d a b (b - (d + kb * t)) (vOf kb t r d) then
    all (fun D M' => walkG ci nxt
      (fun n e du' M'' => rec i t (r + 1) (d + n) a b (max m (vOf kb t r d)) z e du' M'')
      (UInt8.ofNat (i + 1)) bm kb
      (mkMask (fun n => decide (d + kb * t + n ≤ b) &&
        live kb np kd bestLe gLe fLe (fun _ _ => true) i t (r + 1) (d + n) a b (max m (vOf kb t r d))) kb)
      du D M') (s3 q) M
  else M

/-- The prefix continued with links of weight 4. -/
def k4Part (ci nxt : ℕ → ℕ) (s4 : ℕ → List ℕ) (kb np bm : ℕ)
    (kd : ℕ → ℕ) (bestLe : ℕ → ℕ → ℤ → Bool) (gLe : ℕ → ℕ → ℕ → ℤ → Bool)
    (fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool)
    (rec : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℕ → ℕ → ℕ → ByteArray → ByteArray)
    (i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ) (z q du : ℕ) (M : ByteArray) : ByteArray :=
  if k4Ok gLe kb i (kd i) t a (b - (d + kb * t)) (vOf kb t r d) then
    all (fun D M' => walkG ci nxt
      (fun n e du' M'' => rec i (t + 1) (r + 1) (d + n) a b (max m (vOf kb t r d)) z e du' M'')
      (UInt8.ofNat (i + 1)) bm kb
      (mkMask (fun n => decide (d + kb * t + kb + n ≤ b) &&
        live kb np kd bestLe gLe fLe (fun _ _ => true) i (t + 1) (r + 1) (d + n) a b
          (max m (vOf kb t r d))) kb)
      du D M') (s4 q) M
  else M

theorem go_zero (kb i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ) (z q du : ℕ) (M : ByteArray) :
    go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early 0 i t r d a b m z q du M
      = ByteArray.empty := rfl

theorem go_succ (kb fuel i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ) (z q du : ℕ) (M : ByteArray) :
    go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early (fuel + 1) i t r d a b m z q
        du M =
      if gate i r (q + 8192 * d) = true then
        seqB (compPart ci nxt s3 jl kb np bm kd lo hi bestLe gLe fLe early
            (go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early fuel)
            i t r d a b m z q du M)
          (fun M1 => seqB (k3Part ci nxt s3 kb np bm kd bestLe gLe fLe
              (go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early fuel)
              i t r d a b m z q du M1)
            (fun M2 => k4Part ci nxt s4 kb np bm kd bestLe gLe fLe
              (go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early fuel)
              i t r d a b m z q du M2))
      else M := rfl

theorem seqB_id {M1 M : ByteArray} {f : ByteArray → ByteArray} (h1 : Id1 M1 M)
    (hf : ∀ X, Id1 (f X) X) : Id1 (seqB M1 f) M := by
  unfold seqB
  by_cases hz : (M1.size == 0) = true
  · rw [if_pos hz]
    exact Or.inl (by simpa using hz)
  · rw [if_neg hz]
    exact (hf M1).trans h1

theorem seqB_found {M1 : ByteArray} (f : ByteArray → ByteArray) (h : M1.size = 0) :
    (seqB M1 f).size = 0 := by
  unfold seqB
  rw [if_pos (by simpa using h)]
  exact h

/-- If the first step is not "found" it gives the table back, and the next step decides. -/
theorem seqB_next {M1 M : ByteArray} {f : ByteArray → ByteArray} (h1 : Id1 M1 M)
    (hf : (f M).size = 0) : (seqB M1 f).size = 0 := by
  rcases h1 with h | h
  · exact seqB_found f h
  · rw [h]
    unfold seqB
    split_ifs with hz
    · simpa using hz
    · exact hf

section Ids

variable {kb : ℕ} {rec : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℕ → ℕ → ℕ → ByteArray → ByteArray}

theorem comp_id (hrec : ∀ i t r d a b m z q du M, Id1 (rec i t r d a b m z q du M) M)
    (i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ) (z q du : ℕ) (M : ByteArray) :
    Id1 (compPart ci nxt s3 jl kb np bm kd lo hi bestLe gLe fLe early rec i t r d a b m z q du
      M) M := by
  unfold compPart
  split_ifs
  · exact Or.inl ByteArray.size_empty
  · exact all_id _ (fun D M' => walkG_id _ (fun n e du' M'' => hrec _ _ _ _ _ _ _ _ _ _ _) _ _ _
      _ _ _ _) _ _
  · exact Or.inr rfl

theorem k3_id (hrec : ∀ i t r d a b m z q du M, Id1 (rec i t r d a b m z q du M) M)
    (i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ) (z q du : ℕ) (M : ByteArray) :
    Id1 (k3Part ci nxt s3 kb np bm kd bestLe gLe fLe rec i t r d a b m z q du M) M := by
  unfold k3Part
  split_ifs
  · exact all_id _ (fun D M' => walkG_id _ (fun n e du' M'' => hrec _ _ _ _ _ _ _ _ _ _ _) _ _ _
      _ _ _ _) _ _
  · exact Or.inr rfl

theorem k4_id (hrec : ∀ i t r d a b m z q du M, Id1 (rec i t r d a b m z q du M) M)
    (i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ) (z q du : ℕ) (M : ByteArray) :
    Id1 (k4Part ci nxt s4 kb np bm kd bestLe gLe fLe rec i t r d a b m z q du M) M := by
  unfold k4Part
  split_ifs
  · exact all_id _ (fun D M' => walkG_id _ (fun n e du' M'' => hrec _ _ _ _ _ _ _ _ _ _ _) _ _ _
      _ _ _ _) _ _
  · exact Or.inr rfl

end Ids

/-- The search gives "found" or the table back. -/
theorem go_id (kb : ℕ) : ∀ (fuel i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ) (z q du : ℕ)
    (M : ByteArray),
    Id1 (go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early fuel i t r d a b m z q du
      M) M := by
  intro fuel
  induction fuel with
  | zero =>
    intro i t r d a b m z q du M
    rw [go_zero]
    exact Or.inl ByteArray.size_empty
  | succ fuel ih =>
    intro i t r d a b m z q du M
    rw [go_succ]
    split_ifs
    · exact seqB_id (comp_id ih _ _ _ _ _ _ _ _ _ _ _)
        (fun M1 => seqB_id (k3_id ih _ _ _ _ _ _ _ _ _ _ _)
          (fun M2 => k4_id ih _ _ _ _ _ _ _ _ _ _ _))
    · exact Or.inr rfl

/-! ### The rule along a list of rows -/

/-- The gate of part `tp` of `nt` at a prefix with `r` rows of piece `i`. -/
def Gate (gi gr nt tp i r key : ℕ) : Prop := i ≠ gi ∨ r ≠ gr ∨ key % nt = tp

/-- A piece `i` that is complete with `r` rows and the key `key` is followed in part `tp`: the
gate is not in the piece, or the piece has passed it, or the key of the last prefix is `tp`. -/
def Early (gi gr nt tp i r key : ℕ) : Prop := i ≠ gi ∨ gr ≤ r ∨ key % nt = tp

/-- A row: at most `k - 1` blocks of permutation words, joined by doors, in different classes. -/
def RowOk (k : ℕ) (v : List ℕ) (R : List (List ℕ)) : Prop :=
  R.length ≤ k - 2 ∧ (∀ w ∈ v :: R, PermW k w) ∧ List.IsChain (DoorEq k) (v :: R) ∧
    List.Pairwise (fun a b => ¬ a ~r b) (v :: R)

/-- The prefix may be the whole piece `i`: a ring has at least two rows, its holes are in the
window and it closes; a sequence is a record. -/
def FinOk (k : ℕ) (kd lo hi : ℕ → ℕ) (i r d : ℕ) (m v : ℤ) (z last : List ℕ) : Prop :=
  if kd i = 0 then 2 ≤ r ∧ lo i ≤ d ∧ d ≤ hi i ∧ WLink k 3 last z else m < v

/-- The rule holds along the rows `rest` (see the head of the file). -/
def JAlong (k np : ℕ) (enc : List ℕ → ℕ) (kd lo hi : ℕ → ℕ) (bestLe : ℕ → ℕ → ℤ → Bool)
    (gLe : ℕ → ℕ → ℕ → ℤ → Bool) (fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool)
    (GP EP : ℕ → ℕ → ℕ → Prop) :
    ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → List ℕ → List ℕ → List (List ℕ) → List TRow → Prop
  | i, t, r, d, a, _, m, z, last, _, [] =>
    GP i r (enc last + 8192 * d) ∧
      FinOk k kd lo hi i r d m (vOf (k - 1) t r d) z last ∧ i + 1 = np ∧ a ≤ vOf (k - 1) t r d
  | _, _, _, _, _, _, _, _, _, _, (_, []) :: _ => False
  | i, t, r, d, a, b, m, z, last, usedC, (0, v :: R) :: rest =>
    GP i r (enc last + 8192 * d) ∧ RowOk k v R ∧
      k3Ok gLe fLe i (kd i) t r d a b (b - (d + (k - 1) * t)) (vOf (k - 1) t r d) = true ∧
      WLink k 3 last v ∧ (∀ u ∈ usedC, ∀ w ∈ v :: R, ¬ u ~r w) ∧
      d + (k - 1) * t + (k - 2 - R.length) ≤ b ∧
      JAlong k np enc kd lo hi bestLe gLe fLe GP EP i t (r + 1) (d + (k - 2 - R.length)) a b
        (max m (vOf (k - 1) t r d)) z ((v :: R).getLast (List.cons_ne_nil v R)) (usedC ++ v :: R)
        rest
  | i, t, r, d, a, b, m, z, last, usedC, (1, v :: R) :: rest =>
    GP i r (enc last + 8192 * d) ∧ RowOk k v R ∧
      k4Ok gLe (k - 1) i (kd i) t a (b - (d + (k - 1) * t)) (vOf (k - 1) t r d) = true ∧
      WLink k 4 last v ∧ (∀ u ∈ usedC, ∀ w ∈ v :: R, ¬ u ~r w) ∧
      d + (k - 1) * t + (k - 1) + (k - 2 - R.length) ≤ b ∧
      JAlong k np enc kd lo hi bestLe gLe fLe GP EP i (t + 1) (r + 1)
        (d + (k - 2 - R.length)) a b (max m (vOf (k - 1) t r d)) z
        ((v :: R).getLast (List.cons_ne_nil v R)) (usedC ++ v :: R) rest
  | i, t, r, d, a, b, m, z, last, _, (_ + 2, v :: R) :: rest =>
    GP i r (enc last + 8192 * d) ∧ RowOk k v R ∧
      FinOk k kd lo hi i r d m (vOf (k - 1) t r d) z last ∧ i + 1 ≠ np ∧
      bestLe i (b - (d + (k - 1) * t)) (a - vOf (k - 1) t r d) = true ∧
      EP i r (enc last + 8192 * d) ∧ k - 2 - R.length ≤ b - (d + (k - 1) * t) ∧
      JAlong k np enc kd lo hi bestLe gLe fLe GP EP (i + 1) 0 1 (k - 2 - R.length)
        (a - vOf (k - 1) t r d) (b - (d + (k - 1) * t)) (-((k - 1 : ℕ) : ℤ)) v
        ((v :: R).getLast (List.cons_ne_nil v R)) (v :: R) rest

/-- The blocks of a list of rows. -/
def blocksR (rest : List TRow) : List (List ℕ) := (rest.map Prod.snd).flatten

theorem blocksR_cons (kdr : ℕ) (Q : List (List ℕ)) (rest : List TRow) :
    blocksR ((kdr, Q) :: rest) = Q ++ blocksR rest := rfl

theorem compOk_last {i r y : ℕ} {a v : ℤ} (h : i + 1 = np) (hav : a ≤ v) :
    compOk np bestLe ea i r a y v = true := by
  unfold compOk
  simp [h, hav]

theorem compOk_jump {i r y : ℕ} {a v : ℤ} (h : i + 1 ≠ np) (hb : bestLe i y (a - v) = true)
    (hg : ea i r = true) : compOk np bestLe ea i r a y v = true := by
  unfold compOk
  simp [h, hb, hg]

theorem shape_true (E : Enc k enc ci nxt s3 s4 jl st) {i r d : ℕ} {m v : ℤ} {z last : List ℕ}
    (hfin : FinOk k kd lo hi i r d m v z last) (hlast : PermW k last) (hz : PermW k z) :
    (if kd i == 0 then
        decide (2 ≤ r) && decide (lo i ≤ d) && decide (d ≤ hi i) &&
          (s3 (enc last)).contains (enc z)
      else decide (m < v)) = true := by
  unfold FinOk at hfin
  by_cases hc : kd i = 0
  · rw [if_pos hc] at hfin
    have hm := E.s3_mem last z hlast hz hfin.2.2.2
    simp [hc, hfin.1, hfin.2.1, hfin.2.2.1, hm]
  · rw [if_neg hc] at hfin
    simp [hc, hfin]

section Parts

variable {rec : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℕ → ℕ → ℕ → ByteArray → ByteArray}

/-- The last piece is complete and has the needed value: found. -/
theorem comp_last (E : Enc k enc ci nxt s3 s4 jl st) {i t r d : ℕ} {a : ℤ} {b : ℕ} {m : ℤ}
    {z last : List ℕ} (du : ℕ) (M : ByteArray)
    (hfin : FinOk k kd lo hi i r d m (vOf (k - 1) t r d) z last) (hlast : PermW k last)
    (hz : PermW k z) (hl : i + 1 = np) (hav : a ≤ vOf (k - 1) t r d) :
    (compPart ci nxt s3 jl (k - 1) np bm kd lo hi bestLe gLe fLe early rec i t r d a b m
      (enc z) (enc last) du M).size = 0 := by
  have h1 := compOk_last (bestLe := bestLe) (ea := (fun i' r' => early i' r' (enc last + 8192 * d))) (r := r)
    (y := b - (d + (k - 1) * t)) hl hav
  have h2 := shape_true E hfin hlast hz
  have hl' : (i + 1 == np) = true := by simpa using hl
  unfold compPart compCond
  rw [h1, h2, if_pos (show (true && true) = true from rfl), if_pos hl']
  exact ByteArray.size_empty

/-- A piece that is not the last is complete: the next piece starts at every word. -/
theorem comp_jump (E : Enc k enc ci nxt s3 s4 jl st) {i t r d : ℕ} {a : ℤ} {b : ℕ} {m : ℤ}
    {z last : List ℕ} (du : ℕ) (M : ByteArray)
    (hfin : FinOk k kd lo hi i r d m (vOf (k - 1) t r d) z last) (hlast : PermW k last)
    (hz : PermW k z) (hl : i + 1 ≠ np)
    (hb : bestLe i (b - (d + (k - 1) * t)) (a - vOf (k - 1) t r d) = true)
    (hg : early i r (enc last + 8192 * d) = true) :
    compPart ci nxt s3 jl (k - 1) np bm kd lo hi bestLe gLe fLe early rec i t r d a b m
        (enc z) (enc last) du M =
      all (fun D M' => walkG ci nxt
        (fun n e du' M'' =>
          rec (i + 1) 0 1 n (a - vOf (k - 1) t r d) (b - (d + (k - 1) * t)) (-((k - 1 : ℕ) : ℤ))
            D e du' M'')
        (UInt8.ofNat (i + 2)) bm (k - 1)
        (mkMask (fun n => decide (n ≤ b - (d + (k - 1) * t)) &&
          live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) (i + 1) 0 1 n (a - vOf (k - 1) t r d)
            (b - (d + (k - 1) * t)) (-((k - 1 : ℕ) : ℤ))) (k - 1)) du D M') jl M := by
  have h1 := compOk_jump (np := np) (bestLe := bestLe) (ea := (fun i' r' => early i' r' (enc last + 8192 * d))) hl hb hg
  have h2 := shape_true E hfin hlast hz
  have hl' : ¬ (i + 1 == np) = true := by simpa using hl
  unfold compPart compCond
  rw [h1, h2, if_pos (show (true && true) = true from rfl), if_neg hl']

theorem k3_pos {i t r d : ℕ} {a : ℤ} {b : ℕ} {m : ℤ} (z q du : ℕ) (M : ByteArray) (kb : ℕ)
    (h : k3Ok gLe fLe i (kd i) t r d a b (b - (d + kb * t)) (vOf kb t r d) = true) :
    k3Part ci nxt s3 kb np bm kd bestLe gLe fLe rec i t r d a b m z q du M =
      all (fun D M' => walkG ci nxt
        (fun n e du' M'' => rec i t (r + 1) (d + n) a b (max m (vOf kb t r d)) z e du' M'')
        (UInt8.ofNat (i + 1)) bm kb
        (mkMask (fun n => decide (d + kb * t + n ≤ b) &&
          live kb np kd bestLe gLe fLe (fun _ _ => true) i t (r + 1) (d + n) a b (max m (vOf kb t r d)))
          kb)
        du D M') (s3 q) M := by
  unfold k3Part
  rw [if_pos h]

theorem k4_pos {i t r d : ℕ} {a : ℤ} {b : ℕ} {m : ℤ} (z q du : ℕ) (M : ByteArray) (kb : ℕ)
    (h : k4Ok gLe kb i (kd i) t a (b - (d + kb * t)) (vOf kb t r d) = true) :
    k4Part ci nxt s4 kb np bm kd bestLe gLe fLe rec i t r d a b m z q du M =
      all (fun D M' => walkG ci nxt
        (fun n e du' M'' => rec i (t + 1) (r + 1) (d + n) a b (max m (vOf kb t r d)) z e du' M'')
        (UInt8.ofNat (i + 1)) bm kb
        (mkMask (fun n => decide (d + kb * t + kb + n ≤ b) &&
          live kb np kd bestLe gLe fLe (fun _ _ => true) i (t + 1) (r + 1) (d + n) a b
            (max m (vOf kb t r d))) kb)
        du D M') (s4 q) M := by
  unfold k4Part
  rw [if_pos h]

end Parts

/-- Along the rule, something is done at the prefix. -/
theorem live_of_fin {i t r d : ℕ} {a : ℤ} {b : ℕ} {m : ℤ} {z last : List ℕ}
    (hfin : FinOk k kd lo hi i r d m (vOf (k - 1) t r d) z last)
    (h1 : compOk np bestLe (fun _ _ => true) i r a (b - (d + (k - 1) * t)) (vOf (k - 1) t r d)
      = true) :
    live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) i t r d a b m = true := by
  have h0 : (if (kd i == 0) = true then decide (2 ≤ r) else decide (m < vOf (k - 1) t r d))
      = true := by
    unfold FinOk at hfin
    by_cases hc : kd i = 0
    · rw [if_pos hc] at hfin
      simp [hc, hfin.1]
    · rw [if_neg hc] at hfin
      simp [hc, hfin]
  unfold live
  rw [h0, h1]
  simp only [Bool.and_self, Bool.or_true]

theorem live_of_along : ∀ (rest : List TRow) (i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ)
    (z last : List ℕ) (usedC : List (List ℕ)),
    JAlong k np enc kd lo hi bestLe gLe fLe GP EP i t r d a b m z last usedC rest →
    live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) i t r d a b m = true
  | [], i, t, r, d, a, b, m, z, last, usedC, h => by
    simp only [JAlong] at h
    obtain ⟨_, hfin, hnp, hav⟩ := h
    exact live_of_fin hfin (compOk_last hnp hav)
  | (_, []) :: _, _, _, _, _, _, _, _, _, _, _, h => by simp [JAlong] at h
  | (0, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, h => by
    simp only [JAlong] at h
    unfold live
    rw [h.2.2.1]
    rfl
  | (1, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, h => by
    simp only [JAlong] at h
    unfold live
    rw [h.2.2.1]
    simp only [Bool.or_true, Bool.true_or]
  | (kdr + 2, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, h => by
    simp only [JAlong] at h
    obtain ⟨_, _, hfin, hnp, hb, hg, _, _⟩ := h
    exact live_of_fin hfin (compOk_jump hnp hb rfl)

/-- Along the rule the number of the piece is below the number of pieces. -/
theorem lt_of_along : ∀ (rest : List TRow) (i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ)
    (z last : List ℕ) (usedC : List (List ℕ)),
    JAlong k np enc kd lo hi bestLe gLe fLe GP EP i t r d a b m z last usedC rest → i < np
  | [], i, t, r, d, a, b, m, z, last, usedC, h => by
    simp only [JAlong] at h
    omega
  | (_, []) :: _, _, _, _, _, _, _, _, _, _, _, h => by simp [JAlong] at h
  | (0, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, h => by
    simp only [JAlong] at h
    exact lt_of_along rest _ _ _ _ _ _ _ _ _ _ h.2.2.2.2.2.2
  | (1, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, h => by
    simp only [JAlong] at h
    exact lt_of_along rest _ _ _ _ _ _ _ _ _ _ h.2.2.2.2.2.2
  | (kdr + 2, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, h => by
    simp only [JAlong] at h
    have := lt_of_along rest _ _ _ _ _ _ _ _ _ _ h.2.2.2.2.2.2.2
    omega

/-- The search finds the end of a list of rows of which it has reached a prefix, if the rule
holds along the rest. -/
theorem go_complete (E : Enc k enc ci nxt s3 s4 jl st) (hk : 2 ≤ k) (hnp : np ≤ 255)
    (hG : ∀ i r key, GP i r key → gate i r key = true)
    (hE : ∀ i r key, EP i r key → early i r key = true) :
    ∀ (rest : List TRow) (fuel i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ) (z last : List ℕ)
      (usedC usedA : List (List ℕ)) (du : ℕ) (M : ByteArray),
      PermW k last → PermW k z → (∀ u ∈ usedA, PermW k u) → (∀ u ∈ usedC, PermW k u) →
      MInv enc ci M usedA → MC enc ci M (UInt8.ofNat (i + 1)) usedC → MB M (i + 1) →
      Bud bm du usedA (blocksR rest) →
      JAlong k np enc kd lo hi bestLe gLe fLe GP EP i t r d a b m z last usedC rest →
      (go ci nxt s3 s4 jl (k - 1) np bm kd lo hi bestLe gLe fLe gate early fuel i t r d a b m
        (enc z) (enc last) du M).size = 0 := by
  intro rest
  induction rest with
  | nil =>
    intro fuel i t r d a b m z last usedC usedA du M hlast hz _ _ _ _ _ _ halong
    cases fuel with
    | zero => rw [go_zero]; exact ByteArray.size_empty
    | succ fuel =>
      simp only [JAlong] at halong
      obtain ⟨hgate, hfin, hlastp, hav⟩ := halong
      rw [go_succ, if_pos (hG _ _ _ hgate)]
      apply seqB_found
      exact comp_last E du M hfin hlast hz hlastp hav
  | cons x rest' ih =>
    intro fuel i t r d a b m z last usedC usedA du M hlast hz husedA husedC hM hC hB hbud halong
    cases fuel with
    | zero => rw [go_zero]; exact ByteArray.size_empty
    | succ fuel =>
      obtain ⟨kdr, Q⟩ := x
      cases Q with
      | nil => simp [JAlong] at halong
      | cons v R =>
        have hilt := lt_of_along _ _ _ _ _ _ _ _ _ _ _ halong
        have hgoid := go_id (ci := ci) (nxt := nxt) (s3 := s3) (s4 := s4) (jl := jl) (np := np)
          (bm := bm) (kd := kd) (lo := lo) (hi := hi) (bestLe := bestLe) (gLe := gLe)
          (fLe := fLe) (gate := gate) (early := early) (k - 1) fuel
        rw [blocksR_cons] at hbud
        have hlastmem : (v :: R).getLast (List.cons_ne_nil v R) ∈ v :: R := List.getLast_mem _
        have e : k - 1 - 1 - R.length = k - 2 - R.length := by omega
        match kdr, halong with
        | 0, halong =>
          simp only [JAlong] at halong
          obtain ⟨hgate, ⟨hR, hperm, hdoor, hpw⟩, hk3, hlink, hnew, hwt, halong'⟩ := halong
          have hv := hperm v List.mem_cons_self
          have hlive := live_of_along _ _ _ _ _ _ _ _ _ _ _ halong'
          rw [go_succ, if_pos (hG _ _ _ hgate)]
          refine seqB_next (comp_id hgoid _ _ _ _ _ _ _ _ _ _ _) (seqB_found _ ?_)
          have hbit := mkMask_bit (fun n => decide (d + (k - 1) * t + n ≤ b) &&
            live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) i t (r + 1) (d + n) a b
              (max m (vOf (k - 1) t r d))) (k - 1) R.length (by omega) (by
              rw [e, Bool.and_eq_true]
              exact ⟨decide_eq_true hwt, hlive⟩)
          rw [k3_pos _ _ _ _ _ hk3]
          exact step_found E hk
            (fun _ n e du' M'' =>
              go ci nxt s3 s4 jl (k - 1) np bm kd lo hi bestLe gLe fLe gate early fuel
                i t (r + 1) (d + n) a b (max m (vOf (k - 1) t r d)) (enc z) e du' M'')
            (fun _ n e du' M'' => hgoid _ _ _ _ _ _ _ _ _ _ _) (UInt8.ofNat (i + 1)) (i + 1)
            (le_of_eq (toNat_ofNat8 (by omega))) bm _ du _ M v R usedA usedC (blocksR rest')
            (E.s3_mem last v hlast hv hlink) hR
            hbit
            hperm hdoor hM hC hB husedA husedC hnew hpw hbud
            (fun M' du' hM' hC' hB' hbud' =>
              ih fuel _ _ _ _ _ _ _ z _ (usedC ++ v :: R) (usedA ++ v :: R) du' M'
                (hperm _ hlastmem) hz
                (fun u hu => (List.mem_append.mp hu).elim (husedA u) (hperm u))
                (fun u hu => (List.mem_append.mp hu).elim (husedC u) (hperm u))
                hM' hC' hB' hbud' halong')
        | 1, halong =>
          simp only [JAlong] at halong
          obtain ⟨hgate, ⟨hR, hperm, hdoor, hpw⟩, hk4, hlink, hnew, hwt, halong'⟩ := halong
          have hv := hperm v List.mem_cons_self
          have hlive := live_of_along _ _ _ _ _ _ _ _ _ _ _ halong'
          rw [go_succ, if_pos (hG _ _ _ hgate)]
          refine seqB_next (comp_id hgoid _ _ _ _ _ _ _ _ _ _ _)
            (seqB_next (k3_id hgoid _ _ _ _ _ _ _ _ _ _ _) ?_)
          have hbit := mkMask_bit (fun n => decide (d + (k - 1) * t + (k - 1) + n ≤ b) &&
            live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) i (t + 1) (r + 1) (d + n) a b
              (max m (vOf (k - 1) t r d))) (k - 1) R.length (by omega) (by
              rw [e, Bool.and_eq_true]
              exact ⟨decide_eq_true hwt, hlive⟩)
          rw [k4_pos _ _ _ _ _ hk4]
          exact step_found E hk
            (fun _ n e du' M'' =>
              go ci nxt s3 s4 jl (k - 1) np bm kd lo hi bestLe gLe fLe gate early fuel
                i (t + 1) (r + 1) (d + n) a b (max m (vOf (k - 1) t r d)) (enc z) e du' M'')
            (fun _ n e du' M'' => hgoid _ _ _ _ _ _ _ _ _ _ _) (UInt8.ofNat (i + 1)) (i + 1)
            (le_of_eq (toNat_ofNat8 (by omega))) bm _ du _ M v R usedA usedC (blocksR rest')
            (E.s4_mem last v hlast hv hlink) hR
            hbit
            hperm hdoor hM hC hB husedA husedC hnew hpw hbud
            (fun M' du' hM' hC' hB' hbud' =>
              ih fuel _ _ _ _ _ _ _ z _ (usedC ++ v :: R) (usedA ++ v :: R) du' M'
                (hperm _ hlastmem) hz
                (fun u hu => (List.mem_append.mp hu).elim (husedA u) (hperm u))
                (fun u hu => (List.mem_append.mp hu).elim (husedC u) (hperm u))
                hM' hC' hB' hbud' halong')
        | kdr + 2, halong =>
          simp only [JAlong] at halong
          obtain ⟨hgate, ⟨hR, hperm, hdoor, hpw⟩, hfin, hnpne, hbest, hg2, hwt, halong'⟩ := halong
          have hv := hperm v List.mem_cons_self
          have hilt' := lt_of_along _ _ _ _ _ _ _ _ _ _ _ halong'
          have hlive := live_of_along _ _ _ _ _ _ _ _ _ _ _ halong'
          rw [go_succ, if_pos (hG _ _ _ hgate)]
          apply seqB_found
          have hbit := mkMask_bit (fun n => decide (n ≤ b - (d + (k - 1) * t)) &&
            live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) (i + 1) 0 1 n (a - vOf (k - 1) t r d)
              (b - (d + (k - 1) * t)) (-((k - 1 : ℕ) : ℤ))) (k - 1) R.length (by omega) (by
              rw [e, Bool.and_eq_true]
              exact ⟨decide_eq_true hwt, hlive⟩)
          rw [comp_jump E du M hfin hlast hz hnpne hbest (hE _ _ _ hg2)]
          exact step_found E hk
            (fun D n e du' M'' =>
              go ci nxt s3 s4 jl (k - 1) np bm kd lo hi bestLe gLe fLe gate early fuel
                (i + 1) 0 1 n (a - vOf (k - 1) t r d) (b - (d + (k - 1) * t))
                (-((k - 1 : ℕ) : ℤ)) D e du' M'')
            (fun _ n e du' M'' => hgoid _ _ _ _ _ _ _ _ _ _ _) (UInt8.ofNat (i + 2)) (i + 2)
            (le_of_eq (toNat_ofNat8 (by omega))) bm _ du _ M v R usedA [] (blocksR rest')
            (E.jl_mem v hv) hR
            hbit
            hperm hdoor hM (mc_of_mb hB (by omega)) (fun j => le_trans (hB j) (by omega)) husedA
            (by simp) (by simp) hpw hbud
            (fun M' du' hM' hC' hB' hbud' =>
              ih fuel _ _ _ _ _ _ _ v _ (v :: R) (usedA ++ v :: R) du' M'
                (hperm _ hlastmem) hv
                (fun u hu => (List.mem_append.mp hu).elim (husedA u) (hperm u))
                hperm hM' hC' hB' hbud' halong')

/-! ### The parts and the gate -/

/-- Beyond the gate. -/
def Past (gi gr i r : ℕ) : Prop := gi < i ∨ (i = gi ∧ gr < r)

theorem gate_of_ne {i r : ℕ} (h : ¬ (i = gi ∧ r = gr)) (nt tp key : ℕ) :
    Gate gi gr nt tp i r key := by
  unfold Gate
  by_cases h1 : i = gi
  · exact Or.inr (Or.inl fun h2 => h ⟨h1, h2⟩)
  · exact Or.inl h1

theorem gate_of_past {i r : ℕ} (h : Past gi gr i r) (nt tp key : ℕ) :
    Gate gi gr nt tp i r key :=
  gate_of_ne (by unfold Past at h; omega) nt tp key

theorem past_row {i r : ℕ} (h : Past gi gr i r) : Past gi gr i (r + 1) := by
  unfold Past at h ⊢
  omega

theorem past_jump {i r : ℕ} (h : Past gi gr i r) : Past gi gr (i + 1) 1 := by
  unfold Past at h ⊢
  omega

/-- Beyond the gate every part of the search is the whole search. -/
theorem along_past (nt tp : ℕ) : ∀ (rest : List TRow) (i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ)
    (z last : List ℕ) (usedC : List (List ℕ)), Past gi gr i r →
    JAlong k np enc kd lo hi bestLe gLe fLe (Gate gi gr 1 0)
      (Early gi gr 1 0) i t r d a b m z last usedC rest →
    JAlong k np enc kd lo hi bestLe gLe fLe (Gate gi gr nt tp)
      (Early gi gr nt tp) i t r d a b m z last usedC rest
  | [], i, t, r, d, a, b, m, z, last, usedC, hp, h => by
    simp only [JAlong] at h ⊢
    exact ⟨gate_of_past hp _ _ _, h.2⟩
  | (_, []) :: _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [JAlong] at h
  | (0, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, hp, h => by
    simp only [JAlong] at h ⊢
    obtain ⟨_, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨gate_of_past hp _ _ _, h2, h3, h4, h5, h6,
      along_past nt tp rest _ _ _ _ _ _ _ _ _ _ (past_row hp) h7⟩
  | (1, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, hp, h => by
    simp only [JAlong] at h ⊢
    obtain ⟨_, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨gate_of_past hp _ _ _, h2, h3, h4, h5, h6,
      along_past nt tp rest _ _ _ _ _ _ _ _ _ _ (past_row hp) h7⟩
  | (kdr + 2, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, hp, h => by
    simp only [JAlong] at h ⊢
    obtain ⟨_, h2, h3, h4, h5, _, h7, h8⟩ := h
    refine ⟨gate_of_past hp _ _ _, h2, h3, h4, h5, ?_, h7,
      along_past nt tp rest _ _ _ _ _ _ _ _ _ _ (past_jump hp) h8⟩
    unfold Past at hp
    unfold Early
    omega

/-- A list of rows along which the rule holds passes the gate of one of the `nt` parts. -/
theorem along_gate (hnt : 0 < nt) : ∀ (rest : List TRow) (i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ)
    (z last : List ℕ) (usedC : List (List ℕ)),
    JAlong k np enc kd lo hi bestLe gLe fLe (Gate gi gr 1 0)
      (Early gi gr 1 0) i t r d a b m z last usedC rest →
    ∃ tp, tp < nt ∧
      JAlong k np enc kd lo hi bestLe gLe fLe (Gate gi gr nt tp)
      (Early gi gr nt tp) i t r d a b m z last usedC rest
  | [], i, t, r, d, a, b, m, z, last, usedC, h => by
    refine ⟨(enc last + 8192 * d) % nt, Nat.mod_lt _ hnt, ?_⟩
    simp only [JAlong] at h ⊢
    exact ⟨Or.inr (Or.inr rfl), h.2⟩
  | (_, []) :: _, _, _, _, _, _, _, _, _, _, _, h => by simp [JAlong] at h
  | (0, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, h => by
    by_cases hp : Past gi gr i r
    · exact ⟨0, hnt, along_past nt 0 _ _ _ _ _ _ _ _ _ _ _ hp h⟩
    simp only [JAlong] at h
    obtain ⟨_, h2, h3, h4, h5, h6, h7⟩ := h
    by_cases hat : i = gi ∧ r = gr
    · refine ⟨(enc last + 8192 * d) % nt, Nat.mod_lt _ hnt, ?_⟩
      simp only [JAlong]
      exact ⟨Or.inr (Or.inr rfl), h2, h3, h4, h5, h6,
        along_past nt _ rest _ _ _ _ _ _ _ _ _ _ (Or.inr ⟨hat.1, by omega⟩) h7⟩
    · obtain ⟨tp, htp, hA⟩ := along_gate hnt rest _ _ _ _ _ _ _ _ _ _ h7
      refine ⟨tp, htp, ?_⟩
      simp only [JAlong]
      exact ⟨gate_of_ne hat _ _ _, h2, h3, h4, h5, h6, hA⟩
  | (1, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, h => by
    by_cases hp : Past gi gr i r
    · exact ⟨0, hnt, along_past nt 0 _ _ _ _ _ _ _ _ _ _ _ hp h⟩
    simp only [JAlong] at h
    obtain ⟨_, h2, h3, h4, h5, h6, h7⟩ := h
    by_cases hat : i = gi ∧ r = gr
    · refine ⟨(enc last + 8192 * d) % nt, Nat.mod_lt _ hnt, ?_⟩
      simp only [JAlong]
      exact ⟨Or.inr (Or.inr rfl), h2, h3, h4, h5, h6,
        along_past nt _ rest _ _ _ _ _ _ _ _ _ _ (Or.inr ⟨hat.1, by omega⟩) h7⟩
    · obtain ⟨tp, htp, hA⟩ := along_gate hnt rest _ _ _ _ _ _ _ _ _ _ h7
      refine ⟨tp, htp, ?_⟩
      simp only [JAlong]
      exact ⟨gate_of_ne hat _ _ _, h2, h3, h4, h5, h6, hA⟩
  | (kdr + 2, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, h => by
    by_cases hp : Past gi gr i r
    · exact ⟨0, hnt, along_past nt 0 _ _ _ _ _ _ _ _ _ _ _ hp h⟩
    simp only [JAlong] at h
    obtain ⟨_, h2, h3, h4, h5, _, h7, h8⟩ := h
    by_cases hat : i = gi ∧ r = gr
    · -- at the gate: the part of this prefix
      refine ⟨(enc last + 8192 * d) % nt, Nat.mod_lt _ hnt, ?_⟩
      simp only [JAlong]
      exact ⟨Or.inr (Or.inr rfl), h2, h3, h4, h5, Or.inr (Or.inl (le_of_eq hat.2.symm)), h7,
        along_past nt _ rest _ _ _ _ _ _ _ _ _ _ (Or.inl (by omega)) h8⟩
    · by_cases hi : i = gi
      · -- the piece of the gate is complete above the gate: the part of the key of its end
        refine ⟨(enc last + 8192 * d) % nt, Nat.mod_lt _ hnt, ?_⟩
        simp only [JAlong]
        exact ⟨gate_of_ne hat _ _ _, h2, h3, h4, h5, Or.inr (Or.inr rfl), h7,
          along_past nt _ rest _ _ _ _ _ _ _ _ _ _ (Or.inl (by omega)) h8⟩
      · obtain ⟨tp, htp, hA⟩ := along_gate hnt rest _ _ _ _ _ _ _ _ _ _ h8
        refine ⟨tp, htp, ?_⟩
        simp only [JAlong]
        exact ⟨gate_of_ne hat _ _ _, h2, h3, h4, h5, Or.inl hi, h7, hA⟩

/-! ### Several gates -/

/-- The rule along a list of rows with the gates of two families holds with every gate that
follows from them. -/
theorem along_map2 {G1 G2 G3 E1 E2 E3 : ℕ → ℕ → ℕ → Prop}
    (hG : ∀ i r key, G1 i r key → G2 i r key → G3 i r key)
    (hE : ∀ i r key, E1 i r key → E2 i r key → E3 i r key) :
    ∀ (rest : List TRow) (i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ)
    (z last : List ℕ) (usedC : List (List ℕ)),
    JAlong k np enc kd lo hi bestLe gLe fLe G1 E1 i t r d a b m z last usedC rest →
    JAlong k np enc kd lo hi bestLe gLe fLe G2 E2 i t r d a b m z last usedC rest →
    JAlong k np enc kd lo hi bestLe gLe fLe G3 E3 i t r d a b m z last usedC rest
  | [], i, t, r, d, a, b, m, z, last, usedC, h, h' => by
    simp only [JAlong] at h h' ⊢
    exact ⟨hG _ _ _ h.1 h'.1, h.2⟩
  | (_, []) :: _, _, _, _, _, _, _, _, _, _, _, h, _ => by simp [JAlong] at h
  | (0, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, h, h' => by
    simp only [JAlong] at h h' ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨hG _ _ _ h1 h'.1, h2, h3, h4, h5, h6,
      along_map2 hG hE rest _ _ _ _ _ _ _ _ _ _ h7 h'.2.2.2.2.2.2⟩
  | (1, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, h, h' => by
    simp only [JAlong] at h h' ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨hG _ _ _ h1 h'.1, h2, h3, h4, h5, h6,
      along_map2 hG hE rest _ _ _ _ _ _ _ _ _ _ h7 h'.2.2.2.2.2.2⟩
  | (kdr + 2, v :: R) :: rest, i, t, r, d, a, b, m, z, last, usedC, h, h' => by
    simp only [JAlong] at h h' ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    exact ⟨hG _ _ _ h1 h'.1, h2, h3, h4, h5, hE _ _ _ h6 h'.2.2.2.2.2.1, h7,
      along_map2 hG hE rest _ _ _ _ _ _ _ _ _ _ h8 h'.2.2.2.2.2.2.2⟩

/-- The gates `gs` of part `tp` at a prefix with `r` rows of piece `i`: every gate with its digit
of `tp` (mixed radix, the first gate is the lowest digit). -/
def GateL : List (ℕ × ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ → Prop
  | [], _, _, _, _ => True
  | g :: gs, tp, i, r, key =>
    Gate g.1 g.2.1 g.2.2 (tp % g.2.2) i r key ∧ GateL gs (tp / g.2.2) i r key

/-- A piece `i` that is complete with `r` rows and the key `key` is followed in part `tp`. -/
def EarlyL : List (ℕ × ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ → Prop
  | [], _, _, _, _ => True
  | g :: gs, tp, i, r, key =>
    Early g.1 g.2.1 g.2.2 (tp % g.2.2) i r key ∧ EarlyL gs (tp / g.2.2) i r key

theorem gateL_true : ∀ (gs : List (ℕ × ℕ × ℕ)) (tp i r key : ℕ),
    GateL gs tp i r key → gateD (digs gs tp) i r key = true
  | [], _, _, _, _, _ => rfl
  | g :: gs, tp, i, r, key, h => by
    simp only [GateL] at h
    simp only [digs, gateD, Bool.and_eq_true]
    refine ⟨?_, gateL_true gs _ _ _ _ h.2⟩
    rcases h.1 with h1 | h1 | h1 <;> simp [h1]

theorem earlyL_true : ∀ (gs : List (ℕ × ℕ × ℕ)) (tp i r key : ℕ),
    EarlyL gs tp i r key → earlyD (digs gs tp) i r key = true
  | [], _, _, _, _, _ => rfl
  | g :: gs, tp, i, r, key, h => by
    simp only [EarlyL] at h
    simp only [digs, earlyD, Bool.and_eq_true]
    refine ⟨?_, earlyL_true gs _ _ _ _ h.2⟩
    rcases h.1 with h1 | h1 | h1 <;> simp [h1]

/-- A list of rows along which the rule holds passes the gates of one of the `gprod gs` parts:
the digit of the part at a gate is the key of the prefix at the gate, or the key of the end of
the piece of the gate when the piece is complete before the gate, or 0 when the list does not
reach the gate. -/
theorem along_gates : ∀ (gs : List (ℕ × ℕ × ℕ)), (∀ g ∈ gs, 0 < g.2.2) →
    ∀ (rest : List TRow) (i t r d : ℕ) (a : ℤ) (b : ℕ) (m : ℤ)
    (z last : List ℕ) (usedC : List (List ℕ)),
    JAlong k np enc kd lo hi bestLe gLe fLe (fun _ _ _ => True) (fun _ _ _ => True)
      i t r d a b m z last usedC rest →
    ∃ tp, tp < gprod gs ∧
      JAlong k np enc kd lo hi bestLe gLe fLe (GateL gs tp) (EarlyL gs tp)
        i t r d a b m z last usedC rest
  | [], _, rest, i, t, r, d, a, b, m, z, last, usedC, h =>
    ⟨0, Nat.one_pos, along_map2 (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial)
      rest _ _ _ _ _ _ _ _ _ _ h h⟩
  | g :: gs, hg, rest, i, t, r, d, a, b, m, z, last, usedC, h => by
    have hn : 0 < g.2.2 := hg g List.mem_cons_self
    obtain ⟨t1, ht1, h1⟩ := along_gate (gi := g.1) (gr := g.2.1) (nt := g.2.2) hn
      rest _ _ _ _ _ _ _ _ _ _
      (along_map2 (G3 := Gate g.1 g.2.1 1 0) (E3 := Early g.1 g.2.1 1 0)
        (fun _ _ _ _ _ => Or.inr (Or.inr (Nat.mod_one _)))
        (fun _ _ _ _ _ => Or.inr (Or.inr (Nat.mod_one _)))
        rest _ _ _ _ _ _ _ _ _ _ h h)
    obtain ⟨t2, ht2, h2⟩ := along_gates gs (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      rest _ _ _ _ _ _ _ _ _ _ h
    have e1 : (t1 + g.2.2 * t2) % g.2.2 = t1 := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt ht1
    have e2 : (t1 + g.2.2 * t2) / g.2.2 = t2 := by
      rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt ht1, Nat.zero_add]
    refine ⟨t1 + g.2.2 * t2, ?_, ?_⟩
    · have h3 : g.2.2 * (t2 + 1) ≤ g.2.2 * gprod gs := Nat.mul_le_mul_left _ ht2
      rw [Nat.mul_add, Nat.mul_one] at h3
      simp only [gprod]
      omega
    · refine along_map2 (G1 := Gate g.1 g.2.1 g.2.2 t1) (G2 := GateL gs t2) ?_ ?_
        rest _ _ _ _ _ _ _ _ _ _ h1 h2
      · intro i r key ha hb
        simp only [GateL, e1, e2]
        exact ⟨ha, hb⟩
      · intro i r key ha hb
        simp only [EarlyL, e1, e2]
        exact ⟨ha, hb⟩

/-- **The search is complete.**  If all `gprod gs` parts of the gates `gs` answer `false`, the
rule holds along no list of rows that starts at the word `1 2 … k` and obeys the bound on shared
classes. -/
theorem not_along_of_parts (E : Enc k enc ci nxt s3 s4 jl st) (hk : 2 ≤ k) (hnp : np ≤ 255)
    (hid : PermW k (List.range' 1 k)) {gs : List (ℕ × ℕ × ℕ)} (hgs : ∀ g ∈ gs, 0 < g.2.2)
    {V : ℤ} {W sz fuel : ℕ}
    (hs : ∀ tp, tp < gprod gs →
      searchPart ci nxt s3 s4 jl st (k - 1) np bm kd lo hi bestLe gLe fLe V W sz fuel
        (gateD (digs gs tp)) (earlyD (digs gs tp)) = false)
    (R1 : List (List ℕ)) (rest : List TRow)
    (hR1 : R1.length ≤ k - 2) (hperm : ∀ w ∈ List.range' 1 k :: R1, PermW k w)
    (hdoor : List.IsChain (DoorEq k) (List.range' 1 k :: R1))
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) (List.range' 1 k :: R1))
    (hW : k - 2 - R1.length ≤ W)
    (hbud : Bud bm 0 [] ((List.range' 1 k :: R1) ++ blocksR rest)) :
    ¬ JAlong k np enc kd lo hi bestLe gLe fLe (Gate gi gr 1 0)
      (Early gi gr 1 0) 0 0 1 (k - 2 - R1.length) V W
      (-((k - 1 : ℕ) : ℤ)) (List.range' 1 k)
      ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _)) (List.range' 1 k :: R1) rest := by
  intro hA
  obtain ⟨tp, htp, hP⟩ := along_gates gs hgs rest _ _ _ _ _ _ _ _ _ _
    (along_map2 (G3 := fun _ _ _ => True) (E3 := fun _ _ _ => True)
      (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) rest _ _ _ _ _ _ _ _ _ _ hA hA)
  have hG := gateL_true gs tp
  have hE := earlyL_true gs tp
  have hnp0 := lt_of_along _ _ _ _ _ _ _ _ _ _ _ hP
  have hlive := live_of_along _ _ _ _ _ _ _ _ _ _ _ hP
  have e : k - 1 - 1 - R1.length = k - 2 - R1.length := by omega
  have hbit := mkMask_bit (fun n => decide (n ≤ W) &&
    live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) 0 0 1 n V W (-((k - 1 : ℕ) : ℤ)))
    (k - 1) R1.length (by omega) (by
      rw [e, Bool.and_eq_true]
      exact ⟨decide_eq_true hW, hlive⟩)
  have hm0 : ∀ j, (marks0 sz).get! j = 0 := fun j => S.get!_marks0 sz j
  have h := walkG_complete E hk
    (fun n e du M =>
      go ci nxt s3 s4 jl (k - 1) np bm kd lo hi bestLe gLe fLe (gateD (digs gs tp))
        (earlyD (digs gs tp)) fuel 0 0 1 n V W (-((k - 1 : ℕ) : ℤ)) st e du M)
    (fun n e du M => go_id (k - 1) fuel _ _ _ _ _ _ _ _ _ _ _) (UInt8.ofNat 1) 1
    (le_of_eq (toNat_ofNat8 (by omega))) bm
    (mkMask (fun n => decide (n ≤ W) &&
      live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) 0 0 1 n V W
        (-((k - 1 : ℕ) : ℤ))) (k - 1))
    0 (marks0 sz) (List.range' 1 k) R1 [] [] (blocksR rest) hR1
    hbit hperm hdoor (PS.minv_marks0 enc ci sz)
    (fun j hj => by
      rw [hm0] at hj
      exact absurd hj (by decide))
    (fun j => by rw [hm0]; decide) (by simp) (by simp) (by simp) hpw hbud
    (fun M' du' hM' hC' hB' hbud' => by
      rw [E.st_eq]
      exact go_complete E hk hnp hG hE rest fuel 0 0 1 _ V W _ (List.range' 1 k) _
        (List.range' 1 k :: R1) (List.range' 1 k :: R1) du' M'
        (hperm _ (List.getLast_mem _)) hid hperm hperm (by simpa using hM') (by simpa using hC')
        hB' (by simpa using hbud') hP)
  rw [← E.st_eq] at h
  have h3 : searchPart ci nxt s3 s4 jl st (k - 1) np bm kd lo hi bestLe gLe fLe V W sz fuel
      (gateD (digs gs tp)) (earlyD (digs gs tp)) = true := by
    unfold searchPart
    exact beq_iff_eq.mpr h
  rw [hs tp htp] at h3
  cases h3

end Engine

end J15
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.J15.not_along_of_parts
