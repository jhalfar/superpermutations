import Superperm.Groups

/-!
# One position for a whole rotation class, and the word as a literal tree

`Superperm/Literal.lean` gives one position for every permutation and rebuilds the word, as one
number, in every kernel check.  For eleven symbols both are too expensive.  This file changes two
things and reuses everything else.

**Rotation classes.**  In the words in question every permutation `p'` is followed by its rotations:
some stretch of `2K-1` letters reads `x ++ x.take (K-1)` for a rotation `x` of `p'`, and so contains
all `K` rotations of `p'`.  The certificate therefore has one entry for every arrangement that
*ends* with the symbol `K-1` (there are `(K-1)!`): a position `pos` and a number `r < 16`.  The
leaf test `leafCyc` compares the `2K-1` digits of the word at `pos` with the digits
`r, …, r+2K-2` of `c * M`, where `c` is the code of `p'` and `M = 1 + 16^K + 16^(2K) + 16^(3K)`, so
that `c * M` spells `p' ++ p' ++ p' ++ p'`.  `rot_window` shows that every rotation of `p'` is then
a window of the word.

**A literal tree.**  The tree of blocks that `Literal.get` reads is written out in the generated
files as a term (`WT.node`, `WT.leaf` of block constants), the number `W` is *defined* from that
tree (`unb`), and one kernel computation `chkT B K d tree W = true` shows `tree = build B K d W`.
A check of a branch then unfolds only the blocks it reads.  `getT` is `Literal.get` with fewer
kernel steps per level.
-/

namespace LiteralSuperperm

open SuperpermutationBounds

/-! ### The literal tree -/

/-- `chkT B K d t x = true` says that `t` is the tree `build B K d x`.  (The mask is made by a
shift and not, as in `build`, by a power: the kernel computes `Nat.pow` with its big-number
arithmetic only for exponents up to `2 ^ 24`, and eleven symbols need 88 million bits.) -/
def chkT (B K : Nat) : Nat → WT → Nat → Bool
  | 0, .leaf y, x => Nat.beq y x
  | d + 1, .node l r, x =>
    and
      (chkT B K d l (Nat.land x
        (Nat.sub (Nat.shiftLeft 1 (Nat.mul 4 (Nat.add (Nat.mul B (Nat.pow 2 d)) K))) 1)))
      (chkT B K d r (Nat.shiftRight x (Nat.mul 4 (Nat.mul B (Nat.pow 2 d)))))
  | _, _, _ => false

theorem chkT_sound (B K : Nat) : ∀ (d : Nat) (t : WT) (x : Nat),
    chkT B K d t x = true → t = build B K d x := by
  intro d
  induction d with
  | zero =>
    intro t x h
    cases t with
    | leaf y =>
      have hy : y = x := Nat.eq_of_beq_eq_true h
      rw [hy]
      rfl
    | node l r => exact absurd h (by simp [chkT])
  | succ d ih =>
    intro t x h
    cases t with
    | leaf y => exact absurd h (by simp [chkT])
    | node l r =>
      have h' : (chkT B K d l (Nat.land x
            (Nat.sub (Nat.shiftLeft 1 (Nat.mul 4 (Nat.add (Nat.mul B (Nat.pow 2 d)) K))) 1)) &&
          chkT B K d r (Nat.shiftRight x (Nat.mul 4 (Nat.mul B (Nat.pow 2 d))))) = true := h
      rw [Bool.and_eq_true] at h'
      have hsh : Nat.shiftLeft 1 (Nat.mul 4 (Nat.add (Nat.mul B (Nat.pow 2 d)) K)) =
          Nat.pow 2 (Nat.mul 4 (Nat.add (Nat.mul B (Nat.pow 2 d)) K)) := Nat.one_shiftLeft _
      rw [hsh] at h'
      rw [ih l _ h'.1, ih r _ h'.2]
      rfl

/-- The number spelt by a tree whose left half serves `h / 4` digits: the leaves, each shifted to
its place and joined by `or`.  (This is only a definition; that the tree is `build … (unb tree h)`
is what `chkT` checks.) -/
def unb : WT → Nat → Nat
  | .leaf x, _ => x
  | .node l r, h =>
    Nat.lor (unb l (Nat.shiftRight h 1)) (Nat.shiftLeft (unb r (Nat.shiftRight h 1)) h)

/-- `Literal.get` for a tree whose left half serves `h / 4` digits, at the bit position `q`. -/
def getT : WT → Nat → Nat → Nat
  | .leaf x, _, q => Nat.shiftRight x q
  | .node l r, h, q =>
    bif Nat.ble h q then getT r (Nat.shiftRight h 1) (Nat.sub q h)
    else getT l (Nat.shiftRight h 1) q

theorem getT_build (B K : Nat) : ∀ (d x pos h : Nat), (∀ d', d = d' + 1 → h = 4 * (B * 2 ^ d')) →
    getT (build B K d x) h (4 * pos) = get B d (build B K d x) pos := by
  intro d
  induction d with
  | zero =>
    intro x pos h _
    rfl
  | succ d ih =>
    intro x pos h hh
    have hh' : h = 4 * (B * 2 ^ d) := hh d rfl
    have hhalf : ∀ d', d = d' + 1 → Nat.shiftRight h 1 = 4 * (B * 2 ^ d') := by
      intro d' hd
      subst hd
      show h >>> 1 = _
      rw [Nat.shiftRight_eq_div_pow, hh', Nat.pow_succ]
      have : B * (2 ^ d' * 2) = B * 2 ^ d' * 2 := by rw [Nat.mul_assoc]
      omega
    by_cases hlt : pos < B * 2 ^ d
    · have hb : Nat.ble (Nat.succ pos) (Nat.mul B (Nat.pow 2 d)) = true :=
        Nat.ble_eq_true_of_le hlt
      have hb' : Nat.ble h (4 * pos) = false := by
        rw [← Bool.not_eq_true]
        intro hc
        have := Nat.le_of_ble_eq_true hc
        omega
      show (bif Nat.ble h (4 * pos) then _ else getT (build B K d _) (Nat.shiftRight h 1) (4 * pos)) =
        (bif Nat.ble (Nat.succ pos) (Nat.mul B (Nat.pow 2 d)) then get B d (build B K d _) pos else _)
      rw [hb, hb', cond_true, cond_false]
      exact ih _ pos _ hhalf
    · have hb : Nat.ble (Nat.succ pos) (Nat.mul B (Nat.pow 2 d)) = false := by
        rw [← Bool.not_eq_true]
        intro hc
        exact hlt (Nat.le_of_ble_eq_true hc)
      have hb' : Nat.ble h (4 * pos) = true := Nat.ble_eq_true_of_le (by omega)
      have hq : Nat.sub (4 * pos) h = 4 * (pos - B * 2 ^ d) := by
        show 4 * pos - h = _
        omega
      show (bif Nat.ble h (4 * pos) then
          getT (build B K d _) (Nat.shiftRight h 1) (Nat.sub (4 * pos) h) else _) =
        (bif Nat.ble (Nat.succ pos) (Nat.mul B (Nat.pow 2 d)) then _
          else get B d (build B K d _) (Nat.sub pos (Nat.mul B (Nat.pow 2 d))))
      rw [hb, hb', cond_true, cond_false, hq]
      exact ih _ _ _ hhalf

/-! ### Codes of concatenations -/

theorem code_append (l₁ l₂ : List Nat) :
    code (l₁ ++ l₂) = code l₁ + 16 ^ l₁.length * code l₂ := by
  induction l₁ with
  | nil => simp [code]
  | cons a t ih =>
    simp only [List.cons_append, code, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 16 (16 ^ t.length), Nat.add_assoc]

theorem code_lt (l : List Nat) (h : ∀ a ∈ l, a < 16) : code l < 16 ^ l.length := by
  induction l with
  | nil => simp [code]
  | cons a t ih =>
    have ha : a < 16 := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [code, List.length_cons, Nat.pow_succ]
    omega

/-- The digits of `code (u ++ (m ++ v))` at position `u.length` spell `m`. -/
theorem window_code (u m v : List Nat) (hu : ∀ x ∈ u, x < 16) (hm : ∀ x ∈ m, x < 16) :
    code (u ++ (m ++ v)) / 16 ^ u.length % 16 ^ m.length = code m := by
  have h1 := code_lt u hu
  have h2 := code_lt m hm
  rw [code_append, code_append, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt h1, Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]

theorem mod_div_mod (x n i k : Nat) (h : i + k ≤ n) :
    x % 16 ^ n / 16 ^ i % 16 ^ k = x / 16 ^ i % 16 ^ k := by
  have hn : n = i + (n - i) := by omega
  rw [hn, Nat.pow_add, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 16 (by omega))

/-- If `c` is the code of `a ++ b` then every stretch of `c * M` that starts at one of the first
16 digits contains the rotation `b ++ a`, at an offset below `K`. -/
theorem rot_window {K r M : Nat} (a b : List Nat) (hK8 : 8 ≤ K) (hlen : a.length + b.length = K)
    (hb : 0 < b.length) (ha16 : ∀ x ∈ a, x < 16) (hb16 : ∀ x ∈ b, x < 16) (hr : r < 16)
    (hM : M = 1 + 16 ^ K * (1 + 16 ^ K * (1 + 16 ^ K))) :
    ∃ i, i < K ∧ code (a ++ b) * M / 16 ^ (r + i) % 16 ^ K = code (b ++ a) := by
  have hab : (a ++ b).length = K := by simp [hlen]
  have hba : (b ++ a).length = K := by simp; omega
  have hc4 : code (a ++ b) * M =
      code ((a ++ b) ++ ((a ++ b) ++ ((a ++ b) ++ (a ++ b)))) := by
    rw [code_append (a ++ b), code_append (a ++ b), code_append (a ++ b), hab, hM]
    generalize code (a ++ b) = c
    generalize 16 ^ K = y
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_comm, Nat.mul_left_comm]
  have hba16 : ∀ x ∈ b ++ a, x < 16 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hb16 x h
    · exact ha16 x h
  have hab16 : ∀ x ∈ a ++ b, x < 16 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact ha16 x h
    · exact hb16 x h
  rw [hc4]
  by_cases h1 : r ≤ a.length
  · refine ⟨a.length - r, by omega, ?_⟩
    have hsplit : (a ++ b) ++ ((a ++ b) ++ ((a ++ b) ++ (a ++ b))) =
        a ++ ((b ++ a) ++ (b ++ ((a ++ b) ++ (a ++ b)))) := by simp
    have hoff : r + (a.length - r) = a.length := by omega
    rw [hsplit, hoff, ← hba]
    exact window_code _ _ _ ha16 hba16
  · by_cases h2 : r ≤ a.length + K
    · refine ⟨a.length + K - r, by omega, ?_⟩
      have hsplit : (a ++ b) ++ ((a ++ b) ++ ((a ++ b) ++ (a ++ b))) =
          ((a ++ b) ++ a) ++ ((b ++ a) ++ (b ++ (a ++ b))) := by simp
      have hoff : r + (a.length + K - r) = ((a ++ b) ++ a).length := by
        simp only [List.length_append]; omega
      rw [hsplit, hoff, ← hba]
      refine window_code _ _ _ ?_ hba16
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hab16 x h
      · exact ha16 x h
    · refine ⟨a.length + 2 * K - r, by omega, ?_⟩
      have hsplit : (a ++ b) ++ ((a ++ b) ++ ((a ++ b) ++ (a ++ b))) =
          ((a ++ b) ++ ((a ++ b) ++ a)) ++ ((b ++ a) ++ b) := by simp
      have hoff : r + (a.length + 2 * K - r) = ((a ++ b) ++ ((a ++ b) ++ a)).length := by
        simp only [List.length_append]; omega
      rw [hsplit, hoff, ← hba]
      refine window_code _ _ _ ?_ hba16
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hab16 x h
      · rcases List.mem_append.mp h with h | h
        · exact hab16 x h
        · exact ha16 x h

/-! ### The leaf test and the check for one branch -/

/-- At a leaf: the table entry holds a position (`S` bits, mask `mS`) and above it a number `r`
(4 bits).  The `Kw = 2K-1` digits of the word at the position must be the digits `r, …` of `c * M`. -/
def leafCyc (Kw L S mS mW M h0 : Nat) (tree : WT) (c tbl : Nat) : Bool :=
  and (Nat.ble (Nat.add (Nat.land tbl mS) Kw) L)
    (Nat.beq (Nat.land (getT tree h0 (Nat.mul 4 (Nat.land tbl mS))) mW)
      (Nat.land (Nat.shiftRight (Nat.mul c M) (Nat.mul 4 (Nat.land (Nat.shiftRight tbl S) 15))) mW))

theorem leafCyc_sound {Kw L S mS mW M h0 B d W c tbl : Nat} (hmW : mW = 2 ^ (4 * Kw) - 1)
    (hh0 : ∀ d', d = d' + 1 → h0 = 4 * (B * 2 ^ d'))
    (h : leafCyc Kw L S mS mW M h0 (build B Kw d W) c tbl = true) :
    ∃ pos r, pos + Kw ≤ L ∧ r < 16 ∧ W / 16 ^ pos % 16 ^ Kw = c * M / 16 ^ r % 16 ^ Kw := by
  have h' : (Nat.ble (Nat.add (Nat.land tbl mS) Kw) L &&
      Nat.beq (Nat.land (getT (build B Kw d W) h0 (Nat.mul 4 (Nat.land tbl mS))) mW)
        (Nat.land (Nat.shiftRight (Nat.mul c M)
          (Nat.mul 4 (Nat.land (Nat.shiftRight tbl S) 15))) mW)) = true := h
  rw [Bool.and_eq_true] at h'
  have h15 : Nat.land (Nat.shiftRight tbl S) 15 = Nat.shiftRight tbl S % 16 :=
    Nat.and_two_pow_sub_one_eq_mod _ 4
  refine ⟨Nat.land tbl mS, Nat.shiftRight tbl S % 16, Nat.le_of_ble_eq_true h'.1,
    Nat.mod_lt _ (by decide), ?_⟩
  have h2 := Nat.eq_of_beq_eq_true h'.2
  rw [h15] at h2
  have h3 : getT (build B Kw d W) h0 (4 * Nat.land tbl mS) &&& (2 ^ (4 * Kw) - 1) =
      (c * M) >>> (4 * (Nat.shiftRight tbl S % 16)) &&& (2 ^ (4 * Kw) - 1) := by
    rw [← hmW]; exact h2
  rw [getT_build B Kw d W _ h0 hh0, Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_two_pow_sub_one_eq_mod, Nat.pow_mul, shiftRight_four_mul] at h3
  have hfour : (2 : Nat) ^ 4 = 16 := by decide
  rw [hfour, get_build] at h3
  exact h3

/-- The check for the branch whose first choices are `K-1` and then `t`: every arrangement of
the other symbols, appended to these, passes `leafCyc`.  (An arrangement is built from its last
symbol to its first, so these are the arrangements that end with `t` reversed and then `K-1`.) -/
def partCyc (K Kw L S mS mW M h0 : Nat) (tree : WT) (stride : Nat) (t : List Nat) (tbl : Nat) :
    Bool :=
  go (leafCyc Kw L S mS mW M h0 tree) (Nat.sub K (Nat.succ t.length))
    ((Nat.pred K :: t).foldl erase1 (List.range K)) ((Nat.pred K :: t).foldl step 0) tbl stride

/-- **Soundness.**  If `partCyc` succeeds for every duplicate-free choice `t` of `s` symbols
below `K-1`, the word spelt by `W` contains every permutation. -/
theorem covers_of_cyc {K K1 Kw L S mS mW M B d h0 W stride s : Nat} {tree : WT}
    (hK : 0 < K) (hK8 : 8 ≤ K) (hK16 : K ≤ 16) (hK1 : K = K1 + 1) (hKw : Kw = 2 * K - 1)
    (hmW : mW = 2 ^ (4 * Kw) - 1)
    (hM : M = 1 + 16 ^ K * (1 + 16 ^ K * (1 + 16 ^ K)))
    (hh0 : h0 = 4 * (B * 2 ^ (d - 1)))
    (htree : chkT B Kw d tree W = true)
    (hs : s + 1 ≤ K)
    (items : List (List Nat × Nat))
    (hitems : ∀ x ∈ items, partCyc K Kw L S mS mW M h0 tree stride x.1 x.2 = true)
    (hpre : ∀ t : List Nat, t.length = s → t.Nodup → (∀ a ∈ t, a < K1) →
      ∃ x ∈ items, x.1 = t) :
    Covers (wordOf K L W hK) := by
  have hK1' : K1 = K - 1 := by omega
  subst hK1' hKw
  have hh0' : ∀ d', d = d' + 1 → h0 = 4 * (B * 2 ^ d') := by
    intro d' hd
    subst hd
    exact hh0
  have htree' : tree = build B (2 * K - 1) d W := chkT_sound _ _ _ _ _ htree
  subst htree'
  intro p hplen hpnd
  -- the choices of the walk for `p`: last symbol first
  let P : List Nat := (p.map Fin.val).reverse
  have hPrev : P.reverse = p.map Fin.val := List.reverse_reverse _
  have hPlen : P.length = K := by simp [P, hplen]
  have hPnd : P.Nodup := by
    simp only [P, List.nodup_reverse]
    exact hpnd.map Fin.val_injective
  have hPlt : ∀ a ∈ P, a < K := by
    intro a ha
    simp only [P, List.mem_reverse] at ha
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    exact x.isLt
  have hPperm : P.Perm (List.range K) := perm_range_of_nodup P hPlen hPnd hPlt
  -- rotate so that the symbol `K-1` comes first
  have hmem : K - 1 ∈ P := hPperm.symm.subset (List.mem_range.mpr (by omega))
  obtain ⟨A, Bq, hAB⟩ := List.append_of_mem hmem
  have hRperm : ((K - 1) :: (Bq ++ A)).Perm P := by
    rw [hAB]
    exact (List.perm_middle.trans (List.Perm.cons _ List.perm_append_comm)).symm
  have hRnd : ((K - 1) :: (Bq ++ A)).Nodup := hRperm.nodup_iff.mpr hPnd
  have hRnd' := List.nodup_cons.mp hRnd
  have hRlen : (Bq ++ A).length = K - 1 := by
    have := hRperm.length_eq
    rw [hPlen, List.length_cons] at this
    omega
  have hRlt : ∀ x ∈ Bq ++ A, x < K - 1 := by
    intro x hx
    have h1 : x < K := hPlt x (hRperm.subset (List.mem_cons_of_mem _ hx))
    have h2 : x ≠ K - 1 := fun h => hRnd'.1 (h ▸ hx)
    omega
  -- the branch
  have htd : (Bq ++ A).take s ++ (Bq ++ A).drop s = Bq ++ A := List.take_append_drop s _
  have htlen : ((Bq ++ A).take s).length = s := by
    rw [List.length_take, hRlen]; omega
  obtain ⟨x, hx, hx1⟩ := hpre ((Bq ++ A).take s) htlen (hRnd'.2.sublist (List.take_sublist s _))
    (fun y hy => hRlt y (List.mem_of_mem_take hy))
  have hpart := hitems x hx
  rw [hx1] at hpart
  have hall : (Nat.pred K :: (Bq ++ A).take s ++ (Bq ++ A).drop s) = (K - 1) :: (Bq ++ A) := by
    rw [List.cons_append, htd]; rfl
  have hq : ((Bq ++ A).drop s).Perm
      ((Nat.pred K :: (Bq ++ A).take s).foldl erase1 (List.range K)) :=
    perm_foldl_erase1 _ _ _ (by rw [hall]; exact hRperm.trans hPperm)
  have hremlen : ((Nat.pred K :: (Bq ++ A).take s).foldl erase1 (List.range K)).length =
      Nat.sub K (Nat.succ ((Bq ++ A).take s).length) := by
    rw [← hq.length_eq, List.length_drop, hRlen, htlen]
    show K - 1 - s = K - (s + 1)
    omega
  obtain ⟨tb, ht⟩ := go_sound _ _ _ _ _ _ hpart hremlen _ hq
  rw [← List.foldl_append, hall] at ht
  -- the code the leaf saw is that of `a ++ b`, and `p` is `b ++ a`
  have hcode : ((K - 1) :: (Bq ++ A)).foldl step 0 = code (A.reverse ++ (Bq.reverse ++ [K - 1])) := by
    have := foldl_step_reverse (A.reverse ++ (Bq.reverse ++ [K - 1]))
    rw [← this]
    simp
  have hp : p.map Fin.val = (Bq.reverse ++ [K - 1]) ++ A.reverse := by
    rw [← hPrev, hAB]
    simp
  rw [hcode] at ht
  obtain ⟨pos, r, hpos, hr, hwin⟩ := leafCyc_sound hmW hh0' ht
  have hAlt : ∀ x ∈ A.reverse, x < 16 := by
    intro x hx
    have : x ∈ P := by rw [hAB]; exact List.mem_append_left _ (List.mem_reverse.mp hx)
    exact Nat.lt_of_lt_of_le (hPlt x this) hK16
  have hBlt : ∀ x ∈ Bq.reverse ++ [K - 1], x < 16 := by
    intro x hx
    have : x ∈ P := by
      rw [hAB]
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_reverse.mp h))
      · rw [List.mem_singleton.mp h]; exact List.mem_append_right _ (List.mem_cons_self ..)
    exact Nat.lt_of_lt_of_le (hPlt x this) hK16
  have hablen : A.reverse.length + (Bq.reverse ++ [K - 1]).length = K := by
    have := hPlen
    rw [hAB] at this
    simp at this ⊢
    omega
  obtain ⟨i, hi, hrot⟩ := rot_window A.reverse (Bq.reverse ++ [K - 1]) hK8 hablen (by simp)
    hAlt hBlt hr hM
  have hwin' : W / 16 ^ (pos + i) % 16 ^ K = code (p.map Fin.val) := by
    rw [hp, ← hrot, Nat.pow_add, ← Nat.div_div_eq_div_mul, ← mod_div_mod _ (2 * K - 1) i K (by omega),
      hwin, mod_div_mod _ (2 * K - 1) i K (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  exact infix_of_window hK hK16 p hplen (by omega) hwin'

/-- The grouped form (see `Superperm/Groups.lean`): the branches are those of all groups, and
the groups list every choice of `s + 1` symbols below `K-1`. -/
theorem covers_of_cyc_groups {K K1 Kw L S mS mW M B d h0 W stride s : Nat} {tree : WT}
    (hK : 0 < K) (hK8 : 8 ≤ K) (hK16 : K ≤ 16) (hK1 : K = K1 + 1) (hKw : Kw = 2 * K - 1)
    (hmW : mW = 2 ^ (4 * Kw) - 1)
    (hM : M = 1 + 16 ^ K * (1 + 16 ^ K * (1 + 16 ^ K)))
    (hh0 : h0 = 4 * (B * 2 ^ (d - 1)))
    (htree : chkT B Kw d tree W = true)
    (hs : s + 2 ≤ K)
    (groups : List (List (List Nat) × List (List Nat × Nat)))
    (hok : ∀ g ∈ groups, ∀ x ∈ g.2, partCyc K Kw L S mS mW M h0 tree stride x.1 x.2 = true)
    (htails : tailsComplete K1 s groups = true)
    (hgroups : ∀ g ∈ groups, groupOK K1 g.1 g.2 = true) :
    Covers (wordOf K L W hK) := by
  apply covers_of_cyc hK hK8 hK16 hK1 hKw hmW hM hh0 htree hs (groups.flatMap Prod.snd)
  · intro x hx
    obtain ⟨g, hg, hxg⟩ := List.mem_flatMap.mp hx
    exact hok g hg x hxg
  · exact hpre_of_groups htails hgroups

end LiteralSuperperm
