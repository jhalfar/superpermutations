import Challenge
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Range

/-!
# A kernel-checkable certificate that a literal word is a superpermutation

The word is one natural number `W` whose base-16 digits, least significant
first, are the symbols.  A certificate is a table of positions: for every
permutation `p` of `0, …, K-1` it names a position `pos` such that the `K`
digits of `W` starting at `pos` spell `p`.

`part` walks the tree of all arrangements of the unused symbols (one level
per symbol), slicing the table as it descends, and at every leaf compares
the window of `W` at the tabulated position with the arrangement it has
built.  Nothing about the table has to be proven: a wrong entry makes the
comparison fail.  `covers_of_parts` turns successful runs of `part`, one
for each way of fixing the first `s` choices, into
`SuperpermutationBounds.Covers` for the word spelt by `W`.

All functions that the kernel has to evaluate are written with the bare
`Nat.add`, `Nat.land`, … so that each step is one kernel big-number
operation, and `W` is accessed through a binary tree of small blocks so
that no step copies the whole word.
-/

namespace LiteralSuperperm

open SuperpermutationBounds

/-! ### Base-16 digits -/

/-- The `k` lowest base-16 digits of `x`, least significant first. -/
def digits : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, x => x % 16 :: digits k (x / 16)

@[simp] theorem digits_length (k x : Nat) : (digits k x).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [digits, ih]

theorem digits_add (a b x : Nat) :
    digits (a + b) x = digits a x ++ digits b (x / 16 ^ a) := by
  induction a generalizing x with
  | zero => simp [digits]
  | succ a ih =>
    have h : a + 1 + b = (a + b) + 1 := by omega
    rw [h]
    simp only [digits, List.cons_append, ih]
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ']

theorem digits_mod (k x : Nat) : digits k (x % 16 ^ k) = digits k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [digits]
    rw [Nat.pow_succ', Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self, ih]

/-- Little-endian base-16 value of a list of digits. -/
def code : List Nat → Nat
  | [] => 0
  | a :: t => a + 16 * code t

theorem digits_code (p : List Nat) (h : ∀ a ∈ p, a < 16) :
    digits p.length (code p) = p := by
  induction p with
  | nil => rfl
  | cons a t ih =>
    have ha : a < 16 := h a (by simp)
    have ht : ∀ b ∈ t, b < 16 := fun b hb => h b (by simp [hb])
    simp only [List.length_cons, digits, code]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
      Nat.add_mul_div_left _ _ (by decide : 0 < 16), Nat.div_eq_of_lt ha, Nat.zero_add, ih ht]

/-- The word spelt by `W`: its `L` lowest base-16 digits, as symbols of `Fin K`. -/
def wordOf (K L W : Nat) (hK : 0 < K) : List (Fin K) :=
  (digits L W).map (fun x => ⟨x % K, Nat.mod_lt _ hK⟩)

@[simp] theorem wordOf_length (K L W : Nat) (hK : 0 < K) : (wordOf K L W hK).length = L := by
  simp [wordOf]

/-- If the `K` digits of `W` at `pos` spell `p`, then `p` is a factor of the word. -/
theorem infix_of_window {K L W pos : Nat} (hK : 0 < K) (hK16 : K ≤ 16)
    (p : List (Fin K)) (hp : p.length = K) (hpos : pos + K ≤ L)
    (hwin : W / 16 ^ pos % 16 ^ K = code (p.map Fin.val)) :
    ∃ u v : List (Fin K), wordOf K L W hK = u ++ p ++ v := by
  have hsplit : L = pos + (K + (L - pos - K)) := by omega
  have hd : digits K (W / 16 ^ pos) = p.map Fin.val := by
    rw [← digits_mod, hwin]
    have hlen : (p.map Fin.val).length = K := by simp [hp]
    have h := digits_code (p.map Fin.val) (by
      intro a ha
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
      exact Nat.lt_of_lt_of_le x.isLt hK16)
    rwa [hlen] at h
  have hback : (p.map Fin.val).map (fun x => (⟨x % K, Nat.mod_lt _ hK⟩ : Fin K)) = p := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id p]
    apply List.map_congr_left
    intro a _
    exact Fin.ext (Nat.mod_eq_of_lt a.isLt)
  refine ⟨(digits pos W).map (fun x => ⟨x % K, Nat.mod_lt _ hK⟩),
    (digits (L - pos - K) (W / 16 ^ pos / 16 ^ K)).map (fun x => ⟨x % K, Nat.mod_lt _ hK⟩), ?_⟩
  unfold wordOf
  conv_lhs => rw [hsplit]
  rw [digits_add, digits_add, hd, List.map_append, List.map_append, hback, List.append_assoc]

/-! ### Random access to the digits of `W` through a tree of blocks -/

/-- A binary tree whose leaves hold short stretches of the word. -/
inductive WT where
  | leaf (x : Nat)
  | node (l r : WT)

/-- `build B K d x`: a tree of depth `d` over the digits of `x`.  A subtree of
depth `d` serves the positions below `B * 2 ^ d`; its left half keeps `K`
digits beyond its own range, so that every window of `K` digits lies inside
one leaf. -/
def build (B K : Nat) : Nat → Nat → WT
  | 0, x => .leaf x
  | d + 1, x =>
    .node
      (build B K d (Nat.land x
        (Nat.sub (Nat.pow 2 (Nat.mul 4 (Nat.add (Nat.mul B (Nat.pow 2 d)) K))) 1)))
      (build B K d (Nat.shiftRight x (Nat.mul 4 (Nat.mul B (Nat.pow 2 d)))))

/-- A number whose `K` lowest digits are the digits at `pos` of the number the tree was built from. -/
def get (B : Nat) : Nat → WT → Nat → Nat
  | 0, .leaf x, pos => Nat.shiftRight x (Nat.mul 4 pos)
  | d + 1, .node l r, pos =>
    bif Nat.ble (Nat.succ pos) (Nat.mul B (Nat.pow 2 d)) then get B d l pos
    else get B d r (Nat.sub pos (Nat.mul B (Nat.pow 2 d)))
  | _, _, _ => 0

theorem shiftRight_four_mul (x pos : Nat) : x >>> (4 * pos) = x / 16 ^ pos := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem get_build (B K : Nat) : ∀ (d x pos : Nat),
    get B d (build B K d x) pos % 16 ^ K = x / 16 ^ pos % 16 ^ K := by
  intro d
  induction d with
  | zero =>
    intro x pos
    show (x >>> (4 * pos)) % 16 ^ K = _
    rw [shiftRight_four_mul]
  | succ d ih =>
    intro x pos
    by_cases hlt : pos < B * 2 ^ d
    · have hb : Nat.ble (Nat.succ pos) (Nat.mul B (Nat.pow 2 d)) = true :=
        Nat.ble_eq_true_of_le hlt
      show (bif Nat.ble (Nat.succ pos) (Nat.mul B (Nat.pow 2 d)) then _ else _) % 16 ^ K = _
      rw [hb, cond_true, ih]
      show (x &&& (2 ^ (4 * (B * 2 ^ d + K)) - 1)) / 16 ^ pos % 16 ^ K = _
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.pow_mul]
      have hsum : B * 2 ^ d + K = pos + (B * 2 ^ d + K - pos) := by omega
      have hfour : (2 : Nat) ^ 4 = 16 := by decide
      rw [hfour, hsum, Nat.pow_add, Nat.mod_mul_right_div_self]
      apply Nat.mod_mod_of_dvd
      exact Nat.pow_dvd_pow 16 (by omega)
    · have hb : Nat.ble (Nat.succ pos) (Nat.mul B (Nat.pow 2 d)) = false := by
        rw [← Bool.not_eq_true]
        intro h
        exact hlt (Nat.le_of_ble_eq_true h)
      show (bif Nat.ble (Nat.succ pos) (Nat.mul B (Nat.pow 2 d)) then _ else _) % 16 ^ K = _
      rw [hb, cond_false, ih]
      show (x >>> (4 * (B * 2 ^ d))) / 16 ^ (pos - B * 2 ^ d) % 16 ^ K = _
      rw [shiftRight_four_mul, Nat.div_div_eq_div_mul, ← Nat.pow_add]
      have : B * 2 ^ d + (pos - B * 2 ^ d) = pos := by omega
      rw [this]

/-! ### The walk over all arrangements -/

/-- Remove the first occurrence of `a`. -/
def erase1 : List Nat → Nat → List Nat
  | [], _ => []
  | b :: t, a => bif Nat.beq b a then t else b :: erase1 t a

theorem erase1_eq (l : List Nat) (a : Nat) : erase1 l a = l.erase a := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    by_cases h : b = a
    · subst h
      simp [erase1]
    · have hb : Nat.beq b a = false := by
        rw [← Bool.not_eq_true]
        intro hh
        exact h (Nat.eq_of_beq_eq_true hh)
      simp [erase1, hb, ih, h]

/-- Run `f a t` for every `a` of the list; each `a` gets the table `stride` bits further on. -/
def loop (f : Nat → Nat → Bool) (stride : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | a :: t, tbl => and (f a tbl) (loop f stride t (Nat.shiftRight tbl stride))

theorem loop_sound {f : Nat → Nat → Bool} {stride : Nat} :
    ∀ (l : List Nat) (tbl : Nat), loop f stride l tbl = true →
      ∀ a ∈ l, ∃ t, f a t = true := by
  intro l
  induction l with
  | nil => intro _ _ a ha; simp at ha
  | cons b t ih =>
    intro tbl h a ha
    have h' : (f b tbl && loop f stride t (Nat.shiftRight tbl stride)) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨tbl, h'.1⟩
    · exact ih _ h'.2 a ha

/-- One more symbol appended to a partial arrangement (most significant digit first). -/
def step (c a : Nat) : Nat := Nat.add (Nat.mul c 16) a

/-- All arrangements of the `r` symbols in `rem`, each handed to `leaf` together
with the slice of the table that belongs to it. -/
def go (leaf : Nat → Nat → Bool) : Nat → List Nat → Nat → Nat → Nat → Bool
  | 0, _, c, tbl, _ => leaf c tbl
  | r + 1, rem, c, tbl, stride =>
    loop (fun a t => go leaf r (erase1 rem a) (step c a) t (Nat.div stride r)) stride rem tbl

theorem go_sound (leaf : Nat → Nat → Bool) :
    ∀ (r : Nat) (rem : List Nat) (c tbl stride : Nat),
      go leaf r rem c tbl stride = true → rem.length = r →
      ∀ q : List Nat, q.Perm rem → ∃ t, leaf (q.foldl step c) t = true := by
  intro r
  induction r with
  | zero =>
    intro rem c tbl stride h hlen q hq
    have hrem : rem = [] := List.length_eq_zero_iff.mp hlen
    subst hrem
    have hq' : q = [] := List.perm_nil.mp hq
    subst hq'
    exact ⟨tbl, h⟩
  | succ r ih =>
    intro rem c tbl stride h hlen q hq
    have hqlen : q.length = r + 1 := by rw [hq.length_eq, hlen]
    obtain ⟨a, q', rfl⟩ := List.exists_cons_of_length_eq_add_one hqlen
    have ha : a ∈ rem := hq.subset (by simp)
    obtain ⟨t, ht⟩ := loop_sound rem tbl h a ha
    have hq' : q'.Perm (erase1 rem a) := by
      rw [erase1_eq]
      exact (List.cons_perm_iff_perm_erase.mp hq).2
    have hlen' : (erase1 rem a).length = r := by
      rw [erase1_eq, List.length_erase_of_mem ha, hlen]
      rfl
    exact ih (erase1 rem a) (step c a) t (Nat.div stride r) ht hlen' q' hq'

/-! ### The leaf test and the check for one branch -/

/-- At a leaf: read the position from the table and compare the window of the word with `c`. -/
def leafChk (K L mS mK B d : Nat) (tree : WT) (c tbl : Nat) : Bool :=
  and (Nat.ble (Nat.add (Nat.land tbl mS) K) L)
    (Nat.beq (Nat.land (get B d tree (Nat.land tbl mS)) mK) c)

theorem leafChk_sound {K L mS mK B d W c tbl : Nat} (hmK : mK = 2 ^ (4 * K) - 1)
    (h : leafChk K L mS mK B d (build B K d W) c tbl = true) :
    ∃ pos, pos + K ≤ L ∧ W / 16 ^ pos % 16 ^ K = c := by
  have h' : (Nat.ble (Nat.add (Nat.land tbl mS) K) L &&
      Nat.beq (Nat.land (get B d (build B K d W) (Nat.land tbl mS)) mK) c) = true := h
  rw [Bool.and_eq_true] at h'
  refine ⟨Nat.land tbl mS, Nat.le_of_ble_eq_true h'.1, ?_⟩
  have h2 := Nat.eq_of_beq_eq_true h'.2
  have h3 : get B d (build B K d W) (Nat.land tbl mS) &&& (2 ^ (4 * K) - 1) = c := by
    rw [← hmK]; exact h2
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.pow_mul] at h3
  have hfour : (2 : Nat) ^ 4 = 16 := by decide
  rw [hfour, get_build] at h3
  exact h3

/-- The check for the branch whose first choices are `pre`: every arrangement of
the other symbols, appended to `pre`, is found in the word at the position the
table gives.  (`stride` is the number of table bits of one child subtree.) -/
def part (K L mS mK B d W stride : Nat) (pre : List Nat) (tbl : Nat) : Bool :=
  go (leafChk K L mS mK B d (build B K d W)) (Nat.sub K pre.length)
    (pre.foldl erase1 (List.range K)) (pre.foldl step 0) tbl stride

theorem foldl_step_reverse (p : List Nat) : p.reverse.foldl step 0 = code p := by
  induction p with
  | nil => rfl
  | cons a t ih =>
    rw [List.reverse_cons, List.foldl_append, ih]
    show Nat.add (Nat.mul (code t) 16) a = a + 16 * code t
    show code t * 16 + a = a + 16 * code t
    omega

theorem perm_foldl_erase1 : ∀ (pre q R : List Nat), (pre ++ q).Perm R →
    q.Perm (pre.foldl erase1 R) := by
  intro pre
  induction pre with
  | nil => intro q R h; exact h
  | cons a pre ih =>
    intro q R h
    have h' := (List.cons_perm_iff_perm_erase.mp h).2
    rw [← erase1_eq] at h'
    exact ih q (erase1 R a) h'

/-- A duplicate-free list of `K` numbers below `K` is an arrangement of `0, …, K-1`. -/
theorem perm_range_of_nodup {K : Nat} (l : List Nat) (hlen : l.length = K) (hnd : l.Nodup)
    (hlt : ∀ a ∈ l, a < K) : l.Perm (List.range K) := by
  have hsub : l ⊆ List.range K := fun a ha => List.mem_range.mpr (hlt a ha)
  have hsp : l.Subperm (List.range K) := List.subperm_of_subset hnd hsub
  exact hsp.perm_of_length_le (by simp [hlen])

/-- **Soundness.**  If `part` succeeds for every duplicate-free choice `pre` of the
first `s` symbols, the word spelt by `W` contains every permutation. -/
theorem covers_of_parts {K L mS mK B d W stride s : Nat} (hK : 0 < K) (hK16 : K ≤ 16)
    (hmK : mK = 2 ^ (4 * K) - 1) (hs : s ≤ K)
    (items : List (List Nat × Nat))
    (hitems : ∀ x ∈ items, part K L mS mK B d W stride x.1 x.2 = true)
    (hpre : ∀ pre : List Nat, pre.length = s → pre.Nodup → (∀ a ∈ pre, a < K) →
      ∃ x ∈ items, x.1 = pre) :
    Covers (wordOf K L W hK) := by
  intro p hplen hpnd
  -- the choices, in the order in which the walk makes them: last symbol of `p` first
  let P : List Nat := (p.map Fin.val).reverse
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
  have htd : P.take s ++ P.drop s = P := List.take_append_drop s P
  have hprelen : (P.take s).length = s := by simp [hPlen, hs]
  have hprend : (P.take s).Nodup := hPnd.sublist (List.take_sublist s P)
  have hprelt : ∀ a ∈ P.take s, a < K := fun a ha => hPlt a (List.mem_of_mem_take ha)
  obtain ⟨x, hx, hx1⟩ := hpre (P.take s) hprelen hprend hprelt
  have hpart := hitems x hx
  rw [hx1] at hpart
  have hq : (P.drop s).Perm ((P.take s).foldl erase1 (List.range K)) :=
    perm_foldl_erase1 (P.take s) (P.drop s) (List.range K) (by rw [htd]; exact hPperm)
  have hremlen : ((P.take s).foldl erase1 (List.range K)).length = Nat.sub K (P.take s).length := by
    rw [← hq.length_eq, List.length_drop, hPlen, hprelen]
    rfl
  obtain ⟨t, ht⟩ := go_sound _ _ _ _ _ _ hpart hremlen (P.drop s) hq
  rw [← List.foldl_append, htd] at ht
  have hcode : P.foldl step 0 = code (p.map Fin.val) := foldl_step_reverse _
  rw [hcode] at ht
  obtain ⟨pos, hpos, hwin⟩ := leafChk_sound hmK ht
  exact infix_of_window hK hK16 p hplen hpos hwin

/-! ### All choices of the first `s` symbols -/

/-- All duplicate-free lists of `s` numbers below `K`. -/
def prefixes (K : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | s + 1 => (prefixes K s).flatMap fun pre =>
      ((List.range K).filter fun a => !pre.contains a).map fun a => a :: pre

theorem mem_prefixes (K : Nat) : ∀ (s : Nat) (pre : List Nat), pre.length = s → pre.Nodup →
    (∀ a ∈ pre, a < K) → pre ∈ prefixes K s := by
  intro s
  induction s with
  | zero =>
    intro pre hlen _ _
    have : pre = [] := List.length_eq_zero_iff.mp hlen
    subst this
    simp [prefixes]
  | succ s ih =>
    intro pre hlen hnd hlt
    obtain ⟨a, pre', rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    have hnd' := List.nodup_cons.mp hnd
    have hmem := ih pre' (by simpa using hlen) hnd'.2 (fun b hb => hlt b (by simp [hb]))
    simp only [prefixes, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range]
    refine ⟨pre', hmem, a, ⟨hlt a (by simp), ?_⟩, rfl⟩
    simpa using hnd'.1

/-- The table of branches lists every choice of the first `s` symbols: its first
components are, in order, the list `prefixes K s`. -/
def itemsComplete (K s : Nat) (items : List (List Nat × Nat)) : Bool :=
  items.map Prod.fst == prefixes K s

theorem hpre_of_itemsComplete {K s : Nat} {items : List (List Nat × Nat)}
    (h : itemsComplete K s items = true) :
    ∀ pre : List Nat, pre.length = s → pre.Nodup → (∀ a ∈ pre, a < K) →
      ∃ x ∈ items, x.1 = pre := by
  intro pre hlen hnd hlt
  have hmem := mem_prefixes K s pre hlen hnd hlt
  have heq : items.map Prod.fst = prefixes K s := by
    simpa [itemsComplete] using h
  rw [← heq] at hmem
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hmem
  exact ⟨x, hx, hxe⟩

/-- The form in which the generated files use the result. -/
theorem hasWord_of_parts {K L mS mK B d W stride s : Nat} (hK : 0 < K) (hK16 : K ≤ 16)
    (hmK : mK = 2 ^ (4 * K) - 1) (hs : s ≤ K)
    (items : List (List Nat × Nat))
    (hitems : ∀ x ∈ items, part K L mS mK B d W stride x.1 x.2 = true)
    (hcomplete : itemsComplete K s items = true) :
    HasWord K L :=
  ⟨wordOf K L W hK,
    covers_of_parts hK hK16 hmK hs items hitems (hpre_of_itemsComplete hcomplete),
    by simp⟩

end LiteralSuperperm
