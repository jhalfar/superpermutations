import Superperm.Cyc
import Superperm.TreeOk

/-!
# Twelve symbols: the tree checked leaf by leaf, and branches in groups two levels deep

**The tree.**  `Superperm/TreeOk.lean` replaces the check `chkT` of `Superperm/Cyc.lean`, which
computes on the whole word, by `okT`, which looks at single blocks, and proves that the tree is
then `build B K d (valT B d tree)`.  `chkT_build` turns that into the hypothesis of
`covers_of_cyc`.

**Groups.**  `Superperm/Groups.lean` extends the tails of a group by one symbol.  With 55,440
branches the list of tails itself (7,920) would be too long for one check, so `groupOKj` extends
by `j` symbols (`extAll`); with `j = 2` the list of tails has 990 entries.
-/

namespace LiteralSuperperm

open SuperpermutationBounds

theorem chkT_build (B K : Nat) : ∀ (d x : Nat), chkT B K d (build B K d x) x = true := by
  intro d
  induction d with
  | zero =>
    intro x
    show Nat.beq x x = true
    exact Nat.beq_refl x
  | succ d ih =>
    intro x
    have hsh : Nat.shiftLeft 1 (Nat.mul 4 (Nat.add (Nat.mul B (Nat.pow 2 d)) K)) =
        Nat.pow 2 (Nat.mul 4 (Nat.add (Nat.mul B (Nat.pow 2 d)) K)) := Nat.one_shiftLeft _
    show (chkT B K d (build B K d (Nat.land x
          (Nat.sub (Nat.pow 2 (Nat.mul 4 (Nat.add (Nat.mul B (Nat.pow 2 d)) K))) 1)))
        (Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.mul 4 (Nat.add (Nat.mul B (Nat.pow 2 d)) K))) 1)) &&
      chkT B K d (build B K d (Nat.shiftRight x (Nat.mul 4 (Nat.mul B (Nat.pow 2 d)))))
        (Nat.shiftRight x (Nat.mul 4 (Nat.mul B (Nat.pow 2 d))))) = true
    rw [hsh, ih, ih]
    rfl

/-! ### Groups whose tails are extended by `j` symbols -/

/-- `f` holds for every list made from `t` by putting `j` more symbols below `K` in front, one
after the other, each different from those already there. -/
def extAll (K : Nat) (f : List Nat → Bool) : Nat → List Nat → Bool
  | 0, t => f t
  | j + 1, t => ((List.range K).filter fun a => !t.contains a).all fun a => extAll K f j (a :: t)

theorem extAll_sound (K : Nat) (f : List Nat → Bool) : ∀ (j : Nat) (t e : List Nat),
    extAll K f j t = true → e.length = j → (e ++ t).Nodup → (∀ a ∈ e, a < K) →
    f (e ++ t) = true := by
  intro j
  induction j with
  | zero =>
    intro t e h hlen _ _
    have : e = [] := List.length_eq_zero_iff.mp hlen
    subst this
    exact h
  | succ j ih =>
    intro t e h hlen hnd hlt
    rcases List.eq_nil_or_concat e with he | ⟨e', b, he⟩
    · subst he
      simp at hlen
    · rw [List.concat_eq_append] at he
      subst he
      have hlen' : e'.length = j := by simpa using hlen
      have heq : e' ++ [b] ++ t = e' ++ (b :: t) := by simp
      rw [heq] at hnd ⊢
      have hbt : (b :: t).Nodup := hnd.sublist (List.sublist_append_right _ _)
      have hb : b ∈ (List.range K).filter fun a => !t.contains a := by
        rw [List.mem_filter, List.mem_range]
        refine ⟨hlt b (by simp), ?_⟩
        simpa using (List.nodup_cons.mp hbt).1
      have h1 : extAll K f j (b :: t) = true := List.all_eq_true.mp h b hb
      exact ih (b :: t) e' h1 hlen' hnd (fun a ha => hlt a (by simp [ha]))

/-- Every tail of the group, extended by any `j` symbols, is the first component of an item of
the group. -/
def groupOKj (K j : Nat) (tails : List (List Nat)) (its : List (List Nat × Nat)) : Bool :=
  tails.all fun t => extAll K (fun pre => its.any fun x => x.1 == pre) j t

theorem hpre_of_groupsj {K s j : Nat} {groups : List (List (List Nat) × List (List Nat × Nat))}
    (htails : tailsComplete K s groups = true)
    (hgroups : ∀ g ∈ groups, groupOKj K j g.1 g.2 = true) :
    ∀ pre : List Nat, pre.length = s + j → pre.Nodup → (∀ a ∈ pre, a < K) →
      ∃ x ∈ groups.flatMap Prod.snd, x.1 = pre := by
  intro pre hlen hnd hlt
  have htd : pre.take j ++ pre.drop j = pre := List.take_append_drop j pre
  have htmem : pre.drop j ∈ prefixes K s :=
    mem_prefixes K s (pre.drop j) (by rw [List.length_drop, hlen]; omega)
      (hnd.sublist (List.drop_sublist j pre)) (fun b hb => hlt b (List.mem_of_mem_drop hb))
  have heq : groups.flatMap Prod.fst = prefixes K s := by
    simpa [tailsComplete] using htails
  rw [← heq] at htmem
  obtain ⟨g, hg, htg⟩ := List.mem_flatMap.mp htmem
  have h1 := List.all_eq_true.mp (hgroups g hg) (pre.drop j) htg
  have h2 := extAll_sound K _ j (pre.drop j) (pre.take j) h1
    (by rw [List.length_take, hlen]; omega) (by rw [htd]; exact hnd)
    (fun a ha => hlt a (List.mem_of_mem_take ha))
  rw [htd] at h2
  obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp h2
  exact ⟨x, List.mem_flatMap.mpr ⟨g, hg, hx⟩, by simpa using hxe⟩

/-! ### Soundness in the form the generated files for twelve symbols use -/

/-- `covers_of_cyc` with the tree given as `build … W`. -/
theorem covers_of_cyc_tree {K K1 Kw L S mS mW M B d h0 W stride s : Nat} {tree : WT}
    (hK : 0 < K) (hK8 : 8 ≤ K) (hK16 : K ≤ 16) (hK1 : K = K1 + 1) (hKw : Kw = 2 * K - 1)
    (hmW : mW = 2 ^ (4 * Kw) - 1)
    (hM : M = 1 + 16 ^ K * (1 + 16 ^ K * (1 + 16 ^ K)))
    (hh0 : h0 = 4 * (B * 2 ^ (d - 1)))
    (htree : tree = build B Kw d W)
    (hs : s + 1 ≤ K)
    (items : List (List Nat × Nat))
    (hitems : ∀ x ∈ items, partCyc K Kw L S mS mW M h0 tree stride x.1 x.2 = true)
    (hpre : ∀ t : List Nat, t.length = s → t.Nodup → (∀ a ∈ t, a < K1) →
      ∃ x ∈ items, x.1 = t) :
    Covers (wordOf K L W hK) :=
  covers_of_cyc hK hK8 hK16 hK1 hKw hmW hM hh0 (by rw [htree]; exact chkT_build _ _ _ _) hs
    items hitems hpre

/-- **Soundness, leaf-by-leaf tree and groups `j` levels deep.**  The word is the one the tree
spells. -/
theorem covers_of_cyc_ok {K K1 Kw L S mS mW M B d h0 stride s j : Nat} {tree : WT}
    (hK : 0 < K) (hK8 : 8 ≤ K) (hK16 : K ≤ 16) (hK1 : K = K1 + 1) (hKw : Kw = 2 * K - 1)
    (hmW : mW = 2 ^ (4 * Kw) - 1)
    (hM : M = 1 + 16 ^ K * (1 + 16 ^ K * (1 + 16 ^ K)))
    (hh0 : h0 = 4 * (B * 2 ^ (d - 1)))
    (hKB : Kw ≤ B)
    (htree : okT B Kw mW d tree = true)
    (hs : s + j + 1 ≤ K)
    (groups : List (List (List Nat) × List (List Nat × Nat)))
    (hok : ∀ g ∈ groups, ∀ x ∈ g.2, partCyc K Kw L S mS mW M h0 tree stride x.1 x.2 = true)
    (htails : tailsComplete K1 s groups = true)
    (hgroups : ∀ g ∈ groups, groupOKj K1 j g.1 g.2 = true) :
    Covers (wordOf K L (valT B d tree) hK) := by
  apply covers_of_cyc_tree hK hK8 hK16 hK1 hKw hmW hM hh0 (okT_sound hmW hKB d tree htree).1 hs
    (groups.flatMap Prod.snd)
  · intro x hx
    obtain ⟨g, hg, hxg⟩ := List.mem_flatMap.mp hx
    exact hok g hg x hxg
  · exact hpre_of_groupsj htails hgroups

end LiteralSuperperm
