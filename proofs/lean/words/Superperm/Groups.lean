import Superperm.Literal

/-!
# Many branches: completeness of the list of branches, checked group by group

`covers_of_parts` needs to know that the certificate has a branch for every duplicate-free
choice of the first symbols.  `itemsComplete` checks that in one kernel computation, whose
cost grows faster than the number of branches (0.6 s for 720 branches, more than 30 s and
1 GB for 5,040).  For a certificate with thousands of branches the branches come in groups
(one per generated file); a group lists the tails it covers (a tail is a branch without its
first choice) and is checked on its own, and one more check says that the tails of all
groups are exactly `prefixes K s`.
-/

namespace LiteralSuperperm

open SuperpermutationBounds

/-- Every tail `t` of the group, extended by any symbol `a` that does not occur in it, is the
first component of an item of the group. -/
def groupOK (K : Nat) (tails : List (List Nat)) (its : List (List Nat × Nat)) : Bool :=
  tails.all fun t =>
    ((List.range K).filter fun a => !t.contains a).all fun a =>
      its.any fun x => x.1 == a :: t

/-- The tails of all groups are, in order, the list `prefixes K s`. -/
def tailsComplete (K s : Nat) (groups : List (List (List Nat) × List (List Nat × Nat))) : Bool :=
  groups.flatMap Prod.fst == prefixes K s

theorem hpre_of_groups {K s : Nat} {groups : List (List (List Nat) × List (List Nat × Nat))}
    (htails : tailsComplete K s groups = true)
    (hgroups : ∀ g ∈ groups, groupOK K g.1 g.2 = true) :
    ∀ pre : List Nat, pre.length = s + 1 → pre.Nodup → (∀ a ∈ pre, a < K) →
      ∃ x ∈ groups.flatMap Prod.snd, x.1 = pre := by
  intro pre hlen hnd hlt
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  have hnd' := List.nodup_cons.mp hnd
  have htmem : t ∈ prefixes K s :=
    mem_prefixes K s t (by simpa using hlen) hnd'.2 (fun b hb => hlt b (by simp [hb]))
  have heq : groups.flatMap Prod.fst = prefixes K s := by
    simpa [tailsComplete] using htails
  rw [← heq] at htmem
  obtain ⟨g, hg, htg⟩ := List.mem_flatMap.mp htmem
  have h1 := List.all_eq_true.mp (hgroups g hg) t htg
  have ha : a ∈ (List.range K).filter fun a => !t.contains a := by
    rw [List.mem_filter, List.mem_range]
    refine ⟨hlt a (by simp), ?_⟩
    simpa using hnd'.1
  have h2 := List.all_eq_true.mp h1 a ha
  obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp h2
  exact ⟨x, List.mem_flatMap.mpr ⟨g, hg, hx⟩, by simpa using hxe⟩

/-- **Soundness, grouped form.**  The items are those of all groups. -/
theorem covers_of_groups {K L mS mK B d W stride s : Nat} (hK : 0 < K) (hK16 : K ≤ 16)
    (hmK : mK = 2 ^ (4 * K) - 1) (hs : s + 1 ≤ K)
    (groups : List (List (List Nat) × List (List Nat × Nat)))
    (hok : ∀ g ∈ groups, ∀ x ∈ g.2, part K L mS mK B d W stride x.1 x.2 = true)
    (htails : tailsComplete K s groups = true)
    (hgroups : ∀ g ∈ groups, groupOK K g.1 g.2 = true) :
    Covers (wordOf K L W hK) := by
  apply covers_of_parts hK hK16 hmK hs (groups.flatMap Prod.snd)
  · intro x hx
    obtain ⟨g, hg, hxg⟩ := List.mem_flatMap.mp hx
    exact hok g hg x hxg
  · exact hpre_of_groups htails hgroups

end LiteralSuperperm
