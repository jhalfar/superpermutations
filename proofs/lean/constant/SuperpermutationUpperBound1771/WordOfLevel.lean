import SuperpermutationUpperBound1771.Levels
import SuperpermutationUpperBound.Assembly.CircleRows

/-!
# From one level to a word

`word_of_level` completes a level once and joins the closed trails with connector cycles.
It is the list form of `GenericBounds.family_word_ledger`: the hypotheses are a level whose
rows meet every 2-loop (`BlockComplete`) and a cycle cover of its trails (`SafeComp`); the
conclusion is the ledger of `exists_word_of_circle_rows`, with the row and class counts of the
completion written out.  `overlap_bound` is the arithmetic of
`Bounds.circle_overlap_length_bound`, proved again here because that file imports the
ten-symbol family.
-/

namespace SuperpermutationUpperBound1771

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

theorem univ_flatMap_getElem_perm (cc : List (List (Row Nat))) :
    ((Finset.univ.toList : List (Fin cc.length)).flatMap (fun i => cc[i.val])).Perm
      cc.flatten := by
  have hu : (Finset.univ.toList : List (Fin cc.length)).Perm (List.finRange cc.length) :=
    (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (List.nodup_finRange _)).mpr (by simp)
  have h1 := hu.flatMap_right (fun i : Fin cc.length => cc[i.val])
  have h2 : (List.finRange cc.length).flatMap (fun i => cc[i.val]) = cc.flatten := by
    rw [List.flatMap_def, List.map_getElem_finRange]
  rw [h2] at h1
  exact h1

/-- One completion of a level, joined by connector cycles: a word with its exact ledger. -/
theorem word_of_level {A : List Nat} {h : Nat} {comps : List (List (Row Nat))}
    {circles : List (List Nat)} {K ell : Nat} (hK : K = h + 3) (hell : ell ≤ h)
    (L : Level A h comps) (hA : A.length = h + 1) (hn : 3 ≤ h + 1)
    (hAnodup : A.Nodup) (hA9 : 9 ∉ A) (hA10 : 10 ∉ A)
    (hfull : (10 :: (A ++ [9])).Perm (List.range K))
    (hcomplete : BlockComplete A comps.flatten)
    (hvalid : CircleFamilyValid h circles)
    (hsafe : ∀ rs ∈ comps, SafeComp rs 10 h circles)
    (S : Finset Nat) (hS : ∀ c ∈ circles, ∀ a ∈ c, a ∈ S)
    (hcs : ∀ c ∈ circles, ∀ a ∈ c, a < K) :
    ∃ t J : Nat, ∃ w : Word K, IsSuperpermutation w ∧ t ≤ circles.length ∧
      J ≤ min t (S.card.descFactorial ell) ∧
      w.length = (K + 1) * ((h + 1) * (h + 1 + 1) * comps.flatten.length) +
        ((h + 1) * comps.flatten.length + (comps.flatten.map Row.charge).sum) +
        h * circles.length + (h - 1) * t - ell * (t - J) := by
  subst hK
  have hb := L.basedOn_flatten
  have hperm := completionComps_flatten_perm comps 10 h hn (L.len hA) L.kind
  have hrowmem : ∀ (i : Fin (completionComps comps 10 h).length) (r : Row Nat),
      r ∈ (completionComps comps 10 h)[i.val] → r ∈ Completion.packingRows comps.flatten 10 :=
    fun i r hr => hperm.mem_iff.mp (List.mem_flatten.mpr ⟨_, List.getElem_mem i.isLt, hr⟩)
  have hvalidrows := Completion.packingRows_valid hb hA10 (by decide : (10 : Nat) ≠ 9)
  have hne : A ≠ [] := by
    intro he
    rw [he] at hA
    simp at hA
  obtain ⟨t, J, w, hw, ht, hJ, hl⟩ := exists_word_of_circle_rows
    (I := Fin (completionComps comps 10 h).length) (K := h + 3) (ell := ell)
    (fun i => (completionComps comps 10 h)[i.val]) circles (by omega) (by omega)
    (fun i r hr => by
      have := (hvalidrows r (hrowmem i r hr)).2
      omega)
    (fun i r hr => (hvalidrows r (hrowmem i r hr)).1.2.2.1)
    (fun i => L.completion_closed 10 hA hn _ (List.getElem_mem i.isLt))
    (by simpa using hvalid)
    (fun i => by
      obtain ⟨rs, hrs, q, hq, he⟩ := mem_completionComps.mp
        (List.getElem_mem (l := completionComps comps 10 h) i.isLt)
      obtain ⟨c, hc, v, hv, hcv⟩ := (hsafe rs hrs).sound hvalid hn ⟨q, hq⟩
      refine ⟨c, hc, v, ?_, hcv⟩
      show HeadVertex (completionComps comps 10 h)[i.val] v
      rw [he]
      exact hv)
    S hS hcs
    (fun i r hr a ha => List.mem_range.mp
      (hfull.mem_iff.mp (Completion.packingRows_word_mem hb (hrowmem i r hr) ha)))
    (fun p hp => by
      obtain ⟨r, hr, has⟩ := Completion.packingRows_cover hb hcomplete hAnodup hne hA9 hA10
        (by decide) (hp.trans hfull.symm)
      obtain ⟨W, hW, hrW⟩ := List.mem_flatten.mp (hperm.mem_iff.mpr hr)
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hW
      exact ⟨⟨i, hi⟩, r, hrW, has⟩)
  refine ⟨t, J, w, hw, ht, hJ, ?_⟩
  have hfl := (univ_flatMap_getElem_perm (completionComps comps 10 h)).trans hperm
  have hvis := (hfl.map Row.visible).sum_eq
  have hcount := hfl.length_eq
  have hr : ∀ r ∈ comps.flatten, r.Valid ∧ r.base.length = h + 1 :=
    fun r hr => ⟨(hb r hr).1, (hb r hr).2.1.length_eq.trans hA⟩
  rw [Completion.packingRows_visible_sum 10 (h + 1) hr] at hvis
  rw [Completion.packingRows_length 10 (h + 1) hr] at hcount
  rw [hl, hvis, hcount]
  simp only [show h + 3 - 3 = h by omega, show h + 3 - 4 = h - 1 by omega]

/-- The overlap ledger is at most the bound with `c` components. -/
theorem overlap_bound {base m a t J c V len : Nat} (ha : 2 ≤ a) (ham : a ≤ m) (ht : t ≤ c)
    (hj : J ≤ min t V) (hlen : len = base + (m - 2) * t - (m - a) * (t - J)) :
    len ≤ base + (a - 2) * c + (m - a) * min c V := by
  have hJt : J ≤ t := (Nat.le_min.mp hj).1
  have hJV : J ≤ V := (Nat.le_min.mp hj).2
  have hJm : J ≤ min c V := Nat.le_min.mpr ⟨hJt.trans ht, hJV⟩
  obtain ⟨x, rfl⟩ : ∃ x, m = a + x := ⟨m - a, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, a = y + 2 := ⟨a - 2, by omega⟩
  have e1 : y + 2 + x - 2 = y + x := by omega
  have e2 : y + 2 + x - (y + 2) = x := by omega
  have e3 : y + 2 - 2 = y := by omega
  rw [e1, e2] at hlen
  rw [e2, e3]
  have h1 : x * (t - J) + x * J = x * t := by rw [← Nat.mul_add, Nat.sub_add_cancel hJt]
  have h2 : x * J ≤ x * min c V := Nat.mul_le_mul_left x hJm
  have h3 : y * t ≤ y * c := Nat.mul_le_mul_left y ht
  rw [Nat.add_mul] at hlen
  generalize x * (t - J) = p1 at *
  generalize x * J = p2 at *
  generalize x * t = p3 at *
  generalize x * min c V = p4 at *
  generalize y * t = p5 at *
  generalize y * c = p6 at *
  omega

end SuperpermutationUpperBound1771
