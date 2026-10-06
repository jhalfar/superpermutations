import SuperpermutationUpperBound.CircleTransport.TrackCounts
import SuperpermutationUpperBound.Foundation.SupportedWords

/-!
# Closed walks whose winding is not divisible by the number of ports

The transport lemmas (`transportWalk_closedTrail`, `transportWalk_winding_divisible`) assume
`(h : ℤ) ∣ signedExcess rs` for a closed trail `rs` whose rows have `h` ports.  A closed walk
that violates this is not lost.  Written `m` times in a row it is again a closed trail (a list
of row occurrences), its signed excess is `m` times as large, and for `m = h` the hypothesis
holds.  `SafeCircleCover.transport` has no divisibility hypothesis at all.

I use this for the 144 short walks of the selection: each is written nine times and
transported from port 0.  `transportWalk_rep_inventory` says that this lists every transported
row once, provided the ports met at the nine passes are all different.
-/

set_option linter.unusedSectionVars false

namespace SuperpermutationUpperBound1771

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

variable {α : Type} [DecidableEq α]

/-- The walk written `m` times. -/
def rep : Nat → List (Row α) → List (Row α)
  | 0, _ => []
  | m + 1, rs => rs ++ rep m rs

theorem mem_rep {m : Nat} {rs : List (Row α)} {r : Row α} (h : r ∈ rep m rs) : r ∈ rs := by
  induction m with
  | zero => simp [rep] at h
  | succ m ih =>
    rcases List.mem_append.mp h with h | h
    · exact h
    · exact ih h

theorem signedExcess_append (a b : List (Row α)) :
    signedExcess (a ++ b) = signedExcess a + signedExcess b := by
  simp only [signedExcess, List.length_append, List.map_append, List.sum_append]
  push_cast
  ring

theorem signedExcess_rep (m : Nat) (rs : List (Row α)) :
    signedExcess (rep m rs) = (m : Int) * signedExcess rs := by
  induction m with
  | zero => simp [rep, signedExcess]
  | succ m ih =>
    rw [rep, signedExcess_append, ih]
    push_cast
    ring

theorem pathRunsTo_rep {first : Row α} {rest : List (Row α)}
    (h : PathRunsTo (first :: rest) first) (m : Nat) :
    PathRunsTo (rep (m + 1) (first :: rest)) first := by
  induction m with
  | zero => simpa [rep] using h
  | succ m ih =>
    have he : rep (m + 1) (first :: rest) = first :: (rest ++ rep m (first :: rest)) := rfl
    rw [he] at ih
    have h2 := pathRunsTo_append h ih
    simpa [rep] using h2

/-- A closed trail written `m ≥ 1` times is a closed trail. -/
theorem closedTrail_rep {rs : List (Row α)} (hc : ClosedTrail rs) {m : Nat} (hm : 0 < m) :
    ClosedTrail (rep m rs) := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hc.1
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hh := hc.2
  change ∀ pair ∈ (first :: rest).zip (rot (first :: rest) 1), _ at hh
  rw [rot_cons_one] at hh
  have hp : PathRunsTo (first :: rest) first :=
    (rowTrailCompatible_loop_iff_zip first first rest).mpr hh
  have hr := pathRunsTo_rep hp m
  have he : rep (m + 1) (first :: rest) = first :: (rest ++ rep m (first :: rest)) := rfl
  rw [he] at hr ⊢
  exact closedTrail_of_pathRunsTo hr

/-- The transport of the `m`-fold walk is a closed trail from every port, and it satisfies
the divisibility condition one level up. -/
theorem transported_rep_closed {rs : List (Row α)} (hc : ClosedTrail rs) {m : Nat} (hm : 0 < m)
    (newOrd : α) (h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hdiv : (h : Int) ∣ (m : Int) * signedExcess rs) (p : Nat) (hp : p < h) :
    ClosedTrail (transportWalk (rep m rs) newOrd p) ∧
      ((h + 1 : Nat) : Int) ∣ signedExcess (transportWalk (rep m rs) newOrd p) := by
  have hlen' : ∀ r ∈ rep m rs, r.base.length = h + 1 := fun r hr => hlen r (mem_rep hr)
  have hkind' : ∀ r ∈ rep m rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2 :=
    fun r hr => hkind r (mem_rep hr)
  have hw : (h : Int) ∣ signedExcess (rep m rs) := by rw [signedExcess_rep]; exact hdiv
  exact ⟨transportWalk_closedTrail (closedTrail_rep hc hm) newOrd h hn hlen' hkind' hw p hp,
    transportWalk_winding_divisible (rep m rs) newOrd h hn hlen' hkind' hw p hp⟩

/-- Transporting a concatenation: the second part starts at the port where the first ends. -/
theorem transportWalk_append (pre post : List (Row α)) (newOrd : α) (p : Nat) :
    transportWalk (pre ++ post) newOrd p =
      transportWalk pre newOrd p ++ transportWalk post newOrd (completionExit pre p) := by
  induction pre generalizing p with
  | nil => rfl
  | cons r pre ih =>
    simp only [List.cons_append, transportWalk, completionExit, ih, List.append_assoc]

/-- The ports at which the passes of the `m`-fold walk start. -/
def orbitPorts (rs : List (Row α)) : Nat → Nat → List Nat
  | 0, _ => []
  | m + 1, p => p :: orbitPorts rs m (completionExit rs p)

theorem transportWalk_rep (rs : List (Row α)) (newOrd : α) (m p : Nat) :
    transportWalk (rep m rs) newOrd p =
      (orbitPorts rs m p).flatMap (fun q => transportWalk rs newOrd q) := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih =>
    rw [rep, transportWalk_append, ih]
    rfl

/-- If the passes start at all `h` ports, once each, the transported `m`-fold walk lists
the transported rows of the walk once each. -/
theorem transportWalk_rep_inventory (rs : List (Row α)) (newOrd : α) (h m p : Nat)
    (hn : 3 ≤ h + 1) (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hports : (orbitPorts rs m p).Perm (List.range h)) :
    (transportWalk (rep m rs) newOrd p).Perm (Transport.packingRows rs newOrd) := by
  rw [transportWalk_rep]
  have h1 := hports.flatMap_right (fun q => transportWalk rs newOrd q)
  have h2 := transportWalk_inventory rs newOrd h hn hlen
  have h3 : (List.finRange h).flatMap (fun p => transportWalk rs newOrd p.val) =
      (List.range h).flatMap (fun q => transportWalk rs newOrd q) := by
    rw [← map_val_finRange h, List.flatMap_map]
  rw [h3] at h2
  exact h1.trans h2

end SuperpermutationUpperBound1771
