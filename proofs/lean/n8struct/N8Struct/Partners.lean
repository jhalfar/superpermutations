import N8Struct.PackBase

/-!
# The placements that miss the identity placement

`partners_complete`: a placement disjoint from the identity placement starts at one of the 21 states
`partners`.  The check over the 720 states is split into six kernel `decide`s, one per first letter of
the state (120 states each).  For a state `h` that is not a partner the check finds a row `x` of the
identity walk whose renamed loop `canon (h x)` is a loop of the identity walk; since
`placement h = h · placement id6`, the two placements meet there.
-/

namespace N8Struct

open SuperpermutationUpperBound

/-- The part of `allStatesB` with first letter `a`. -/
def allStatesFromB (a : Nat) (p : State → Bool) : Bool :=
  (List.range 6).all fun b => b == a ||
  (List.range 6).all fun c => c == a || c == b ||
  (List.range 6).all fun d => d == a || d == b || d == c ||
  (List.range 6).all fun e => e == a || e == b || e == c || e == d ||
  (List.range 6).all fun f => f == a || f == b || f == c || f == d || f == e ||
  p [a, b, c, d, e, f]

theorem allStatesB_split (p : State → Bool) :
    allStatesB p = (List.range 6).all (fun a => allStatesFromB a p) := rfl

/-- The finite condition: a partner, or a witness that the placements meet. -/
def PartnerOrMeets (h : State) : Prop :=
  h ∈ partners ∨ ∃ x ∈ basesId, canon (relabel h x) ∈ loopsId

instance (h : State) : Decidable (PartnerOrMeets h) := by
  unfold PartnerOrMeets
  infer_instance

theorem check0 : allStatesFromB 0 (fun h => decide (PartnerOrMeets h)) = true := by decide +kernel
theorem check1 : allStatesFromB 1 (fun h => decide (PartnerOrMeets h)) = true := by decide +kernel
theorem check2 : allStatesFromB 2 (fun h => decide (PartnerOrMeets h)) = true := by decide +kernel
theorem check3 : allStatesFromB 3 (fun h => decide (PartnerOrMeets h)) = true := by decide +kernel
theorem check4 : allStatesFromB 4 (fun h => decide (PartnerOrMeets h)) = true := by decide +kernel
theorem check5 : allStatesFromB 5 (fun h => decide (PartnerOrMeets h)) = true := by decide +kernel

theorem partnerOrMeets_all : ∀ h, IsState h → PartnerOrMeets h := by
  apply forall_stateP
  rw [allStatesB_split, List.all_eq_true]
  intro a ha
  have ha6 : a < 6 := List.mem_range.mp ha
  match a, ha6 with
  | 0, _ => exact check0
  | 1, _ => exact check1
  | 2, _ => exact check2
  | 3, _ => exact check3
  | 4, _ => exact check4
  | 5, _ => exact check5

theorem partners_complete : ∀ h, IsState h → Disj (placement id6) (placement h) → h ∈ partners := by
  intro h hh hd
  rcases partnerOrMeets_all h hh with hp | ⟨x, hx, hL⟩
  · exact hp
  · exfalso
    rw [← basesId_eq] at hx
    rw [← loopsId_eq] at hL
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    obtain ⟨s, hs, hse⟩ := List.mem_map.mp hL
    have hr' : relabelRow h r ∈ placement h := by
      rw [placement_eq_map hh]
      exact List.mem_map_of_mem hr
    exact hd s hs (relabelRow h r) hr' hse

theorem partners_states : ∀ h ∈ partners, IsState h := by decide +kernel

theorem partners_disj : ∀ h ∈ partners, Disj (placement id6) (placement h) := by
  intro h hh
  rw [disj_iff_loops, loopsId_eq]
  have ht : (h, loopsOf (placement h)) ∈ partnerTable := by
    rw [← partnerTable_eq]
    exact List.mem_map_of_mem hh
  have hc : ∀ p ∈ partnerTable, ∀ L ∈ loopsId, L ∉ p.2 := by decide +kernel
  exact hc _ ht

end N8Struct

#print axioms N8Struct.partners_complete
#print axioms N8Struct.partners_disj
