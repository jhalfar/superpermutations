import SuperpermutationUpperBound43586371.BlockUp

/-!
# Pointer certificates for part of the ports of a trail

A trail with many rows and ports can need more memory in one kernel check than allowed. `PortsRange`
is the pointer certificate restricted to the ports `lo ≤ j < hi`; ranges that fit together give the
full certificate (`PortsCovered`).
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound.Certificates.CircleBase

/-- The pointer certificate for the ports `lo ≤ j < hi` of the trail `W`. -/
def PortsRange (W : List (Row Nat)) (circles : List (List Nat)) (h lo hi : Nat)
    (ptrs : List MixedPointer) : Prop :=
  ∀ j < h, lo ≤ j → j < hi → ∃ p ∈ ptrs, p.component = 0 ∧ p.port = j ∧ p.Valid [W] circles 10 h

instance (W : List (Row Nat)) (circles : List (List Nat)) (h lo hi : Nat)
    (ptrs : List MixedPointer) : Decidable (PortsRange W circles h lo hi ptrs) := by
  unfold PortsRange
  infer_instance

theorem portsRange_append {L : List (List (Row Nat))} {circles : List (List Nat)}
    {h lo mid hi : Nat} {m1 m2 : List MixedPointer}
    (h1 : ∀ W ∈ L, PortsRange W circles h lo mid m1)
    (h2 : ∀ W ∈ L, PortsRange W circles h mid hi m2) :
    ∀ W ∈ L, PortsRange W circles h lo hi (m1 ++ m2) := by
  intro W hW j hj hlo hhi
  by_cases hm : j < mid
  · obtain ⟨p, hp, hpj⟩ := h1 W hW j hj hlo hm
    exact ⟨p, List.mem_append_left _ hp, hpj⟩
  · obtain ⟨p, hp, hpj⟩ := h2 W hW j hj (by omega) hhi
    exact ⟨p, List.mem_append_right _ hp, hpj⟩

theorem portsCovered_of_range {L : List (List (Row Nat))} {circles : List (List Nat)}
    {h : Nat} {m : List MixedPointer} (hr : ∀ W ∈ L, PortsRange W circles h 0 h m) :
    ∀ W ∈ L, ∃ m, PortsCovered W circles h m :=
  fun W hW => ⟨m, fun j hj => hr W hW j hj (Nat.zero_le _) hj⟩

end SuperpermutationUpperBound43586371
