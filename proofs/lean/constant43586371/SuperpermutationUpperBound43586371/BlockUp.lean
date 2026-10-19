import SuperpermutationUpperBound43586371.BlockG

/-!
# What a stage needs from a block, and blocks with cycles chosen one level up

`BlockFam` lists what `Stage.advance` uses about the block placed above every pending loop `d`
(for `d` a permutation of the canonical loop): the relabelled trails one level above the block
(a level), their cycles and the loops without a row, with the counts.  Two kinds of certificate
give one:

* `BlockCert.fam`: the cycles are chosen on the completion of the block level and extended once
  (`BlockG.lean`; the nested ledger of the derivation of the nested constants);
* `BlockCertUp.fam`: the cycles are chosen one level up, on the completion of the trails one
  level above the block (step (B)'s choice: the 26 cycles on 16 symbols of `s103_old2_0`), with a
  pointer certificate for every one of these trails.
-/

namespace SuperpermutationUpperBound43586371

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound.Certificates.CircleBase

/-- What `Stage.advance` uses about the block above a pending loop `d`. -/
structure BlockFam where
  F : Frame
  trailsR : List Nat → List (List (Row Nat))
  circlesR : List Nat → List (List Nat)
  loopsR : List Nat → List (List Nat)
  nrows : Nat
  nq : Nat
  ncirc : Nat
  nd : Nat
  frame : F.OK
  level : ∀ d, d.Perm F.d0 → Level F.alph' (F.h + 1) (trailsR d)
  safe : ∀ d, d.Perm F.d0 → ∀ W ∈ trailsR d, SafeComp W 10 (F.h + 1) (circlesR d)
  valid : ∀ d, d.Perm F.d0 → CircleFamilyValid (F.h + 1) (circlesR d)
  support : ∀ d, d.Perm F.d0 → ∀ c ∈ circlesR d, ∀ a ∈ c, a ∈ 10 :: F.alph'
  rows : ∀ d, (trailsR d).flatten.length = (F.h + 1) * nrows
  charge : ∀ d, ((trailsR d).flatten.map Row.charge).sum = (F.h + 1) * nq
  ncircR : ∀ d, (circlesR d).length = ncirc
  loops_perm : ∀ d, d.Perm F.d0 → ∀ e ∈ loopsR d, e.Perm F.alph
  nloops : ∀ d, (loopsR d).length = nd
  cover : ∀ d, d.Perm F.d0 → ∀ t ∈ above3T F.t1 F.t2 F.t3 d,
    (∀ y, InInsertionBlock F.z t y → ∃ r ∈ (trailsR d).flatten, CyclicEq r.base y) ∨
      (∃ e ∈ loopsR d, CyclicEq e t)

/-- A block with its cycles on the completion of the block level. -/
def BlockCert.fam (K : BlockCert) : BlockFam where
  F := K.F
  trailsR := K.B.trailsR K.F
  circlesR := K.B.circlesR K.F
  loopsR := K.B.loopsR K.F
  nrows := K.B.nrows
  nq := K.B.nq
  ncirc := K.F.h * K.B.ncyc
  nd := K.B.nd
  frame := K.ok.frame
  level := fun _ hd => BlockData.levelR K.ok hd
  safe := fun d _ => BlockData.safeR K.ok K.ports d
  valid := fun _ hd => BlockData.circlesR_valid K.ok hd
  support := fun _ hd => BlockData.circlesR_support K.ok hd
  rows := fun d => (BlockData.countsR K.ok d).1
  charge := fun d => (BlockData.countsR K.ok d).2
  ncircR := fun d => BlockData.circlesR_length K.ok d
  loops_perm := fun _ hd => BlockData.loopsR_perm K.ok hd
  nloops := fun d => BlockData.loopsR_length K.ok d
  cover := fun _ hd _ ht => BlockData.coverR K.ok hd ht

/-- A block with its cycles one level up: `cyc1` meets every trail of `B.trails F` from every
one of its `h + 1` ports.  (`B.cyc` is not used; the certificates set it to `[]`.) -/
structure BlockCertUp where
  F : Frame
  B : BlockData
  ok : BlockOK F B
  cyc1 : List (List Nat)
  valid1 : CircleFamilyValid (F.h + 1) cyc1
  support1 : ∀ c ∈ cyc1, ∀ a ∈ c, a ∈ 10 :: F.alph'
  ports1 : ∀ W ∈ B.trails F, ∃ m, PortsCovered W cyc1 (F.h + 1) m

namespace BlockCertUp

variable (K : BlockCertUp)

def circlesR (d : List Nat) : List (List Nat) := K.cyc1.map (List.map (relab K.F.d0 d))

theorem safe_canon : ∀ W ∈ K.B.trails K.F, SafeComp W 10 (K.F.h + 1) K.cyc1 := by
  intro W hW
  have L := BlockData.level K.ok
  have hA : K.F.alph'.length = K.F.h + 1 + 1 := by
    simp only [Frame.alph', List.length_cons, K.F.alph_length]
  obtain ⟨m, hm⟩ := K.ports1 W hW
  exact hm.safeComp (by have := K.F.hn; omega) (L.len hA W hW) (L.kind W hW)

theorem safeR (d : List Nat) : ∀ W ∈ K.B.trailsR K.F d, SafeComp W 10 (K.F.h + 1) (K.circlesR d) := by
  intro W hW
  obtain ⟨W0, hW0, rfl⟩ := List.mem_map.mp hW
  have h := safeComp_map (relab K.F.d0 d) (K.safe_canon W0 hW0)
  rwa [BlockData.relab_fix K.ok K.ok.frame.ten_d0] at h

theorem validR {d : List Nat} (hd : d.Perm K.F.d0) : CircleFamilyValid (K.F.h + 1) (K.circlesR d) :=
  circleFamilyValid_map _ (BlockData.relab_inj K.ok hd) K.valid1

theorem supportR {d : List Nat} (hd : d.Perm K.F.d0) :
    ∀ c ∈ K.circlesR d, ∀ a ∈ c, a ∈ 10 :: K.F.alph' := by
  intro c hc a ha
  obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
  obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
  by_cases hm : a0 ∈ K.F.d0
  · exact List.mem_cons_of_mem _ (K.ok.frame.sub _ (relab_mem hd hm))
  · rw [BlockData.relab_fix K.ok hm]
    exact K.support1 c0 hc0 a0 ha0

/-- A block with its cycles one level up. -/
def fam : BlockFam where
  F := K.F
  trailsR := K.B.trailsR K.F
  circlesR := K.circlesR
  loopsR := K.B.loopsR K.F
  nrows := K.B.nrows
  nq := K.B.nq
  ncirc := K.cyc1.length
  nd := K.B.nd
  frame := K.ok.frame
  level := fun _ hd => BlockData.levelR K.ok hd
  safe := fun d _ => K.safeR d
  valid := fun _ hd => K.validR hd
  support := fun _ hd => K.supportR hd
  rows := fun d => (BlockData.countsR K.ok d).1
  charge := fun d => (BlockData.countsR K.ok d).2
  ncircR := fun d => by simp [circlesR]
  loops_perm := fun _ hd => BlockData.loopsR_perm K.ok hd
  nloops := fun d => BlockData.loopsR_length K.ok d
  cover := fun _ hd _ ht => BlockData.coverR K.ok hd ht

end BlockCertUp

/-! ### Pointer certificates for a list of trails (from step (B) `BlockB.lean`) -/

def portsB (circles : List (List Nat)) (h : Nat) :
    List (List (Row Nat)) → List (List MixedPointer) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | W :: Ws, m :: ms => decide (PortsCovered W circles h m) && portsB circles h Ws ms

theorem portsB_sound {circles : List (List Nat)} {h : Nat} :
    ∀ (Ws : List (List (Row Nat))) (ms : List (List MixedPointer)),
      portsB circles h Ws ms = true → ∀ W ∈ Ws, ∃ m, PortsCovered W circles h m := by
  intro Ws
  induction Ws with
  | nil => intro _ _ W hW; simp at hW
  | cons a Ws ih =>
    intro ms hb W hW
    cases ms with
    | nil => simp [portsB] at hb
    | cons m ms =>
      have h' : (decide (PortsCovered a circles h m) && portsB circles h Ws ms) = true := hb
      rw [Bool.and_eq_true] at h'
      rcases List.mem_cons.mp hW with rfl | hW
      · exact ⟨m, of_decide_eq_true h'.1⟩
      · exact ih ms h'.2 W hW

theorem forall_mem_take_drop' {α : Type} {Q : α → Prop} {L : List α} (s : Nat)
    (h1 : ∀ t ∈ L.take s, Q t) (h2 : ∀ t ∈ L.drop s, Q t) : ∀ t ∈ L, Q t := by
  intro t ht
  rw [← List.take_append_drop s L] at ht
  rcases List.mem_append.mp ht with ht | ht
  · exact h1 t ht
  · exact h2 t ht

theorem forall_mem_of_take_eq' {α : Type} {Q : α → Prop} {L : List α} (s : Nat)
    (hl : L.length ≤ s) (h1 : ∀ t ∈ L.take s, Q t) : ∀ t ∈ L, Q t := by
  rw [List.take_of_length_le hl] at h1
  exact h1

end SuperpermutationUpperBound43586371
