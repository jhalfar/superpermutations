import SuperpermutationUpperBound1771.Hybrid

/-!
# Thirteen symbols

From a certificate `Cert`: the selection on 12 symbols has 10! rows with total charge
1,780,800, every one of its 7,200 closed trails is covered by one of 7,875 connector cycles
(the 203 cycles of the certificate with letter 12 in each of their nine gaps, and the word of
each of the 6,048 loops without a row), and one completion gives a superpermutation on 13
symbols of length at most 6,747,849,960.
-/

namespace SuperpermutationUpperBound1771

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport

theorem length_flatMap_const {β γ : Type} (l : List β) (f : β → List γ) (c : Nat)
    (hf : ∀ x ∈ l, (f x).length = c) : (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, hf a (by simp),
      ih (fun x hx => hf x (by simp [hx])), List.length_cons]
    ring

theorem sum_flatMap_const {β : Type} (l : List β) (f : β → List Nat) (c : Nat)
    (hf : ∀ x ∈ l, (f x).sum = c) : (l.flatMap f).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.sum_append, hf a (by simp),
      ih (fun x hx => hf x (by simp [hx])), List.length_cons]
    ring

theorem flatten_flatMap {β γ : Type} (l : List β) (f : β → List (List γ)) :
    (l.flatMap f).flatten = l.flatMap (fun x => (f x).flatten) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.flatten_append, ih, List.flatMap_cons]

/-- Pointwise inventories of transported walks add up. -/
theorem map_flatten_perm_packingRows (ws : List (List (Row Nat)))
    (F : List (Row Nat) → List (Row Nat)) (z : Nat)
    (hF : ∀ w ∈ ws, (F w).Perm (Transport.packingRows w z)) :
    (ws.map F).flatten.Perm (Transport.packingRows ws.flatten z) := by
  induction ws with
  | nil => simp [Transport.packingRows]
  | cons w rest ih =>
    have hp : Transport.packingRows (w :: rest).flatten z =
        Transport.packingRows w z ++ Transport.packingRows rest.flatten z := by
      simp [Transport.packingRows, List.flatten_cons, List.flatMap_append]
    rw [List.map_cons, List.flatten_cons, hp]
    exact (hF w (by simp)).append (ih (fun w' hw' => hF w' (by simp [hw'])))

namespace Cert

variable (C : Cert)

/-! ### Counts -/

theorem small11_basedOn : BasedOn alph10 9 C.small11.flatten := by
  intro r hr
  obtain ⟨w, hw, hrw⟩ := List.mem_flatten.mp hr
  obtain ⟨g, hg, hwg⟩ := C.mem_small11 hw
  exact (C.groupFacts g hg).basedOn w hwg r hrw

theorem small11_counts : C.small11.flatten.length = 18144 ∧
    (C.small11.flatten.map Row.charge).sum = 8736 := by
  have he : C.small11.flatten = C.groups.flatMap (fun g => g.walks.flatten) :=
    flatten_flatMap C.groups Group.walks
  constructor
  · rw [he, length_flatMap_const C.groups _ 378 (fun g hg => (C.groupFacts g hg).rowCount),
      C.groupCount]
  · rw [he, List.map_flatMap,
      sum_flatMap_const C.groups _ 182 (fun g hg => (C.groupFacts g hg).charge), C.groupCount]

theorem small12_perm : C.small12.flatten.Perm (Transport.packingRows C.small11.flatten 12) :=
  map_flatten_perm_packingRows C.small11 _ 12 (fun _ hw => C.small_inventory hw)

theorem small12_counts : C.small12.flatten.length = 181440 ∧
    (C.small12.flatten.map Row.charge).sum = 87360 := by
  have hc := Transport.packingRows_counts C.small11.flatten 12 alph10.length
    (C.small11_basedOn.ready (by decide) (by decide))
  have hp := C.small12_perm
  rw [C.small11_counts.1, C.small11_counts.2] at hc
  exact ⟨hp.length_eq.trans hc.1, ((hp.map Row.charge).sum_eq).trans hc.2.1⟩

theorem d11_length : C.d11.length = 6048 := by
  unfold d11
  rw [length_flatMap_const C.groups _ 126 (fun g hg => (C.groupFacts g hg).dcount), C.groupCount]

theorem charts12_counts : C.charts12.flatten.length = 60480 ∧
    (C.charts12.flatten.map Row.charge).sum = 0 := by
  constructor
  · unfold charts12
    rw [← List.flatMap_def, length_flatMap_const C.d11 _ 10, C.d11_length]
    intro x hx
    rw [Partition.fullChart_length]
    exact (C.d11_perm hx).length_eq
  · apply sum_map_eq_zero
    intro r hr
    obtain ⟨W, hW, hrW⟩ := List.mem_flatten.mp hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hW
    exact Partition.fullChart_charge x 12 9 r hrW

theorem comps12_counts : C.comps12.flatten.length = 3628800 ∧
    (C.comps12.flatten.map Row.charge).sum = 1780800 := by
  have he : C.comps12.flatten = C.big12.flatten ++ C.small12.flatten ++ C.charts12.flatten := by
    unfold comps12
    rw [List.flatten_append, List.flatten_append]
  constructor
  · rw [he, List.length_append, List.length_append, C.big12_counts.1, C.small12_counts.1,
      C.charts12_counts.1]
  · rw [he, List.map_append, List.map_append, List.sum_append, List.sum_append,
      C.big12_counts.2, C.small12_counts.2, C.charts12_counts.2]

/-! ### The connector cycles -/

theorem circles_fresh : ∀ c ∈ C.circles, 12 ∉ c := by
  intro c hc hm
  exact (by decide : 12 ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11]) (C.circles_support c hc 12 hm)

theorem extended_valid : CircleFamilyValid 10 (extendCircles C.circles 12) :=
  C.circles_valid.extend 12 C.circles_fresh

theorem circles12_valid : CircleFamilyValid 10 C.circles12 := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact C.extended_valid c hc
  · have hp := C.d11_perm hc
    exact ⟨hp.length_eq, hp.nodup_iff.mpr (by decide)⟩

theorem circles12_length : C.circles12.length = 7875 := by
  unfold circles12
  rw [List.length_append, extendCircles_length 9 C.circles 12
    (fun c hc => (C.circles_valid c hc).1), C.circleCount, C.d11_length]

/-- The letters that occur in connector cycles on 13 symbols: all but the satellite. -/
def letters12 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12]

theorem circles12_support : ∀ c ∈ C.circles12, ∀ a ∈ c, a ∈ letters12 := by
  intro c hc a ha
  rcases List.mem_append.mp hc with hc | hc
  · simp only [extendCircles, circleExtensions, fullBases, List.mem_flatMap, List.mem_map,
      List.mem_range] at hc
    obtain ⟨c0, hc0, j, _, rfl⟩ := hc
    rcases List.mem_cons.mp ((insertLetter_perm c0 12 j).mem_iff.mp ha) with rfl | ha0
    · decide
    · exact (by decide : ∀ b ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11], b ∈ letters12) a
        (C.circles_support c0 hc0 a ha0)
  · exact (by decide : ∀ b ∈ alph10, b ∈ letters12) a ((C.d11_perm hc).mem_iff.mp ha)

theorem safe12 : ∀ rs ∈ C.comps12, SafeComp rs 10 10 C.circles12 := by
  intro rs hrs
  have hleft : ∀ c ∈ extendCircles C.circles 12, c ∈ C.circles12 :=
    fun c hc => List.mem_append_left _ hc
  rcases List.mem_append.mp hrs with hrs | hrs
  · rcases List.mem_append.mp hrs with hrs | hrs
    · obtain ⟨W, hW, p, hp, rfl⟩ := mem_transportComps.mp hrs
      exact ((C.bigSafe W hW).transport 12 (by decide) C.circles_valid
        (C.level11.len (by decide) W hW) (C.level11.kind W hW)
        (C.level11.fresh (by decide) W hW) p hp).mono hleft
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrs
      obtain ⟨g, hg, hwg⟩ := C.mem_small11 hw
      have hb := (C.groupFacts g hg).basedOn w hwg
      exact (((C.groupFacts g hg).safe w hwg).transport 12 (by decide) C.circles_valid
        (fun r hr => C.small_len hw r (mem_rep hr)) (fun r hr => C.small_kind hw r (mem_rep hr))
        (fun r hr hm => (by decide : 10 ∉ alph10) ((hb r (mem_rep hr)).2.1.mem_iff.mp hm))
        0 (by decide)).mono hleft
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hrs
    have hl : x.length = 10 := (C.d11_perm hx).length_eq
    exact SafeComp.fullChart x 12 9 10 10 C.circles12 (List.mem_append_right _ hx)
      (by intro he; rw [he] at hl; simp at hl)

/-! ### The word -/

/-- A superpermutation on 13 symbols of length at most 6,747,849,960. -/
theorem word13 (C : Cert) : ∃ w : Word 13, IsSuperpermutation w ∧ w.length ≤ 6747849960 := by
  obtain ⟨t, J, w, hw, ht, hJ, hl⟩ := word_of_level (K := 13) (ell := 3) (h := 10) rfl
    (by decide) C.level12 (by decide) (by decide) (by decide : alph11.Nodup)
    (by decide) (by decide) (by decide : (10 :: (alph11 ++ [9])).Perm (List.range 13))
    C.complete12 C.circles12_valid C.safe12 letters12.toFinset
    (fun c hc a ha => List.mem_toFinset.mpr (C.circles12_support c hc a ha))
    (fun c hc a ha => (by decide : ∀ b ∈ letters12, b < 13) a (C.circles12_support c hc a ha))
  rw [C.comps12_counts.1, C.comps12_counts.2, C.circles12_length] at hl
  rw [C.circles12_length] at ht
  have hcard : letters12.toFinset.card = 12 := by decide
  have hdesc : Nat.descFactorial 12 3 = 1320 := by decide
  rw [hcard, hdesc] at hJ
  have hl' : w.length = 6747798750 + (11 - 2) * t - (11 - 8) * (t - J) := by omega
  have hb := overlap_bound (base := 6747798750) (m := 11) (a := 8) (c := 7875) (V := 1320)
    (by decide) (by decide) ht hJ hl'
  have hmin : min 7875 1320 = 1320 := by decide
  rw [hmin] at hb
  exact ⟨w, hw, by omega⟩

end Cert

end SuperpermutationUpperBound1771
