import SuperpermutationUpperBound43586371.UniR.RBlockRows
import SuperpermutationUpperBound43586371.Uniform.Ports

/-!
# Ports and the shared cycles of R'(m) (`PROOF_R.md`, section 6)

Over a walk the completion port moves by `4` (odd `m`, `m` periods) or `2` (even `m`, `m/2` periods); the walk
is one item with one start port (odd `m`) or two (even `m`).  The cycles `cyc τ i0 ε = 10 :: rot (rot d0 i0 ++ [τ]) ε`
(`τ ∈ {t1, t2}`; `i0, ε ∈ {0}` for odd `m`, `{0, 1}` for even `m`) meet the completion of every walk of the block
from every port: the full row `u ++ [C]` of a suitable period, completed at port `m - 1 - g + ε`, has its head on
`cyc A i0 ε` (`walkD_safe`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SuperpermutationUpperBound43586371.UniR

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound43586371.Uniform

/-! ### Port shifts -/

theorem Pg.period_steps (p : Pg) (h3 : 3 ≤ p.q.length) :
    ((p.period).map stepOf).sum = (p.mid1.length + p.q.length + 8) * (p.mid1.length + p.q.length + 1) + 4 := by
  simp only [Pg.period, List.map_append, List.sum_append]
  rw [sweep_steps _ _ _ (by rw [p.len_arrW h3]; omega) (by omega),
    sweep_steps _ _ _ (by rw [p.len_arrU]; omega) (by omega),
    sweep_steps _ _ _ (by rw [p.len_arrY h3]; omega) (by omega),
    sweep_steps _ _ _ (by rw [p.len_arrV h3]; omega) (by omega),
    p.len_arrW h3, p.len_arrU, p.len_arrY h3, p.len_arrV h3]
  rw [show p.mid1.length + p.q.length + 2 - 1 = p.mid1.length + p.q.length + 1 by omega]
  ring

theorem walkR_steps (d0 : List Nat) (g A B C s P : Nat) (hg1 : 1 ≤ g) (hg : g + 4 ≤ d0.length) :
    ((walkR d0 g A B C s P).map stepOf).sum = P * ((d0.length + 8) * (d0.length + 1) + 4) := by
  unfold walkR
  rw [List.map_flatMap, sum_flatMap_const _ _ ((d0.length + 8) * (d0.length + 1) + 4) (fun k _ => by
    obtain ⟨h1, h2⟩ := pgOf_lens' d0 g A B C (s + 2 * k + 2) hg
    rw [Pg.period_steps _ (by rw [h2]; omega), h1, h2,
      show d0.length - 2 - g + (g + 2) = d0.length by omega])]
  simp

theorem walkR_baselen (d0 : List Nat) (g A B C s P : Nat) (hg1 : 1 ≤ g) (hg : g + 4 ≤ d0.length)
    (hnd : (C :: B :: A :: d0).Nodup) (h9 : 9 ∉ C :: B :: A :: d0) :
    ∀ r ∈ walkR d0 g A B C s P, r.base.length = (d0.length + 2) + 1 := by
  intro r hr
  have := ((walkR_basedOn d0 g A B C s P hg1 hg hnd h9) r hr).2.1.length_eq
  simp at this; omega

theorem walkR_exit_odd (d0 : List Nat) (g A B C : Nat) (hg1 : 1 ≤ g) (hg : g + 4 ≤ d0.length)
    (hnd : (C :: B :: A :: d0).Nodup) (h9 : 9 ∉ C :: B :: A :: d0) (hodd : d0.length % 2 = 1) (s : Nat)
    (q : Nat) (hq : q < d0.length + 2) :
    completionExit (walkR d0 g A B C s d0.length) q = (q + 4) % (d0.length + 2) := by
  rw [exit_sum (d0.length + 2) (by omega) _ (walkR_baselen d0 g A B C s _ hg1 hg hnd h9) q hq,
    walkR_steps d0 g A B C s _ hg1 hg]
  have he : d0.length * ((d0.length + 8) * (d0.length + 1) + 4) =
      4 + (d0.length + 2) * (d0.length * d0.length + 7 * d0.length - 2) := by
    have h2 : 2 ≤ d0.length * d0.length + 7 * d0.length := by nlinarith
    zify [h2]
    ring
  rw [he, ← Nat.add_assoc, Nat.add_mul_mod_self_left]

theorem walkR_exit_even (d0 : List Nat) (g A B C : Nat) (hg1 : 1 ≤ g) (hg : g + 4 ≤ d0.length)
    (hnd : (C :: B :: A :: d0).Nodup) (h9 : 9 ∉ C :: B :: A :: d0) (hev : d0.length % 2 = 0) (s : Nat)
    (q : Nat) (hq : q < d0.length + 2) :
    completionExit (walkR d0 g A B C s (d0.length / 2)) q = (q + 2) % (d0.length + 2) := by
  rw [exit_sum (d0.length + 2) (by omega) _ (walkR_baselen d0 g A B C s _ hg1 hg hnd h9) q hq,
    walkR_steps d0 g A B C s _ hg1 hg]
  obtain ⟨u, hu⟩ : ∃ u, d0.length = 2 * u := ⟨d0.length / 2, by omega⟩
  rw [hu, show 2 * u / 2 = u by omega]
  have he : u * ((2 * u + 8) * (2 * u + 1) + 4) = 2 + (2 * u + 2) * (2 * u * u + 7 * u - 1) := by
    have h2 : 1 ≤ 2 * u * u + 7 * u := by nlinarith
    zify [h2]
    ring
  rw [he, ← Nat.add_assoc, Nat.add_mul_mod_self_left]

/-! ### Orbits -/

theorem orbit_even_mem (h p t : Nat) (hh : 0 < h) (hev : h % 2 = 0) (hp : p < h) (ht : t < h)
    (hpar : t % 2 = p % 2) : t ∈ (List.range (h / 2)).map (fun i => (p + 2 * i) % h) := by
  rcases Nat.lt_or_ge t p with hlt | hge
  · refine List.mem_map.mpr ⟨(t + h - p) / 2, List.mem_range.mpr (by omega), ?_⟩
    rw [show p + 2 * ((t + h - p) / 2) = t + h by omega, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
  · refine List.mem_map.mpr ⟨(t - p) / 2, List.mem_range.mpr (by omega), ?_⟩
    rw [show p + 2 * ((t - p) / 2) = t by omega, Nat.mod_eq_of_lt ht]

theorem orbit_even_perm (h : Nat) (hh : 0 < h) (hev : h % 2 = 0) :
    ((List.range 2).flatMap fun p => (List.range (h / 2)).map (fun i => (p + 2 * i) % h)).Perm
      (List.range h) := by
  have e : ((List.range 2).flatMap fun p => (List.range (h / 2)).map (fun i => (p + 2 * i) % h)) =
      (List.range (h / 2)).map (fun i => 2 * i) ++ (List.range (h / 2)).map (fun i => 1 + 2 * i) := by
    rw [show List.range 2 = [0, 1] from rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    congr 1
    · refine List.map_congr_left (fun i hi => ?_)
      have := List.mem_range.mp hi; rw [Nat.mod_eq_of_lt (by omega)]; ring
    · refine List.map_congr_left (fun i hi => ?_)
      have := List.mem_range.mp hi; rw [Nat.mod_eq_of_lt (by omega)]
  rw [e]
  have hnd : ((List.range (h / 2)).map (fun i => 2 * i) ++ (List.range (h / 2)).map (fun i => 1 + 2 * i)).Nodup := by
    refine List.nodup_append.mpr ⟨List.Nodup.map (fun a b hab => by omega) List.nodup_range,
      List.Nodup.map (fun a b hab => by omega) List.nodup_range, ?_⟩
    intro x hx y hy hxy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
    omega
  refine (hnd.subperm (fun x hx => ?_)).perm_of_length_le (by simp; omega)
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx; have := List.mem_range.mp ha; exact List.mem_range.mpr (by omega)
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx; have := List.mem_range.mp ha; exact List.mem_range.mpr (by omega)

/-! ### The special row of a walk and its completion -/

theorem sum_steps_parity (l : List (Row Nat)) (h : ∀ r ∈ l, stepOf r % 2 = 1) :
    (l.map stepOf).sum % 2 = l.length % 2 := by
  induction l with
  | nil => simp
  | cons r rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h r (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    omega

theorem fullAt_mem_completion (pre post : List (Row Nat)) (r : Row Nat) (hr : r.visible = r.base.length)
    (q : Nat) : fullAt r 10 (completionExit pre q) ∈ completionWalk (pre ++ r :: post) 10 q := by
  rw [completionWalk_append]
  apply List.mem_append_right
  rw [completionWalk]
  apply List.mem_append_left
  simp only [Completion.portPath, hr, if_true, Transport.fullPathAt]
  split_ifs with h0
  · rw [h0]; simp
  · simp

/-- The period of the special row. -/
def kStar (m g s i0 : Nat) : Nat :=
  if (g + i0 - s) % 2 = 0 then (g + i0 - s) / 2 else (g + i0 - s + m) / 2

theorem kStar_spec (m g s i0 : Nat) (hg1 : 1 ≤ g) (hg5 : 2 * g + 5 ≤ m) (hs : s ≤ 1) (hi0 : i0 ≤ 1)
    (hpar : m % 2 = 0 → (g + i0 - s) % 2 = 0) (hodd : m % 2 = 1 → s = 0 ∧ i0 = 0) :
    (s + 2 * kStar m g s i0 + 2 + (m - 2 - g)) % m = i0 ∧
      kStar m g s i0 < (if m % 2 = 1 then m else m / 2) := by
  unfold kStar
  by_cases he : (g + i0 - s) % 2 = 0
  · rw [if_pos he]
    refine ⟨?_, ?_⟩
    · rw [show s + 2 * ((g + i0 - s) / 2) + 2 + (m - 2 - g) = i0 + m by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · split_ifs <;> omega
  · rw [if_neg he]
    have hm1 : m % 2 = 1 := by by_contra hc; exact he (hpar (by omega))
    obtain ⟨rfl, rfl⟩ := hodd hm1
    refine ⟨?_, ?_⟩
    · rw [show 0 + 2 * ((g + 0 - 0 + m) / 2) + 2 + (m - 2 - g) = 0 + m + m by omega, Nat.add_mod_right,
        Nat.add_mod_right, Nat.zero_mod]
    · rw [if_pos hm1]; omega

/-- The walk splits at the full row `u ++ [C]` of period `k`. -/
theorem walkR_split (d0 : List Nat) (g A B C s P k : Nat) (hg1 : 1 ≤ g) (hg : g + 4 ≤ d0.length)
    (hk : k < P) : ∃ pre post, walkR d0 g A B C s P =
      pre ++ fullRow (pgOf (rot d0 (s + 2 * k + 2)) g A B C).arrU C :: post ∧
      pre.length = k * (d0.length + 12) + 4 := by
  let per := fun k => (pgOf (rot d0 (s + 2 * k + 2)) g A B C).period
  have hper : ∀ k, per k = (List.range (d0.length + 12)).map (pgOf (rot d0 (s + 2 * k + 2)) g A B C).rowAt := by
    intro k
    show (pgOf _ g A B C).period = _
    rw [Pg.period_eq_range]
    obtain ⟨h1, h2⟩ := pgOf_lens' d0 g A B C (s + 2 * k + 2) hg
    rw [h1, h2, show d0.length - 2 - g + (g + 2) = d0.length by omega]
  have hrow4 : (pgOf (rot d0 (s + 2 * k + 2)) g A B C).rowAt 4 =
      fullRow (pgOf (rot d0 (s + 2 * k + 2)) g A B C).arrU C := by
    simp only [Pg.rowAt]
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)]
    simp [sweepRow, rot_zero, pgOf]
  have hrange : List.range P = List.range k ++ k :: (List.range (P - k - 1)).map (fun i => k + 1 + i) := by
    conv_lhs => rw [show P = k + (P - k - 1 + 1) by omega, List.range_add, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero]
    congr 2
    refine List.map_congr_left (fun i _ => ?_); simp only [Function.comp_def]; omega
  have hpk : per k = [(pgOf (rot d0 (s + 2 * k + 2)) g A B C).rowAt 0,
      (pgOf (rot d0 (s + 2 * k + 2)) g A B C).rowAt 1, (pgOf (rot d0 (s + 2 * k + 2)) g A B C).rowAt 2,
      (pgOf (rot d0 (s + 2 * k + 2)) g A B C).rowAt 3] ++
      (pgOf (rot d0 (s + 2 * k + 2)) g A B C).rowAt 4 ::
        (List.range (d0.length + 12 - 5)).map (fun i => (pgOf (rot d0 (s + 2 * k + 2)) g A B C).rowAt (5 + i)) := by
    rw [hper k, show d0.length + 12 = 5 + (d0.length + 12 - 5) by omega, List.range_add]
    simp [List.range_succ, Function.comp_def]
  refine ⟨(List.range k).flatMap per ++ [(pgOf (rot d0 (s + 2 * k + 2)) g A B C).rowAt 0,
      (pgOf (rot d0 (s + 2 * k + 2)) g A B C).rowAt 1, (pgOf (rot d0 (s + 2 * k + 2)) g A B C).rowAt 2,
      (pgOf (rot d0 (s + 2 * k + 2)) g A B C).rowAt 3],
    (List.range (d0.length + 12 - 5)).map (fun i => (pgOf (rot d0 (s + 2 * k + 2)) g A B C).rowAt (5 + i)) ++
      ((List.range (P - k - 1)).map (fun i => k + 1 + i)).flatMap per, ?_, ?_⟩
  · show (List.range P).flatMap per = _
    rw [hrange, List.flatMap_append, List.flatMap_cons, hpk, ← hrow4]
    simp
  · rw [List.length_append, length_flatMap_const _ _ (d0.length + 12) (fun k _ => by
      rw [hper k]; simp)]
    simp

/-! ### The shared cycles -/

/-- `10 :: rot (rot d0 i0 ++ [τ]) ε`. -/
def cycR (d0 : List Nat) (τ i0 ε : Nat) : List Nat := 10 :: rot (rot d0 i0 ++ [τ]) ε

/-- The cycles of the block: 2 for odd `m`, 8 for even `m`. -/
def cyclesR (d0 : List Nat) (t1 t2 : Nat) : List (List Nat) :=
  if d0.length % 2 = 1 then [cycR d0 t1 0 0, cycR d0 t2 0 0]
  else [t1, t2].flatMap fun τ => [0, 1].flatMap fun i0 => [0, 1].map fun ε => cycR d0 τ i0 ε

/-- Start ports per walk: 1 for odd `m`, 2 for even `m`. -/
def gpR (m : Nat) : Nat := if m % 2 = 1 then 1 else 2

theorem port_solve (t S h : Nat) (hh : 0 < h) (ht : t < h) :
    ((t + (h - S % h)) % h + S) % h = t := by
  rw [Nat.mod_add_mod]
  have h1 := Nat.mod_add_div S h
  have h2 := Nat.mod_lt S hh
  have e : t + (h - S % h) + S = t + h * (S / h + 1) := by
    zify [h2.le] at h1 ⊢
    linarith
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

theorem port_solve_par (t S h : Nat) (hev : h % 2 = 0) (hS : S % 2 = 0) (hh : 0 < h) :
    ((t + (h - S % h)) % h) % 2 = t % 2 := by
  rw [Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hev)]
  have hR : (S % h) % 2 = 0 := by rw [Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hev)]; exact hS
  have hR' : S % h ≤ h := (Nat.mod_lt S hh).le
  generalize S % h = R at hR hR'
  omega

/-- The head of the completed row `u ++ [C]` at port `|mid1| + 1 + ε` lies on a shared cycle. -/
theorem head_on_cycle (p : Pg) (d0 : List Nat) (o2 i0 ε : Nat) (h3 : 3 ≤ p.q.length)
    (hlist : p.list = rot d0 o2) (hlen : p.list.length = d0.length) (hε : ε ≤ 1)
    (hi0 : (o2 + p.mid1.length) % d0.length = i0 % d0.length) :
    CyclicEq (cycR d0 p.A i0 ε) (fullAt (fullRow p.arrU p.C) 10 (p.mid1.length + 1 + ε)).head := by
  set Y := p.mid1 ++ [p.A] ++ p.q with hY
  set t := p.mid1.length + 1 + ε with ht
  have hYl : Y.length = p.mid1.length + p.q.length + 1 := by simp [hY]; omega
  have hU : p.arrU = Y ++ [p.B] := by simp [Pg.arrU, hY]
  have hins : insertLetter ((Y ++ [p.B]) ++ [p.C]) 10 t = (Y.take t ++ [10] ++ Y.drop t) ++ [p.B, p.C] := by
    unfold insertLetter
    rw [show (Y ++ [p.B]) ++ [p.C] = Y ++ [p.B, p.C] by simp, List.take_append_of_le_length (by omega),
      List.drop_append_of_le_length (by omega)]
    simp
  have hhead : (fullAt (fullRow p.arrU p.C) 10 t).head = Y.take t ++ [10] ++ Y.drop t := by
    show (insertLetter ((p.arrU) ++ [p.C]) 10 t).take ((insertLetter (p.arrU ++ [p.C]) 10 t).length - 2) = _
    rw [hU, hins]
    exact List.take_left' (by simp; omega)
  rw [hhead]
  have htl : (Y.take t).length = t := by simp; omega
  have hrot : rot (Y.take t ++ [10] ++ Y.drop t) t = cycR d0 p.A i0 ε := by
    have e := rot_append_length (Y.take t) ([10] ++ Y.drop t)
    rw [htl] at e
    rw [List.append_assoc, e]
    unfold cycR
    simp only [List.singleton_append, List.cons_append]
    congr 1
    rw [List.nil_append, ← rot_eq_drop_append_take_of_le _ _ (by omega), ht, ← rot_add]
    congr 1
    rw [hY, show p.mid1.length + 1 = (p.mid1 ++ [p.A]).length by simp, rot_append_length]
    rw [← List.append_assoc]
    congr 1
    have hq : p.q ++ p.mid1 = rot p.list p.mid1.length := by simp only [Pg.list]; rw [rot_append_length]
    rw [hq, hlist, rot_add, ← rot_mod d0 (o2 + p.mid1.length), hi0, rot_mod]
  rw [← hrot]
  exact (CyclicEq.of_rot (by simp) t).symm

section

variable {d0 : List Nat} {t1 t2 t3 : Nat}

theorem walkD_exit (S : Setting d0 t1 t2 t3) (h9 : 9 ∉ t3 :: t2 :: t1 :: d0) {d : Nat × Nat × Nat}
    (hd : d ∈ Dl d0.length) (q : Nat) (hq : q < d0.length + 2) :
    completionExit (walkD d0 t1 t2 t3 d) q =
      (q + (if d0.length % 2 = 1 then 4 else 2)) % (d0.length + 2) := by
  obtain ⟨hg3, hg5, hσ, -⟩ := mem_Dl hd
  have hperm : (t3 :: rB d.2.1 t1 t2 :: rA d.2.1 t1 t2 :: d0).Perm (t3 :: t2 :: t1 :: d0) := by
    unfold rA rB; split_ifs
    · exact List.Perm.refl _
    · exact (List.Perm.swap _ _ _).cons _
  have hnd := hperm.nodup_iff.mpr S.nd
  have h9' : 9 ∉ t3 :: rB d.2.1 t1 t2 :: rA d.2.1 t1 t2 :: d0 := fun hm => h9 (hperm.mem_iff.mp hm)
  unfold walkD Pm
  split_ifs with hm
  · exact walkR_exit_odd d0 _ _ _ _ (by omega) (by omega) hnd h9' hm _ q hq
  · exact walkR_exit_even d0 _ _ _ _ (by omega) (by omega) hnd h9' (by omega) _ q hq

theorem walkD_rows (S : Setting d0 t1 t2 t3) (h9 : 9 ∉ t3 :: t2 :: t1 :: d0) {d : Nat × Nat × Nat}
    (hd : d ∈ Dl d0.length) : ∀ r ∈ walkD d0 t1 t2 t3 d, r.base.length = (d0.length + 2) + 1 ∧
      (r.visible = r.base.length ∨ r.visible = r.base.length - 2) := by
  intro r hr
  have hb := (walkD_basedOn S h9 hd) r hr
  exact ⟨by have := hb.2.1.length_eq; simp at this; omega, hb.2.2.2⟩

/-- The shared cycles meet the completion of every walk of the block from every port. -/
theorem walkD_safe (S : Setting d0 t1 t2 t3) (h9 : 9 ∉ t3 :: t2 :: t1 :: d0) {d : Nat × Nat × Nat}
    (hd : d ∈ Dl d0.length) :
    SafeComp (rep ((d0.length + 2) / gpR d0.length) (walkD d0 t1 t2 t3 d)) 10 (d0.length + 2)
      (cyclesR d0 t1 t2) := by
  obtain ⟨hg3, hg5, hσ, hs⟩ := mem_Dl hd
  set m := d0.length with hm
  set h := m + 2 with hh
  set g := d.1
  set s := d.2.2
  intro j
  -- the cycle and the port
  set i0 := if m % 2 = 1 then 0 else (s + g) % 2 with hi0
  set M1 := m - 2 - g with hM1
  set ε := if m % 2 = 1 then 0 else (j.val + h - (M1 + 1)) % 2 with hε
  have hε1 : ε ≤ 1 := by simp only [hε]; split_ifs <;> omega
  have hi01 : i0 ≤ 1 := by simp only [hi0]; split_ifs <;> omega
  set k := kStar m g s i0 with hk
  obtain ⟨hkmod, hkP⟩ := kStar_spec m g s i0 (by omega) hg5 (by omega) hi01
    (fun he => by simp only [hi0, show ¬ (m % 2 = 1) by omega, if_false]; omega)
    (fun ho => ⟨by omega, by simp only [hi0, ho, if_true]⟩)
  have hkP' : k < Pm m := by unfold Pm; exact hkP
  set p := pgOf (rot d0 (s + 2 * k + 2)) g (rA d.2.1 t1 t2) (rB d.2.1 t1 t2) t3 with hp
  obtain ⟨hl1, hl2⟩ := pgOf_lens' d0 g (rA d.2.1 t1 t2) (rB d.2.1 t1 t2) t3 (s + 2 * k + 2) (by omega)
  obtain ⟨pre, post, hW, hpre⟩ := walkR_split d0 g (rA d.2.1 t1 t2) (rB d.2.1 t1 t2) t3 s (Pm m) k
    (by omega) (by omega) hkP'
  have hWd : walkD d0 t1 t2 t3 d = pre ++ fullRow p.arrU t3 :: post := hW
  set t := M1 + 1 + ε with ht
  have htl : t < h := by omega
  -- the head on the cycle
  have hcyc := head_on_cycle p d0 (s + 2 * k + 2) i0 ε (by rw [hl2]; omega) (pgOf_list _ _ _ _ _)
    (by rw [pgOf_list]; simp) hε1 (by rw [hl1, hkmod, Nat.mod_eq_of_lt (by omega)])
  rw [hl1] at hcyc
  -- rows of pre
  have hrows := walkD_rows S h9 hd
  rw [hWd] at hrows
  have hpre_rows : ∀ r ∈ pre, r.base.length = h + 1 := fun r hr => (hrows r (by simp [hr])).1
  set Sp := (pre.map stepOf).sum with hSp
  set q := (t + (h - Sp % h)) % h with hq
  have hqh : q < h := Nat.mod_lt _ (by omega)
  have hexit : completionExit pre q = t := by
    rw [exit_sum h (by omega) pre hpre_rows q hqh, hq, port_solve t Sp h (by omega) htl]
  -- q is reached from j
  have hqorb : q ∈ orbitPorts (walkD d0 t1 t2 t3 d) (h / gpR m) j.val := by
    have hex := walkD_exit S h9 hd
    rw [orbit_eq (by omega) hex _ j.val j.isLt]
    unfold gpR
    split_ifs with hmo
    · rw [Nat.div_one]
      exact (orbit_perm h j.val (by omega) (by omega)).mem_iff.mpr (List.mem_range.mpr hqh)
    · have hstep : ∀ r ∈ pre, stepOf r % 2 = 1 := by
        intro r hr
        obtain ⟨hl, hk⟩ := hrows r (by simp [hr])
        unfold stepOf; rw [hl]; split_ifs <;> omega
      have hSp2 : Sp % 2 = 0 := by
        rw [hSp, sum_steps_parity pre hstep, hpre]
        have hk2 : (k * (d0.length + 12)) % 2 = 0 := by
          rw [Nat.mul_mod, show (d0.length + 12) % 2 = 0 by omega]; simp
        omega
      have hqpar : q % 2 = t % 2 := port_solve_par t Sp h (by omega) hSp2 (by omega)
      have hM1h : M1 + 1 < h := by omega
      have htj : t % 2 = j.val % 2 := by
        rw [ht, hε, if_neg hmo]; omega
      exact orbit_even_mem h j.val q (by omega) (by omega) j.isLt hqh (by omega)
  -- the incidence
  have hmemc : cycR d0 p.A i0 ε ∈ cyclesR d0 t1 t2 := by
    have hA : p.A = t1 ∨ p.A = t2 := by
      show rA d.2.1 t1 t2 = t1 ∨ rA d.2.1 t1 t2 = t2
      unfold rA; split_ifs <;> simp
    unfold cyclesR
    split_ifs with hmo
    · have hi0z : i0 = 0 := by rw [hi0, if_pos hmo]
      have hez : ε = 0 := by rw [hε, if_pos hmo]
      rw [hi0z, hez]
      rcases hA with h' | h' <;> rw [h'] <;> simp
    · simp only [List.mem_flatMap, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false]
      refine ⟨p.A, by rcases hA with h' | h' <;> simp [h'], i0, by omega, ε, by omega, rfl⟩
  refine ⟨cycR d0 p.A i0 ε, hmemc, Or.inl ⟨List.mem_cons_self, _, ⟨_, ?_, rfl⟩, hcyc⟩⟩
  rw [completionWalk_rep]
  refine List.mem_flatMap.mpr ⟨q, hqorb, ?_⟩
  rw [hWd]
  have hmem := fullAt_mem_completion pre post (fullRow p.arrU t3) (by simp [fullRow]) q
  rw [hexit] at hmem
  exact hmem

end

end SuperpermutationUpperBound43586371.UniR
