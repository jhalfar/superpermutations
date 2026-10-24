import LowerBounds.KPot

/-!
# Rule JS on words (the written proof, section 3.3)

For a row with last entry `q` the entry of the next block is `tau2 k q` (the door, `DoorEq`).

* `link_tau2` (**Lemma JS1**, the part that is used): if `v` follows `q` behind a link of kind `kd`
  (weight 3 or 4) and `v` lies in the class of `tau2 k q`, then `tau2 k v` follows `tau2 k q` behind a
  link of the same kind.  (So `v` is `j3(q)` or `j4(q)`; uniqueness is `eq_rotate_of_head`.)
* `tau2_getLast_row`: a row with `k - 1` blocks ends where it started (`tau2` of its last entry is its
  first entry); so the first row of a junction as in JS2 has at most `k - 2` blocks.
* `JSBad R R'`: the rows `R`, `R'` are a shiftable junction: `R'` has at least two blocks and its
  first block lies in the class of `tau2` of the last entry of `R`.  `NoJS L`: no consecutive rows of
  `L` are a shiftable junction.
* `shift_of_not_noJS` (**Lemma JS2, Lemma JS3**): a sequence with a shiftable junction gives a
  sequence with the same number of rows, links and holes, the same kinds of links, a potential that
  is at least as large at every cut (the potentials have `b ≥ 0`: they are natural numbers) and the
  same at the end, so `Good` is kept, and `psi` one larger.
* `psi_le`: `psi` is bounded on sequences with `n` rows; so a good counterexample with the largest
  `psi` has no shiftable junction (Theorem JS; used in `K16Pot.lean`).
-/

namespace SuperpermLowerBounds
namespace K16

open S (PermW WLink DoorEq doorW)
open PS (TRow IsSeq holesT linksT LinkK)
open KS (phiAt Good hdK)

variable {k : ℕ}

/-! ### The next block -/

/-- The entry of the next block of a row whose last entry is `x`. -/
def tau2 (k : ℕ) (x : List ℕ) : List ℕ := doorW (x.rotate (k - 1))

theorem permW_of_perm {x y : List ℕ} (h : PermW k x) (hp : x.Perm y) : PermW k y :=
  ⟨hp.nodup_iff.mp h.1, hp.length_eq.symm.trans h.2.1, fun a => hp.mem_iff.symm.trans (h.2.2 a)⟩

theorem permW_tau2 (hk : 2 ≤ k) {x : List ℕ} (h : PermW k x) : PermW k (tau2 k x) := by
  have hy := h.rotate (k - 1)
  obtain ⟨a, b, X, hxe, _⟩ := S.exists_cons_cons hy.2.1 hk
  unfold tau2
  rw [hxe, S.doorW_cons]
  rw [hxe] at hy
  refine permW_of_perm hy ?_
  have h1 : ([a, b] ++ X).Perm (X ++ [a, b]) := List.perm_append_comm
  have h2 : (X ++ [a, b]).Perm (X ++ [b, a]) := List.Perm.append_left X (List.Perm.swap b a [])
  exact h1.trans h2

theorem take_prefix (A B : List ℕ) {n : ℕ} (h : A.length = n) : (A ++ B).take n = A := by
  subst h
  simp

theorem rot_last (l : List ℕ) (x : ℕ) {n : ℕ} (h : l.length = n) : (l ++ [x]).rotate n = x :: l := by
  subst h
  exact List.rotate_append_length_eq l [x]

theorem wlink2_tau2 (hk : 2 ≤ k) {x : List ℕ} (h : x.length = k) : WLink k 2 x (tau2 k x) := by
  have hy : (x.rotate (k - 1)).length = k := by rw [List.length_rotate, h]
  obtain ⟨a, b, X, hxe, hX⟩ := S.exists_cons_cons hy hk
  unfold WLink tau2
  rw [hxe, S.doorW_cons]
  exact (take_prefix X [b, a] hX).symm

/-- A word of length at least 5, split for Lemma JS1. -/
theorem decomp5 (hk : 5 ≤ k) {q : List ℕ} (hq : q.length = k) :
    ∃ (q1 q2 c d m : ℕ) (Z : List ℕ), q = q1 :: q2 :: c :: d :: (Z ++ [m]) ∧ Z.length = k - 5 := by
  match q, hq with
  | q1 :: q2 :: c :: d :: rest, h =>
    have hr : rest ≠ [] := by
      intro h0
      subst h0
      simp at h
      omega
    refine ⟨q1, q2, c, d, rest.getLast hr, rest.dropLast, by rw [List.dropLast_append_getLast hr],
      ?_⟩
    simp only [List.length_cons] at h
    rw [List.length_dropLast]
    omega
  | [], h => simp at h; omega
  | [_], h => simp at h; omega
  | [_, _], h => simp at h; omega
  | [_, _, _], h => simp at h; omega

/-- A rotation of a word without repeated letters is fixed by its first letter. -/
theorem eq_rotate_of_head {l v : List ℕ} (hl : l.Nodup) (hv : l ~r v) {j : ℕ} (hj : j < l.length)
    (hh : v.head? = l[j]?) : v = l.rotate j := by
  obtain ⟨n, rfl⟩ := hv
  have hpos : 0 < l.length := by omega
  rw [← List.rotate_mod l n] at hh ⊢
  have hn : n % l.length < l.length := Nat.mod_lt _ hpos
  rw [List.head?_rotate hn, List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hj,
    Option.some_inj] at hh
  rw [(hl.getElem_inj_iff).mp hh]

/-- **Lemma JS1** (the part used by the shift): the class of `tau2 q` behind `q`, then the class of
`tau2 (tau2 q)` behind `tau2 q`, with the same weight. -/
theorem link_tau2 (hk : 5 ≤ k) {kd : ℕ} (hkd : kd ≤ 1) {q v : List ℕ} (hq : PermW k q)
    (hl : LinkK k kd q v) (hc : v ~r tau2 k q) : LinkK k kd (tau2 k q) (tau2 k v) := by
  have hTp := permW_tau2 (by omega) hq
  obtain ⟨q1, q2, c, d, m, Z, rfl, hZ⟩ := decomp5 hk hq.2.1
  have hrot : (q1 :: q2 :: c :: d :: (Z ++ [m])).rotate (k - 1) = m :: q1 :: q2 :: c :: d :: Z :=
    rot_last (q1 :: q2 :: c :: d :: Z) m (by simp; omega)
  have hT : tau2 k (q1 :: q2 :: c :: d :: (Z ++ [m])) = q2 :: c :: d :: (Z ++ [q1, m]) := by
    unfold tau2
    rw [hrot, S.doorW_cons]
    simp
  rw [hT] at hTp hc ⊢
  have hTn := hTp.1
  have hrotT : (q2 :: c :: d :: (Z ++ [q1, m])).rotate (k - 1) = m :: q2 :: c :: d :: (Z ++ [q1]) := by
    have e : q2 :: c :: d :: (Z ++ [q1, m]) = (q2 :: c :: d :: (Z ++ [q1])) ++ [m] := by simp
    rw [e]
    exact rot_last _ m (by simp; omega)
  have hv := List.take_append_drop (k - 3) v
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkd with rfl | rfl
  · -- weight 3: `v` begins with `c d Z`, so `v` is `tau2 q` rotated by one
    have h3 : WLink k 3 (q1 :: q2 :: c :: d :: (Z ++ [m])) v := hl.1 rfl
    unfold WLink at h3
    rw [hrot] at h3
    have hd : (m :: q1 :: q2 :: c :: d :: Z).drop 3 = c :: d :: Z := rfl
    rw [hd] at h3
    have hvh : v.head? = some c := by
      rw [← hv, ← h3]
      rfl
    have hve : v = (q2 :: c :: d :: (Z ++ [q1, m])).rotate 1 :=
      eq_rotate_of_head hTn hc.symm (by simp) (by rw [hvh]; rfl)
    have hv' : v = (c :: d :: (Z ++ [q1, m])) ++ [q2] := by
      rw [hve]
      simp
    refine ⟨fun _ => ?_, fun h0 => absurd h0 (by norm_num)⟩
    unfold WLink
    rw [hrotT]
    unfold tau2
    rw [hv', rot_last (c :: d :: (Z ++ [q1, m])) q2 (by simp; omega), S.doorW_cons]
    have e2 : d :: (Z ++ [q1, m]) ++ [c, q2] = (d :: (Z ++ [q1])) ++ [m, c, q2] := by simp
    rw [e2, take_prefix _ _ (by simp; omega)]
    rfl
  · -- weight 4: `v` begins with `d Z`, so `v` is `tau2 q` rotated by two
    have h4 : WLink k 4 (q1 :: q2 :: c :: d :: (Z ++ [m])) v := hl.2 rfl
    unfold WLink at h4
    rw [hrot] at h4
    have hd : (m :: q1 :: q2 :: c :: d :: Z).drop 4 = d :: Z := rfl
    rw [hd] at h4
    have hv4 := List.take_append_drop (k - 4) v
    have hvh : v.head? = some d := by
      rw [← hv4, ← h4]
      rfl
    have hve : v = (q2 :: c :: d :: (Z ++ [q1, m])).rotate 2 :=
      eq_rotate_of_head hTn hc.symm (by simp) (by rw [hvh]; rfl)
    have hv' : v = (d :: (Z ++ [q1, m, q2])) ++ [c] := by
      rw [hve]
      simp
    refine ⟨fun h0 => absurd h0 (by norm_num), fun _ => ?_⟩
    unfold WLink
    rw [hrotT]
    unfold tau2
    rw [hv', rot_last (d :: (Z ++ [q1, m, q2])) c (by simp; omega), S.doorW_cons]
    have e2 : Z ++ [q1, m, q2] ++ [d, c] = (Z ++ [q1]) ++ [m, q2, d, c] := by simp
    rw [e2, take_prefix _ _ (by simp; omega)]
    rfl

/-! ### A row with `k - 1` blocks ends where it started -/

theorem tau2_snoc (hk : 2 ≤ k) (p : List ℕ) (m : ℕ) (hp : p.length = k - 1) :
    tau2 k (p ++ [m]) = p.rotate 1 ++ [m] := by
  unfold tau2
  rw [rot_last p m hp]
  cases p with
  | nil => simp at hp; omega
  | cons p0 P => simp [S.doorW_cons]

theorem chain_last (hk : 2 ≤ k) : ∀ (rest : List (List ℕ)) (p : List ℕ) (m : ℕ), p.length = k - 1 →
    List.IsChain (DoorEq k) ((p ++ [m]) :: rest) →
    ((p ++ [m]) :: rest).getLast (List.cons_ne_nil _ _) = p.rotate rest.length ++ [m]
  | [], p, m, _, _ => by simp
  | y :: rest, p, m, hp, hch => by
    have h2 := List.isChain_cons_cons.mp hch
    have hy : y = p.rotate 1 ++ [m] := by
      have := h2.1
      unfold DoorEq at this
      rw [this]
      exact tau2_snoc hk p m hp
    subst hy
    rw [List.getLast_cons (List.cons_ne_nil _ _),
      chain_last hk rest (p.rotate 1) m (by rw [List.length_rotate]; exact hp) h2.2,
      List.rotate_rotate]
    simp [Nat.add_comm]

/-- In a row with `k - 1` blocks the next block of the last entry is the first block. -/
theorem tau2_getLast_row (hk : 3 ≤ k) {Rb : List (List ℕ)} (hRb : Rb ≠ [])
    (hw : ∀ w ∈ Rb, PermW k w) (hdoors : List.IsChain (WLink k 2) Rb)
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) Rb) (hlen : Rb.length = k - 1) :
    tau2 k (Rb.getLast hRb) = Rb.head hRb := by
  have hD := S.door_chain hk Rb hw hdoors hpw
  obtain ⟨e, rest, rfl⟩ := List.exists_cons_of_ne_nil hRb
  have he := hw e List.mem_cons_self
  have hene : e ≠ [] := by
    intro h0
    have := he.2.1
    rw [h0] at this
    simp at this
    omega
  have hsplit := List.dropLast_append_getLast hene
  have hpl : e.dropLast.length = k - 1 := by rw [List.length_dropLast, he.2.1]
  have hD' : List.IsChain (DoorEq k) ((e.dropLast ++ [e.getLast hene]) :: rest) := by
    rw [hsplit]
    exact hD
  have hl := chain_last (by omega) rest e.dropLast (e.getLast hene) hpl hD'
  have e1 : (e :: rest).getLast hRb
      = ((e.dropLast ++ [e.getLast hene]) :: rest).getLast (List.cons_ne_nil _ _) := by
    simp only [hsplit]
  rw [e1, hl, tau2_snoc (by omega) _ _ (by rw [List.length_rotate]; exact hpl), List.rotate_rotate]
  have hrl : rest.length + 1 = e.dropLast.length := by
    simp only [List.length_cons] at hlen
    omega
  rw [hrl, List.rotate_length, hsplit]
  rfl

/-! ### Classes after a replacement by a rotation -/

theorem pairwise_replace {A B : List (List ℕ)} {v v' : List ℕ}
    (h : List.Pairwise (fun a b => ¬ a ~r b) (A ++ v :: B)) (hv : v' ~r v) :
    List.Pairwise (fun a b => ¬ a ~r b) (A ++ v' :: B) := by
  rw [List.pairwise_append, List.pairwise_cons] at h ⊢
  obtain ⟨hA, ⟨hvB, hB⟩, hAB⟩ := h
  refine ⟨hA, ⟨fun b hb hr => hvB b hb (hv.symm.trans hr), hB⟩, ?_⟩
  intro a ha b hb hr
  rcases List.mem_cons.mp hb with rfl | hb'
  · exact hAB a ha v List.mem_cons_self (hr.trans hv)
  · exact hAB a ha b (List.mem_cons_of_mem _ hb') hr

/-! ### Chains after replacing two neighbours -/

theorem chain_replace {α : Type} {R : α → α → Prop} {U W : List α} {x y x' y' : α}
    (h : List.IsChain R (U ++ x :: y :: W)) (hin : ∀ z, R z x → R z x') (hxy : R x' y')
    (hout : ∀ z, R y z → R y' z) : List.IsChain R (U ++ x' :: y' :: W) := by
  rw [List.isChain_append_cons_cons] at h ⊢
  obtain ⟨h1, _, h3⟩ := h
  refine ⟨?_, hxy, ?_⟩
  · rw [List.isChain_append] at h1 ⊢
    obtain ⟨hU, _, hUx⟩ := h1
    refine ⟨hU, List.isChain_singleton _, ?_⟩
    intro z hz w hw
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hw
    subst hw
    exact hin z (hUx z hz x rfl)
  · rw [List.isChain_cons] at h3 ⊢
    exact ⟨fun z hz => hout z (h3.1 z hz), h3.2⟩

/-! ### Shiftable junctions -/

/-- The rows `R`, `R'` are a shiftable junction. -/
def JSBad (k : ℕ) (R R' : TRow) : Prop :=
  ∃ (hR : R.2 ≠ []) (v f : List ℕ) (F : List (List ℕ)), R'.2 = v :: f :: F ∧
    v ~r tau2 k (R.2.getLast hR)

/-- No two consecutive rows are a shiftable junction. -/
def NoJS (k : ℕ) (L : List TRow) : Prop :=
  ∀ U R R' W, L = U ++ R :: R' :: W → ¬ JSBad k R R'

/-- The measure of Theorem JS: every block counted with the number of rows after its row. -/
def psi : List TRow → ℕ
  | [] => 0
  | x :: L => x.2.length * L.length + psi L

/-- `psi` of the rows `U` followed by `n` rows. -/
def psiOff (n : ℕ) : List TRow → ℕ
  | [] => 0
  | x :: U => x.2.length * (U.length + n) + psiOff n U

theorem psi_append : ∀ (U V : List TRow), psi (U ++ V) = psiOff V.length U + psi V
  | [], V => by simp [psiOff]
  | x :: U, V => by
    simp only [List.cons_append, psi, psiOff, List.length_append, psi_append U V]
    ring

theorem psi_le : ∀ (L : List TRow), (∀ x ∈ L, x.2.length ≤ k - 1) →
    psi L ≤ (k - 1) * L.length * L.length
  | [], _ => by simp [psi]
  | x :: L, h => by
    have ih := psi_le L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    simp only [psi, List.length_cons]
    have : x.2.length * L.length ≤ (k - 1) * L.length := Nat.mul_le_mul_right _ hx
    nlinarith

/-! ### Links, kinds and holes after a shift -/

theorem linksT_eq_fst : ∀ L : List TRow, linksT L = ((L.map Prod.fst).tail).countP (· != 0)
  | [] => rfl
  | x :: L => by simp [linksT, List.countP_map, Function.comp_def]

theorem linksT_congr {L N : List TRow} (h : L.map Prod.fst = N.map Prod.fst) :
    linksT L = linksT N := by
  rw [linksT_eq_fst, linksT_eq_fst, h]

theorem hdK_congr : ∀ {L N : List TRow}, L.map Prod.fst = N.map Prod.fst → hdK L = hdK N
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: L, y :: N, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact h.1

/-- The potential of a cut grows when the holes before it go down (`b ≥ 0`). -/
theorem phiAt_le_of {a b h : ℕ} {A A' B B' : List TRow} (hA : A.length = A'.length)
    (hl : linksT A = linksT A') (hh : holesT k A' ≤ holesT k A) (hd : hdK B = hdK B') :
    phiAt k a b h A B ≤ phiAt k a b h A' B' := by
  unfold phiAt
  by_cases h0 : A = []
  · have h0' : A' = [] := List.length_eq_zero_iff.mp (by rw [← hA, h0]; rfl)
    simp [h0, h0']
  · have h0' : A' ≠ [] := fun h' => h0 (List.length_eq_zero_iff.mp (by rw [hA, h']; rfl))
    rw [if_neg h0, if_neg h0', hd, hl, hA]
    have hb : (b : ℤ) * (holesT k A' : ℤ) ≤ (b : ℤ) * (holesT k A : ℤ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hh) (by positivity)
    unfold KS.fK
    split_ifs
    · rw [KS.potN_eq, KS.potN_eq]
      linarith
    · rw [KS.potS_eq, KS.potS_eq]
      linarith

/-- `Good` is kept when every cut has at least the potential and the end the same. -/
theorem good_transfer {a b h : ℕ} {L N : List TRow}
    (hcut : ∀ i, phiAt k a b h (L.take i) (L.drop i) ≤ phiAt k a b h (N.take i) (N.drop i))
    (hT : phiAt k a b h N [] = phiAt k a b h L []) (hG : Good k a b h L) : Good k a b h N := by
  intro A0 B0 hN
  have hA0 : N.take A0.length = A0 ∧ N.drop A0.length = B0 := by
    rw [hN]
    simp
  obtain ⟨A1, B1, hL1, hge⟩ := hG (L.take A0.length) (L.drop A0.length)
    (List.take_append_drop _ _).symm
  refine ⟨N.take A1.length, N.drop A1.length, (List.take_append_drop _ _).symm, ?_⟩
  have e1 : L.take A1.length = A1 ∧ L.drop A1.length = B1 := by
    rw [hL1]
    simp
  have c0 := hcut A0.length
  have c1 := hcut A1.length
  rw [hA0.1, hA0.2] at c0
  rw [e1.1, e1.2] at c1
  rw [hT]
  linarith

theorem holes_take_pair {R0 R1 S0 S1 : TRow} {W : List TRow}
    (h0 : k - 1 - S0.2.length ≤ k - 1 - R0.2.length)
    (h01 : (k - 1 - S0.2.length) + (k - 1 - S1.2.length)
      = (k - 1 - R0.2.length) + (k - 1 - R1.2.length)) :
    ∀ j, holesT k ((S0 :: S1 :: W).take j) ≤ holesT k ((R0 :: R1 :: W).take j)
  | 0 => by simp [holesT]
  | 1 => by simpa [holesT] using h0
  | j + 2 => by
    simp only [List.take_succ_cons, PS.holesT_cons]
    omega

/-- **Lemmas JS2, JS3**: a sequence with a shiftable junction gives a sequence with the same rows,
links and holes, `psi` one larger and at least the potential at every cut. -/
theorem shift_of_not_noJS (hk : 5 ≤ k) {L : List TRow} (hL : IsSeq k L)
    (htag : ∀ x ∈ L, x.1 ≤ 1) (hn : ¬ NoJS k L) :
    ∃ N : List TRow, IsSeq k N ∧ (∀ x ∈ N, x.1 ≤ 1) ∧ N.length = L.length ∧
      linksT N = linksT L ∧ holesT k N = holesT k L ∧ psi N = psi L + 1 ∧
      ∀ a b h, Good k a b h L → Good k a b h N := by
  unfold NoJS at hn
  push Not at hn
  obtain ⟨U, ⟨kdR, Rb⟩, ⟨kd', Q'⟩, W, rfl, hR, v, f, F, hQ', hc⟩ := hn
  simp only at hQ' hR hc
  subst hQ'
  set q := Rb.getLast hR with hq
  -- facts about the old sequence
  have hRmem : ((kdR, Rb) : TRow) ∈ U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W := by simp
  have hR'mem : ((kd', v :: f :: F) : TRow) ∈ U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W := by simp
  have hwR := hL.words _ hRmem
  have hwR' := hL.words _ hR'mem
  have hqp : PermW k q := hwR q (List.getLast_mem hR)
  have hvp : PermW k v := hwR' v (by simp)
  have hkd' : kd' ≤ 1 := htag _ hR'mem
  have hcl := hL.classes
  have hflat : ((U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W).map Prod.snd).flatten
      = ((U.map Prod.snd).flatten ++ Rb) ++ v :: (f :: F ++ (W.map Prod.snd).flatten) := by
    simp
  rw [hflat] at hcl
  have hRpw : List.Pairwise (fun a b => ¬ a ~r b) Rb :=
    (List.pairwise_append.mp (List.pairwise_append.mp hcl).1).2.1
  have hvf : ¬ v ~r f := by
    have := (List.pairwise_cons.mp (List.pairwise_append.mp hcl).2.1).1
    exact this f (by simp)
  have hvRb : ∀ w ∈ Rb, ¬ w ~r v := by
    intro w hw
    exact (List.pairwise_append.mp hcl).2.2 w (List.mem_append_right _ hw) v List.mem_cons_self
  -- the link between the two rows and the doors
  have hlinkRR : LinkK k kd' q v := by
    have hc2 := (hL.infix ⟨U, W, by simp⟩ : IsSeq k [(kdR, Rb), (kd', v :: f :: F)]).links
    exact (List.isChain_pair.mp hc2) hR (List.cons_ne_nil _ _)
  have hdR' := hL.doors _ hR'mem
  have hdvf := List.isChain_cons_cons.mp hdR'
  have hfe : f = tau2 k v := S.door_of_link (by omega) hvp (hwR' f (by simp)) hdvf.1 hvf
  -- the first row has at most `k - 2` blocks
  have hsz := hL.size_le _ hRmem
  have hsz' := hL.size_le _ hR'mem
  simp only at hsz hsz'
  have hRlen : Rb.length + 1 ≤ k - 1 := by
    by_contra hcon
    have hlen : Rb.length = k - 1 := by omega
    have ht := tau2_getLast_row (by omega) hR hwR (hL.doors _ hRmem) hRpw hlen
    rw [← hq] at ht
    rw [ht] at hc
    exact hvRb _ (List.head_mem hR) hc.symm
  -- the new sequence
  refine ⟨U ++ (kdR, Rb ++ [tau2 k q]) :: (kd', f :: F) :: W, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx w hw
      rcases List.mem_append.mp hx with hx | hx
      · exact hL.words x (List.mem_append_left _ hx) w hw
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases List.mem_append.mp hw with hw | hw
        · exact hwR w hw
        · rw [List.mem_singleton.mp hw]
          exact permW_tau2 (by omega) hqp
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hwR' w (List.mem_cons_of_mem _ hw)
      · exact hL.words x (by simp [hx]) w hw
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hL.pieces_ne x (List.mem_append_left _ hx)
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · exact hL.pieces_ne x (by simp [hx])
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hL.size_le x (List.mem_append_left _ hx)
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only [List.length_append, List.length_singleton]
        exact hRlen
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only [List.length_cons] at hsz' ⊢
        omega
      · exact hL.size_le x (by simp [hx])
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hL.doors x (List.mem_append_left _ hx)
      rcases List.mem_cons.mp hx with rfl | hx
      · refine List.IsChain.append (hL.doors _ hRmem) (List.isChain_singleton _) ?_
        intro z hz w hw
        rw [List.getLast?_eq_some_getLast hR, Option.mem_def, Option.some.injEq] at hz
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hw
        rw [← hz, ← hw]
        exact wlink2_tau2 (by omega) hqp.2.1
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hdvf.2
      · exact hL.doors x (by simp [hx])
    · refine chain_replace hL.links ?_ ?_ ?_
      · intro z hz hzx hy
        have e : ((kdR, Rb ++ [tau2 k q]) : TRow).2.head hy = Rb.head hR := by
          simp [List.head_append_of_ne_nil hR]
        rw [e]
        exact hz hzx hR
      · intro hx hy
        have e1 : ((kdR, Rb ++ [tau2 k q]) : TRow).2.getLast hx = tau2 k q := by simp
        have e2 : ((kd', f :: F) : TRow).2.head hy = tau2 k v := by simp [hfe]
        rw [e1, e2]
        exact link_tau2 hk hkd' hqp hlinkRR hc
      · intro z hz hy hzz
        have e : ((kd', f :: F) : TRow).2.getLast hy
            = ((kd', v :: f :: F) : TRow).2.getLast (List.cons_ne_nil _ _) := by
          simp [List.getLast_cons]
        rw [e]
        exact hz (List.cons_ne_nil _ _) hzz
    · have hflat' : ((U ++ (kdR, Rb ++ [tau2 k q]) :: (kd', f :: F) :: W).map Prod.snd).flatten
          = ((U.map Prod.snd).flatten ++ Rb) ++ tau2 k q :: (f :: F ++ (W.map Prod.snd).flatten) := by
        simp
      rw [hflat']
      exact pairwise_replace hcl hc.symm
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact htag x (List.mem_append_left _ hx)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact htag (kdR, Rb) hRmem
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hkd'
    · exact htag x (by simp [hx])
  · simp
  · exact linksT_congr (by simp)
  · simp only [PS.holesT_append, PS.holesT_cons]
    simp only [List.length_append, List.length_cons, List.length_nil] at hsz' ⊢
    omega
  · rw [psi_append, psi_append]
    simp only [psi, List.length_cons, List.length_append, List.length_nil]
    ring
  · intro a b h hG
    refine good_transfer ?_ ?_ hG
    · intro i
      refine phiAt_le_of (by simp) (linksT_congr (by simp [List.map_take])) ?_
        (hdK_congr (by simp [List.map_drop]))
      rw [List.take_append, List.take_append, PS.holesT_append, PS.holesT_append]
      have := holes_take_pair (k := k) (R0 := (kdR, Rb)) (R1 := (kd', v :: f :: F))
        (S0 := (kdR, Rb ++ [tau2 k q])) (S1 := (kd', f :: F)) (W := W)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_cons, List.length_nil] at hsz' ⊢; omega)
        (i - U.length)
      omega
    · have hne1 : U ++ (kdR, Rb ++ [tau2 k q]) :: (kd', f :: F) :: W ≠ [] := by simp
      have hne2 : U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W ≠ [] := by simp
      rw [KS.phiAt_end a b h hne1, KS.phiAt_end a b h hne2]
      have el : linksT (U ++ (kdR, Rb ++ [tau2 k q]) :: (kd', f :: F) :: W)
          = linksT (U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W) := linksT_congr (by simp)
      have eh : holesT k (U ++ (kdR, Rb ++ [tau2 k q]) :: (kd', f :: F) :: W)
          = holesT k (U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W) := by
        simp only [PS.holesT_append, PS.holesT_cons]
        simp only [List.length_append, List.length_cons, List.length_nil] at hsz' ⊢
        omega
      rw [el, eh]
      simp

end K16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K16.link_tau2
#print axioms SuperpermLowerBounds.K16.shift_of_not_noJS
