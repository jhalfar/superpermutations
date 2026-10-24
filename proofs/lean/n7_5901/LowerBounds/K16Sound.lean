import LowerBounds.K16Search
import LowerBounds.K16Word

/-!
# The search of `K16Search.lean` is complete (the written proof, section 3.3, "Completeness")

The proof is that of `KSound.lean` (it reuses `KS.RuleK`, `KS.KAlong`, the walks and the gate), with one
more hypothesis along the sequence: `NoJSAlong k last rest`, no row of `rest` is the second row of a
shiftable junction.  A row that Rule JS refuses has at least two blocks and begins in the class of the
next block of the last entry before it (the encoding gives `nxt (enc q) = enc (tau2 q)` and classes from
`ci`), so such a row is the second row of a shiftable junction.

`KStmt16 k js code fN fS cut`: the rule holds along no sequence that (if `js`) has no shiftable
junction.  `kstmt16_of_parts`: if every part of the search answers `false`, `KStmt16` holds.
-/

namespace SuperpermLowerBounds
namespace K16

open S (PermW WLink DoorEq Sub)
open PS (TRow Enc MInv walk all marks0 LinkK PCont IsSeq relabSeq)
open KS (walkG fK RuleK KAlong)

/-! ### The calls below a sequence for one kind of link -/

/-- As `KS.stepWM`, with the mask of Rule JS for every first block. -/
def stepJ (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray) (kb mk : ℕ) (js : Bool)
    (cq : ℕ) (c : Bool) (l : List ℕ) (M : ByteArray) : ByteArray :=
  if c then all (fun D M' => walkG ci nxt visit kb (jsM js ci cq D mk) D M') l M else M

theorem stepJ_sub (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray)
    (hv : ∀ n e M, Sub (visit n e M) M) (kb mk : ℕ) (js : Bool) (cq : ℕ) (c : Bool) (l : List ℕ)
    (M : ByteArray) : Sub (stepJ ci nxt visit kb mk js cq c l M) M := by
  unfold stepJ
  by_cases hc : c = true
  · rw [if_pos hc]
    exact PS.all_sub _ (fun D M' => KS.walkG_sub ci nxt visit hv kb _ D M') l M
  · rw [if_neg hc]
    exact Sub.refl M

theorem stepJ_found (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray)
    (hv : ∀ n e M, Sub (visit n e M) M) (kb mk : ℕ) (js : Bool) (cq : ℕ) {c : Bool}
    (hc : c = true) (P : ByteArray → Prop) (hP : ∀ M' M, Sub M' M → P M → P M') (D : ℕ)
    (hD : ∀ M, P M → (walkG ci nxt visit kb (jsM js ci cq D mk) D M).size = 0) {l : List ℕ}
    (hl : D ∈ l) {M : ByteArray} (hM : P M) : (stepJ ci nxt visit kb mk js cq c l M).size = 0 := by
  unfold stepJ
  rw [if_pos hc]
  exact PS.all_found (fun D' M' => walkG ci nxt visit kb (jsM js ci cq D' mk) D' M')
    (fun D' M' => KS.walkG_sub ci nxt visit hv kb _ D' M') P hP D hD l M hl hM

/-! ### The equations of the search -/

section Eqs

variable (ci nxt : ℕ → ℕ) (s3 s4 : ℕ → List ℕ) (kb : ℕ) (code mask : ℕ → ℕ → ℕ → ℕ)
  (fN fS : ℕ → ℕ → ℕ → ℤ) (cut : ℕ → ℕ → ℕ → ℤ → ℤ → Bool) (js : Bool) (fg nt tp : ℕ)

theorem go_zero (t r d : ℕ) (m M : ℤ) (q : ℕ) (B : ByteArray) :
    go ci nxt s3 s4 kb code mask fN fS cut js fg nt tp 0 t r d m M q B = ByteArray.empty := rfl

theorem go_succ (fuel t r d : ℕ) (m M : ℤ) (q : ℕ) (B : ByteArray) :
    go ci nxt s3 s4 kb code mask fN fS cut js fg nt tp (fuel + 1) t r d m M q B =
      if code t r d = 0 then B
      else if code t r d = 1 then ByteArray.empty
      else if (fuel != fg || (q + 8192 * d) % nt == tp) = true then
        if (stepJ ci nxt (fun n e B'' =>
            go ci nxt s3 s4 kb code mask fN fS cut js fg nt tp fuel t (r + 1) (d + n)
              (min m (fN t r d)) (max M (fN t r d)) e B'') kb (mask t (r + 1) d) js (ci (nxt q))
            (code t r d != 3 && cut t r d (min m (fN t r d)) (max M (fN t r d))) (s3 q) B).size = 0
        then
          stepJ ci nxt (fun n e B'' =>
            go ci nxt s3 s4 kb code mask fN fS cut js fg nt tp fuel t (r + 1) (d + n)
              (min m (fN t r d)) (max M (fN t r d)) e B'') kb (mask t (r + 1) d) js (ci (nxt q))
            (code t r d != 3 && cut t r d (min m (fN t r d)) (max M (fN t r d))) (s3 q) B
        else
          stepJ ci nxt (fun n e B'' =>
            go ci nxt s3 s4 kb code mask fN fS cut js fg nt tp fuel (t + 1) (r + 1) (d + n)
              (min m (fS t r d)) (max M (fS t r d)) e B'') kb (mask (t + 1) (r + 1) d) js
            (ci (nxt q))
            (code t r d != 2 && cut t r d (min m (fS t r d)) (max M (fS t r d))) (s4 q)
            (stepJ ci nxt (fun n e B'' =>
              go ci nxt s3 s4 kb code mask fN fS cut js fg nt tp fuel t (r + 1) (d + n)
                (min m (fN t r d)) (max M (fN t r d)) e B'') kb (mask t (r + 1) d) js (ci (nxt q))
              (code t r d != 3 && cut t r d (min m (fN t r d)) (max M (fN t r d))) (s3 q) B)
      else B := by
  rw [go]
  simp only [stepJ, beq_iff_eq, bne_iff_ne, ne_eq, Bool.and_eq_true, ite_not]
  split_ifs <;> simp_all

theorem go_sub : ∀ (fuel t r d : ℕ) (m M : ℤ) (q : ℕ) (B : ByteArray),
    Sub (go ci nxt s3 s4 kb code mask fN fS cut js fg nt tp fuel t r d m M q B) B := by
  intro fuel
  induction fuel with
  | zero =>
    intro t r d m M q B
    rw [go_zero]
    exact S.sub_of_size_zero ByteArray.size_empty B
  | succ fuel ih =>
    intro t r d m M q B
    rw [go_succ]
    have h1 := stepJ_sub ci nxt (fun n e B'' =>
      go ci nxt s3 s4 kb code mask fN fS cut js fg nt tp fuel t (r + 1) (d + n)
        (min m (fN t r d)) (max M (fN t r d)) e B'')
      (fun n e B'' => ih _ _ _ _ _ _ _) kb (mask t (r + 1) d) js (ci (nxt q))
      (code t r d != 3 && cut t r d (min m (fN t r d)) (max M (fN t r d))) (s3 q) B
    have h2 := fun X => stepJ_sub ci nxt (fun n e B'' =>
      go ci nxt s3 s4 kb code mask fN fS cut js fg nt tp fuel (t + 1) (r + 1) (d + n)
        (min m (fS t r d)) (max M (fS t r d)) e B'')
      (fun n e B'' => ih _ _ _ _ _ _ _) kb (mask (t + 1) (r + 1) d) js (ci (nxt q))
      (code t r d != 2 && cut t r d (min m (fS t r d)) (max M (fS t r d))) (s4 q) X
    split_ifs
    · exact Sub.refl B
    · exact S.sub_of_size_zero ByteArray.size_empty B
    · exact h1
    · exact (h2 _).trans h1
    · exact Sub.refl B

end Eqs

/-! ### No shiftable junction along the rest of a sequence -/

/-- No row of `rest` is the second row of a shiftable junction (the row before the first row of
`rest` has last entry `last`). -/
def NoJSAlong (k : ℕ) : List ℕ → List TRow → Prop
  | _, [] => True
  | _, (_, []) :: _ => True
  | last, (_, v :: R) :: rest =>
    (R ≠ [] → ¬ v ~r tau2 k last) ∧ NoJSAlong k ((v :: R).getLast (List.cons_ne_nil v R)) rest

theorem noJSAlong_of_noJS : ∀ (rest : List TRow) (x : TRow) (hx : x.2 ≠ []),
    (∀ y ∈ rest, y.2 ≠ []) → NoJS k (x :: rest) → NoJSAlong k (x.2.getLast hx) rest
  | [], _, _, _, _ => trivial
  | (kd, []) :: _, _, _, hne, _ => absurd rfl (hne (kd, []) List.mem_cons_self)
  | (kd, v :: R) :: rest', x, hx, hne, hno => by
    refine ⟨?_, ?_⟩
    · intro hR hrot
      obtain ⟨f, F, rfl⟩ := List.exists_cons_of_ne_nil hR
      exact hno [] x (kd, v :: f :: F) rest' rfl ⟨hx, v, f, F, rfl, hrot⟩
    · exact noJSAlong_of_noJS rest' (kd, v :: R) (List.cons_ne_nil v R)
        (fun y hy => hne y (List.mem_cons_of_mem _ hy))
        (fun U R1 R2 W heq => hno (x :: U) R1 R2 W (by rw [heq]; rfl))

theorem getLast_map_cons (g : List ℕ → List ℕ) (v : List ℕ) (R : List (List ℕ)) :
    (g v :: R.map g).getLast (List.cons_ne_nil _ _) = g ((v :: R).getLast (List.cons_ne_nil _ _)) := by
  have h := List.getLast_map (f := g) (l := v :: R) (by simp)
  exact h

theorem tau2_map (hk : 2 ≤ k) (f : ℕ → ℕ) {x : List ℕ} (hx : x.length = k) :
    tau2 k (x.map f) = (tau2 k x).map f := by
  have hy : (x.rotate (k - 1)).length = k := by rw [List.length_rotate, hx]
  obtain ⟨a, b, X, hxe, _⟩ := S.exists_cons_cons hy hk
  unfold tau2
  rw [← List.map_rotate, hxe]
  simp [S.doorW_cons]

theorem noJSAlong_relab (hk : 2 ≤ k) {e : List ℕ} (he : PermW k e) :
    ∀ (rest : List TRow) (last : List ℕ), PermW k last → (∀ y ∈ rest, ∀ w ∈ y.2, PermW k w) →
      NoJSAlong k last rest → NoJSAlong k (last.map (S.relab e)) (relabSeq e rest)
  | [], _, _, _, _ => trivial
  | (kd, []) :: rest', _, _, _, _ => trivial
  | (kd, v :: R) :: rest', last, hlast, hw, h => by
    obtain ⟨h1, h2⟩ := h
    have hv : PermW k v := hw _ List.mem_cons_self v List.mem_cons_self
    show (R.map (List.map (S.relab e)) ≠ [] →
        ¬ v.map (S.relab e) ~r tau2 k (last.map (S.relab e))) ∧
      NoJSAlong k ((v.map (S.relab e) :: R.map (List.map (S.relab e))).getLast
        (List.cons_ne_nil _ _)) (relabSeq e rest')
    refine ⟨?_, ?_⟩
    · intro hR
      have hR' : R ≠ [] := by
        intro h0
        rw [h0] at hR
        exact hR rfl
      rw [tau2_map hk _ hlast.2.1]
      exact S.not_isRotated_map_relab he hv (permW_tau2 hk hlast) (h1 hR')
    · rw [getLast_map_cons]
      exact noJSAlong_relab hk he rest' _ (hw _ List.mem_cons_self _ (List.getLast_mem _))
        (fun y hy => hw y (List.mem_cons_of_mem _ hy)) h2

/-! ### Completeness of the engine -/

section Engine

variable {k : ℕ} {enc : List ℕ → ℕ} {ci nxt : ℕ → ℕ} {s3 s4 : ℕ → List ℕ} {jl : List ℕ}
  {st : ℕ} {code mask : ℕ → ℕ → ℕ → ℕ} {fN fS : ℕ → ℕ → ℕ → ℤ}
  {cut : ℕ → ℕ → ℕ → ℤ → ℤ → Bool} {js : Bool} {fg nt tp : ℕ}

/-- The mask with Rule JS keeps the bit of a row that is not refused. -/
theorem jsM_bit (E : Enc k enc ci nxt s3 s4 jl st) (hk : 2 ≤ k) {last v : List ℕ}
    {R : List (List ℕ)} (hlast : PermW k last) (hv : PermW k v) {mk : ℕ}
    (hbit : (mk / 2 ^ R.length) % 2 = 1) (hjs : js = true → R ≠ [] → ¬ v ~r tau2 k last) :
    (jsM js ci (ci (nxt (enc last))) (enc v) mk / 2 ^ R.length) % 2 = 1 := by
  unfold jsM
  by_cases hj : (js && ci (enc v) == ci (nxt (enc last))) = true
  · rw [if_pos hj]
    simp only [Bool.and_eq_true, beq_iff_eq] at hj
    have hRnil : R = [] := by
      by_contra hR
      apply hjs hj.1 hR
      have e := E.nxt_eq last (tau2 k last) hlast rfl
      rw [e] at hj
      exact E.ci_inj v (tau2 k last) hv (permW_tau2 hk hlast) hj.2
    subst hRnil
    simp only [List.length_nil, pow_zero, Nat.div_one] at hbit ⊢
    rw [Nat.mod_mod]
    exact hbit
  · rw [if_neg hj]
    exact hbit

/-- The search finds the end of a sequence of which it has reached a prefix, if the rule holds
along the rest of the sequence and (with Rule JS) no row of the rest is refused. -/
theorem go_complete (E : Enc k enc ci nxt s3 s4 jl st) (hk : 2 ≤ k)
    (hmask : ∀ t r d j, j < k - 1 → code t r (d + (k - 2 - j)) ≠ 0 →
      (mask t r d / 2 ^ j) % 2 = 1) :
    ∀ (fuel : ℕ) (rest : List TRow) (t r d : ℕ) (m M : ℤ) (B : ByteArray) (last : List ℕ)
      (used : List (List ℕ)),
      PermW k last → (∀ u ∈ used, PermW k u) → MInv enc ci B used → PCont k last used rest →
      KAlong k enc code fN fS cut fg nt tp fuel t r d m M last rest →
      (js = true → NoJSAlong k last rest) →
      (go ci nxt s3 s4 (k - 1) code mask fN fS cut js fg nt tp fuel t r d m M (enc last) B).size
        = 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intros
    rw [go_zero]
    exact ByteArray.size_empty
  | succ fuel ih =>
    intro rest t r d m M B last used hlast hused hM hcont halong hjs
    rw [go_succ]
    cases rest with
    | nil =>
      simp only [KAlong] at halong
      rw [if_neg (by omega), if_pos halong]
      exact ByteArray.size_empty
    | cons Q rest' =>
      obtain ⟨kd, Q⟩ := Q
      cases Q with
      | nil => exact hcont.elim
      | cons v R =>
        obtain ⟨hR, hperm, hlink, hdoor, hnew, hpw, hcont'⟩ := hcont
        unfold KAlong at halong
        obtain ⟨hkd, hcode, hcut, hgate, hnext, halong'⟩ := halong
        have hjs1 : js = true → R ≠ [] → ¬ v ~r tau2 k last := fun h => (hjs h).1
        have hjs2 : js = true → NoJSAlong k ((v :: R).getLast (List.cons_ne_nil v R)) rest' :=
          fun h => (hjs h).2
        have hc0 : ¬ code t r d = 0 := by omega
        have hc1 : ¬ code t r d = 1 := by omega
        have hc : (fuel != fg || (enc last + 8192 * d) % nt == tp) = true := by
          rcases hgate with h | h <;> simp [h]
        rw [if_neg hc0, if_neg hc1, if_pos hc]
        have hv : PermW k v := hperm v List.mem_cons_self
        have hused' : ∀ u ∈ used ++ v :: R, PermW k u := by
          intro u hu
          rcases List.mem_append.mp hu with h | h
          · exact hused u h
          · exact hperm u h
        have hsubg : ∀ (t' r' d' : ℕ) (m' M' : ℤ) (n e : ℕ) (B'' : ByteArray),
            Sub (go ci nxt s3 s4 (k - 1) code mask fN fS cut js fg nt tp fuel t' r' (d' + n) m' M'
              e B'') B'' :=
          fun t' r' d' m' M' n e B'' => go_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        have hbit : (jsM js ci (ci (nxt (enc last))) (enc v) (mask (t + kd) (r + 1) d)
            / 2 ^ R.length) % 2 = 1 :=
          jsM_bit E hk hlast hv (hmask _ _ _ _ (by omega) hnext) hjs1
        have hwalk : ∀ B', MInv enc ci B' used →
            (walkG ci nxt (fun n e B'' =>
              go ci nxt s3 s4 (k - 1) code mask fN fS cut js fg nt tp fuel (t + kd) (r + 1) (d + n)
                (min m (fK fN fS kd t r d)) (max M (fK fN fS kd t r d)) e B'') (k - 1)
              (jsM js ci (ci (nxt (enc last))) (enc v) (mask (t + kd) (r + 1) d)) (enc v) B').size
              = 0 := by
          intro B' hB'
          have h := KS.walkG_complete E
            (fun n e B'' =>
              go ci nxt s3 s4 (k - 1) code mask fN fS cut js fg nt tp fuel (t + kd) (r + 1) (d + n)
                (min m (fK fN fS kd t r d)) (max M (fK fN fS kd t r d)) e B'')
            (hsubg _ _ _ _ _) R (k - 2)
            (jsM js ci (ci (nxt (enc last))) (enc v) (mask (t + kd) (r + 1) d)) v B' used hR hbit
            hperm hdoor hB' hused hnew hpw
            (by
              intro B'' hB''
              exact ih rest' _ _ _ _ _ B'' _ (used ++ v :: R) (hperm _ (List.getLast_mem _))
                hused' hB'' hcont' halong' hjs2)
          rw [show k - 2 + 1 = k - 1 from by omega] at h
          exact h
        have hPsub : ∀ B' B : ByteArray, Sub B' B → MInv enc ci B used → MInv enc ci B' used :=
          fun B' B hs hB => hB.sub hs
        have h1 := stepJ_sub ci nxt (fun n e B'' =>
          go ci nxt s3 s4 (k - 1) code mask fN fS cut js fg nt tp fuel t (r + 1) (d + n)
            (min m (fN t r d)) (max M (fN t r d)) e B'') (hsubg _ _ _ _ _) (k - 1)
          (mask t (r + 1) d) js (ci (nxt (enc last)))
          (code t r d != 3 && cut t r d (min m (fN t r d)) (max M (fN t r d))) (s3 (enc last)) B
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkd with rfl | rfl
        · have hwalk' : ∀ B', MInv enc ci B' used →
              (walkG ci nxt (fun n e B'' =>
                go ci nxt s3 s4 (k - 1) code mask fN fS cut js fg nt tp fuel t (r + 1) (d + n)
                  (min m (fN t r d)) (max M (fN t r d)) e B'') (k - 1)
                (jsM js ci (ci (nxt (enc last))) (enc v) (mask t (r + 1) d)) (enc v)
                B').size = 0 := by
            simpa [fK] using hwalk
          have hcut' : cut t r d (min m (fN t r d)) (max M (fN t r d)) = true := by
            simpa [fK] using hcut
          have hcc : (code t r d != 3 && cut t r d (min m (fN t r d)) (max M (fN t r d)))
              = true := by
            rw [hcut', Bool.and_true]
            rcases hcode with h | h <;> simp [h]
          have hf := stepJ_found ci nxt (fun n e B'' =>
              go ci nxt s3 s4 (k - 1) code mask fN fS cut js fg nt tp fuel t (r + 1) (d + n)
                (min m (fN t r d)) (max M (fN t r d)) e B'') (hsubg _ _ _ _ _) (k - 1)
            (mask t (r + 1) d) js (ci (nxt (enc last))) hcc
            (fun B' => MInv enc ci B' used) hPsub (enc v) hwalk'
            (E.s3_mem last v hlast hv (hlink.1 rfl)) hM
          rw [if_pos hf]
          exact hf
        · have hwalk' : ∀ B', MInv enc ci B' used →
              (walkG ci nxt (fun n e B'' =>
                go ci nxt s3 s4 (k - 1) code mask fN fS cut js fg nt tp fuel (t + 1) (r + 1) (d + n)
                  (min m (fS t r d)) (max M (fS t r d)) e B'') (k - 1)
                (jsM js ci (ci (nxt (enc last))) (enc v) (mask (t + 1) (r + 1) d))
                (enc v) B').size = 0 := by
            simpa [fK] using hwalk
          have hcut' : cut t r d (min m (fS t r d)) (max M (fS t r d)) = true := by
            simpa [fK] using hcut
          have hcc : (code t r d != 2 && cut t r d (min m (fS t r d)) (max M (fS t r d)))
              = true := by
            rw [hcut', Bool.and_true]
            rcases hcode with h | h <;> simp [h]
          split_ifs with hz1
          · exact hz1
          · exact stepJ_found ci nxt (fun n e B'' =>
                go ci nxt s3 s4 (k - 1) code mask fN fS cut js fg nt tp fuel (t + 1) (r + 1) (d + n)
                  (min m (fS t r d)) (max M (fS t r d)) e B'') (hsubg _ _ _ _ _) (k - 1)
              (mask (t + 1) (r + 1) d) js (ci (nxt (enc last))) hcc
              (fun B' => MInv enc ci B' used) hPsub (enc v) hwalk'
              (E.s4_mem last v hlast hv (hlink.2 rfl)) (hM.sub h1)

/-- A part of the search finds a sequence along which the rule holds and no row is refused. -/
theorem searchPart_true (E : Enc k enc ci nxt s3 s4 jl st) (hk : 2 ≤ k)
    (hmask : ∀ t r d j, j < k - 1 → code t r (d + (k - 2 - j)) ≠ 0 →
      (mask t r d / 2 ^ j) % 2 = 1) (sz fuel : ℕ)
    (R1 : List (List ℕ)) (rest : List TRow)
    (hR1 : R1.length ≤ k - 2) (hperm : ∀ w ∈ List.range' 1 k :: R1, PermW k w)
    (hdoor : List.IsChain (DoorEq k) (List.range' 1 k :: R1))
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) (List.range' 1 k :: R1))
    (hcont : PCont k ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _))
      (List.range' 1 k :: R1) rest)
    (halong : KAlong k enc code fN fS cut fg nt tp fuel 0 1 (k - 2 - R1.length) 0 0
      ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _)) rest)
    (hjs : js = true → NoJSAlong k ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _)) rest) :
    searchPart ci nxt s3 s4 st (k - 1) code mask fN fS cut js sz fuel fg nt tp = true := by
  have h := PS.walk_complete E
    (fun n e B => go ci nxt s3 s4 (k - 1) code mask fN fS cut js fg nt tp fuel 0 1 n 0 0 e B)
    (fun n e B => go_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) R1 (k - 2)
    (List.range' 1 k) (marks0 sz) [] hR1 hperm hdoor (PS.minv_marks0 enc ci sz) (by simp)
    (by simp) hpw
    (by
      intro B' hB'
      exact go_complete (code := code) (mask := mask) (fN := fN) (fS := fS) (cut := cut)
        (js := js) (fg := fg) (nt := nt) (tp := tp) E hk hmask fuel rest 0 1 (k - 2 - R1.length)
        0 0 B' _ (List.range' 1 k :: R1) (hperm _ (List.getLast_mem _)) hperm (by simpa using hB')
        hcont halong hjs)
  rw [show k - 2 + 1 = k - 1 from by omega, ← E.st_eq] at h
  unfold searchPart
  rw [h]
  rfl

end Engine

/-! ### The statement -/

/-- The rule holds along no sequence that, with Rule JS, has no shiftable junction. -/
def KStmt16 (k : ℕ) (js : Bool) (code : ℕ → ℕ → ℕ → ℕ) (fN fS : ℕ → ℕ → ℕ → ℤ)
    (cut : ℕ → ℕ → ℕ → ℤ → ℤ → Bool) : Prop :=
  ∀ (x : TRow) (rest : List TRow), IsSeq k (x :: rest) → (js = true → NoJS k (x :: rest)) →
    ¬ RuleK k code fN fS cut 0 1 (k - 1 - x.2.length) 0 0 rest

/-- **A search all of whose parts answer `false` proves the statement.** -/
theorem kstmt16_of_parts {k : ℕ} {enc : List ℕ → ℕ} {ci nxt : ℕ → ℕ} {s3 s4 : ℕ → List ℕ}
    {jl : List ℕ} {st : ℕ} {code mask : ℕ → ℕ → ℕ → ℕ} {fN fS : ℕ → ℕ → ℕ → ℤ}
    {cut : ℕ → ℕ → ℕ → ℤ → ℤ → Bool} {js : Bool} {sz fuel fg nt : ℕ}
    (E : Enc k enc ci nxt s3 s4 jl st) (hk : 3 ≤ k) (hnt : 0 < nt)
    (hmask : ∀ t r d j, j < k - 1 → code t r (d + (k - 2 - j)) ≠ 0 →
      (mask t r d / 2 ^ j) % 2 = 1)
    (hs : ∀ tp, tp < nt →
      searchPart ci nxt s3 s4 st (k - 1) code mask fN fS cut js sz fuel fg nt tp = false) :
    KStmt16 k js code fN fS cut := by
  intro x0 rest0 hL hjs hrule
  obtain ⟨kd0, Q0⟩ := x0
  have hQ0 : Q0 ≠ [] := hL.pieces_ne (kd0, Q0) List.mem_cons_self
  obtain ⟨v0, R0, rfl⟩ := List.exists_cons_of_ne_nil hQ0
  have hv0 : PermW k v0 := hL.words _ List.mem_cons_self v0 List.mem_cons_self
  have hL' := hL.relabel hv0
  have hrule' := KS.ruleK_relab v0 rest0 _ _ _ _ _ hrule
  -- no shiftable junction, along the relabelled rest
  have hjsA : js = true → NoJSAlong k ((v0 :: R0).getLast (List.cons_ne_nil _ _)) rest0 :=
    fun h => noJSAlong_of_noJS rest0 (kd0, v0 :: R0) (List.cons_ne_nil _ _)
      (fun y hy => hL.pieces_ne y (List.mem_cons_of_mem _ hy)) (hjs h)
  have hg : v0.map (S.relab v0) = List.range' 1 k := by
    rw [S.map_relab_self hv0.1, hv0.2.1]
  have hjsR : js = true → NoJSAlong k
      ((List.range' 1 k :: R0.map (List.map (S.relab v0))).getLast (List.cons_ne_nil _ _))
      (relabSeq v0 rest0) := by
    intro h
    rw [← hg, getLast_map_cons]
    exact noJSAlong_relab (by omega) hv0 rest0 _
      (hL.words _ List.mem_cons_self _ (List.getLast_mem _))
      (fun y hy => hL.words y (List.mem_cons_of_mem _ hy)) (hjsA h)
  have hshape : relabSeq v0 ((kd0, v0 :: R0) :: rest0) =
      (kd0, List.range' 1 k :: R0.map (List.map (S.relab v0))) :: relabSeq v0 rest0 := by
    simp [relabSeq, S.map_relab_self hv0.1, hv0.2.1]
  rw [hshape] at hL'
  have elen : k - 1 - (kd0, v0 :: R0).2.length
      = k - 2 - (R0.map (List.map (S.relab v0))).length := by
    simp only [List.length_cons, List.length_map]
    omega
  rw [elen] at hrule'
  generalize R0.map (List.map (S.relab v0)) = R1 at hL' hrule' hjsR
  generalize relabSeq v0 rest0 = rest1 at hL' hrule' hjsR
  have hperm : ∀ w ∈ List.range' 1 k :: R1, PermW k w :=
    hL'.words (kd0, List.range' 1 k :: R1) List.mem_cons_self
  have hcl : List.Pairwise (fun a b => ¬ a ~r b)
      ((List.range' 1 k :: R1) ++ (rest1.map Prod.snd).flatten) := by
    have := hL'.classes
    simp only [List.map_cons, List.flatten_cons] at this
    exact this
  have hcl' := List.pairwise_append.mp hcl
  have hsz := hL'.size_le (kd0, List.range' 1 k :: R1) List.mem_cons_self
  have hR1 : R1.length ≤ k - 2 := by
    simp only [List.length_cons] at hsz
    omega
  have hdoor := S.door_chain hk _ hperm
    (hL'.doors (kd0, List.range' 1 k :: R1) List.mem_cons_self) hcl'.1
  have hcont := PS.pcont_of_seq hk rest1 (kd0, List.range' 1 k :: R1) (List.range' 1 k :: R1)
    (List.cons_ne_nil _ _) hL' hcl'.2.2
  have hne1 : ∀ y ∈ rest1, y.2 ≠ [] :=
    fun y hy => hL'.pieces_ne y (List.mem_cons_of_mem _ hy)
  obtain ⟨tp, htp, hP⟩ := KS.kalong_gate (enc := enc) (fg := fg) hnt fuel rest1 _ _ _ _ _ _
    (KS.kalong_of_rule (enc := enc) fg rest1 fuel _ _ _ _ _
      ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _)) hne1 hrule')
  have h := searchPart_true E (by omega) hmask sz fuel R1 rest1 hR1 hperm hdoor hcl'.1 hcont hP hjsR
  rw [hs tp htp] at h
  cases h

end K16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K16.kstmt16_of_parts
