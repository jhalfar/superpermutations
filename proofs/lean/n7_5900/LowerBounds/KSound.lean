import LowerBounds.PEnc
import LowerBounds.KSearch

/-!
# The search of `KSearch.lean` is complete

`RuleK k code fN fS cut t r d m M rest`: the rule holds along the rows `rest` that continue a
sequence with counters `t`, `r`, `d` and potentials `m`, `M`: every sequence on the way is
continued by the link that follows it (the code allows the kind of the link, and the cut allows it
with the least and the largest potential that include the cut behind the sequence), and the
sequence at the end is a violation.  The rule depends on the kinds of the links and on the numbers
of blocks of the rows only.

`KStmt k code fN fS cut`: the rule holds along no sequence.  `kstmt_of_parts`: if every part of
the search answers `false`, and the mask has a bit for every row after which the code is not `0`,
then `KStmt` holds.  The proof is that of `PSound.lean` and `PSeq.lean` with the two potentials
added to the counters, with the mask and with the look at the marks before a walk; the lemmas
about lists of successors (`all`) and the table of marks are taken from there.
-/

namespace SuperpermLowerBounds
namespace KS

open S (PermW WLink DoorEq Sub)
open PS (TRow Enc MInv walk all marks0 LinkK PCont IsSeq relabSeq)

/-- The potential of the cut behind a sequence that is followed by a link of kind `kd`. -/
def fK (fN fS : ℕ → ℕ → ℕ → ℤ) (kd : ℕ) : ℕ → ℕ → ℕ → ℤ := if kd = 0 then fN else fS

/-! ### Rows with a mask -/

theorem walkM_zero (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray) (mk D : ℕ)
    (M : ByteArray) : walkM ci nxt visit 0 mk D M = M := rfl

theorem walkM_succ (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray) (n mk D : ℕ)
    (M : ByteArray) : walkM ci nxt visit (n + 1) mk D M =
      if mk = 0 then M
      else if M.get! (ci D) = 0 then
        if (if mk % 2 = 1 then visit n D (M.set! (ci D) 1) else M.set! (ci D) 1).size = 0 then
          (if mk % 2 = 1 then visit n D (M.set! (ci D) 1) else M.set! (ci D) 1)
        else (walkM ci nxt visit n (mk / 2) (nxt D)
          (if mk % 2 = 1 then visit n D (M.set! (ci D) 1) else M.set! (ci D) 1)).set! (ci D) 0
      else M := by
  rw [walkM]
  simp only [beq_iff_eq, bne_iff_ne, ne_eq, ite_not]

theorem walkM_sub (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray)
    (hv : ∀ n e M, Sub (visit n e M) M) :
    ∀ (n mk D : ℕ) (M : ByteArray), Sub (walkM ci nxt visit n mk D M) M := by
  intro n
  induction n with
  | zero =>
    intro mk D M
    rw [walkM_zero]
    exact Sub.refl M
  | succ n ih =>
    intro mk D M
    rw [walkM_succ]
    have hvis : Sub (if mk % 2 = 1 then visit n D (M.set! (ci D) 1) else M.set! (ci D) 1)
        (M.set! (ci D) 1) := by
      split_ifs
      · exact hv _ _ _
      · exact Sub.refl _
    generalize (if mk % 2 = 1 then visit n D (M.set! (ci D) 1) else M.set! (ci D) 1) = vis
      at hvis
    by_cases hmk : mk = 0
    · rw [if_pos hmk]
      exact Sub.refl M
    rw [if_neg hmk]
    by_cases h0 : M.get! (ci D) = 0
    · rw [if_pos h0]
      by_cases hz : vis.size = 0
      · rw [if_pos hz]
        exact S.sub_of_size_zero hz M
      · rw [if_neg hz]
        exact S.sub_clear ((ih _ _ _).trans hvis)
    · rw [if_neg h0]
      exact Sub.refl M

/-- The walk with a mask that starts at the first block of a row `v :: R` whose classes are new
finds what the search below the sequence extended by that row finds, if the mask has the bit of
this row. -/
theorem walkM_complete {k : ℕ} {enc : List ℕ → ℕ} {ci nxt : ℕ → ℕ} {s3 s4 : ℕ → List ℕ}
    {jl : List ℕ} {st : ℕ} (E : Enc k enc ci nxt s3 s4 jl st)
    (visit : ℕ → ℕ → ByteArray → ByteArray) (hsub : ∀ n e M, Sub (visit n e M) M) :
    ∀ (R : List (List ℕ)) (n mk : ℕ) (v : List ℕ) (M : ByteArray) (used : List (List ℕ)),
      R.length ≤ n → (mk / 2 ^ R.length) % 2 = 1 → (∀ w ∈ v :: R, PermW k w) →
      List.IsChain (DoorEq k) (v :: R) →
      MInv enc ci M used → (∀ u ∈ used, PermW k u) →
      (∀ u ∈ used, ∀ w ∈ v :: R, ¬ u ~r w) → List.Pairwise (fun a b => ¬ a ~r b) (v :: R) →
      (∀ M', MInv enc ci M' (used ++ v :: R) →
        (visit (n - R.length) (enc ((v :: R).getLast (List.cons_ne_nil v R))) M').size = 0) →
      (walkM ci nxt visit (n + 1) mk (enc v) M).size = 0 := by
  intro R
  induction R with
  | nil =>
    intro n mk v M used _ hbit hperm _ hM hused hnew _ hfin
    have hv := hperm v List.mem_cons_self
    have h0 := PS.unmarked_of_new E hM hused hv (fun u hu => hnew u hu v List.mem_cons_self)
    have hb : mk % 2 = 1 := by simpa using hbit
    have hmk : ¬ mk = 0 := by omega
    have hf : (visit n (enc v) (M.set! (ci (enc v)) 1)).size = 0 := hfin _ (PS.minv_set hM v)
    rw [walkM_succ, if_neg hmk, if_pos h0, if_pos hb, if_pos hf]
    exact hf
  | cons v' R' ih =>
    intro n mk v M used hn hbit hperm hdoor hM hused hnew hpw hfin
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
    have hv := hperm v List.mem_cons_self
    have h0 := PS.unmarked_of_new E hM hused hv (fun u hu => hnew u hu v List.mem_cons_self)
    have hdc := List.isChain_cons_cons.mp hdoor
    have hpc := List.pairwise_cons.mp hpw
    have hused' : ∀ u ∈ used ++ [v], PermW k u := by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hused u h
      · rw [List.mem_singleton.mp h]
        exact hv
    have hmk : ¬ mk = 0 := by
      intro h
      rw [h] at hbit
      simp at hbit
    have hbit' : (mk / 2 / 2 ^ R'.length) % 2 = 1 := by
      have e : mk / 2 / 2 ^ R'.length = mk / 2 ^ (v' :: R').length := by
        rw [Nat.div_div_eq_div_mul, List.length_cons, Nat.pow_succ, Nat.mul_comm]
      rw [e]
      exact hbit
    have hvis : MInv enc ci
        (if mk % 2 = 1 then visit (m + 1) (enc v) (M.set! (ci (enc v)) 1)
          else M.set! (ci (enc v)) 1) (used ++ [v]) := by
      split_ifs
      · exact (PS.minv_set hM v).sub (hsub _ _ _)
      · exact PS.minv_set hM v
    rw [walkM_succ, if_neg hmk, if_pos h0]
    generalize (if mk % 2 = 1 then visit (m + 1) (enc v) (M.set! (ci (enc v)) 1)
      else M.set! (ci (enc v)) 1) = vis at hvis
    by_cases hz : vis.size = 0
    · rw [if_pos hz]
      exact hz
    · rw [if_neg hz, ByteArray.size_set!, E.nxt_eq v v' hv hdc.1]
      apply ih m (mk / 2) v' _ (used ++ [v]) (by simp only [List.length_cons] at hn; omega) hbit'
        (fun w hw => hperm w (List.mem_cons_of_mem _ hw)) hdc.2 hvis hused'
        (by
          intro u hu w hw
          rcases List.mem_append.mp hu with h | h
          · exact hnew u h w (List.mem_cons_of_mem _ hw)
          · rw [List.mem_singleton.mp h]
            exact hpc.1 w hw)
        hpc.2
      intro M' hM'
      have e : used ++ [v] ++ v' :: R' = used ++ v :: v' :: R' := by simp
      rw [e] at hM'
      have h := hfin M' hM'
      rw [List.getLast_cons (List.cons_ne_nil v' R')] at h
      have e2 : m + 1 - (v' :: R').length = m - R'.length := by
        simp only [List.length_cons]
        omega
      rw [e2] at h
      exact h

theorem scanLive_succ (ci nxt : ℕ → ℕ) (M : ByteArray) (n mk D : ℕ) :
    scanLive ci nxt M (n + 1) mk D =
      if mk = 0 then false
      else if M.get! (ci D) = 0 then
        (if mk % 2 = 1 then true else scanLive ci nxt M n (mk / 2) (nxt D))
      else false := by
  rw [scanLive]
  simp only [beq_iff_eq, bne_iff_ne, ne_eq, ite_not]

/-- The look at the marks sees a row `v :: R` whose classes are new, if the mask has the bit of
this row. -/
theorem scanLive_true {k : ℕ} {enc : List ℕ → ℕ} {ci nxt : ℕ → ℕ} {s3 s4 : ℕ → List ℕ}
    {jl : List ℕ} {st : ℕ} (E : Enc k enc ci nxt s3 s4 jl st) :
    ∀ (R : List (List ℕ)) (n mk : ℕ) (v : List ℕ) (M : ByteArray) (used : List (List ℕ)),
      R.length ≤ n → (mk / 2 ^ R.length) % 2 = 1 → (∀ w ∈ v :: R, PermW k w) →
      List.IsChain (DoorEq k) (v :: R) →
      MInv enc ci M used → (∀ u ∈ used, PermW k u) →
      (∀ u ∈ used, ∀ w ∈ v :: R, ¬ u ~r w) →
      scanLive ci nxt M (n + 1) mk (enc v) = true := by
  intro R
  induction R with
  | nil =>
    intro n mk v M used _ hbit hperm _ hM hused hnew
    have hv := hperm v List.mem_cons_self
    have h0 := PS.unmarked_of_new E hM hused hv (fun u hu => hnew u hu v List.mem_cons_self)
    have hb : mk % 2 = 1 := by simpa using hbit
    have hmk : ¬ mk = 0 := by omega
    rw [scanLive_succ, if_neg hmk, if_pos h0, if_pos hb]
  | cons v' R' ih =>
    intro n mk v M used hn hbit hperm hdoor hM hused hnew
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
    have hv := hperm v List.mem_cons_self
    have h0 := PS.unmarked_of_new E hM hused hv (fun u hu => hnew u hu v List.mem_cons_self)
    have hdc := List.isChain_cons_cons.mp hdoor
    have hmk : ¬ mk = 0 := by
      intro h
      rw [h] at hbit
      simp at hbit
    have hbit' : (mk / 2 / 2 ^ R'.length) % 2 = 1 := by
      have e : mk / 2 / 2 ^ R'.length = mk / 2 ^ (v' :: R').length := by
        rw [Nat.div_div_eq_div_mul, List.length_cons, Nat.pow_succ, Nat.mul_comm]
      rw [e]
      exact hbit
    rw [scanLive_succ, if_neg hmk, if_pos h0]
    by_cases hb : mk % 2 = 1
    · rw [if_pos hb]
    · rw [if_neg hb, E.nxt_eq v v' hv hdc.1]
      exact ih m (mk / 2) v' M used (by simp only [List.length_cons] at hn; omega) hbit'
        (fun w hw => hperm w (List.mem_cons_of_mem _ hw)) hdc.2 hM hused
        (fun u hu w hw => hnew u hu w (List.mem_cons_of_mem _ hw))

theorem walkG_sub (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray)
    (hv : ∀ n e M, Sub (visit n e M) M) (n mk D : ℕ) (M : ByteArray) :
    Sub (walkG ci nxt visit n mk D M) M := by
  unfold walkG
  split_ifs
  · exact walkM_sub ci nxt visit hv n mk D M
  · exact Sub.refl M

/-- The walk that is entered only after the look at the marks finds what the walk finds. -/
theorem walkG_complete {k : ℕ} {enc : List ℕ → ℕ} {ci nxt : ℕ → ℕ} {s3 s4 : ℕ → List ℕ}
    {jl : List ℕ} {st : ℕ} (E : Enc k enc ci nxt s3 s4 jl st)
    (visit : ℕ → ℕ → ByteArray → ByteArray) (hsub : ∀ n e M, Sub (visit n e M) M)
    (R : List (List ℕ)) (n mk : ℕ) (v : List ℕ) (M : ByteArray) (used : List (List ℕ))
    (hn : R.length ≤ n) (hbit : (mk / 2 ^ R.length) % 2 = 1) (hperm : ∀ w ∈ v :: R, PermW k w)
    (hdoor : List.IsChain (DoorEq k) (v :: R)) (hM : MInv enc ci M used)
    (hused : ∀ u ∈ used, PermW k u) (hnew : ∀ u ∈ used, ∀ w ∈ v :: R, ¬ u ~r w)
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) (v :: R))
    (hfin : ∀ M', MInv enc ci M' (used ++ v :: R) →
      (visit (n - R.length) (enc ((v :: R).getLast (List.cons_ne_nil v R))) M').size = 0) :
    (walkG ci nxt visit (n + 1) mk (enc v) M).size = 0 := by
  unfold walkG
  rw [if_pos (scanLive_true E R n mk v M used hn hbit hperm hdoor hM hused hnew)]
  exact walkM_complete E visit hsub R n mk v M used hn hbit hperm hdoor hM hused hnew hpw hfin

/-- The calls below a sequence for one kind of link, if the rule allows it. -/
def stepWM (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray) (kb mk : ℕ) (c : Bool)
    (l : List ℕ) (M : ByteArray) : ByteArray :=
  if c then all (fun D M' => walkG ci nxt visit kb mk D M') l M else M

theorem stepWM_sub (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray)
    (hv : ∀ n e M, Sub (visit n e M) M) (kb mk : ℕ) (c : Bool) (l : List ℕ) (M : ByteArray) :
    Sub (stepWM ci nxt visit kb mk c l M) M := by
  unfold stepWM
  by_cases hc : c = true
  · rw [if_pos hc]
    exact PS.all_sub _ (fun D M' => walkG_sub ci nxt visit hv kb mk D M') l M
  · rw [if_neg hc]
    exact Sub.refl M

theorem stepWM_found (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray)
    (hv : ∀ n e M, Sub (visit n e M) M) (kb mk : ℕ) {c : Bool} (hc : c = true)
    (P : ByteArray → Prop) (hP : ∀ M' M, Sub M' M → P M → P M') (D : ℕ)
    (hD : ∀ M, P M → (walkG ci nxt visit kb mk D M).size = 0) {l : List ℕ} (hl : D ∈ l)
    {M : ByteArray} (hM : P M) : (stepWM ci nxt visit kb mk c l M).size = 0 := by
  unfold stepWM
  rw [if_pos hc]
  exact PS.all_found _ (fun D M' => walkG_sub ci nxt visit hv kb mk D M') P hP D hD l M hl hM

/-! ### The equations of the search -/

section Eqs

variable (ci nxt : ℕ → ℕ) (s3 s4 : ℕ → List ℕ) (kb : ℕ) (code mask : ℕ → ℕ → ℕ → ℕ)
  (fN fS : ℕ → ℕ → ℕ → ℤ) (cut : ℕ → ℕ → ℕ → ℤ → ℤ → Bool) (fg nt tp : ℕ)

theorem go_zero (t r d : ℕ) (m M : ℤ) (q : ℕ) (B : ByteArray) :
    go ci nxt s3 s4 kb code mask fN fS cut fg nt tp 0 t r d m M q B = ByteArray.empty := rfl

theorem go_succ (fuel t r d : ℕ) (m M : ℤ) (q : ℕ) (B : ByteArray) :
    go ci nxt s3 s4 kb code mask fN fS cut fg nt tp (fuel + 1) t r d m M q B =
      if code t r d = 0 then B
      else if code t r d = 1 then ByteArray.empty
      else if (fuel != fg || (q + 8192 * d) % nt == tp) = true then
        if (stepWM ci nxt (fun n e B'' =>
            go ci nxt s3 s4 kb code mask fN fS cut fg nt tp fuel t (r + 1) (d + n)
              (min m (fN t r d)) (max M (fN t r d)) e B'') kb (mask t (r + 1) d)
            (code t r d != 3 && cut t r d (min m (fN t r d)) (max M (fN t r d))) (s3 q) B).size = 0
        then
          stepWM ci nxt (fun n e B'' =>
            go ci nxt s3 s4 kb code mask fN fS cut fg nt tp fuel t (r + 1) (d + n)
              (min m (fN t r d)) (max M (fN t r d)) e B'') kb (mask t (r + 1) d)
            (code t r d != 3 && cut t r d (min m (fN t r d)) (max M (fN t r d))) (s3 q) B
        else
          stepWM ci nxt (fun n e B'' =>
            go ci nxt s3 s4 kb code mask fN fS cut fg nt tp fuel (t + 1) (r + 1) (d + n)
              (min m (fS t r d)) (max M (fS t r d)) e B'') kb (mask (t + 1) (r + 1) d)
            (code t r d != 2 && cut t r d (min m (fS t r d)) (max M (fS t r d))) (s4 q)
            (stepWM ci nxt (fun n e B'' =>
              go ci nxt s3 s4 kb code mask fN fS cut fg nt tp fuel t (r + 1) (d + n)
                (min m (fN t r d)) (max M (fN t r d)) e B'') kb (mask t (r + 1) d)
              (code t r d != 3 && cut t r d (min m (fN t r d)) (max M (fN t r d))) (s3 q) B)
      else B := by
  rw [go]
  simp only [stepWM, beq_iff_eq, bne_iff_ne, ne_eq, Bool.and_eq_true, ite_not]
  split_ifs <;> simp_all

theorem go_sub : ∀ (fuel t r d : ℕ) (m M : ℤ) (q : ℕ) (B : ByteArray),
    Sub (go ci nxt s3 s4 kb code mask fN fS cut fg nt tp fuel t r d m M q B) B := by
  intro fuel
  induction fuel with
  | zero =>
    intro t r d m M q B
    rw [go_zero]
    exact S.sub_of_size_zero ByteArray.size_empty B
  | succ fuel ih =>
    intro t r d m M q B
    rw [go_succ]
    have h1 := stepWM_sub ci nxt (fun n e B'' =>
      go ci nxt s3 s4 kb code mask fN fS cut fg nt tp fuel t (r + 1) (d + n)
        (min m (fN t r d)) (max M (fN t r d)) e B'')
      (fun n e B'' => ih _ _ _ _ _ _ _) kb (mask t (r + 1) d)
      (code t r d != 3 && cut t r d (min m (fN t r d)) (max M (fN t r d))) (s3 q) B
    have h2 := fun X => stepWM_sub ci nxt (fun n e B'' =>
      go ci nxt s3 s4 kb code mask fN fS cut fg nt tp fuel (t + 1) (r + 1) (d + n)
        (min m (fS t r d)) (max M (fS t r d)) e B'')
      (fun n e B'' => ih _ _ _ _ _ _ _) kb (mask (t + 1) (r + 1) d)
      (code t r d != 2 && cut t r d (min m (fS t r d)) (max M (fS t r d))) (s4 q) X
    split_ifs
    · exact Sub.refl B
    · exact S.sub_of_size_zero ByteArray.size_empty B
    · exact h1
    · exact (h2 _).trans h1
    · exact Sub.refl B

end Eqs

/-! ### The rule along a sequence -/

/-- The rule holds along the rows `rest` (see the head of this file). -/
def RuleK (k : ℕ) (code : ℕ → ℕ → ℕ → ℕ) (fN fS : ℕ → ℕ → ℕ → ℤ)
    (cut : ℕ → ℕ → ℕ → ℤ → ℤ → Bool) : ℕ → ℕ → ℕ → ℤ → ℤ → List TRow → Prop
  | t, r, d, _, _, [] => code t r d = 1
  | t, r, d, m, M, (kd, Q) :: rest =>
    kd ≤ 1 ∧ (code t r d = 4 ∨ code t r d = 2 + kd) ∧
      cut t r d (min m (fK fN fS kd t r d)) (max M (fK fN fS kd t r d)) = true ∧
      RuleK k code fN fS cut (t + kd) (r + 1) (d + (k - 1 - Q.length))
        (min m (fK fN fS kd t r d)) (max M (fK fN fS kd t r d)) rest

theorem ruleK_code_ne {k : ℕ} {code : ℕ → ℕ → ℕ → ℕ} {fN fS : ℕ → ℕ → ℕ → ℤ}
    {cut : ℕ → ℕ → ℕ → ℤ → ℤ → Bool} {t r d : ℕ} {m M : ℤ} :
    ∀ {rest : List TRow}, RuleK k code fN fS cut t r d m M rest → code t r d ≠ 0
  | [], h => by
    simp only [RuleK] at h
    omega
  | (kd, Q) :: rest, h => by
    simp only [RuleK] at h
    omega

/-- The same with the fuel and the gate of part `tp` of `nt`: nothing is asked once the fuel has
run out, except that the row that follows is visited. -/
def KAlong (k : ℕ) (enc : List ℕ → ℕ) (code : ℕ → ℕ → ℕ → ℕ) (fN fS : ℕ → ℕ → ℕ → ℤ)
    (cut : ℕ → ℕ → ℕ → ℤ → ℤ → Bool) (fg nt tp : ℕ) :
    ℕ → ℕ → ℕ → ℕ → ℤ → ℤ → List ℕ → List TRow → Prop
  | 0, _, _, _, _, _, _, _ => True
  | _ + 1, t, r, d, _, _, _, [] => code t r d = 1
  | _ + 1, _, _, _, _, _, _, (_, []) :: _ => False
  | f + 1, t, r, d, m, M, last, (kd, v :: R) :: rest =>
    kd ≤ 1 ∧ (code t r d = 4 ∨ code t r d = 2 + kd) ∧
      cut t r d (min m (fK fN fS kd t r d)) (max M (fK fN fS kd t r d)) = true ∧
      (f ≠ fg ∨ (enc last + 8192 * d) % nt = tp) ∧
      code (t + kd) (r + 1) (d + (k - 2 - R.length)) ≠ 0 ∧
      KAlong k enc code fN fS cut fg nt tp f (t + kd) (r + 1) (d + (k - 2 - R.length))
        (min m (fK fN fS kd t r d)) (max M (fK fN fS kd t r d))
        ((v :: R).getLast (List.cons_ne_nil v R)) rest

section Engine

variable {k : ℕ} {enc : List ℕ → ℕ} {ci nxt : ℕ → ℕ} {s3 s4 : ℕ → List ℕ} {jl : List ℕ}
  {st : ℕ} {code mask : ℕ → ℕ → ℕ → ℕ} {fN fS : ℕ → ℕ → ℕ → ℤ}
  {cut : ℕ → ℕ → ℕ → ℤ → ℤ → Bool} {fg nt tp : ℕ}

theorem kalong_of_rule (fg : ℕ) :
    ∀ (rest : List TRow) (fuel t r d : ℕ) (m M : ℤ) (last : List ℕ),
      (∀ x ∈ rest, x.2 ≠ []) → RuleK k code fN fS cut t r d m M rest →
      KAlong k enc code fN fS cut fg 1 0 fuel t r d m M last rest
  | _, 0, _, _, _, _, _, _, _, _ => by simp [KAlong]
  | [], _ + 1, _, _, _, _, _, _, _, h => by simpa [KAlong, RuleK] using h
  | (kd, []) :: _, _ + 1, _, _, _, _, _, _, hne, _ => absurd rfl (hne (kd, []) List.mem_cons_self)
  | (kd, v :: R) :: rest, f + 1, t, r, d, m, M, last, hne, h => by
    simp only [RuleK] at h
    have e : k - 1 - (v :: R).length = k - 2 - R.length := by
      simp only [List.length_cons]
      omega
    rw [e] at h
    have hrec := kalong_of_rule fg rest f _ _ _ _ _
      ((v :: R).getLast (List.cons_ne_nil v R)) (fun x hx => hne x (List.mem_cons_of_mem _ hx))
      h.2.2.2
    have hg : f ≠ fg ∨ (enc last + 8192 * d) % 1 = 0 := Or.inr (Nat.mod_one _)
    simp only [KAlong]
    exact ⟨h.1, h.2.1, h.2.2.1, hg, ruleK_code_ne h.2.2.2, hrec⟩

/-- Below the depth of the gate every part of the search is the whole search. -/
theorem kalong_gate_le (nt tp : ℕ) :
    ∀ (fuel : ℕ) (rest : List TRow) (t r d : ℕ) (m M : ℤ) (last : List ℕ), fuel ≤ fg →
      KAlong k enc code fN fS cut fg 1 0 fuel t r d m M last rest →
      KAlong k enc code fN fS cut fg nt tp fuel t r d m M last rest
  | 0, _, _, _, _, _, _, _, _, _ => by simp [KAlong]
  | _ + 1, [], _, _, _, _, _, _, _, h => by simpa [KAlong] using h
  | _ + 1, (_, []) :: _, _, _, _, _, _, _, _, h => by simp [KAlong] at h
  | f + 1, (kd, v :: R) :: rest, t, r, d, m, M, last, hf, h => by
    unfold KAlong at h ⊢
    exact ⟨h.1, h.2.1, h.2.2.1, Or.inl (by omega), h.2.2.2.2.1,
      kalong_gate_le nt tp f rest _ _ _ _ _ _ (by omega) h.2.2.2.2.2⟩

/-- A sequence along which the rule holds passes the gate of one of the `nt` parts. -/
theorem kalong_gate (hnt : 0 < nt) :
    ∀ (fuel : ℕ) (rest : List TRow) (t r d : ℕ) (m M : ℤ) (last : List ℕ),
      KAlong k enc code fN fS cut fg 1 0 fuel t r d m M last rest →
      ∃ tp, tp < nt ∧ KAlong k enc code fN fS cut fg nt tp fuel t r d m M last rest
  | 0, _, _, _, _, _, _, _, _ => ⟨0, hnt, by simp [KAlong]⟩
  | _ + 1, [], _, _, _, _, _, _, h => ⟨0, hnt, by simpa [KAlong] using h⟩
  | _ + 1, (_, []) :: _, _, _, _, _, _, _, h => by simp [KAlong] at h
  | f + 1, (kd, v :: R) :: rest, t, r, d, m, M, last, h => by
    unfold KAlong at h
    by_cases hf : f = fg
    · refine ⟨(enc last + 8192 * d) % nt, Nat.mod_lt _ hnt, ?_⟩
      have hrec := kalong_gate_le (enc := enc) (code := code) (fN := fN) (fS := fS) (cut := cut)
        (fg := fg) nt ((enc last + 8192 * d) % nt) f rest _ _ _ _ _ _ (by omega) h.2.2.2.2.2
      unfold KAlong
      exact ⟨h.1, h.2.1, h.2.2.1, Or.inr rfl, h.2.2.2.2.1, hrec⟩
    · obtain ⟨tp, htp, hA⟩ := kalong_gate hnt f rest _ _ _ _ _ _ h.2.2.2.2.2
      refine ⟨tp, htp, ?_⟩
      unfold KAlong
      exact ⟨h.1, h.2.1, h.2.2.1, Or.inl hf, h.2.2.2.2.1, hA⟩

/-- The search finds the end of a sequence of which it has reached a prefix, if the rule holds
along the rest of the sequence. -/
theorem go_complete (E : Enc k enc ci nxt s3 s4 jl st) (hk : 2 ≤ k)
    (hmask : ∀ t r d j, j < k - 1 → code t r (d + (k - 2 - j)) ≠ 0 →
      (mask t r d / 2 ^ j) % 2 = 1) :
    ∀ (fuel : ℕ) (rest : List TRow) (t r d : ℕ) (m M : ℤ) (B : ByteArray) (last : List ℕ)
      (used : List (List ℕ)),
      PermW k last → (∀ u ∈ used, PermW k u) → MInv enc ci B used → PCont k last used rest →
      KAlong k enc code fN fS cut fg nt tp fuel t r d m M last rest →
      (go ci nxt s3 s4 (k - 1) code mask fN fS cut fg nt tp fuel t r d m M (enc last) B).size
        = 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intros
    rw [go_zero]
    exact ByteArray.size_empty
  | succ fuel ih =>
    intro rest t r d m M B last used hlast hused hM hcont halong
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
            Sub (go ci nxt s3 s4 (k - 1) code mask fN fS cut fg nt tp fuel t' r' (d' + n) m' M'
              e B'') B'' :=
          fun t' r' d' m' M' n e B'' => go_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        have hbit : (mask (t + kd) (r + 1) d / 2 ^ R.length) % 2 = 1 :=
          hmask _ _ _ _ (by omega) hnext
        have hwalk : ∀ B', MInv enc ci B' used →
            (walkG ci nxt (fun n e B'' =>
              go ci nxt s3 s4 (k - 1) code mask fN fS cut fg nt tp fuel (t + kd) (r + 1) (d + n)
                (min m (fK fN fS kd t r d)) (max M (fK fN fS kd t r d)) e B'') (k - 1)
              (mask (t + kd) (r + 1) d) (enc v) B').size = 0 := by
          intro B' hB'
          have h := walkG_complete E
            (fun n e B'' =>
              go ci nxt s3 s4 (k - 1) code mask fN fS cut fg nt tp fuel (t + kd) (r + 1) (d + n)
                (min m (fK fN fS kd t r d)) (max M (fK fN fS kd t r d)) e B'')
            (hsubg _ _ _ _ _) R (k - 2) (mask (t + kd) (r + 1) d) v B' used hR hbit hperm hdoor
            hB' hused hnew hpw
            (by
              intro B'' hB''
              exact ih rest' _ _ _ _ _ B'' _ (used ++ v :: R) (hperm _ (List.getLast_mem _))
                hused' hB'' hcont' halong')
          rw [show k - 2 + 1 = k - 1 from by omega] at h
          exact h
        have hPsub : ∀ B' B : ByteArray, Sub B' B → MInv enc ci B used → MInv enc ci B' used :=
          fun B' B hs hB => hB.sub hs
        have h1 := stepWM_sub ci nxt (fun n e B'' =>
          go ci nxt s3 s4 (k - 1) code mask fN fS cut fg nt tp fuel t (r + 1) (d + n)
            (min m (fN t r d)) (max M (fN t r d)) e B'') (hsubg _ _ _ _ _) (k - 1)
          (mask t (r + 1) d)
          (code t r d != 3 && cut t r d (min m (fN t r d)) (max M (fN t r d))) (s3 (enc last)) B
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkd with rfl | rfl
        · have hwalk' : ∀ B', MInv enc ci B' used →
              (walkG ci nxt (fun n e B'' =>
                go ci nxt s3 s4 (k - 1) code mask fN fS cut fg nt tp fuel t (r + 1) (d + n)
                  (min m (fN t r d)) (max M (fN t r d)) e B'') (k - 1) (mask t (r + 1) d) (enc v)
                B').size = 0 := by
            simpa [fK] using hwalk
          have hcut' : cut t r d (min m (fN t r d)) (max M (fN t r d)) = true := by
            simpa [fK] using hcut
          have hcc : (code t r d != 3 && cut t r d (min m (fN t r d)) (max M (fN t r d)))
              = true := by
            rw [hcut', Bool.and_true]
            rcases hcode with h | h <;> simp [h]
          have hf := stepWM_found ci nxt (fun n e B'' =>
              go ci nxt s3 s4 (k - 1) code mask fN fS cut fg nt tp fuel t (r + 1) (d + n)
                (min m (fN t r d)) (max M (fN t r d)) e B'') (hsubg _ _ _ _ _) (k - 1)
            (mask t (r + 1) d) hcc
            (fun B' => MInv enc ci B' used) hPsub (enc v) hwalk'
            (E.s3_mem last v hlast hv (hlink.1 rfl)) hM
          rw [if_pos hf]
          exact hf
        · have hwalk' : ∀ B', MInv enc ci B' used →
              (walkG ci nxt (fun n e B'' =>
                go ci nxt s3 s4 (k - 1) code mask fN fS cut fg nt tp fuel (t + 1) (r + 1) (d + n)
                  (min m (fS t r d)) (max M (fS t r d)) e B'') (k - 1) (mask (t + 1) (r + 1) d)
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
          · exact stepWM_found ci nxt (fun n e B'' =>
                go ci nxt s3 s4 (k - 1) code mask fN fS cut fg nt tp fuel (t + 1) (r + 1) (d + n)
                  (min m (fS t r d)) (max M (fS t r d)) e B'') (hsubg _ _ _ _ _) (k - 1)
              (mask (t + 1) (r + 1) d) hcc
              (fun B' => MInv enc ci B' used) hPsub (enc v) hwalk'
              (E.s4_mem last v hlast hv (hlink.2 rfl)) (hM.sub h1)

/-- A part of the search finds a sequence along which the rule holds. -/
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
      ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _)) rest) :
    searchPart ci nxt s3 s4 st (k - 1) code mask fN fS cut sz fuel fg nt tp = true := by
  have h := PS.walk_complete E
    (fun n e B => go ci nxt s3 s4 (k - 1) code mask fN fS cut fg nt tp fuel 0 1 n 0 0 e B)
    (fun n e B => go_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) R1 (k - 2)
    (List.range' 1 k) (marks0 sz) [] hR1 hperm hdoor (PS.minv_marks0 enc ci sz) (by simp)
    (by simp) hpw
    (by
      intro B' hB'
      exact go_complete (code := code) (mask := mask) (fN := fN) (fS := fS) (cut := cut)
        (fg := fg) (nt := nt) (tp := tp) E hk hmask fuel rest 0 1 (k - 2 - R1.length) 0 0 B' _
        (List.range' 1 k :: R1) (hperm _ (List.getLast_mem _)) hperm (by simpa using hB') hcont
        halong)
  rw [show k - 2 + 1 = k - 1 from by omega, ← E.st_eq] at h
  unfold searchPart
  rw [h]
  rfl

/-- The parts evaluated as tasks are the parts. -/
theorem par_false {part : ℕ → Bool} {pa pb : ℕ} (h : par part pa pb = false) :
    ∀ tp, pa ≤ tp → tp < pb → part tp = false := by
  intro tp h1 h2
  unfold par at h
  rw [List.any_map, List.any_eq_false] at h
  have h3 := h (tp - pa) (List.mem_range.mpr (by omega))
  have e : pa + (tp - pa) = tp := by omega
  simpa [Task.spawn, e] using h3

end Engine

/-! ### The statement -/

/-- The rule holds along no sequence. -/
def KStmt (k : ℕ) (code : ℕ → ℕ → ℕ → ℕ) (fN fS : ℕ → ℕ → ℕ → ℤ)
    (cut : ℕ → ℕ → ℕ → ℤ → ℤ → Bool) : Prop :=
  ∀ (x : TRow) (rest : List TRow), IsSeq k (x :: rest) →
    ¬ RuleK k code fN fS cut 0 1 (k - 1 - x.2.length) 0 0 rest

theorem ruleK_relab {k : ℕ} {code : ℕ → ℕ → ℕ → ℕ} {fN fS : ℕ → ℕ → ℕ → ℤ}
    {cut : ℕ → ℕ → ℕ → ℤ → ℤ → Bool} (e : List ℕ) :
    ∀ (rest : List TRow) (t r d : ℕ) (m M : ℤ), RuleK k code fN fS cut t r d m M rest →
      RuleK k code fN fS cut t r d m M (relabSeq e rest)
  | [], _, _, _, _, _, h => h
  | (kd, Q) :: rest, t, r, d, m, M, h => by
    show RuleK k code fN fS cut t r d m M
      ((kd, Q.map (List.map (S.relab e))) :: relabSeq e rest)
    simp only [RuleK, List.length_map] at h ⊢
    exact ⟨h.1, h.2.1, h.2.2.1, ruleK_relab e rest _ _ _ _ _ h.2.2.2⟩

/-- **A search all of whose parts answer `false` proves the statement.** -/
theorem kstmt_of_parts {k : ℕ} {enc : List ℕ → ℕ} {ci nxt : ℕ → ℕ} {s3 s4 : ℕ → List ℕ}
    {jl : List ℕ} {st : ℕ} {code mask : ℕ → ℕ → ℕ → ℕ} {fN fS : ℕ → ℕ → ℕ → ℤ}
    {cut : ℕ → ℕ → ℕ → ℤ → ℤ → Bool} {sz fuel fg nt : ℕ}
    (E : Enc k enc ci nxt s3 s4 jl st) (hk : 3 ≤ k) (hnt : 0 < nt)
    (hmask : ∀ t r d j, j < k - 1 → code t r (d + (k - 2 - j)) ≠ 0 →
      (mask t r d / 2 ^ j) % 2 = 1)
    (hs : ∀ tp, tp < nt →
      searchPart ci nxt s3 s4 st (k - 1) code mask fN fS cut sz fuel fg nt tp = false) :
    KStmt k code fN fS cut := by
  intro x0 rest0 hL hrule
  obtain ⟨kd0, Q0⟩ := x0
  have hQ0 : Q0 ≠ [] := hL.pieces_ne (kd0, Q0) List.mem_cons_self
  obtain ⟨v0, R0, rfl⟩ := List.exists_cons_of_ne_nil hQ0
  have hv0 : PermW k v0 := hL.words _ List.mem_cons_self v0 List.mem_cons_self
  have hL' := hL.relabel hv0
  have hrule' := ruleK_relab v0 rest0 _ _ _ _ _ hrule
  have hshape : relabSeq v0 ((kd0, v0 :: R0) :: rest0) =
      (kd0, List.range' 1 k :: R0.map (List.map (S.relab v0))) :: relabSeq v0 rest0 := by
    simp [relabSeq, S.map_relab_self hv0.1, hv0.2.1]
  rw [hshape] at hL'
  have elen : k - 1 - (kd0, v0 :: R0).2.length
      = k - 2 - (R0.map (List.map (S.relab v0))).length := by
    simp only [List.length_cons, List.length_map]
    omega
  rw [elen] at hrule'
  generalize R0.map (List.map (S.relab v0)) = R1 at hL' hrule'
  generalize relabSeq v0 rest0 = rest1 at hL' hrule'
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
  obtain ⟨tp, htp, hP⟩ := kalong_gate (enc := enc) (fg := fg) hnt fuel rest1 _ _ _ _ _ _
    (kalong_of_rule (enc := enc) fg rest1 fuel _ _ _ _ _
      ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _)) hne1 hrule')
  have h := searchPart_true E (by omega) hmask sz fuel R1 rest1 hR1 hperm hdoor hcl'.1 hcont hP
  rw [hs tp htp] at h
  cases h

end KS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.KS.kstmt_of_parts
