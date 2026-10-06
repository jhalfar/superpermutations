/-
Completeness of the search of `KSearch.lean`, and the lemmas that cut it into parts.
New file (not in williamechols/superperm8-ge-46130).  The last theorem follows the proof of
`affine_bound_of_search_false` in that project's `AffineSound.lean`.  Apache-2.0, as the project.
-/
import Superperm8.KCode
import Superperm8.AffineEncoding

/-!
# The search on numbers is complete

`affine_bound_of_fsearch_false`: if `fsearch A Cc Bd fuel = false`, then every trail of marked
rows satisfies `A * rows ≤ Bd + Cc * charge`.

`ref_of_cover` cuts a search into parts: a search `a + b` rows deep below a state finds nothing
if a list `cover` of paths of length `a` contains every path that the search reaches
(`fsearchK (leafCover cover) a st [] = false`), and the search `b` rows deep finds nothing below
the end of each of these paths.
-/

namespace Superperm8
namespace K

/-! ### Bit sets -/

theorem bit_eq (S i : Nat) : bit S i = S.testBit i := by
  show Nat.beq ((S >>> i) &&& 1) 1 = S.testBit i
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : S / 2 ^ i % 2 = 1
  · rw [h]; simp
  · have h0 : S / 2 ^ i % 2 = 0 := by omega
    rw [h0]; simp; rfl

theorem bit_setBit (S i j : Nat) : bit (setBit S i) j = (bit S j || decide (i = j)) := by
  rw [bit_eq, bit_eq]
  show (S ||| 1 <<< i).testBit j = _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem bit_zero (i : Nat) : bit 0 i = false := by
  rw [bit_eq]; exact Nat.zero_testBit i

theorem bit_setBit_true {S i j : Nat} (h : bit (setBit S i) j = true) : bit S j = true ∨ i = j := by
  rw [bit_setBit, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (of_decide_eq_true h)

/-! ### Scores -/

/-- `A * rows - Cc * charge`. -/
def scoreZ (A Cc : Nat) (rows : List MarkedRow) : Int :=
  (A : Int) * (rows.length : Int) - (Cc : Int) * (chargeSum rows : Int)

theorem chargeSum_nil' : chargeSum [] = 0 := rfl

theorem chargeSum_cons' (x : MarkedRow) (xs : List MarkedRow) :
    chargeSum (x :: xs) = x.charge + chargeSum xs := by simp [chargeSum]

theorem chargeSum_append' (xs ys : List MarkedRow) :
    chargeSum (xs ++ ys) = chargeSum xs + chargeSum ys := by simp [chargeSum]

theorem scoreZ_nil (A Cc : Nat) : scoreZ A Cc [] = 0 := by simp [scoreZ, chargeSum_nil']

theorem scoreZ_cons (A Cc : Nat) (x : MarkedRow) (xs : List MarkedRow) :
    scoreZ A Cc (x :: xs) = ((A : Int) - (Cc : Int) * (x.charge : Int)) + scoreZ A Cc xs := by
  simp only [scoreZ, chargeSum_cons', List.length_cons]
  push_cast
  ring

theorem scoreZ_append (A Cc : Nat) (xs ys : List MarkedRow) :
    scoreZ A Cc (xs ++ ys) = scoreZ A Cc xs + scoreZ A Cc ys := by
  simp only [scoreZ, chargeSum_append', List.length_append]
  push_cast
  ring

theorem scoreZ_map_relabel (A Cc : Nat) (σ : Perm8) (rows : List MarkedRow) :
    scoreZ A Cc (rows.map (relabelMarkedRow σ)) = scoreZ A Cc rows := by
  simp [scoreZ, chargeSum_map_relabel]

/-- Every non-empty prefix of `xs` has positive score, counted from `s`. -/
def PosFrom (A Cc : Nat) (s : Nat) (xs : List MarkedRow) : Prop :=
  ∀ k : Nat, 0 < k → k ≤ xs.length → 0 < (s : Int) + scoreZ A Cc (xs.take k)

theorem posFrom_head {A Cc s : Nat} {x : MarkedRow} {xs : List MarkedRow}
    (h : PosFrom A Cc s (x :: xs)) : (Cc : Int) * (x.charge : Int) < (s : Int) + (A : Int) := by
  have h1 := h 1 (by omega) (by simp)
  rw [List.take_succ_cons, List.take_zero, scoreZ_cons, scoreZ_nil] at h1
  omega

theorem posFrom_tail {A Cc s s' : Nat} {x : MarkedRow} {xs : List MarkedRow}
    (h : PosFrom A Cc s (x :: xs))
    (hs' : (s' : Int) = (s : Int) + ((A : Int) - (Cc : Int) * (x.charge : Int))) :
    PosFrom A Cc s' xs := by
  intro k hk hlen
  have h1 := h (k + 1) (by omega) (by simp; omega)
  rw [List.take_succ_cons, scoreZ_cons] at h1
  omega

theorem posFrom_map_relabel {A Cc : Nat} (σ : Perm8) (rows : List MarkedRow)
    (h : PosFrom A Cc 0 rows) : PosFrom A Cc 0 (rows.map (relabelMarkedRow σ)) := by
  intro k hk hlen
  have h1 := h k hk (by simpa using hlen)
  rw [← List.map_take, scoreZ_map_relabel]
  exact h1

theorem modelTrail_drop' (rows : List MarkedRow) (h : ModelTrail rows) (n : Nat) :
    ModelTrail (rows.drop n) :=
  ⟨fun y hy => h.1 y (List.mem_of_mem_drop hy),
    h.2.1.suffix (List.drop_suffix n rows),
    h.2.2.sublist (List.drop_sublist n rows)⟩

/-! ### What the bit sets must avoid -/

/-- Position `v` of the row `x` is visible. -/
def Vis (x : MarkedRow) (v : Nat) : Prop := v < x.row.length ∧ ∀ j ∈ x.omitted, j.val ≠ v

/-- No row of `xs` uses a block of `B` or shows a class of `C`. -/
def FAvoid (B C : Nat) (xs : List MarkedRow) : Prop :=
  ∀ x ∈ xs, bit B (bidx (code x.row.start)) = false ∧
    ∀ v, Vis x v → bit C (cidx (code ((F^[v]) x.row.start))) = false

theorem favoid_zero (xs : List MarkedRow) : FAvoid 0 0 xs :=
  fun _ _ => ⟨bit_zero _, fun _ _ => bit_zero _⟩

theorem mem_visibleMask {x : MarkedRow} {v : Nat} (h : Vis x v) :
    rClass ((F^[v]) x.row.start) ∈ x.visibleMask :=
  Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1, h.2⟩, rfl⟩

theorem favoid_step {B C C' : Nat} {x : MarkedRow} {xs : List MarkedRow}
    (ha : FAvoid B C (x :: xs)) (hp : (x :: xs).Pairwise MarkedDisjoint)
    (hC' : ∀ j, bit C' j = true → bit C j = true ∨
      ∃ v, Vis x v ∧ cidx (code ((F^[v]) x.row.start)) = j) :
    FAvoid (setBit B (bidx (code x.row.start))) C' xs := by
  intro y hy
  obtain ⟨hb, hc⟩ := ha y (List.mem_cons_of_mem _ hy)
  have hxy : MarkedDisjoint x y := (List.pairwise_cons.mp hp).1 y hy
  constructor
  · rw [bit_setBit, hb, Bool.false_or]
    apply decide_eq_false
    intro he
    exact hxy.1 (fBlock_eq_of_bidx_eq he)
  · intro v hv
    rw [← Bool.not_eq_true]
    intro hbit
    rcases hC' _ hbit with h1 | ⟨w, hw, he⟩
    · rw [hc v hv] at h1
      cases h1
    · have hcl : rClass ((F^[w]) x.row.start) = rClass ((F^[v]) y.row.start) :=
        rClass_eq_of_cidx_eq he
      have h1 := mem_visibleMask hw
      rw [hcl] at h1
      exact (Finset.disjoint_left.mp hxy.2) h1 (mem_visibleMask hv)

/-! ### The rows at one start -/

/-- Number of omitted positions before position `i`. -/
def cnt (om : Finset (Fin 7)) (i : Nat) : Nat := (om.filter fun j => j.val < i).card

theorem cnt_zero (om : Finset (Fin 7)) : cnt om 0 = 0 := by simp [cnt]

theorem cnt_succ : ∀ (om : Finset (Fin 7)) (i : Fin 7),
    cnt om (i.val + 1) = cnt om i.val + (if i ∈ om then 1 else 0) := by
  decide +kernel

theorem cnt_le (om : Finset (Fin 7)) (i : Nat) : cnt om i ≤ om.card := Finset.card_filter_le _ _

theorem cnt_eq_card {om : Finset (Fin 7)} {L : Nat} (h : ∀ j ∈ om, j.val < L) :
    cnt om L = om.card := by
  unfold cnt
  rw [Finset.filter_true_of_mem h]

theorem rowAcc_unfold (mk : Nat → Nat → Nat → St) (kmax C0 n i k sc Cacc : Nat) (acc : List St) :
    rowAcc mk kmax C0 (n + 1) i k sc Cacc acc =
      bif bit C0 (cidx sc) then
        bif and (Nat.ble 1 i) (Nat.ble (k + 1) kmax) then
          rowAcc mk kmax C0 n (i + 1) (k + 1) (rotF sc) Cacc acc
        else acc
      else
        bif Nat.ble (6 - i + k) kmax then
          mk (6 - i + k) sc (setBit Cacc (cidx sc)) ::
            rowAcc mk kmax C0 n (i + 1) k (rotF sc) (setBit Cacc (cidx sc))
              (bif and (Nat.ble 1 i) (Nat.ble (k + 1) kmax) then
                rowAcc mk kmax C0 n (i + 1) (k + 1) (rotF sc) Cacc acc
              else acc)
        else
          rowAcc mk kmax C0 n (i + 1) k (rotF sc) (setBit Cacc (cidx sc))
            (bif and (Nat.ble 1 i) (Nat.ble (k + 1) kmax) then
              rowAcc mk kmax C0 n (i + 1) (k + 1) (rotF sc) Cacc acc
            else acc) := rfl

/-- `rowAcc` keeps what it was given. -/
theorem rowAcc_acc (mk : Nat → Nat → Nat → St) (kmax C0 : Nat) {c : St} :
    ∀ (n i k sc Cacc : Nat) (acc : List St), c ∈ acc → c ∈ rowAcc mk kmax C0 n i k sc Cacc acc := by
  intro n
  induction n with
  | zero => intro i k sc Cacc acc h; exact h
  | succ n ih =>
    intro i k sc Cacc acc h
    rw [rowAcc_unfold]
    have hom : c ∈ (bif and (Nat.ble 1 i) (Nat.ble (k + 1) kmax) then
        rowAcc mk kmax C0 n (i + 1) (k + 1) (rotF sc) Cacc acc else acc) := by
      cases and (Nat.ble 1 i) (Nat.ble (k + 1) kmax)
      · exact h
      · exact ih _ _ _ _ _ h
    cases bit C0 (cidx sc)
    · simp only [cond_false]
      cases Nat.ble (6 - i + k) kmax
      · simp only [cond_false]
        exact ih _ _ _ _ _ hom
      · simp only [cond_true]
        exact List.mem_cons_of_mem _ (ih _ _ _ _ _ hom)
    · simp only [cond_true]
      exact hom

/-- The row with start `q`, length code `L` and omitted set `om` is among the rows of `rowAcc`,
if its charge is at most `kmax` and its visible classes are free in `C0`. -/
theorem rowAcc_complete (mk : Nat → Nat → Nat → St) (kmax C0 : Nat) (q : Perm8) (L : Fin 7)
    (om : Finset (Fin 7))
    (hint : ∀ j ∈ om, 0 < j.val ∧ j.val < L.val)
    (hch : 6 - L.val + om.card ≤ kmax)
    (hfree : ∀ v, v ≤ L.val → (∀ t ∈ om, t.val ≠ v) → bit C0 (cidx (code ((F^[v]) q))) = false) :
    ∀ (n i Cacc : Nat) (acc : List St), n + i = 7 → i ≤ L.val →
      (∀ j, bit Cacc j = true → bit C0 j = true ∨
        ∃ v, v < i ∧ (∀ t ∈ om, t.val ≠ v) ∧ cidx (code ((F^[v]) q)) = j) →
      ∃ C', (∀ j, bit C' j = true → bit C0 j = true ∨
          ∃ v, v ≤ L.val ∧ (∀ t ∈ om, t.val ≠ v) ∧ cidx (code ((F^[v]) q)) = j) ∧
        mk (6 - L.val + om.card) (code ((F^[L.val]) q)) C' ∈
          rowAcc mk kmax C0 n i (cnt om i) (code ((F^[i]) q)) Cacc acc := by
  intro n
  induction n with
  | zero =>
    intro i Cacc acc hni hiL _
    have := L.isLt
    omega
  | succ n ih =>
    intro i Cacc acc hni hiL hinv
    have hL7 := L.isLt
    have hi7 : i < 7 := by omega
    have hrot : rotF (code ((F^[i]) q)) = code ((F^[i + 1]) q) := by
      rw [Function.iterate_succ_apply', code_F]
    have hcardk : om.card ≤ kmax := by omega
    rw [rowAcc_unfold, hrot]
    by_cases hmem : (⟨i, hi7⟩ : Fin 7) ∈ om
    · -- position `i` is omitted
      have hi := hint _ hmem
      simp only at hi
      have hcs : cnt om (i + 1) = cnt om i + 1 := by
        have := cnt_succ om ⟨i, hi7⟩
        simp only [hmem, if_true] at this
        exact this
      have hk : cnt om i + 1 ≤ kmax := by
        have := cnt_le om (i + 1)
        omega
      have hand : and (Nat.ble 1 i) (Nat.ble (cnt om i + 1) kmax) = true := by
        rw [Bool.and_eq_true]
        exact ⟨Nat.ble_eq_true_of_le hi.1, Nat.ble_eq_true_of_le hk⟩
      obtain ⟨C', hC', hin⟩ := ih (i + 1) Cacc acc (by omega) (by omega) (by
        intro j hj
        rcases hinv j hj with h1 | ⟨v, hv, hvis, he⟩
        · exact Or.inl h1
        · exact Or.inr ⟨v, by omega, hvis, he⟩)
      rw [hcs] at hin
      refine ⟨C', hC', ?_⟩
      rw [hand]
      simp only [cond_true]
      cases bit C0 (cidx (code ((F^[i]) q)))
      · simp only [cond_false]
        cases Nat.ble (6 - i + cnt om i) kmax
        · simp only [cond_false]
          exact rowAcc_acc mk kmax C0 _ _ _ _ _ _ hin
        · simp only [cond_true]
          exact List.mem_cons_of_mem _ (rowAcc_acc mk kmax C0 _ _ _ _ _ _ hin)
      · simp only [cond_true]
        exact hin
    · -- position `i` is visible
      have hvis : ∀ t ∈ om, t.val ≠ i := by
        intro t ht he
        apply hmem
        have : t = ⟨i, hi7⟩ := Fin.ext he
        rw [← this]; exact ht
      have hbit : bit C0 (cidx (code ((F^[i]) q))) = false := hfree i hiL hvis
      have hcs : cnt om (i + 1) = cnt om i := by
        have := cnt_succ om ⟨i, hi7⟩
        simp only [hmem, if_false] at this
        exact this
      have hinv' : ∀ j, bit (setBit Cacc (cidx (code ((F^[i]) q)))) j = true → bit C0 j = true ∨
          ∃ v, v < i + 1 ∧ (∀ t ∈ om, t.val ≠ v) ∧ cidx (code ((F^[v]) q)) = j := by
        intro j hj
        rcases bit_setBit_true hj with h1 | h1
        · rcases hinv j h1 with h2 | ⟨v, hv, hvv, he⟩
          · exact Or.inl h2
          · exact Or.inr ⟨v, by omega, hvv, he⟩
        · exact Or.inr ⟨i, by omega, hvis, h1⟩
      rw [hbit]
      simp only [cond_false]
      by_cases hlast : i = L.val
      · -- the row ends here
        have hck : cnt om i = om.card := by
          rw [hlast]; exact cnt_eq_card (fun j hj => (hint j hj).2)
        have hble : Nat.ble (6 - i + cnt om i) kmax = true := by
          apply Nat.ble_eq_true_of_le
          rw [hck, hlast]; exact hch
        refine ⟨setBit Cacc (cidx (code ((F^[i]) q))), ?_, ?_⟩
        · intro j hj
          rcases hinv' j hj with h1 | ⟨v, hv, hvv, he⟩
          · exact Or.inl h1
          · exact Or.inr ⟨v, by omega, hvv, he⟩
        · rw [hble]
          simp only [cond_true]
          rw [hck, hlast]
          exact List.mem_cons_self
      · -- the row goes on
        obtain ⟨C', hC', hin⟩ := ih (i + 1) (setBit Cacc (cidx (code ((F^[i]) q))))
          (bif and (Nat.ble 1 i) (Nat.ble (cnt om i + 1) kmax) then
            rowAcc mk kmax C0 n (i + 1) (cnt om i + 1) (code ((F^[i + 1]) q)) Cacc acc
          else acc) (by omega) (by omega) hinv'
        rw [hcs] at hin
        refine ⟨C', hC', ?_⟩
        cases Nat.ble (6 - i + cnt om i) kmax
        · simp only [cond_false]
          exact hin
        · simp only [cond_true]
          exact List.mem_cons_of_mem _ hin

/-! ### The children of a state -/

theorem childrenAt_acc (A Cc : Nat) (st : St) (qc : Nat) {c : St} {acc : List St} (h : c ∈ acc) :
    c ∈ childrenAt A Cc st qc acc := rowAcc_acc _ _ _ _ _ _ _ _ _ h

theorem charge_eq (x : MarkedRow) : x.charge = 6 - x.row.lengthCode.val + x.omitted.card := by
  have := x.row.lengthCode.isLt
  simp only [MarkedRow.charge, Row.length]
  omega

/-- The state after the row `x` is among the states that `childrenAt` lists for the start of `x`. -/
theorem childrenAt_complete (A Cc : Nat) (hCc : 0 < Cc) (st : St) (x : MarkedRow)
    (hx : x.OmissionsInterior)
    (hfree : ∀ v, Vis x v → bit st.C (cidx (code ((F^[v]) x.row.start))) = false)
    (hpos : Cc * x.charge < st.s + A) (acc : List St) :
    ∃ c ∈ childrenAt A Cc st (code x.row.start) acc,
      c.uc = code x.row.lastState ∧ c.B = setBit st.B (bidx (code x.row.start)) ∧
      c.s = st.s + A - Cc * x.charge ∧
      ∀ j, bit c.C j = true → bit st.C j = true ∨
        ∃ v, Vis x v ∧ cidx (code ((F^[v]) x.row.start)) = j := by
  have hint : ∀ j ∈ x.omitted, 0 < j.val ∧ j.val < x.row.lengthCode.val := by
    intro j hj
    have := hx j hj
    simp only [Row.length] at this
    omega
  have hch : 6 - x.row.lengthCode.val + x.omitted.card ≤ (st.s + A - 1) / Cc := by
    rw [Nat.le_div_iff_mul_le hCc, ← charge_eq, Nat.mul_comm]
    omega
  obtain ⟨C', hC', hin⟩ := rowAcc_complete
    (fun ch sc C' => (⟨sc, setBit st.B (bidx (code x.row.start)), C', st.s + A - Cc * ch⟩ : St))
    ((st.s + A - 1) / Cc) st.C x.row.start x.row.lengthCode x.omitted hint hch
    (fun v hv hvis => hfree v ⟨by simp only [Row.length]; omega, hvis⟩)
    7 0 st.C acc rfl (Nat.zero_le _) (fun j hj => Or.inl hj)
  rw [cnt_zero] at hin
  refine ⟨_, hin, rfl, rfl, ?_, ?_⟩
  · show st.s + A - Cc * (6 - x.row.lengthCode.val + x.omitted.card) = st.s + A - Cc * x.charge
    rw [charge_eq]
  · intro j hj
    rcases hC' j hj with h1 | ⟨v, hv, hvis, he⟩
    · exact Or.inl h1
    · exact Or.inr ⟨v, ⟨by simp only [Row.length]; omega, hvis⟩, he⟩

theorem mem_foldr_of {f : Nat → List St → List St} {c : St}
    (hmono : ∀ a acc, c ∈ acc → c ∈ f a acc) {a : Nat} (hc : ∀ acc, c ∈ f a acc) :
    ∀ (l : List Nat), a ∈ l → ∀ acc0, c ∈ l.foldr f acc0 := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons b t ih =>
    intro h acc0
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with h1 | h1
    · rw [← h1]; exact hc _
    · exact hmono _ _ (ih h1 acc0)

/-- The state after a row `x` that follows `last` is among the children. -/
theorem children_complete (A Cc : Nat) (hCc : 0 < Cc) (st : St) (last x : MarkedRow)
    (hcomp : MarkedCompatible last x) (huc : st.uc = code last.row.lastState)
    (hx : x.OmissionsInterior)
    (hB : bit st.B (bidx (code x.row.start)) = false)
    (hfree : ∀ v, Vis x v → bit st.C (cidx (code ((F^[v]) x.row.start))) = false)
    (hpos : Cc * x.charge < st.s + A) :
    ∃ c ∈ children A Cc st,
      c.uc = code x.row.lastState ∧ c.B = setBit st.B (bidx (code x.row.start)) ∧
      c.s = st.s + A - Cc * x.charge ∧
      ∀ j, bit c.C j = true → bit st.C j = true ∨
        ∃ v, Vis x v ∧ cidx (code ((F^[v]) x.row.start)) = j := by
  have hsix : code x.row.start ∈ sixCodes st.uc := by
    rw [huc]; exact code_mem_sixCodes hcomp
  -- for every accumulator
  have hall : ∀ acc, ∃ c ∈ childrenAt A Cc st (code x.row.start) acc,
      c.uc = code x.row.lastState ∧ c.B = setBit st.B (bidx (code x.row.start)) ∧
      c.s = st.s + A - Cc * x.charge ∧
      ∀ j, bit c.C j = true → bit st.C j = true ∨
        ∃ v, Vis x v ∧ cidx (code ((F^[v]) x.row.start)) = j :=
    fun acc => childrenAt_complete A Cc hCc st x hx hfree hpos acc
  -- induction over the six starts
  have key : ∀ (l : List Nat), code x.row.start ∈ l → ∀ acc0,
      ∃ c ∈ l.foldr (fun qc acc => bif bit st.B (bidx qc) then acc
          else childrenAt A Cc st qc acc) acc0,
        c.uc = code x.row.lastState ∧ c.B = setBit st.B (bidx (code x.row.start)) ∧
        c.s = st.s + A - Cc * x.charge ∧
        ∀ j, bit c.C j = true → bit st.C j = true ∨
          ∃ v, Vis x v ∧ cidx (code ((F^[v]) x.row.start)) = j := by
    intro l
    induction l with
    | nil => intro h; cases h
    | cons b t ih =>
      intro h acc0
      rw [List.foldr_cons]
      rcases List.mem_cons.mp h with h1 | h1
      · rw [← h1, hB]
        simp only [cond_false]
        exact hall _
      · obtain ⟨c, hc, hp⟩ := ih h1 acc0
        refine ⟨c, ?_, hp⟩
        cases bit st.B (bidx b)
        · simp only [cond_false]
          exact childrenAt_acc A Cc st b hc
        · simp only [cond_true]
          exact hc
  exact key _ hsix []

/-! ### The search finds every trail -/

theorem anyIdx_of_mem {f : St → Nat → Bool} {c : St} (hf : ∀ i, f c i = true) :
    ∀ (l : List St) (j : Nat), c ∈ l → anyIdx f l j = true := by
  intro l
  induction l with
  | nil => intro j h; cases h
  | cons b t ih =>
    intro j h
    show (f b j || anyIdx f t (j + 1)) = true
    rcases List.mem_cons.mp h with h1 | h1
    · rw [← h1, hf j]; rfl
    · rw [ih (j + 1) h1, Bool.or_true]

theorem fsearchK_succ (A Cc Bd : Nat) (leaf : St → List Nat → Bool) (fuel : Nat) (st : St)
    (key : List Nat) :
    fsearchK A Cc Bd leaf (fuel + 1) st key =
      bif Nat.blt Bd st.s then true
      else anyIdx (fun c i => fsearchK A Cc Bd leaf fuel c (i :: key)) (children A Cc st) 0 := rfl

/-- A trail that continues from the state `st` and ends above `Bd` is found. -/
theorem fsearchK_complete (A Cc Bd : Nat) (hCc : 0 < Cc) (fuel : Nat) :
    ∀ (xs : List MarkedRow) (last : MarkedRow) (st : St) (key : List Nat),
      ModelTrail xs → (∀ x, xs.head? = some x → MarkedCompatible last x) →
      st.uc = code last.row.lastState → FAvoid st.B st.C xs → PosFrom A Cc st.s xs →
      (Bd : Int) < (st.s : Int) + scoreZ A Cc xs →
      fsearchK A Cc Bd (fun _ _ => true) fuel st key = true := by
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro xs last st key hm hh huc ha hp hv
    rw [fsearchK_succ]
    by_cases hdone : Bd < st.s
    · have : Nat.blt Bd st.s = true := by simpa [Nat.blt_eq] using hdone
      rw [this]; rfl
    · have hnb : Nat.blt Bd st.s = false := by
        rw [← Bool.not_eq_true]; simpa [Nat.blt_eq] using hdone
      rw [hnb]
      simp only [cond_false]
      cases xs with
      | nil =>
        rw [scoreZ_nil] at hv
        omega
      | cons x rest =>
        have ht := posFrom_head hp
        have hpos : Cc * x.charge < st.s + A := by exact_mod_cast ht
        obtain ⟨hB, hfree⟩ := ha x List.mem_cons_self
        obtain ⟨c, hc, huc', hB', hs', hC'⟩ := children_complete A Cc hCc st last x
          (hh x rfl) huc (hm.1 x List.mem_cons_self) hB hfree hpos
        apply anyIdx_of_mem (c := c) _ _ _ hc
        intro i
        have hsz : (c.s : Int) = (st.s : Int) + ((A : Int) - (Cc : Int) * (x.charge : Int)) := by
          rw [hs']
          omega
        apply ih rest x c (i :: key) (modelTrail_tail hm)
        · intro y hy
          cases rest with
          | nil => simp at hy
          | cons z zs =>
            simp only [List.head?_cons, Option.some.injEq] at hy
            subst y
            exact (List.isChain_cons_cons.mp hm.2.1).1
        · exact huc'
        · rw [hB']
          exact favoid_step ha hm.2.2 hC'
        · exact posFrom_tail hp hsz
        · rw [scoreZ_cons] at hv
          omega

theorem code_one : code (1 : Perm8) = idc := by decide

/-- A trail that starts at the identity, has positive prefix scores and ends above `Bd` is
found. -/
theorem fsearch_complete (A Cc Bd : Nat) (hCc : 0 < Cc) (fuel : Nat) (rows : List MarkedRow)
    (hm : ModelTrail rows) (hp : PosFrom A Cc 0 rows) (hv : (Bd : Int) < scoreZ A Cc rows)
    (hs : ∀ x, rows.head? = some x → x.row.start = 1) : fsearch A Cc Bd fuel = true := by
  cases rows with
  | nil =>
    rw [scoreZ_nil] at hv
    omega
  | cons x rest =>
    have hx1 : x.row.start = 1 := hs x rfl
    have ht := posFrom_head hp
    have hpos : Cc * x.charge < 0 + A := by
      have : (Cc : Int) * (x.charge : Int) < (A : Int) := by simpa using ht
      have h2 : Cc * x.charge < A := by exact_mod_cast this
      omega
    obtain ⟨c, hc, huc', hB', hs', hC'⟩ := childrenAt_complete A Cc hCc ⟨0, 0, 0, 0⟩ x
      (hm.1 x List.mem_cons_self) (fun _ _ => bit_zero _) hpos []
    rw [hx1, code_one] at hc
    apply anyIdx_of_mem (c := c) _ _ _ hc
    intro i
    have hsz : (c.s : Int) = ((0 : Nat) : Int) + ((A : Int) - (Cc : Int) * (x.charge : Int)) := by
      rw [hs']
      simp only at hpos ⊢
      omega
    apply fsearchK_complete A Cc Bd hCc fuel rest x c [i] (modelTrail_tail hm)
    · intro y hy
      cases rest with
      | nil => simp at hy
      | cons z zs =>
        simp only [List.head?_cons, Option.some.injEq] at hy
        subst y
        exact (List.isChain_cons_cons.mp hm.2.1).1
    · exact huc'
    · rw [hB']
      exact favoid_step (favoid_zero _) hm.2.2 hC'
    · exact posFrom_tail hp hsz
    · rw [scoreZ_cons] at hv
      omega

/-- The search on numbers implies the bound for all trails: delete a non-positive prefix from a
shortest counterexample (as in `affine_bound_of_search_false` of `AffineSound.lean`). -/
theorem affine_bound_of_fsearch_false (A Cc Bd : Nat) (hCc : 0 < Cc) (fuel : Nat)
    (hf : fsearch A Cc Bd fuel = false) (rows : List MarkedRow) (hm : ModelTrail rows) :
    scoreZ A Cc rows ≤ (Bd : Int) := by
  suffices h : ∀ n : Nat, ∀ t : List MarkedRow, t.length = n → ModelTrail t →
      scoreZ A Cc t ≤ (Bd : Int) by
    exact h rows.length rows rfl hm
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t hlen hmodel
    by_contra hv
    have hv' : (Bd : Int) < scoreZ A Cc t := by omega
    have hp : PosFrom A Cc 0 t := by
      intro k hk hkn
      by_contra hn
      have hsuf := ih (t.drop k).length (by simp [← hlen]; omega)
        (t.drop k) rfl (modelTrail_drop' t hmodel k)
      have he : scoreZ A Cc t = scoreZ A Cc (t.take k) + scoreZ A Cc (t.drop k) := by
        rw [← scoreZ_append, List.take_append_drop]
      simp only [Int.natCast_zero, Int.zero_add] at hn
      omega
    cases t with
    | nil =>
      rw [scoreZ_nil] at hv'
      omega
    | cons x xs =>
      have htrue := fsearch_complete A Cc Bd hCc fuel ((x :: xs).map (relabelMarkedRow x.row.start.symm))
        (modelTrail_map_relabel _ _ hmodel) (posFrom_map_relabel _ _ hp)
        (by rw [scoreZ_map_relabel]; exact hv')
        (by
          intro y hy
          simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hy
          subst y
          exact relabelPerm_self_symm _)
      rw [hf] at htrue
      contradiction

/-- The same, in natural numbers. -/
theorem affine_bound_nat (A Cc Bd : Nat) (hCc : 0 < Cc) (fuel : Nat)
    (hf : fsearch A Cc Bd fuel = false) (rows : List MarkedRow) (hm : ModelTrail rows) :
    A * rows.length ≤ Bd + Cc * chargeSum rows := by
  have h := affine_bound_of_fsearch_false A Cc Bd hCc fuel hf rows hm
  unfold scoreZ at h
  have h2 : (A : Int) * (rows.length : Int) ≤ (Bd : Int) + (Cc : Int) * (chargeSum rows : Int) := by
    omega
  exact_mod_cast h2

/-! ### Cutting the search into parts -/

theorem beqKey_eq : ∀ (a b : List Nat), beqKey a b = true → a = b := by
  intro a
  induction a with
  | nil => intro b h; cases b with
    | nil => rfl
    | cons _ _ => cases h
  | cons x s ih => intro b h; cases b with
    | nil => cases h
    | cons y t =>
      have h' : (Nat.beq x y && beqKey s t) = true := h
      rw [Bool.and_eq_true] at h'
      rw [Nat.eq_of_beq_eq_true h'.1, ih t h'.2]

theorem memKey_mem : ∀ (cover : List (List Nat)) (key : List Nat), memKey key cover = true →
    key ∈ cover := by
  intro cover
  induction cover with
  | nil => intro key h; cases h
  | cons k t ih =>
    intro key h
    have h' : (beqKey key k || memKey key t) = true := h
    rcases Bool.or_eq_true_iff.mp h' with h1 | h1
    · rw [beqKey_eq _ _ h1]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih key h1)

theorem anyIdx_split {f1 f2 : St → Nat → Bool} (d : St) :
    ∀ (l : List St) (j : Nat), anyIdx f1 l j = true → anyIdx f2 l j = false →
      ∃ i, f1 (nthD l i d) (j + i) = true ∧ f2 (nthD l i d) (j + i) = false := by
  intro l
  induction l with
  | nil => intro j h; cases h
  | cons c t ih =>
    intro j h1 h2
    have h1' : (f1 c j || anyIdx f1 t (j + 1)) = true := h1
    have h2' : (f2 c j || anyIdx f2 t (j + 1)) = false := h2
    rw [Bool.or_eq_false_iff] at h2'
    rcases Bool.or_eq_true_iff.mp h1' with h | h
    · exact ⟨0, h, h2'.1⟩
    · obtain ⟨i, hi1, hi2⟩ := ih (j + 1) h h2'.2
      refine ⟨i + 1, ?_, ?_⟩
      · rw [show j + (i + 1) = j + 1 + i by omega]; exact hi1
      · rw [show j + (i + 1) = j + 1 + i by omega]; exact hi2

theorem anyIdx_congr {f1 f2 : St → Nat → Bool} (h : ∀ c i, f1 c i = f2 c i) :
    ∀ (l : List St) (j : Nat), anyIdx f1 l j = anyIdx f2 l j := by
  intro l
  induction l with
  | nil => intro j; rfl
  | cons c t ih =>
    intro j
    show (f1 c j || anyIdx f1 t (j + 1)) = (f2 c j || anyIdx f2 t (j + 1))
    rw [h, ih]

/-- Fuel adds up. -/
theorem fsearchK_add (A Cc Bd : Nat) (leaf : St → List Nat → Bool) (b : Nat) :
    ∀ (a : Nat) (st : St) (key : List Nat),
      fsearchK A Cc Bd leaf (a + b) st key =
        fsearchK A Cc Bd (fun st' key' => fsearchK A Cc Bd leaf b st' key') a st key := by
  intro a
  induction a with
  | zero => intro st key; rw [Nat.zero_add]; rfl
  | succ a ih =>
    intro st key
    rw [Nat.succ_add, fsearchK_succ, fsearchK_succ]
    congr 1
    exact anyIdx_congr (fun c i => ih c (i :: key)) _ _

/-- With the leaf that is always `true` the recorded path does not matter. -/
theorem fsearchK_key (A Cc Bd : Nat) : ∀ (fuel : Nat) (st : St) (key key' : List Nat),
    fsearchK A Cc Bd (fun _ _ => true) fuel st key =
      fsearchK A Cc Bd (fun _ _ => true) fuel st key' := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro st key key'
    rw [fsearchK_succ, fsearchK_succ]
    congr 1
    exact anyIdx_congr (fun c i => ih c _ _) _ _

/-- If one leaf makes the search succeed and another makes it fail, there is a path on whose
end the two leaves differ. -/
theorem fsearchK_split (A Cc Bd : Nat) (leaf1 leaf2 : St → List Nat → Bool) :
    ∀ (a : Nat) (st : St) (key : List Nat),
      fsearchK A Cc Bd leaf1 a st key = true → fsearchK A Cc Bd leaf2 a st key = false →
      ∃ path : List Nat, leaf1 (stepPath A Cc st path) (path.reverse ++ key) = true ∧
        leaf2 (stepPath A Cc st path) (path.reverse ++ key) = false := by
  intro a
  induction a with
  | zero =>
    intro st key h1 h2
    exact ⟨[], h1, h2⟩
  | succ a ih =>
    intro st key h1 h2
    rw [fsearchK_succ] at h1 h2
    cases hb : Nat.blt Bd st.s with
    | true =>
      rw [hb] at h2
      cases h2
    | false =>
      rw [hb] at h1 h2
      simp only [cond_false] at h1 h2
      obtain ⟨i, hi1, hi2⟩ := anyIdx_split st _ 0 h1 h2
      rw [Nat.zero_add] at hi1 hi2
      obtain ⟨path, hp1, hp2⟩ := ih _ _ hi1 hi2
      refine ⟨i :: path, ?_, ?_⟩
      · rw [List.reverse_cons, List.append_assoc]; exact hp1
      · rw [List.reverse_cons, List.append_assoc]; exact hp2

/-- Cutting a search: the paths of `cover` are all the paths of length `a` that the search
reaches, and nothing is found below their ends. -/
theorem ref_of_cover (A Cc Bd a b : Nat) (st : St) (cover : List (List Nat))
    (hc : fsearchK A Cc Bd (leafCover cover) a st [] = false)
    (hall : ∀ rp ∈ cover, Ref A Cc Bd b (stepPath A Cc st rp.reverse)) :
    Ref A Cc Bd (a + b) st := by
  unfold Ref
  rw [← Bool.not_eq_true]
  intro h
  rw [fsearchK_add] at h
  obtain ⟨path, hp1, hp2⟩ := fsearchK_split A Cc Bd _ _ a st [] h hc
  rw [List.append_nil] at hp1 hp2
  have hmem : path.reverse ∈ cover := by
    apply memKey_mem
    have : (!memKey path.reverse cover) = false := hp2
    simpa using this
  have := hall _ hmem
  rw [List.reverse_reverse] at this
  unfold Ref at this
  rw [fsearchK_key A Cc Bd b _ path.reverse []] at hp1
  rw [this] at hp1
  cases hp1

theorem forall_nil {P : List Nat → Prop} : ∀ rp ∈ ([] : List (List Nat)), P rp := by
  intro rp h; cases h

theorem forall_cons {P : List Nat → Prop} {a : List Nat} {l : List (List Nat)} (ha : P a)
    (hl : ∀ rp ∈ l, P rp) : ∀ rp ∈ a :: l, P rp := by
  intro rp h
  rcases List.mem_cons.mp h with h1 | h1
  · rw [h1]; exact ha
  · exact hl rp h1

theorem forall_append {P : List Nat → Prop} {l1 l2 : List (List Nat)} (h1 : ∀ rp ∈ l1, P rp)
    (h2 : ∀ rp ∈ l2, P rp) : ∀ rp ∈ l1 ++ l2, P rp := by
  intro rp h
  rcases List.mem_append.mp h with h | h
  · exact h1 rp h
  · exact h2 rp h

/-- A group of paths checked by one evaluation. -/
theorem refs_of_all (A Cc Bd b : Nat) (st : St) (g : List (List Nat))
    (h : g.all (fun rp =>
      !fsearchK A Cc Bd (fun _ _ => true) b (stepPath A Cc st rp.reverse) []) = true) :
    ∀ rp ∈ g, Ref A Cc Bd b (stepPath A Cc st rp.reverse) := by
  intro rp hrp
  have := List.all_eq_true.mp h rp hrp
  unfold Ref
  simpa using this

theorem fsearch_false (A Cc Bd fuel : Nat) (hlen : (rootChildren A Cc).length = 1)
    (h : Ref A Cc Bd fuel (rootSt A Cc)) : fsearch A Cc Bd fuel = false := by
  unfold fsearch rootSt at *
  generalize rootChildren A Cc = l at hlen h ⊢
  cases l with
  | nil => rfl
  | cons c t =>
    cases t with
    | nil =>
      show (fsearchK A Cc Bd (fun _ _ => true) fuel c [0] || false) = false
      rw [Bool.or_false, fsearchK_key A Cc Bd fuel c [0] []]
      exact h
    | cons _ _ => simp at hlen

end K
end Superperm8
