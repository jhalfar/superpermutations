import LowerBounds.J15Sound
import LowerBounds.J16Search

/-!
# The search of `J16Search.lean` is complete

The proof of `J15Sound.lean` with the hooks of the new engine.  `JAlong … i t r d a b m pm pM z
last usedC rest`: the rule of the engine holds along the rows `rest` that continue a prefix of
piece `i` (counters `t`, `r`, `d`, needed value `a`, weight `b`, record `m`, extremes `pm`, `pM`
of the potential over the cuts so far, first entry `z`, last entry `last`, blocks `usedC`).  It is
`J15.JAlong` with the two hooks: `xr c …` at every continuation by a link of kind `c`, `xc …`
where a piece is complete.

`not_along_of_parts`: if every part of the search answers `false`, the rule holds along no list
of rows that starts at the word `1 2 … k` and whose blocks obey the bound on shared classes.

The walks, the marks and the bound on shared classes are those of `J15Sound.lean`, used as they
are.
-/

namespace SuperpermLowerBounds
namespace J16

open S (PermW WLink DoorEq)
open PS (TRow Enc MInv all marks0)
open J15 (mkMask walkJ scanJ walkG vOf compOk k3Ok k4Ok live gateD earlyD digs gprod Id1 MC MB
  Bud seqB seqB_id seqB_found seqB_next all_id walkG_id step_found mkMask_bit toNat_ofNat8 mc_of_mb
  walkG_complete Gate Early RowOk FinOk blocksR blocksR_cons compOk_last compOk_jump shape_true
  Past gate_of_ne gate_of_past past_row past_jump GateL EarlyL gateL_true earlyL_true)

section Engine

variable {k : ℕ} {enc : List ℕ → ℕ} {ci nxt : ℕ → ℕ} {s3 s4 : ℕ → List ℕ} {jl : List ℕ} {st : ℕ}
variable {np bm : ℕ} {kd lo hi : ℕ → ℕ} {bestLe : ℕ → ℕ → ℤ → Bool}
  {gLe : ℕ → ℕ → ℕ → ℤ → Bool} {fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool} {gi gr nt tp : ℕ}
  {gate early : ℕ → ℕ → ℕ → Bool} {GP EP : ℕ → ℕ → ℕ → Prop}
  {xr : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℤ → Bool}
  {xc : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℤ → Bool} {phi : ℕ → ℕ → ℕ → ℕ → ℤ}

/-! ### The search below a prefix, in three steps -/

/-- The prefix may be the whole piece. -/
def compCond (s3 : ℕ → List ℕ) (kb np : ℕ) (kd lo hi : ℕ → ℕ) (bestLe : ℕ → ℕ → ℤ → Bool)
    (early : ℕ → ℕ → ℕ → Bool) (xc : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℤ → Bool)
    (i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ) (z q : ℕ) : Bool :=
  compOk np bestLe (fun i' r' => early i' r' (q + 8192 * d)) i r a (b - (d + kb * t)) (vOf kb t r d) &&
    (if kd i == 0 then
      decide (2 ≤ r) && decide (lo i ≤ d) && decide (d ≤ hi i) && (s3 q).contains z
    else decide (m < vOf kb t r d)) && xc i t r d a b pm pM

/-- The prefix as the whole piece. -/
def compPart (ci nxt : ℕ → ℕ) (s3 : ℕ → List ℕ) (jl : List ℕ) (kb np bm : ℕ)
    (kd lo hi : ℕ → ℕ) (bestLe : ℕ → ℕ → ℤ → Bool) (gLe : ℕ → ℕ → ℕ → ℤ → Bool)
    (fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool) (early : ℕ → ℕ → ℕ → Bool)
    (xc : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℤ → Bool)
    (rec : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℤ → ℤ → ℕ → ℕ → ℕ → ByteArray → ByteArray)
    (i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ) (z q du : ℕ) (M : ByteArray) : ByteArray :=
  if compCond s3 kb np kd lo hi bestLe early xc i t r d a b m pm pM z q then
    if i + 1 == np then ByteArray.empty
    else
      all (fun D M' => walkG ci nxt
        (fun n e du' M'' =>
          rec (i + 1) 0 1 n (a - vOf kb t r d) (b - (d + kb * t)) (-(kb : ℤ)) 0 0 D e du' M'')
        (UInt8.ofNat (i + 2)) bm kb
        (mkMask (fun n => decide (n ≤ b - (d + kb * t)) &&
          live kb np kd bestLe gLe fLe (fun _ _ => true) (i + 1) 0 1 n (a - vOf kb t r d)
            (b - (d + kb * t)) (-(kb : ℤ))) kb) du D M') jl M
  else M

/-- The prefix continued with links of weight 3. -/
def k3Part (ci nxt : ℕ → ℕ) (s3 : ℕ → List ℕ) (kb np bm : ℕ)
    (kd : ℕ → ℕ) (bestLe : ℕ → ℕ → ℤ → Bool) (gLe : ℕ → ℕ → ℕ → ℤ → Bool)
    (fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool) (xr : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℤ → Bool)
    (phi : ℕ → ℕ → ℕ → ℕ → ℤ)
    (rec : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℤ → ℤ → ℕ → ℕ → ℕ → ByteArray → ByteArray)
    (i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ) (z q du : ℕ) (M : ByteArray) : ByteArray :=
  if k3Ok gLe fLe i (kd i) t r d a b (b - (d + kb * t)) (vOf kb t r d) && xr 0 i t r d a b pm pM
  then
    all (fun D M' => walkG ci nxt
      (fun n e du' M'' => rec i t (r + 1) (d + n) a b (max m (vOf kb t r d))
        (min pm (phi 0 t r d)) (max pM (phi 0 t r d)) z e du' M'')
      (UInt8.ofNat (i + 1)) bm kb
      (mkMask (fun n => decide (d + kb * t + n ≤ b) &&
        live kb np kd bestLe gLe fLe (fun _ _ => true) i t (r + 1) (d + n) a b (max m (vOf kb t r d))) kb)
      du D M') (s3 q) M
  else M

/-- The prefix continued with links of weight 4. -/
def k4Part (ci nxt : ℕ → ℕ) (s4 : ℕ → List ℕ) (kb np bm : ℕ)
    (kd : ℕ → ℕ) (bestLe : ℕ → ℕ → ℤ → Bool) (gLe : ℕ → ℕ → ℕ → ℤ → Bool)
    (fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool) (xr : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℤ → Bool)
    (phi : ℕ → ℕ → ℕ → ℕ → ℤ)
    (rec : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℤ → ℤ → ℕ → ℕ → ℕ → ByteArray → ByteArray)
    (i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ) (z q du : ℕ) (M : ByteArray) : ByteArray :=
  if k4Ok gLe kb i (kd i) t a (b - (d + kb * t)) (vOf kb t r d) && xr 1 i t r d a b pm pM then
    all (fun D M' => walkG ci nxt
      (fun n e du' M'' => rec i (t + 1) (r + 1) (d + n) a b (max m (vOf kb t r d))
        (min pm (phi 1 t r d)) (max pM (phi 1 t r d)) z e du' M'')
      (UInt8.ofNat (i + 1)) bm kb
      (mkMask (fun n => decide (d + kb * t + kb + n ≤ b) &&
        live kb np kd bestLe gLe fLe (fun _ _ => true) i (t + 1) (r + 1) (d + n) a b
          (max m (vOf kb t r d))) kb)
      du D M') (s4 q) M
  else M

theorem go_zero (kb i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ) (z q du : ℕ) (M : ByteArray) :
    go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early xr xc phi 0 i t r d a b m pm pM
      z q du M = ByteArray.empty := rfl

theorem go_succ (kb fuel i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ) (z q du : ℕ) (M : ByteArray) :
    go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early xr xc phi (fuel + 1) i t r d a
        b m pm pM z q du M =
      if gate i r (q + 8192 * d) = true then
        seqB (compPart ci nxt s3 jl kb np bm kd lo hi bestLe gLe fLe early xc
            (go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early xr xc phi fuel)
            i t r d a b m pm pM z q du M)
          (fun M1 => seqB (k3Part ci nxt s3 kb np bm kd bestLe gLe fLe xr phi
              (go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early xr xc phi fuel)
              i t r d a b m pm pM z q du M1)
            (fun M2 => k4Part ci nxt s4 kb np bm kd bestLe gLe fLe xr phi
              (go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early xr xc phi fuel)
              i t r d a b m pm pM z q du M2))
      else M := rfl

section Ids

variable {kb : ℕ}
  {rec : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℤ → ℤ → ℕ → ℕ → ℕ → ByteArray → ByteArray}

theorem comp_id (hrec : ∀ i t r d a b m pm pM z q du M, Id1 (rec i t r d a b m pm pM z q du M) M)
    (i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ) (z q du : ℕ) (M : ByteArray) :
    Id1 (compPart ci nxt s3 jl kb np bm kd lo hi bestLe gLe fLe early xc rec i t r d a b m pm pM
      z q du M) M := by
  unfold compPart
  split_ifs
  · exact Or.inl ByteArray.size_empty
  · exact all_id _ (fun D M' => walkG_id _ (fun n e du' M'' => hrec _ _ _ _ _ _ _ _ _ _ _ _ _) _ _
      _ _ _ _ _) _ _
  · exact Or.inr rfl

theorem k3_id (hrec : ∀ i t r d a b m pm pM z q du M, Id1 (rec i t r d a b m pm pM z q du M) M)
    (i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ) (z q du : ℕ) (M : ByteArray) :
    Id1 (k3Part ci nxt s3 kb np bm kd bestLe gLe fLe xr phi rec i t r d a b m pm pM z q du M)
      M := by
  unfold k3Part
  split_ifs
  · exact all_id _ (fun D M' => walkG_id _ (fun n e du' M'' => hrec _ _ _ _ _ _ _ _ _ _ _ _ _) _ _
      _ _ _ _ _) _ _
  · exact Or.inr rfl

theorem k4_id (hrec : ∀ i t r d a b m pm pM z q du M, Id1 (rec i t r d a b m pm pM z q du M) M)
    (i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ) (z q du : ℕ) (M : ByteArray) :
    Id1 (k4Part ci nxt s4 kb np bm kd bestLe gLe fLe xr phi rec i t r d a b m pm pM z q du M)
      M := by
  unfold k4Part
  split_ifs
  · exact all_id _ (fun D M' => walkG_id _ (fun n e du' M'' => hrec _ _ _ _ _ _ _ _ _ _ _ _ _) _ _
      _ _ _ _ _) _ _
  · exact Or.inr rfl

end Ids

/-- The search gives "found" or the table back. -/
theorem go_id (kb : ℕ) : ∀ (fuel i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ) (z q du : ℕ)
    (M : ByteArray),
    Id1 (go ci nxt s3 s4 jl kb np bm kd lo hi bestLe gLe fLe gate early xr xc phi fuel i t r d a b
      m pm pM z q du M) M := by
  intro fuel
  induction fuel with
  | zero =>
    intro i t r d a b m pm pM z q du M
    rw [go_zero]
    exact Or.inl ByteArray.size_empty
  | succ fuel ih =>
    intro i t r d a b m pm pM z q du M
    rw [go_succ]
    split_ifs
    · exact seqB_id (comp_id ih _ _ _ _ _ _ _ _ _ _ _ _ _)
        (fun M1 => seqB_id (k3_id ih _ _ _ _ _ _ _ _ _ _ _ _ _)
          (fun M2 => k4_id ih _ _ _ _ _ _ _ _ _ _ _ _ _))
    · exact Or.inr rfl

/-! ### The rule along a list of rows -/

/-- The rule holds along the rows `rest` (see the head of the file). -/
def JAlong (k np : ℕ) (enc : List ℕ → ℕ) (kd lo hi : ℕ → ℕ) (bestLe : ℕ → ℕ → ℤ → Bool)
    (gLe : ℕ → ℕ → ℕ → ℤ → Bool) (fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool)
    (xr : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℤ → Bool)
    (xc : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℤ → Bool) (phi : ℕ → ℕ → ℕ → ℕ → ℤ)
    (GP EP : ℕ → ℕ → ℕ → Prop) :
    ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℤ → ℤ → List ℕ → List ℕ → List (List ℕ) → List TRow → Prop
  | i, t, r, d, a, b, m, pm, pM, z, last, _, [] =>
    GP i r (enc last + 8192 * d) ∧
      FinOk k kd lo hi i r d m (vOf (k - 1) t r d) z last ∧ i + 1 = np ∧ a ≤ vOf (k - 1) t r d ∧
      xc i t r d a b pm pM = true
  | _, _, _, _, _, _, _, _, _, _, _, _, (_, []) :: _ => False
  | i, t, r, d, a, b, m, pm, pM, z, last, usedC, (0, v :: R) :: rest =>
    GP i r (enc last + 8192 * d) ∧ RowOk k v R ∧
      k3Ok gLe fLe i (kd i) t r d a b (b - (d + (k - 1) * t)) (vOf (k - 1) t r d) = true ∧
      xr 0 i t r d a b pm pM = true ∧
      WLink k 3 last v ∧ (∀ u ∈ usedC, ∀ w ∈ v :: R, ¬ u ~r w) ∧
      d + (k - 1) * t + (k - 2 - R.length) ≤ b ∧
      JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi GP EP i t (r + 1) (d + (k - 2 - R.length))
        a b (max m (vOf (k - 1) t r d)) (min pm (phi 0 t r d)) (max pM (phi 0 t r d)) z
        ((v :: R).getLast (List.cons_ne_nil v R)) (usedC ++ v :: R) rest
  | i, t, r, d, a, b, m, pm, pM, z, last, usedC, (1, v :: R) :: rest =>
    GP i r (enc last + 8192 * d) ∧ RowOk k v R ∧
      k4Ok gLe (k - 1) i (kd i) t a (b - (d + (k - 1) * t)) (vOf (k - 1) t r d) = true ∧
      xr 1 i t r d a b pm pM = true ∧
      WLink k 4 last v ∧ (∀ u ∈ usedC, ∀ w ∈ v :: R, ¬ u ~r w) ∧
      d + (k - 1) * t + (k - 1) + (k - 2 - R.length) ≤ b ∧
      JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi GP EP i (t + 1) (r + 1)
        (d + (k - 2 - R.length)) a b (max m (vOf (k - 1) t r d)) (min pm (phi 1 t r d))
        (max pM (phi 1 t r d)) z ((v :: R).getLast (List.cons_ne_nil v R)) (usedC ++ v :: R) rest
  | i, t, r, d, a, b, m, pm, pM, z, last, _, (_ + 2, v :: R) :: rest =>
    GP i r (enc last + 8192 * d) ∧ RowOk k v R ∧
      FinOk k kd lo hi i r d m (vOf (k - 1) t r d) z last ∧ i + 1 ≠ np ∧
      bestLe i (b - (d + (k - 1) * t)) (a - vOf (k - 1) t r d) = true ∧
      xc i t r d a b pm pM = true ∧
      EP i r (enc last + 8192 * d) ∧ k - 2 - R.length ≤ b - (d + (k - 1) * t) ∧
      JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi GP EP (i + 1) 0 1 (k - 2 - R.length)
        (a - vOf (k - 1) t r d) (b - (d + (k - 1) * t)) (-((k - 1 : ℕ) : ℤ)) 0 0 v
        ((v :: R).getLast (List.cons_ne_nil v R)) (v :: R) rest

section Parts

variable {rec : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ → ℤ → ℤ → ℤ → ℕ → ℕ → ℕ → ByteArray → ByteArray}

/-- The last piece is complete and has the needed value: found. -/
theorem comp_last (E : Enc k enc ci nxt s3 s4 jl st) {i t r d : ℕ} {a : ℤ} {b : ℕ} {m pm pM : ℤ}
    {z last : List ℕ} (du : ℕ) (M : ByteArray)
    (hfin : FinOk k kd lo hi i r d m (vOf (k - 1) t r d) z last) (hlast : PermW k last)
    (hz : PermW k z) (hl : i + 1 = np) (hav : a ≤ vOf (k - 1) t r d)
    (hxc : xc i t r d a b pm pM = true) :
    (compPart ci nxt s3 jl (k - 1) np bm kd lo hi bestLe gLe fLe early xc rec i t r d a b m pm pM
      (enc z) (enc last) du M).size = 0 := by
  have h1 := compOk_last (bestLe := bestLe)
    (ea := (fun i' r' => early i' r' (enc last + 8192 * d))) (r := r)
    (y := b - (d + (k - 1) * t)) hl hav
  have h2 := shape_true (kd := kd) (lo := lo) (hi := hi) E hfin hlast hz
  have hl' : (i + 1 == np) = true := by simpa using hl
  unfold compPart compCond
  rw [h1, h2, hxc, if_pos (show (true && true && true) = true from rfl), if_pos hl']
  exact ByteArray.size_empty

/-- A piece that is not the last is complete: the next piece starts at every word. -/
theorem comp_jump (E : Enc k enc ci nxt s3 s4 jl st) {i t r d : ℕ} {a : ℤ} {b : ℕ} {m pm pM : ℤ}
    {z last : List ℕ} (du : ℕ) (M : ByteArray)
    (hfin : FinOk k kd lo hi i r d m (vOf (k - 1) t r d) z last) (hlast : PermW k last)
    (hz : PermW k z) (hl : i + 1 ≠ np)
    (hb : bestLe i (b - (d + (k - 1) * t)) (a - vOf (k - 1) t r d) = true)
    (hg : early i r (enc last + 8192 * d) = true) (hxc : xc i t r d a b pm pM = true) :
    compPart ci nxt s3 jl (k - 1) np bm kd lo hi bestLe gLe fLe early xc rec i t r d a b m pm pM
        (enc z) (enc last) du M =
      all (fun D M' => walkG ci nxt
        (fun n e du' M'' =>
          rec (i + 1) 0 1 n (a - vOf (k - 1) t r d) (b - (d + (k - 1) * t)) (-((k - 1 : ℕ) : ℤ))
            0 0 D e du' M'')
        (UInt8.ofNat (i + 2)) bm (k - 1)
        (mkMask (fun n => decide (n ≤ b - (d + (k - 1) * t)) &&
          live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) (i + 1) 0 1 n (a - vOf (k - 1) t r d)
            (b - (d + (k - 1) * t)) (-((k - 1 : ℕ) : ℤ))) (k - 1)) du D M') jl M := by
  have h1 := compOk_jump (np := np) (bestLe := bestLe)
    (ea := (fun i' r' => early i' r' (enc last + 8192 * d))) hl hb hg
  have h2 := shape_true (kd := kd) (lo := lo) (hi := hi) E hfin hlast hz
  have hl' : ¬ (i + 1 == np) = true := by simpa using hl
  unfold compPart compCond
  rw [h1, h2, hxc, if_pos (show (true && true && true) = true from rfl), if_neg hl']

theorem k3_pos {i t r d : ℕ} {a : ℤ} {b : ℕ} {m pm pM : ℤ} (z q du : ℕ) (M : ByteArray) (kb : ℕ)
    (h : k3Ok gLe fLe i (kd i) t r d a b (b - (d + kb * t)) (vOf kb t r d) = true)
    (hx : xr 0 i t r d a b pm pM = true) :
    k3Part ci nxt s3 kb np bm kd bestLe gLe fLe xr phi rec i t r d a b m pm pM z q du M =
      all (fun D M' => walkG ci nxt
        (fun n e du' M'' => rec i t (r + 1) (d + n) a b (max m (vOf kb t r d))
          (min pm (phi 0 t r d)) (max pM (phi 0 t r d)) z e du' M'')
        (UInt8.ofNat (i + 1)) bm kb
        (mkMask (fun n => decide (d + kb * t + n ≤ b) &&
          live kb np kd bestLe gLe fLe (fun _ _ => true) i t (r + 1) (d + n) a b (max m (vOf kb t r d)))
          kb)
        du D M') (s3 q) M := by
  unfold k3Part
  rw [h, hx, if_pos (show (true && true) = true from rfl)]

theorem k4_pos {i t r d : ℕ} {a : ℤ} {b : ℕ} {m pm pM : ℤ} (z q du : ℕ) (M : ByteArray) (kb : ℕ)
    (h : k4Ok gLe kb i (kd i) t a (b - (d + kb * t)) (vOf kb t r d) = true)
    (hx : xr 1 i t r d a b pm pM = true) :
    k4Part ci nxt s4 kb np bm kd bestLe gLe fLe xr phi rec i t r d a b m pm pM z q du M =
      all (fun D M' => walkG ci nxt
        (fun n e du' M'' => rec i (t + 1) (r + 1) (d + n) a b (max m (vOf kb t r d))
          (min pm (phi 1 t r d)) (max pM (phi 1 t r d)) z e du' M'')
        (UInt8.ofNat (i + 1)) bm kb
        (mkMask (fun n => decide (d + kb * t + kb + n ≤ b) &&
          live kb np kd bestLe gLe fLe (fun _ _ => true) i (t + 1) (r + 1) (d + n) a b
            (max m (vOf kb t r d))) kb)
        du D M') (s4 q) M := by
  unfold k4Part
  rw [h, hx, if_pos (show (true && true) = true from rfl)]

end Parts

/-- Along the rule, something is done at the prefix. -/
theorem live_of_fin {i t r d : ℕ} {a : ℤ} {b : ℕ} {m : ℤ} {z last : List ℕ}
    (hfin : FinOk k kd lo hi i r d m (vOf (k - 1) t r d) z last)
    (h1 : compOk np bestLe (fun _ _ => true) i r a (b - (d + (k - 1) * t)) (vOf (k - 1) t r d)
      = true) :
    live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) i t r d a b m = true := by
  have h0 : (if (kd i == 0) = true then decide (2 ≤ r) else decide (m < vOf (k - 1) t r d))
      = true := by
    unfold FinOk at hfin
    by_cases hc : kd i = 0
    · rw [if_pos hc] at hfin
      simp [hc, hfin.1]
    · rw [if_neg hc] at hfin
      simp [hc, hfin]
  unfold live
  rw [h0, h1]
  simp only [Bool.and_self, Bool.or_true]

theorem live_of_along : ∀ (rest : List TRow) (i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ)
    (z last : List ℕ) (usedC : List (List ℕ)),
    JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi GP EP i t r d a b m pm pM z last usedC rest →
    live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) i t r d a b m = true
  | [], i, t, r, d, a, b, m, pm, pM, z, last, usedC, h => by
    simp only [JAlong] at h
    obtain ⟨_, hfin, hnp, hav, _⟩ := h
    exact live_of_fin hfin (compOk_last hnp hav)
  | (_, []) :: _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [JAlong] at h
  | (0, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, h => by
    simp only [JAlong] at h
    unfold live
    rw [h.2.2.1]
    rfl
  | (1, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, h => by
    simp only [JAlong] at h
    unfold live
    rw [h.2.2.1]
    simp only [Bool.or_true, Bool.true_or]
  | (kdr + 2, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, h => by
    simp only [JAlong] at h
    obtain ⟨_, _, hfin, hnp, hb, _, _, _, _⟩ := h
    exact live_of_fin hfin (compOk_jump hnp hb rfl)

/-- Along the rule the number of the piece is below the number of pieces. -/
theorem lt_of_along : ∀ (rest : List TRow) (i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ)
    (z last : List ℕ) (usedC : List (List ℕ)),
    JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi GP EP i t r d a b m pm pM z last usedC rest →
    i < np
  | [], i, t, r, d, a, b, m, pm, pM, z, last, usedC, h => by
    simp only [JAlong] at h
    omega
  | (_, []) :: _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [JAlong] at h
  | (0, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, h => by
    simp only [JAlong] at h
    exact lt_of_along rest _ _ _ _ _ _ _ _ _ _ _ _ h.2.2.2.2.2.2.2
  | (1, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, h => by
    simp only [JAlong] at h
    exact lt_of_along rest _ _ _ _ _ _ _ _ _ _ _ _ h.2.2.2.2.2.2.2
  | (kdr + 2, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, h => by
    simp only [JAlong] at h
    have := lt_of_along rest _ _ _ _ _ _ _ _ _ _ _ _ h.2.2.2.2.2.2.2.2
    omega

/-- The search finds the end of a list of rows of which it has reached a prefix, if the rule
holds along the rest. -/
theorem go_complete (E : Enc k enc ci nxt s3 s4 jl st) (hk : 2 ≤ k) (hnp : np ≤ 255)
    (hG : ∀ i r key, GP i r key → gate i r key = true)
    (hE : ∀ i r key, EP i r key → early i r key = true) :
    ∀ (rest : List TRow) (fuel i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ) (z last : List ℕ)
      (usedC usedA : List (List ℕ)) (du : ℕ) (M : ByteArray),
      PermW k last → PermW k z → (∀ u ∈ usedA, PermW k u) → (∀ u ∈ usedC, PermW k u) →
      MInv enc ci M usedA → MC enc ci M (UInt8.ofNat (i + 1)) usedC → MB M (i + 1) →
      Bud bm du usedA (blocksR rest) →
      JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi GP EP i t r d a b m pm pM z last usedC
        rest →
      (go ci nxt s3 s4 jl (k - 1) np bm kd lo hi bestLe gLe fLe gate early xr xc phi fuel i t r d
        a b m pm pM (enc z) (enc last) du M).size = 0 := by
  intro rest
  induction rest with
  | nil =>
    intro fuel i t r d a b m pm pM z last usedC usedA du M hlast hz _ _ _ _ _ _ halong
    cases fuel with
    | zero => rw [go_zero]; exact ByteArray.size_empty
    | succ fuel =>
      simp only [JAlong] at halong
      obtain ⟨hgate, hfin, hlastp, hav, hxc⟩ := halong
      rw [go_succ, if_pos (hG _ _ _ hgate)]
      apply seqB_found
      exact comp_last E du M hfin hlast hz hlastp hav hxc
  | cons x rest' ih =>
    intro fuel i t r d a b m pm pM z last usedC usedA du M hlast hz husedA husedC hM hC hB hbud
      halong
    cases fuel with
    | zero => rw [go_zero]; exact ByteArray.size_empty
    | succ fuel =>
      obtain ⟨kdr, Q⟩ := x
      cases Q with
      | nil => simp [JAlong] at halong
      | cons v R =>
        have hilt := lt_of_along _ _ _ _ _ _ _ _ _ _ _ _ _ halong
        have hgoid := go_id (ci := ci) (nxt := nxt) (s3 := s3) (s4 := s4) (jl := jl) (np := np)
          (bm := bm) (kd := kd) (lo := lo) (hi := hi) (bestLe := bestLe) (gLe := gLe)
          (fLe := fLe) (gate := gate) (early := early) (xr := xr) (xc := xc) (phi := phi)
          (k - 1) fuel
        rw [blocksR_cons] at hbud
        have hlastmem : (v :: R).getLast (List.cons_ne_nil v R) ∈ v :: R := List.getLast_mem _
        have e : k - 1 - 1 - R.length = k - 2 - R.length := by omega
        match kdr, halong with
        | 0, halong =>
          simp only [JAlong] at halong
          obtain ⟨hgate, ⟨hR, hperm, hdoor, hpw⟩, hk3, hx3, hlink, hnew, hwt, halong'⟩ := halong
          have hv := hperm v List.mem_cons_self
          have hlive := live_of_along _ _ _ _ _ _ _ _ _ _ _ _ _ halong'
          rw [go_succ, if_pos (hG _ _ _ hgate)]
          refine seqB_next (comp_id hgoid _ _ _ _ _ _ _ _ _ _ _ _ _) (seqB_found _ ?_)
          have hbit := mkMask_bit (fun n => decide (d + (k - 1) * t + n ≤ b) &&
            live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) i t (r + 1) (d + n) a b
              (max m (vOf (k - 1) t r d))) (k - 1) R.length (by omega) (by
              rw [e, Bool.and_eq_true]
              exact ⟨decide_eq_true hwt, hlive⟩)
          rw [k3_pos _ _ _ _ _ hk3 hx3]
          exact step_found E hk
            (fun _ n e du' M'' =>
              go ci nxt s3 s4 jl (k - 1) np bm kd lo hi bestLe gLe fLe gate early xr xc phi fuel
                i t (r + 1) (d + n) a b (max m (vOf (k - 1) t r d)) (min pm (phi 0 t r d))
                (max pM (phi 0 t r d)) (enc z) e du' M'')
            (fun _ n e du' M'' => hgoid _ _ _ _ _ _ _ _ _ _ _ _ _) (UInt8.ofNat (i + 1)) (i + 1)
            (le_of_eq (toNat_ofNat8 (by omega))) bm _ du _ M v R usedA usedC (blocksR rest')
            (E.s3_mem last v hlast hv hlink) hR
            hbit
            hperm hdoor hM hC hB husedA husedC hnew hpw hbud
            (fun M' du' hM' hC' hB' hbud' =>
              ih fuel _ _ _ _ _ _ _ _ _ z _ (usedC ++ v :: R) (usedA ++ v :: R) du' M'
                (hperm _ hlastmem) hz
                (fun u hu => (List.mem_append.mp hu).elim (husedA u) (hperm u))
                (fun u hu => (List.mem_append.mp hu).elim (husedC u) (hperm u))
                hM' hC' hB' hbud' halong')
        | 1, halong =>
          simp only [JAlong] at halong
          obtain ⟨hgate, ⟨hR, hperm, hdoor, hpw⟩, hk4, hx4, hlink, hnew, hwt, halong'⟩ := halong
          have hv := hperm v List.mem_cons_self
          have hlive := live_of_along _ _ _ _ _ _ _ _ _ _ _ _ _ halong'
          rw [go_succ, if_pos (hG _ _ _ hgate)]
          refine seqB_next (comp_id hgoid _ _ _ _ _ _ _ _ _ _ _ _ _)
            (seqB_next (k3_id hgoid _ _ _ _ _ _ _ _ _ _ _ _ _) ?_)
          have hbit := mkMask_bit (fun n => decide (d + (k - 1) * t + (k - 1) + n ≤ b) &&
            live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) i (t + 1) (r + 1) (d + n) a b
              (max m (vOf (k - 1) t r d))) (k - 1) R.length (by omega) (by
              rw [e, Bool.and_eq_true]
              exact ⟨decide_eq_true hwt, hlive⟩)
          rw [k4_pos _ _ _ _ _ hk4 hx4]
          exact step_found E hk
            (fun _ n e du' M'' =>
              go ci nxt s3 s4 jl (k - 1) np bm kd lo hi bestLe gLe fLe gate early xr xc phi fuel
                i (t + 1) (r + 1) (d + n) a b (max m (vOf (k - 1) t r d)) (min pm (phi 1 t r d))
                (max pM (phi 1 t r d)) (enc z) e du' M'')
            (fun _ n e du' M'' => hgoid _ _ _ _ _ _ _ _ _ _ _ _ _) (UInt8.ofNat (i + 1)) (i + 1)
            (le_of_eq (toNat_ofNat8 (by omega))) bm _ du _ M v R usedA usedC (blocksR rest')
            (E.s4_mem last v hlast hv hlink) hR
            hbit
            hperm hdoor hM hC hB husedA husedC hnew hpw hbud
            (fun M' du' hM' hC' hB' hbud' =>
              ih fuel _ _ _ _ _ _ _ _ _ z _ (usedC ++ v :: R) (usedA ++ v :: R) du' M'
                (hperm _ hlastmem) hz
                (fun u hu => (List.mem_append.mp hu).elim (husedA u) (hperm u))
                (fun u hu => (List.mem_append.mp hu).elim (husedC u) (hperm u))
                hM' hC' hB' hbud' halong')
        | kdr + 2, halong =>
          simp only [JAlong] at halong
          obtain ⟨hgate, ⟨hR, hperm, hdoor, hpw⟩, hfin, hnpne, hbest, hxc, hg2, hwt, halong'⟩ :=
            halong
          have hv := hperm v List.mem_cons_self
          have hilt' := lt_of_along _ _ _ _ _ _ _ _ _ _ _ _ _ halong'
          have hlive := live_of_along _ _ _ _ _ _ _ _ _ _ _ _ _ halong'
          rw [go_succ, if_pos (hG _ _ _ hgate)]
          apply seqB_found
          have hbit := mkMask_bit (fun n => decide (n ≤ b - (d + (k - 1) * t)) &&
            live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) (i + 1) 0 1 n (a - vOf (k - 1) t r d)
              (b - (d + (k - 1) * t)) (-((k - 1 : ℕ) : ℤ))) (k - 1) R.length (by omega) (by
              rw [e, Bool.and_eq_true]
              exact ⟨decide_eq_true hwt, hlive⟩)
          rw [comp_jump E du M hfin hlast hz hnpne hbest (hE _ _ _ hg2) hxc]
          exact step_found E hk
            (fun D n e du' M'' =>
              go ci nxt s3 s4 jl (k - 1) np bm kd lo hi bestLe gLe fLe gate early xr xc phi fuel
                (i + 1) 0 1 n (a - vOf (k - 1) t r d) (b - (d + (k - 1) * t))
                (-((k - 1 : ℕ) : ℤ)) 0 0 D e du' M'')
            (fun _ n e du' M'' => hgoid _ _ _ _ _ _ _ _ _ _ _ _ _) (UInt8.ofNat (i + 2)) (i + 2)
            (le_of_eq (toNat_ofNat8 (by omega))) bm _ du _ M v R usedA [] (blocksR rest')
            (E.jl_mem v hv) hR
            hbit
            hperm hdoor hM (mc_of_mb hB (by omega)) (fun j => le_trans (hB j) (by omega)) husedA
            (by simp) (by simp) hpw hbud
            (fun M' du' hM' hC' hB' hbud' =>
              ih fuel _ _ _ _ _ _ _ _ _ v _ (v :: R) (usedA ++ v :: R) du' M'
                (hperm _ hlastmem) hv
                (fun u hu => (List.mem_append.mp hu).elim (husedA u) (hperm u))
                hperm hM' hC' hB' hbud' halong')

/-! ### The parts and the gate -/

/-- Beyond the gate every part of the search is the whole search. -/
theorem along_past (nt tp : ℕ) : ∀ (rest : List TRow) (i t r d : ℕ) (a : ℤ) (b : ℕ)
    (m pm pM : ℤ) (z last : List ℕ) (usedC : List (List ℕ)), Past gi gr i r →
    JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi (Gate gi gr 1 0)
      (Early gi gr 1 0) i t r d a b m pm pM z last usedC rest →
    JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi (Gate gi gr nt tp)
      (Early gi gr nt tp) i t r d a b m pm pM z last usedC rest
  | [], i, t, r, d, a, b, m, pm, pM, z, last, usedC, hp, h => by
    simp only [JAlong] at h ⊢
    exact ⟨gate_of_past hp _ _ _, h.2⟩
  | (_, []) :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [JAlong] at h
  | (0, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, hp, h => by
    simp only [JAlong] at h ⊢
    obtain ⟨_, h2, h3, h3', h4, h5, h6, h7⟩ := h
    exact ⟨gate_of_past hp _ _ _, h2, h3, h3', h4, h5, h6,
      along_past nt tp rest _ _ _ _ _ _ _ _ _ _ _ _ (past_row hp) h7⟩
  | (1, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, hp, h => by
    simp only [JAlong] at h ⊢
    obtain ⟨_, h2, h3, h3', h4, h5, h6, h7⟩ := h
    exact ⟨gate_of_past hp _ _ _, h2, h3, h3', h4, h5, h6,
      along_past nt tp rest _ _ _ _ _ _ _ _ _ _ _ _ (past_row hp) h7⟩
  | (kdr + 2, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, hp, h => by
    simp only [JAlong] at h ⊢
    obtain ⟨_, h2, h3, h4, h5, h5', _, h7, h8⟩ := h
    refine ⟨gate_of_past hp _ _ _, h2, h3, h4, h5, h5', ?_, h7,
      along_past nt tp rest _ _ _ _ _ _ _ _ _ _ _ _ (past_jump hp) h8⟩
    unfold Past at hp
    unfold Early
    omega

/-- A list of rows along which the rule holds passes the gate of one of the `nt` parts. -/
theorem along_gate (hnt : 0 < nt) : ∀ (rest : List TRow) (i t r d : ℕ) (a : ℤ) (b : ℕ)
    (m pm pM : ℤ) (z last : List ℕ) (usedC : List (List ℕ)),
    JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi (Gate gi gr 1 0)
      (Early gi gr 1 0) i t r d a b m pm pM z last usedC rest →
    ∃ tp, tp < nt ∧
      JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi (Gate gi gr nt tp)
      (Early gi gr nt tp) i t r d a b m pm pM z last usedC rest
  | [], i, t, r, d, a, b, m, pm, pM, z, last, usedC, h => by
    refine ⟨(enc last + 8192 * d) % nt, Nat.mod_lt _ hnt, ?_⟩
    simp only [JAlong] at h ⊢
    exact ⟨Or.inr (Or.inr rfl), h.2⟩
  | (_, []) :: _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [JAlong] at h
  | (0, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, h => by
    by_cases hp : Past gi gr i r
    · exact ⟨0, hnt, along_past nt 0 _ _ _ _ _ _ _ _ _ _ _ _ _ hp h⟩
    simp only [JAlong] at h
    obtain ⟨_, h2, h3, h3', h4, h5, h6, h7⟩ := h
    by_cases hat : i = gi ∧ r = gr
    · refine ⟨(enc last + 8192 * d) % nt, Nat.mod_lt _ hnt, ?_⟩
      simp only [JAlong]
      exact ⟨Or.inr (Or.inr rfl), h2, h3, h3', h4, h5, h6,
        along_past nt _ rest _ _ _ _ _ _ _ _ _ _ _ _ (Or.inr ⟨hat.1, by omega⟩) h7⟩
    · obtain ⟨tp, htp, hA⟩ := along_gate hnt rest _ _ _ _ _ _ _ _ _ _ _ _ h7
      refine ⟨tp, htp, ?_⟩
      simp only [JAlong]
      exact ⟨gate_of_ne hat _ _ _, h2, h3, h3', h4, h5, h6, hA⟩
  | (1, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, h => by
    by_cases hp : Past gi gr i r
    · exact ⟨0, hnt, along_past nt 0 _ _ _ _ _ _ _ _ _ _ _ _ _ hp h⟩
    simp only [JAlong] at h
    obtain ⟨_, h2, h3, h3', h4, h5, h6, h7⟩ := h
    by_cases hat : i = gi ∧ r = gr
    · refine ⟨(enc last + 8192 * d) % nt, Nat.mod_lt _ hnt, ?_⟩
      simp only [JAlong]
      exact ⟨Or.inr (Or.inr rfl), h2, h3, h3', h4, h5, h6,
        along_past nt _ rest _ _ _ _ _ _ _ _ _ _ _ _ (Or.inr ⟨hat.1, by omega⟩) h7⟩
    · obtain ⟨tp, htp, hA⟩ := along_gate hnt rest _ _ _ _ _ _ _ _ _ _ _ _ h7
      refine ⟨tp, htp, ?_⟩
      simp only [JAlong]
      exact ⟨gate_of_ne hat _ _ _, h2, h3, h3', h4, h5, h6, hA⟩
  | (kdr + 2, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, h => by
    by_cases hp : Past gi gr i r
    · exact ⟨0, hnt, along_past nt 0 _ _ _ _ _ _ _ _ _ _ _ _ _ hp h⟩
    simp only [JAlong] at h
    obtain ⟨_, h2, h3, h4, h5, h5', _, h7, h8⟩ := h
    by_cases hat : i = gi ∧ r = gr
    · refine ⟨(enc last + 8192 * d) % nt, Nat.mod_lt _ hnt, ?_⟩
      simp only [JAlong]
      exact ⟨Or.inr (Or.inr rfl), h2, h3, h4, h5, h5', Or.inr (Or.inl (le_of_eq hat.2.symm)), h7,
        along_past nt _ rest _ _ _ _ _ _ _ _ _ _ _ _ (Or.inl (by omega)) h8⟩
    · by_cases hi : i = gi
      · refine ⟨(enc last + 8192 * d) % nt, Nat.mod_lt _ hnt, ?_⟩
        simp only [JAlong]
        exact ⟨gate_of_ne hat _ _ _, h2, h3, h4, h5, h5', Or.inr (Or.inr rfl), h7,
          along_past nt _ rest _ _ _ _ _ _ _ _ _ _ _ _ (Or.inl (by omega)) h8⟩
      · obtain ⟨tp, htp, hA⟩ := along_gate hnt rest _ _ _ _ _ _ _ _ _ _ _ _ h8
        refine ⟨tp, htp, ?_⟩
        simp only [JAlong]
        exact ⟨gate_of_ne hat _ _ _, h2, h3, h4, h5, h5', Or.inl hi, h7, hA⟩

/-! ### Several gates -/

theorem along_map2 {G1 G2 G3 E1 E2 E3 : ℕ → ℕ → ℕ → Prop}
    (hG : ∀ i r key, G1 i r key → G2 i r key → G3 i r key)
    (hE : ∀ i r key, E1 i r key → E2 i r key → E3 i r key) :
    ∀ (rest : List TRow) (i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ)
    (z last : List ℕ) (usedC : List (List ℕ)),
    JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi G1 E1 i t r d a b m pm pM z last usedC rest →
    JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi G2 E2 i t r d a b m pm pM z last usedC rest →
    JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi G3 E3 i t r d a b m pm pM z last usedC rest
  | [], i, t, r, d, a, b, m, pm, pM, z, last, usedC, h, h' => by
    simp only [JAlong] at h h' ⊢
    exact ⟨hG _ _ _ h.1 h'.1, h.2⟩
  | (_, []) :: _, _, _, _, _, _, _, _, _, _, _, _, _, h, _ => by simp [JAlong] at h
  | (0, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, h, h' => by
    simp only [JAlong] at h h' ⊢
    obtain ⟨h1, h2, h3, h3', h4, h5, h6, h7⟩ := h
    exact ⟨hG _ _ _ h1 h'.1, h2, h3, h3', h4, h5, h6,
      along_map2 hG hE rest _ _ _ _ _ _ _ _ _ _ _ _ h7 h'.2.2.2.2.2.2.2⟩
  | (1, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, h, h' => by
    simp only [JAlong] at h h' ⊢
    obtain ⟨h1, h2, h3, h3', h4, h5, h6, h7⟩ := h
    exact ⟨hG _ _ _ h1 h'.1, h2, h3, h3', h4, h5, h6,
      along_map2 hG hE rest _ _ _ _ _ _ _ _ _ _ _ _ h7 h'.2.2.2.2.2.2.2⟩
  | (kdr + 2, v :: R) :: rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, h, h' => by
    simp only [JAlong] at h h' ⊢
    obtain ⟨h1, h2, h3, h4, h5, h5', h6, h7, h8⟩ := h
    exact ⟨hG _ _ _ h1 h'.1, h2, h3, h4, h5, h5', hE _ _ _ h6 h'.2.2.2.2.2.2.1, h7,
      along_map2 hG hE rest _ _ _ _ _ _ _ _ _ _ _ _ h8 h'.2.2.2.2.2.2.2.2⟩

theorem along_gates : ∀ (gs : List (ℕ × ℕ × ℕ)), (∀ g ∈ gs, 0 < g.2.2) →
    ∀ (rest : List TRow) (i t r d : ℕ) (a : ℤ) (b : ℕ) (m pm pM : ℤ)
    (z last : List ℕ) (usedC : List (List ℕ)),
    JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi (fun _ _ _ => True) (fun _ _ _ => True)
      i t r d a b m pm pM z last usedC rest →
    ∃ tp, tp < gprod gs ∧
      JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi (GateL gs tp) (EarlyL gs tp)
        i t r d a b m pm pM z last usedC rest
  | [], _, rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, h =>
    ⟨0, Nat.one_pos, along_map2 (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial)
      rest _ _ _ _ _ _ _ _ _ _ _ _ h h⟩
  | g :: gs, hg, rest, i, t, r, d, a, b, m, pm, pM, z, last, usedC, h => by
    have hn : 0 < g.2.2 := hg g List.mem_cons_self
    obtain ⟨t1, ht1, h1⟩ := along_gate (gi := g.1) (gr := g.2.1) (nt := g.2.2) hn
      rest _ _ _ _ _ _ _ _ _ _ _ _
      (along_map2 (G3 := Gate g.1 g.2.1 1 0) (E3 := Early g.1 g.2.1 1 0)
        (fun _ _ _ _ _ => Or.inr (Or.inr (Nat.mod_one _)))
        (fun _ _ _ _ _ => Or.inr (Or.inr (Nat.mod_one _)))
        rest _ _ _ _ _ _ _ _ _ _ _ _ h h)
    obtain ⟨t2, ht2, h2⟩ := along_gates gs (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      rest _ _ _ _ _ _ _ _ _ _ _ _ h
    have e1 : (t1 + g.2.2 * t2) % g.2.2 = t1 := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt ht1
    have e2 : (t1 + g.2.2 * t2) / g.2.2 = t2 := by
      rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt ht1, Nat.zero_add]
    refine ⟨t1 + g.2.2 * t2, ?_, ?_⟩
    · have h3 : g.2.2 * (t2 + 1) ≤ g.2.2 * gprod gs := Nat.mul_le_mul_left _ ht2
      rw [Nat.mul_add, Nat.mul_one] at h3
      simp only [gprod]
      omega
    · refine along_map2 (G1 := Gate g.1 g.2.1 g.2.2 t1) (G2 := GateL gs t2) ?_ ?_
        rest _ _ _ _ _ _ _ _ _ _ _ _ h1 h2
      · intro i r key ha hb
        simp only [GateL, e1, e2]
        exact ⟨ha, hb⟩
      · intro i r key ha hb
        simp only [EarlyL, e1, e2]
        exact ⟨ha, hb⟩

/-- **The search is complete.**  If all `gprod gs` parts of the gates `gs` answer `false`, the
rule holds along no list of rows that starts at the word `1 2 … k` and obeys the bound on shared
classes. -/
theorem not_along_of_parts (E : Enc k enc ci nxt s3 s4 jl st) (hk : 2 ≤ k) (hnp : np ≤ 255)
    (hid : PermW k (List.range' 1 k)) {gs : List (ℕ × ℕ × ℕ)} (hgs : ∀ g ∈ gs, 0 < g.2.2)
    {V : ℤ} {W sz fuel : ℕ}
    (hs : ∀ tp, tp < gprod gs →
      searchPart ci nxt s3 s4 jl st (k - 1) np bm kd lo hi bestLe gLe fLe xr xc phi V W sz fuel
        (gateD (digs gs tp)) (earlyD (digs gs tp)) = false)
    (R1 : List (List ℕ)) (rest : List TRow)
    (hR1 : R1.length ≤ k - 2) (hperm : ∀ w ∈ List.range' 1 k :: R1, PermW k w)
    (hdoor : List.IsChain (DoorEq k) (List.range' 1 k :: R1))
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) (List.range' 1 k :: R1))
    (hW : k - 2 - R1.length ≤ W)
    (hbud : Bud bm 0 [] ((List.range' 1 k :: R1) ++ blocksR rest)) :
    ¬ JAlong k np enc kd lo hi bestLe gLe fLe xr xc phi (Gate gi gr 1 0)
      (Early gi gr 1 0) 0 0 1 (k - 2 - R1.length) V W
      (-((k - 1 : ℕ) : ℤ)) 0 0 (List.range' 1 k)
      ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _)) (List.range' 1 k :: R1) rest := by
  intro hA
  obtain ⟨tp, htp, hP⟩ := along_gates gs hgs rest _ _ _ _ _ _ _ _ _ _ _ _
    (along_map2 (G3 := fun _ _ _ => True) (E3 := fun _ _ _ => True)
      (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) rest _ _ _ _ _ _ _ _ _ _ _ _ hA hA)
  have hG := gateL_true gs tp
  have hE := earlyL_true gs tp
  have hnp0 := lt_of_along _ _ _ _ _ _ _ _ _ _ _ _ _ hP
  have hlive := live_of_along _ _ _ _ _ _ _ _ _ _ _ _ _ hP
  have e : k - 1 - 1 - R1.length = k - 2 - R1.length := by omega
  have hbit := mkMask_bit (fun n => decide (n ≤ W) &&
    live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) 0 0 1 n V W (-((k - 1 : ℕ) : ℤ)))
    (k - 1) R1.length (by omega) (by
      rw [e, Bool.and_eq_true]
      exact ⟨decide_eq_true hW, hlive⟩)
  have hm0 : ∀ j, (marks0 sz).get! j = 0 := fun j => S.get!_marks0 sz j
  have h := walkG_complete E hk
    (fun n e du M =>
      go ci nxt s3 s4 jl (k - 1) np bm kd lo hi bestLe gLe fLe (gateD (digs gs tp))
        (earlyD (digs gs tp)) xr xc phi fuel 0 0 1 n V W (-((k - 1 : ℕ) : ℤ)) 0 0 st e du M)
    (fun n e du M => go_id (k - 1) fuel _ _ _ _ _ _ _ _ _ _ _ _ _) (UInt8.ofNat 1) 1
    (le_of_eq (toNat_ofNat8 (by omega))) bm
    (mkMask (fun n => decide (n ≤ W) &&
      live (k - 1) np kd bestLe gLe fLe (fun _ _ => true) 0 0 1 n V W
        (-((k - 1 : ℕ) : ℤ))) (k - 1))
    0 (marks0 sz) (List.range' 1 k) R1 [] [] (blocksR rest) hR1
    hbit hperm hdoor (PS.minv_marks0 enc ci sz)
    (fun j hj => by
      rw [hm0] at hj
      exact absurd hj (by decide))
    (fun j => by rw [hm0]; decide) (by simp) (by simp) (by simp) hpw hbud
    (fun M' du' hM' hC' hB' hbud' => by
      rw [E.st_eq]
      exact go_complete E hk hnp hG hE rest fuel 0 0 1 _ V W _ 0 0 (List.range' 1 k) _
        (List.range' 1 k :: R1) (List.range' 1 k :: R1) du' M'
        (hperm _ (List.getLast_mem _)) hid hperm hperm (by simpa using hM') (by simpa using hC')
        hB' (by simpa using hbud') hP)
  rw [← E.st_eq] at h
  have h3 : searchPart ci nxt s3 s4 jl st (k - 1) np bm kd lo hi bestLe gLe fLe xr xc phi V W sz
      fuel (gateD (digs gs tp)) (earlyD (digs gs tp)) = true := by
    unfold searchPart
    exact beq_iff_eq.mpr h
  rw [hs tp htp] at h3
  cases h3

end Engine

end J16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.J16.not_along_of_parts
