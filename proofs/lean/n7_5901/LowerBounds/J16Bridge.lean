import LowerBounds.J16Along
import LowerBounds.J16Tables
import LowerBounds.J16RX
import LowerBounds.K16Defs
import LowerBounds.J15Final

/-!
# The runs of Table C on the class (the bridge between the engine and the interface)

`J16.Evals` has one field per run of Table C (T1; the ten runs of T2; T3', T4', T5, T6' = T6rp, T7, T8,
T9' = T9r): the compiled search `J16.jSearch` with the parameters of the run (kinds in the order of the
run, `V`, `W`, `B`, the window of ring holes, the value range of the rings, the clip, the piece and the
potential of Rule PREV, the pair of Rule ORD, the table) answers `false` in all parts of some list of
gates; and one field `rx` for the ring search behind RX (the exact ring row to 63 holes, section 1.3),
which only the three upper halves of the split VS read.  `J16Final.lean` puts them together.

The tables: every run reads the rows 0..11 of `jrev/capD.txt` (`T5901J.DJ`); the ring row is that of
`jrev/capD.txt` (`DRj`), of `ringcap/capD_r.txt` (`RXRj`, upper halves) or a lowered row (`LO17j`,
`LO20j`, `LO22j`, lower halves).  They are proved valid where the runs read them: the rows within
weight 89 from Theorem K16 (D16 ≤ D, `dj_ge`), the ring row of D from table T' (to 84 holes) and
Theorem K16 (a ring is a chain, `dr_ge`), `RXRj` on 32..55 holes from RX, a lowered row on its window
for the rings of the lower half only (their value is at most `a - 1`, `lo_ge`).
-/

namespace SuperpermLowerBounds
namespace J16

open S (PermW WLink DoorEq)
open PS (TRow IsSeq holesT linksT Closes SeqCapLt RingCapT capF)
open KS (tabA tab2 look2 maxLe maxLeN par)
open J15 (valK wtK IsPieceW Sh negInf bestF bestStep kdF loF hiF gprod gateD digs earlyD bestT gT
  tabA_get tab2_get look2_tab2 par_false arr_map_get Cov valT_eq wtT_eq sh_of_sharedLe seq_piece
  ring_piece holes_le_wtT)
open T5900 T5901 T5901J

/-! ### From the compiled search to the statement on the class -/

theorem jw_of_partsS {k : ℕ} {enc : List ℕ → ℕ} {ci nxt : ℕ → ℕ} {s3 s4 : ℕ → List ℕ}
    {jl : List ℕ} {st sz fuel : ℕ} {gs : List (ℕ × ℕ × ℕ)} {qs : List Q}
    {specs : List (ℕ × ℕ × ℕ)} {V : ℤ} {W B sm : ℕ} {P : ℕ → ℕ → ℕ} {PR : ℕ → ℕ}
    {kd lo hi : ℕ → ℕ} {bestLe : ℕ → ℕ → ℤ → Bool} {gLe : ℕ → ℕ → ℕ → ℤ → Bool}
    {fLe : ℕ → ℕ → ℕ → ℕ → ℤ → Bool} {R : Rules}
    (E : PS.Enc k enc ci nxt s3 s4 jl st) (hspec : qs.map Prod.fst = specs)
    (hne : specs ≠ []) (hnp : specs.length ≤ 255) (hgs : ∀ g ∈ gs, 0 < g.2.2)
    (hoi : R.oi + 1 < qs.length → qs.getD R.oi dq = qs.getD (R.oi + 1) dq)
    (hs : ∀ tp, tp < gprod gs →
      searchPart ci nxt s3 s4 jl st (k - 1) specs.length B kd lo hi bestLe gLe fLe
        (xrF R (k - 1) specs.length kd (fun i y => bestF P PR (k - 1) (specs.drop (i + 1)) y)
          (fun u y => bestF P PR (k - 1) [(u + 1, 0, 0)] y) (segF P (k - 1) R.pa R.pb R.ph))
        (xcF R (k - 1) specs.length kd (fun i y => bestF P PR (k - 1) (specs.drop (i + 1)) y))
        (fun c t r d => potF R.pa R.pb R.ph c t r d) V W sz fuel (gateD (digs gs tp))
        (earlyD (digs gs tp)) = false)
    (H : RunOK k qs W sm P PR kd lo hi bestLe gLe fLe R) : JV k qs V W B := by
  have hl : qs.length = specs.length := by rw [← hspec, List.length_map]
  have hB : BfOf k P PR qs = fun i y => bestF P PR (k - 1) (specs.drop (i + 1)) y := by
    funext i y
    unfold BfOf
    rw [hspec]
  have hne' : qs ≠ [] := by
    intro h
    rw [h] at hspec
    exact hne hspec.symm
  refine jw_of_partsV (sz := sz) (fuel := fuel) E H hne' (by omega) hgs hoi ?_
  rw [hl, hB]
  exact hs

/-- **The compiled search of a run proves its statement on the class** (`k = 7`). -/
theorem jw_of_search {caps : List (List ℕ)} {PRl : List ℕ} {specs : List (ℕ × ℕ × ℕ)} {R : Rules}
    {V W B sm fuel : ℕ} {gs : List (ℕ × ℕ × ℕ)}
    (hne : specs ≠ []) (hnp : specs.length ≤ 255) (hgs : ∀ g ∈ gs, 0 < g.2.2)
    (hlen : specs.length = R.vcl.length)
    (hc : CapsOKV 7 (capF caps) (fun x => PRl.getD x 0) W sm (specs.zip R.vcl))
    (hsm : ∀ q ∈ specs.zip R.vcl, q.1.1 ≤ sm + 1)
    (hR : ∀ i, i < (specs.zip R.vcl).length → vloF R i = ((specs.zip R.vcl).getD i dq).2.1 ∧
      vhiF R i = ((specs.zip R.vcl).getD i dq).2.2)
    (hpa : 0 < R.pa) (hab : R.pa ≤ R.pb) (hXL : 2 * R.ph ≤ (7 - 1) * (R.pb - R.pa) + (7 - 2) * R.pa)
    (hoi : R.oi + 1 < (specs.zip R.vcl).length →
      (specs.zip R.vcl).getD R.oi dq = (specs.zip R.vcl).getD (R.oi + 1) dq ∧
      ((specs.zip R.vcl).getD R.oi dq).1.1 ≠ 0)
    (hclip : R.clip = true → ∀ q ∈ specs.zip R.vcl, q.1.1 = 0 → 0 ≤ q.2.1)
    (hs : ∀ tp, tp < gprod gs → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      jSearch 7 caps PRl specs R V W B fuel gs pa pb = false) :
    JV 7 (specs.zip R.vcl) (V : ℤ) W B := by
  have hmap : (specs.zip R.vcl).map Prod.fst = specs := List.map_fst_zip (le_of_eq hlen)
  have hql : (specs.zip R.vcl).length = specs.length := by
    rw [List.length_zip, hlen, Nat.min_self]
  refine jw_of_partsS (enc := PS.encB 7) (PS.encB_enc 7 (by norm_num) (by norm_num)) hmap hne hnp
    hgs (fun h => (hoi h).1) (fun tp htp => by
      obtain ⟨pa, pb, h1, h2, h⟩ := hs tp htp
      unfold jSearch at h
      simp only [look2_tab2] at h
      exact par_false h tp h1 h2)
    ⟨by norm_num, hc, hsm, ?_, hR, hpa, hab, hXL, fun h => (hoi h).2, hclip, ?_, ?_, ?_⟩
  · intro i hi
    rw [hql] at hi
    rw [hmap]
    exact ⟨arr_map_get specs _ (0, 0, 0) hi, arr_map_get specs _ (0, 0, 0) hi,
      arr_map_get specs _ (0, 0, 0) hi⟩
  · intro i y x hi hy hx
    rw [hql] at hi
    rw [hmap] at hx
    unfold bestT
    split_ifs with hcnd
    · rw [tab2_get _ _ _ (by omega) (by omega)]
      exact decide_eq_true hx
    · rfl
  · intro i u y x hi hy _ hx
    rw [hmap] at hx
    unfold gT
    split_ifs with hcnd
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcnd
      obtain ⟨⟨h1, h2⟩, h3⟩ := hcnd
      rw [tabA_get _ _ _ _ h1 h2 h3]
      exact decide_eq_true hx
    · rfl
  · intro i b r d x hi hb hkd0 hx hcl
    rw [hmap] at hx hcl
    rw [hql] at hi
    beta_reduce
    split_ifs with hcnd
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcnd
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcnd
      have hib : i * (W + 1) + b < specs.length * (W + 1) := by nlinarith
      rw [tabA_get _ _ _ _ hib h3 h4]
      simp only [S.mul_add_div' h2, S.mul_add_mod' h2]
      beta_reduce at hkd0
      rw [hkd0, if_pos (show ((0 : ℕ) == 0) = true from rfl)]
      unfold ringOk
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true']
      refine ⟨hx, ?_⟩
      by_cases hc' : R.clip = true
      · exact Or.inr (hcl hc')
      · exact Or.inl (by simpa using hc')
    · rfl

/-! ### The runs -/

/-- No restriction on the value of a ring. -/
def noC : ℤ × ℤ := (negInf, 1000000000)

/-- A run of Table C on the rows of D and the ring row `PRl` answers `false`, for some fuel and
some gates, in all parts.  `specs` lists the kinds in the order of the run (`(0, lo, hi)` a ring with
`lo … hi` holes, `(s + 1, 0, 0)` a sequence with at most `s` links); the value range of the rings,
the clip, Rule PREV and Rule ORD are in `R`. -/
def Ev (PRl : List ℕ) (specs : List (ℕ × ℕ × ℕ)) (R : Rules) (V W B : ℕ) : Prop :=
  ∃ fuel gs, (∀ g ∈ gs, 0 < g.2.2) ∧ Cov (gprod gs) (jSearch 7 DJ PRl specs R V W B fuel gs)

/-- T1: S7 S7, ORD on pieces 1, 2, PREV on piece 1 with 10,15,25. -/
def rT1 : Rules := ⟨[noC, noC], false, 0, 10, 15, 25, 0⟩
/-- T2 on a window: R S7, PREV on piece 2 with 10,15,40. -/
def rT2 : Rules := ⟨[noC, noC], false, 1, 10, 15, 40, 9⟩
/-- T2, upper half: rings of value at least `a`. -/
def rT2up (a : ℤ) : Rules := ⟨[(a, 1000000000), noC], false, 1, 10, 15, 40, 9⟩
/-- T2, lower half: S7 R, rings of value at most `a - 1`, PREV on piece 1 with 10,15,30. -/
def rT2lo (a : ℤ) : Rules := ⟨[noC, (negInf, a - 1)], false, 0, 10, 15, 30, 9⟩
/-- T3': R S5 R, rings of value at least 0 (the cut at negative need), PREV on piece 2, 10,16,43. -/
def rT3 : Rules := ⟨[(0, 1000000000), noC, (0, 1000000000)], true, 1, 10, 16, 43, 9⟩
/-- T4': R S4 S4, ORD on pieces 2, 3, PREV on piece 2 with 10,16,43. -/
def rT4 : Rules := ⟨[noC, noC, noC], false, 1, 10, 16, 43, 1⟩
/-- T5: plain. -/
def rT5 : Rules := ⟨[noC, noC, noC], false, 9, 10, 15, 25, 9⟩
/-- T6' (T6rp): S2 R R R, rings of value at least 0, PREV on piece 1 with 10,16,25. -/
def rT6 : Rules := ⟨[noC, (0, 1000000000), (0, 1000000000), (0, 1000000000)], true, 0, 10, 16, 25, 9⟩
/-- T7: plain, rings of value at least 0. -/
def rT7 : Rules := ⟨[noC, noC, (0, 1000000000), (0, 1000000000)], true, 9, 10, 15, 25, 9⟩
/-- T8: plain, rings of value at least 0. -/
def rT8 : Rules := ⟨[noC, noC, noC, (0, 1000000000)], true, 9, 10, 15, 25, 9⟩
/-- T9' (T9r): plain, rings of value at least 0. -/
def rT9 : Rules :=
  ⟨[noC, (0, 1000000000), (0, 1000000000), (0, 1000000000), (0, 1000000000)], true, 9, 10, 15, 25, 9⟩

/-- **The runs of Table C.** -/
structure Evals : Prop where
  /-- T1 = J(S7 S7; 50, 84; 1). -/
  t1 : Ev DRj [(8, 0, 0), (8, 0, 0)] rT1 50 84 1
  /-- T2, rings with 8..15 holes. -/
  t2a : Ev DRj [(0, 8, 15), (8, 0, 0)] rT2 46 89 1
  /-- T2, rings with 16..23 holes. -/
  t2b : Ev DRj [(0, 16, 23), (8, 0, 0)] rT2 46 89 1
  /-- T2, rings with 24..31 holes. -/
  t2c : Ev DRj [(0, 24, 31), (8, 0, 0)] rT2 46 89 1
  /-- T2, rings with 32..39 holes and value at least 17 (VS (hi), table `capD_r.txt`). -/
  t2d : Ev RXRj [(0, 32, 39), (8, 0, 0)] (rT2up 17) 46 89 1
  /-- T2, rings with 32..39 holes and value at most 16 (VS (lo), kernel first). -/
  t2e : Ev LO17j [(8, 0, 0), (0, 32, 39)] (rT2lo 17) 46 89 1
  /-- T2, rings with 40..47 holes and value at least 20. -/
  t2f : Ev RXRj [(0, 40, 47), (8, 0, 0)] (rT2up 20) 46 89 1
  /-- T2, rings with 40..47 holes and value at most 19. -/
  t2g : Ev LO20j [(8, 0, 0), (0, 40, 47)] (rT2lo 20) 46 89 1
  /-- T2, rings with 48..55 holes and value at least 23. -/
  t2h : Ev RXRj [(0, 48, 55), (8, 0, 0)] (rT2up 23) 46 89 1
  /-- T2, rings with 48..55 holes and value at most 22. -/
  t2i : Ev LO22j [(8, 0, 0), (0, 48, 55)] (rT2lo 23) 46 89 1
  /-- T2, rings with 56..89 holes. -/
  t2j : Ev DRj [(0, 56, 89), (8, 0, 0)] rT2 46 89 1
  /-- T3' = J(R S5 R; 52, 82; 2), rings with at least 8 holes. -/
  t3 : Ev DRj [(0, 8, 82), (6, 0, 0), (0, 8, 82)] rT3 52 82 2
  /-- T4' = J(R S4 S4; 56, 77; 2), rings with at least 8 holes. -/
  t4 : Ev DRj [(0, 8, 77), (5, 0, 0), (5, 0, 0)] rT4 56 77 2
  /-- T5 = J(S3 S3 S3; 60, 72; 2). -/
  t5 : Ev DRj [(4, 0, 0), (4, 0, 0), (4, 0, 0)] rT5 60 72 2
  /-- T6' (T6rp) = J(S2 R R R; 58, 75; 3), rings with at least 8 holes. -/
  t6 : Ev DRj [(3, 0, 0), (0, 8, 75), (0, 8, 75), (0, 8, 75)] rT6 58 75 3
  /-- T7 = J(S1 S1 R R; 62, 70; 3). -/
  t7 : Ev DRj [(2, 0, 0), (2, 0, 0), (0, 0, 70), (0, 0, 70)] rT7 62 70 3
  /-- T8 = J(S0 S0 S0 R; 66, 65; 2). -/
  t8 : Ev DRj [(1, 0, 0), (1, 0, 0), (1, 0, 0), (0, 0, 65)] rT8 66 65 2
  /-- T9' (T9r) = J(S0 R R R R; 64, 68; 4), rings with at least 8 holes. -/
  t9 : Ev DRj [(1, 0, 0), (0, 8, 68), (0, 8, 68), (0, 8, 68), (0, 8, 68)] rT9 64 68 4
  /-- The ring search for RX (section 1.3; read by the upper halves of VS only). -/
  rx : EvRX

/-! ### The tables are valid where the runs read them -/

/-- D16 ≤ D on the rows 0..7 within weight 89. -/
theorem dj_ge : ∀ t ≤ 7, ∀ x ≤ 89 - 6 * t, capF D16tab t x ≤ capF DJ t x := by decide +kernel

/-- The ring row of D is at least TR' (to 84 holes) or D16_0, to 89 holes. -/
theorem dr_ge : ∀ H ≤ 89, (H ≤ 84 ∧ TRtab.getD H 0 ≤ DRj.getD H 0) ∨ capF D16tab 0 H ≤ DRj.getD H 0 := by
  decide +kernel

/-- `capD_r.txt` is RX on 0..63 holes. -/
theorem rx_ge : ∀ H ≤ 63, RXtab.getD H 0 ≤ RXRj.getD H 0 := by decide +kernel

/-- A lowered row on its window is at least the valid bound or `H + a - 1`. -/
theorem lo_ge17 : ∀ H, 32 ≤ H → H ≤ 39 → (H ≤ 84 ∧ TRtab.getD H 0 ≤ LO17j.getD H 0) ∨
    capF D16tab 0 H ≤ LO17j.getD H 0 ∨ H + 16 ≤ LO17j.getD H 0 := by decide +kernel
theorem lo_ge20 : ∀ H, 40 ≤ H → H ≤ 47 → (H ≤ 84 ∧ TRtab.getD H 0 ≤ LO20j.getD H 0) ∨
    capF D16tab 0 H ≤ LO20j.getD H 0 ∨ H + 19 ≤ LO20j.getD H 0 := by decide +kernel
theorem lo_ge22 : ∀ H, 48 ≤ H → H ≤ 55 → (H ≤ 84 ∧ TRtab.getD H 0 ≤ LO22j.getD H 0) ∨
    capF D16tab 0 H ≤ LO22j.getD H 0 ∨ H + 22 ≤ LO22j.getD H 0 := by decide +kernel

/-- A ring has at most D16_0 rows (it is a chain) and at most TR' rows (to 84 holes). -/
theorem ring_valid (hT : KS.TableT) (hK : K16.TheoremK16) {L : List TRow} (hL : IsSeq 7 L)
    (hk0 : ∀ x ∈ L, x.1 = 0) (h2 : 2 ≤ L.length) (hc : Closes 7 L) (hH : holesT 7 L ≤ 89) :
    L.length ≤ capF D16tab 0 (holesT 7 L) ∧
      (holesT 7 L ≤ 84 → L.length ≤ TRtab.getD (holesT 7 L) 0) := by
  refine ⟨hK 0 (by norm_num) L hL (fun x hx => by rw [hk0 x hx]; omega) (PS.linksT_zero hk0)
    (by omega), fun h84 => hT.2 L hL hk0 h2 hc h84⟩

/-- The rows of D are valid within weight 89 (from Theorem K16). -/
theorem seq_okD (hK : K16.TheoremK16) {W : ℕ} (hW : W ≤ 89) :
    ∀ t, t ≤ 7 → SeqCapLt 7 t (capF DJ t) (W + 1 - (7 - 1) * t) := by
  intro t ht L hL hk1 hl hh
  have h1 := hK t (by omega) L hL hk1 hl (by omega)
  exact le_trans h1 (dj_ge t ht _ (by omega))

/-- The ring row of D for every ring kind. -/
theorem ringOK_D (hT : KS.TableT) (hK : K16.TheoremK16) {W : ℕ} (hW : W ≤ 89) (q : Q) :
    RingOK 7 (fun x => DRj.getD x 0) W q := by
  intro h0 L hV hH
  have hw := hV.1
  unfold IsPieceW at hw
  rw [if_pos h0] at hw
  obtain ⟨hL, hk0, h2, hc, _, _⟩ := hw
  obtain ⟨c1, c2⟩ := ring_valid hT hK hL hk0 h2 hc (by omega)
  rcases dr_ge _ (show holesT 7 L ≤ 89 by omega) with ⟨h84, h3⟩ | h3
  · exact le_trans (c2 h84) h3
  · exact le_trans c1 h3

/-- The ring row of `capD_r.txt` for ring kinds with holes in 0..63 (from RX). -/
theorem ringOK_RX (hRX : RX) {W : ℕ} (q : Q) (hq : q.1.1 = 0 → q.1.2.2 ≤ 63) :
    RingOK 7 (fun x => RXRj.getD x 0) W q := by
  intro h0 L hV _
  have hw := hV.1
  unfold IsPieceW at hw
  rw [if_pos h0] at hw
  obtain ⟨hL, hk0, h2, hc, _, hhi⟩ := hw
  have h63 : holesT 7 L ≤ 63 := le_trans hhi (hq h0)
  exact le_trans (hRX L hL hk0 h2 hc h63) (rx_ge _ h63)

/-- A lowered ring row for the rings of the lower half. -/
theorem ringOK_LO (hT : KS.TableT) (hK : K16.TheoremK16) {W : ℕ} (hW : W ≤ 89) {LO : List ℕ}
    {lo hi : ℕ} {a : ℤ} {c : ℕ} (hca : (c : ℤ) = a - 1)
    (hchk : ∀ H, lo ≤ H → H ≤ hi → (H ≤ 84 ∧ TRtab.getD H 0 ≤ LO.getD H 0) ∨
      capF D16tab 0 H ≤ LO.getD H 0 ∨ H + c ≤ LO.getD H 0) (q : Q)
    (hq : q.1.1 = 0 → q.1.2.1 = lo ∧ q.1.2.2 = hi ∧ q.2.2 = a - 1) :
    RingOK 7 (fun x => LO.getD x 0) W q := by
  intro h0 L hV hH
  have hw := hV.1
  unfold IsPieceW at hw
  rw [if_pos h0] at hw
  obtain ⟨hL, hk0, h2, hc, hlo, hhi⟩ := hw
  obtain ⟨e1, e2, e3⟩ := hq h0
  obtain ⟨c1, c2⟩ := ring_valid hT hK hL hk0 h2 hc (by omega)
  have hv := (hV.2 h0).2
  rw [ring_val hk0, e3] at hv
  have hv' : L.length ≤ holesT 7 L + c := by
    have : (L.length : ℤ) ≤ holesT 7 L + c := by rw [hca]; linarith
    exact_mod_cast this
  rcases hchk (holesT 7 L) (by rw [← e1]; exact hlo) (by rw [← e2]; exact hhi) with
    ⟨h84, h3⟩ | h3 | h3
  · exact le_trans (c2 h84) h3
  · exact le_trans c1 h3
  · exact le_trans hv' h3

/-! ### From the class to the statements of the interface -/

theorem wt_le_sum {L : List TRow} : ∀ {Ls : List (List TRow)}, L ∈ Ls →
    KS.wtT L ≤ (Ls.map KS.wtT).sum
  | _ :: Ls, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · simp
    · simp only [List.map_cons, List.sum_cons]
      have := wt_le_sum h'
      omega

theorem forall₂_class {P : List TRow → Prop} {W : ℕ} :
    ∀ {kinds : List KS.Kind} {qs : List Q} {Ls : List (List TRow)},
    List.Forall₂ (fun (kd : KS.Kind) (q : Q) => ∀ L, K16.IsPieceP P kd L → KS.wtT L ≤ W →
      IsPieceV 7 q L) kinds qs →
    List.Forall₂ (K16.IsPieceP P) kinds Ls → (∀ L ∈ Ls, KS.wtT L ≤ W) →
    List.Forall₂ (IsPieceV 7) qs Ls
  | _, _, _, List.Forall₂.nil, List.Forall₂.nil, _ => List.Forall₂.nil
  | _, _, _, List.Forall₂.cons hr hrs, List.Forall₂.cons hp hps, hw =>
    List.Forall₂.cons (hr _ hp (hw _ List.mem_cons_self))
      (forall₂_class hrs hps (fun L hL => hw L (List.mem_cons_of_mem _ hL)))

theorem jp_of_jv {P : List TRow → Prop} {kinds : List KS.Kind} {qs : List Q} {V : ℤ} {W B : ℕ}
    (hJ : JV 7 qs V W B)
    (hrel : List.Forall₂ (fun (kd : KS.Kind) (q : Q) => ∀ L, K16.IsPieceP P kd L →
      KS.wtT L ≤ W → IsPieceV 7 q L) kinds qs) :
    K16.JP P kinds V W B := by
  intro Ls hLs hsh hw
  have hV := forall₂_class hrel hLs (fun L hL => le_trans (wt_le_sum hL) hw)
  have := hJ Ls hV (sh_of_sharedLe hsh) (by
    have e : Ls.map (wtK 7) = Ls.map KS.wtT := List.map_congr_left fun L _ => (wtT_eq L).symm
    rw [e]
    exact hw)
  have e : Ls.map (valK 7) = Ls.map KS.valT := List.map_congr_left fun L _ => (valT_eq L).symm
  rw [e] at this
  exact this

theorem j_of_jp {kinds : List KS.Kind} {V : ℤ} {W B : ℕ}
    (hseq : ∀ k ∈ kinds, ∃ s, k = .seq s) (h : K16.JP (fun _ => True) kinds V W B) :
    KS.J kinds V W B := by
  intro Ls hLs hsh hw
  refine h Ls ?_ hsh hw
  have : ∀ {kinds : List KS.Kind} {Ls : List (List TRow)}, (∀ k ∈ kinds, ∃ s, k = .seq s) →
      List.Forall₂ KS.IsPiece kinds Ls → List.Forall₂ (K16.IsPieceP (fun _ => True)) kinds Ls := by
    intro kinds Ls hk h
    induction h with
    | nil => exact List.Forall₂.nil
    | @cons a b l1 l2 hab _ ih =>
      obtain ⟨s, rfl⟩ := hk a List.mem_cons_self
      exact List.Forall₂.cons hab (ih fun k hk' => hk k (List.mem_cons_of_mem _ hk'))
  exact this hseq hLs

/-- A sequence piece of the interface is a piece of the class. -/
theorem rel_seq {P : List TRow → Prop} {W s : ℕ} (c : ℤ × ℤ) :
    ∀ L, K16.IsPieceP P (.seq s) L → KS.wtT L ≤ W → IsPieceV 7 ((s + 1, 0, 0), c) L :=
  fun _ h _ => ⟨seq_piece h, fun h0 => absurd h0 (Nat.succ_ne_zero s)⟩

/-- A ring of the interface is a piece of the class: its holes lie in the window and its value in
the range. -/
theorem rel_ring (hK : K16.TheoremK16) {P : List TRow → Prop} {W lo hi : ℕ} {vlo vhi : ℤ}
    (hW : W ≤ 89)
    (hwin : ∀ L, KS.IsPiece .ring L → P L → holesT 7 L ≤ W → lo ≤ holesT 7 L ∧ holesT 7 L ≤ hi)
    (hlo : ∀ L, KS.IsPiece .ring L → P L → vlo ≤ KS.valT L ∨ vlo = negInf)
    (hhi : ∀ L, KS.IsPiece .ring L → P L → KS.valT L ≤ vhi ∨ vhi = 1000000000) :
    ∀ L, K16.IsPieceP P .ring L → KS.wtT L ≤ W → IsPieceV 7 ((0, lo, hi), (vlo, vhi)) L := by
  intro L ⟨hR, hP⟩ hw
  have hH : holesT 7 L ≤ W := le_trans (holes_le_wtT L) hw
  obtain ⟨hwl, hwh⟩ := hwin L hR hP hH
  refine ⟨ring_piece hR hwl hwh, fun _ => ?_⟩
  show vlo ≤ valK 7 L ∧ valK 7 L ≤ vhi
  obtain ⟨hL, hk0, _, _⟩ := hR
  have hc := hK 0 (by norm_num) L hL (fun x hx => by rw [hk0 x hx]; omega) (PS.linksT_zero hk0)
    (by omega)
  have hb : capF D16tab 0 (holesT 7 L) ≤ 200 := by
    have : ∀ H ≤ 89, capF D16tab 0 H ≤ 200 := by decide +kernel
    exact this _ (by omega)
  have hv : valK 7 L = (L.length : ℤ) - (holesT 7 L : ℤ) := ring_val hk0
  rw [← valT_eq]
  constructor
  · rcases hlo L ⟨hL, hk0, ‹_›, ‹_›⟩ hP with h | h
    · exact h
    · rw [h, valT_eq, hv]
      unfold negInf
      omega
  · rcases hhi L ⟨hL, hk0, ‹_›, ‹_›⟩ hP with h | h
    · exact h
    · rw [h, valT_eq, hv]
      omega

end J16
end SuperpermLowerBounds
