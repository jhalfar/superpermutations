import LowerBounds.KDefs
import LowerBounds.PRules
import LowerBounds.J15Final

/-!
# Statement RX (the written proof, section 1.3)

The exact ring row to 63 holes: a ring with exactly `x ≤ 63` holes has at most `RX(x)` rows.  It is read
only by the upper halves of the split VS of T2 (rings with 32 to 55 holes), whose table is
`ringcap/capD_r.txt` (`T5901J.RXRj`, equal to `RXtab` on 0..63).

The written proof proves RX by the ring search of [P] 8.2 for an exact number of holes, with the chain row
of set B, I1, I2 on 0 to 63 holes (three programs, 1,588,850,620 kept prefixes).  Here: `EvRX` is that
search in Lean (`PS.ringSearch` of the proof of 5,899, with the chain row `T'_0` of 5,900, which is set B
with I1, I2), and `rx_of_search` is its completeness (`PS.ringCapT_of_search`) with `T'_0` valid by
`KS.TableT`.
-/

namespace SuperpermLowerBounds
namespace J16

open T5900

/-- RX(0..63) (section 1.3); the entry 1 means that no ring with that number of holes exists. -/
def RXtab : List ℕ :=
  [5, 1, 2, 1, 1, 1, 10, 6, 16, 3, 13, 14, 15, 16, 21, 22,
   27, 25, 33, 28, 35, 31, 37, 33, 38, 36, 40, 41, 46, 43, 48, 49,
   50, 50, 56, 53, 58, 58, 59, 60, 65, 62, 67, 67, 69, 69, 71, 71,
   76, 77, 78, 78, 84, 81, 82, 83, 86, 87, 89, 89, 91, 90, 93, 92]

/-- **Statement RX.** -/
def RX : Prop := PS.RingCapT 7 (fun x => RXtab.getD x 0) 63

/-- The ring search for RX (to 63 holes, with the chain row `T'_0`) answers `false` in all parts. -/
def EvRX : Prop :=
  ∃ fuel ds nt, 0 < nt ∧ J15.Cov nt (PS.ringSearch 7 (Ttab.getD 0 []) RXtab 63 fuel ds nt)

/-- **RX from its ring search.** -/
theorem rx_of_search (hT : KS.TableT) (h : EvRX) : RX := by
  obtain ⟨fuel, ds, nt, hnt, hc⟩ := h
  have hlen : KS.Tlen.getD 0 0 = 85 := rfl
  refine PS.ringCapT_of_search (by norm_num) (by norm_num) hnt ?_ hc
  intro L h1 h2 h3 h4
  exact hT.1 0 (by norm_num) L h1 h2 h3 (by rw [hlen]; omega)

end J16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.J16.rx_of_search
