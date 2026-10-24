import LowerBounds.K16Rules
import LowerBounds.K16Thm
import LowerBounds.PFinal

/-!
# The kernel alone at defect 16 from search equations (the written proof, sections 3.2 to 3.4)

`Ev P s lo hi a b h js`: the statement F(s; lo - 1, hi) on the table `P` was searched with the potential
`(a, b, h)` and Rule JS if `js` (the search of `K16Search.lean`): every part lies in a range of parts
that answered `false`.

* `Evals`: the eleven statements K0 .. K10 of Table C as run: the table of the run (`Utab s` for K5 ..
  K10, `D16tab` for K0 .. K4), `lo = LO_s + 1`, `hi = G = 96 - 6 s`, the potential of section 3.2, Rule
  JS on for K2, K1, K0.
* `kernel_of_search`: the equations give the eleven statements `Kernel16` (`seqCap_of_k16search`).
* `theoremK16_of_search`: with Theorem K of 5,900, Theorem K16 (`theoremK16_of`, `cl16_of`).
-/

namespace SuperpermLowerBounds
namespace K16

open T5899 T5900 T5901
open PS (SeqCapLt capF)

/-- F(s; lo - 1, hi) on `P` was searched with the potential `(a, b, h)` and Rule JS if `js`. -/
def Ev (P : List (List ℕ)) (s lo hi a b h : ℕ) (js : Bool) : Prop :=
  ∃ fuel ds nt, 0 < nt ∧ PS.Covered nt (seqSearch 7 P s lo hi a b h js fuel ds nt)

/-- The eleven kernel statements of Table C as they were run. -/
structure Evals : Prop where
  k10 : Ev Utab10 10 36 36 10 16 25 false
  k9 : Ev Utab9 9 36 42 10 16 25 false
  k8 : Ev Utab8 8 36 48 10 16 25 false
  k7 : Ev Utab7 7 36 54 10 16 25 false
  k6 : Ev Utab6 6 38 60 10 16 25 false
  k5 : Ev Utab5 5 38 66 10 16 25 false
  k4 : Ev D16tab 4 42 72 10 15 25 false
  k3 : Ev D16tab 3 49 78 10 15 30 false
  k2 : Ev D16tab 2 52 84 20 29 60 true
  k1 : Ev D16tab 1 56 90 20 29 60 true
  k0 : Ev D16tab 0 66 96 17 24 5 true

/-- F(s; LO, G) from its evaluated search. -/
theorem fRow_of_ev {P : List (List ℕ)} {s LO G a b h : ℕ} {js : Bool}
    (hE : Ev P s (LO + 1) G a b h js) : FRow P s LO G := by
  intro hlow hprev
  obtain ⟨fuel, ds, nt, hnt, hc⟩ := hE
  exact seqCap_of_k16search (by norm_num) (by norm_num) hnt hlow hprev hc

/-- **The eleven kernel statements from their evaluated searches.** -/
theorem kernel_of_search (hE : Evals) : Kernel16 :=
  ⟨fRow_of_ev hE.k0, fRow_of_ev hE.k1, fRow_of_ev hE.k2, fRow_of_ev hE.k3, fRow_of_ev hE.k4,
    fRow_of_ev hE.k5, fRow_of_ev hE.k6, fRow_of_ev hE.k7, fRow_of_ev hE.k8, fRow_of_ev hE.k9,
    fRow_of_ev hE.k10⟩

/-- **Theorem K16 from Theorem K of 5,900 and the evaluated searches.** -/
theorem theoremK16_of_search (hK : KS.TheoremK) (hE : Evals) : TheoremK16 :=
  theoremK16_of_kernel hK (kernel_of_search hE)

end K16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K16.kernel_of_search
#print axioms SuperpermLowerBounds.K16.theoremK16_of_search
