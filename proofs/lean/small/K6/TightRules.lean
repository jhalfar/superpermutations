import K6.Engine
import K6.TightTab

/-!
# The rules of the search of the tight case (defect 4) on 6 symbols

A family of `T` trails (rows joined by seams of weight 3); the first trail starts at `1 2 3 4 5 6`,
the next ones start anywhere (a jump).  The counters (`FC`): the trail `t` (from 0), its rows `r` and
holes `d`, the rows `A` and holes `B` of the finished trails, and the rows `r1` and holes `d1` of the
first trail once it is finished.  With `need = 8 + 4 (T - 1)` and `G = 20 - 5 (T - 1)`:

* continue the trail (`keepN`) while `B + d ≤ G` and the knapsack table `bt` (the most that
  `T - t` chains can add to `rows - holes` within the remaining holes) can still reach `need`;
* end the trail and start the next (`keepJ`) if it is not the last one, its `rows - holes` is at
  most that of the first trail, and the remaining `T - t - 1` chains can still reach `need`;
* found (`bad`): the last trail ends, the sums reach `need` within `G` holes, and no class outside
  the family is dead (`deadB`): every class not used lies in some row of 4 blocks that avoids the
  used classes (a loop).

This file imports no Mathlib: the evaluations load only it.
-/

namespace K6

/-- The knapsack table: `bt n g` for `n ≤ 3` chains and `g ≤ 20` holes. -/
def bt (n g : Nat) : Nat := fld TBT 6 (21 * n + g)

/-- The classes of the row of 4 blocks that starts at the word `i`. -/
def loopMask (i : Nat) : Nat :=
  bit (ci i) ||| bit (ci (nx i)) ||| bit (ci (nx (nx i))) ||| bit (ci (nx (nx (nx i))))

/-- Some class outside `U` lies in no row of 4 blocks that avoids `U`. -/
def deadB (U : Nat) : Bool :=
  (List.range 120).any fun c => !U.testBit c &&
    (List.range 720).all fun i => !(loopMask i).testBit c || (loopMask i &&& U != 0)

/-- The counters of the search: trail `t`, its rows `r` and holes `d`, rows `A` and holes `B` of the
finished trails, rows `r1` and holes `d1` of the first trail, the number of rows `z`, the entry `k0` of
row number `g0` and the entry `k1` of the first row of the second trail (the last entries of these
rows), which select the part. -/
structure FC where
  t : Nat
  r : Nat
  d : Nat
  A : Nat
  B : Nat
  r1 : Nat
  d1 : Nat
  z : Nat
  k0 : Nat
  k1 : Nat

/-- The trail is not better than the first trail (always true for the first trail). -/
def ordOK (c : FC) : Bool := c.t == 0 || Nat.ble (c.r + c.d1) (c.r1 + c.d)

/-- The part: `k0` is `p0` modulo `n0` once there are `g0` rows, and `k1` is `p1` modulo `n1` once
there is a second trail. -/
def gateOK (g0 n0 p0 n1 p1 : Nat) (c : FC) : Bool :=
  (Nat.blt c.z g0 || c.k0 % n0 == p0) && (c.t == 0 || c.k1 % n1 == p1)

/-- The rules of the tight case with `T` trails, part `(p0, p1)` of `n0 × n1`. -/
def famRules (T g0 n0 p0 n1 p1 : Nat) : Rules FC where
  init n e := ⟨0, 1, n, 0, 0, 0, 0, 1, cond (1 == g0) e 0, 0⟩
  stN c n e := ⟨c.t, c.r + 1, c.d + n, c.A, c.B, c.r1, c.d1, c.z + 1,
    cond (c.z + 1 == g0) e c.k0, c.k1⟩
  stJ c n e := ⟨c.t + 1, 1, n, c.A + c.r, c.B + c.d, cond (c.t == 0) c.r c.r1,
    cond (c.t == 0) c.d c.d1, c.z + 1, cond (c.z + 1 == g0) e c.k0, cond (c.t == 0) e c.k1⟩
  keepN c := gateOK g0 n0 p0 n1 p1 c && Nat.ble (c.B + c.d) (20 - 5 * (T - 1)) &&
    Nat.ble (8 + 4 * (T - 1) + c.d + c.B) (c.r + c.A + bt (T - c.t) (20 - 5 * (T - 1) - c.B - c.d))
  keepJ c := gateOK g0 n0 p0 n1 p1 c && Nat.blt (c.t + 1) T && ordOK c &&
    Nat.ble (c.B + c.d) (20 - 5 * (T - 1)) &&
    Nat.ble (8 + 4 * (T - 1) + c.d + c.B)
      (c.r + c.A + bt (T - c.t - 1) (20 - 5 * (T - 1) - c.B - c.d))
  bad c U := gateOK g0 n0 p0 n1 p1 c && (c.t + 1 == T) && ordOK c &&
    Nat.ble (c.B + c.d) (20 - 5 * (T - 1)) && Nat.ble (8 + 4 * (T - 1) + c.d + c.B) (c.r + c.A) &&
    !deadB U

end K6
