# The coefficient of (n-3)! tends to 0: paper proof

2026-10-18. Every lemma below was checked numerically by `check_uniform.py`
(m = 5..61, with d0 = 0..m-1 and with random relabelled letters; log `logs/check_17_61.log`).

## 0. Statement

Theorem. For every rational ε > 0 there is N such that for every n ≥ N there is a word on n symbols that
contains every permutation of the n symbols as a factor and has length at most
n! + (n-1)! + (n-2)! + ε (n-3)!.

Explicitly (these are the choices of the Lean proof, `Uniform/Main.lean`): δ = min(ε, 1); t = an integer
> 40/δ and m0 = 2(t+6)+1; K = an integer > (m0+1)(4/δ)^6; a = m0 + 6K; r = an integer > 8/δ; M = an integer
> 2048 r^4/δ; N = a + 23 + 8r + M. The term a dominates: N ≈ 6K ≈ 6·81·4^6/δ^7 ≈ 2·10^6/δ^7 (with the least
admissible t and K). It is proved in Lean as `coefficient_tends_to_zero` (section 11).

The construction is the nested block method of `the no-seed construction` (Pantone's transport, completion and cycles;
the Lean `Stage` of `constant43586371`) with the simplest block family that still works: no seed, and above
every loop without a row on m old letters (m odd) one caterpillar walk W(m) of m(m+12) rows, its trails met
by one cycle; at even m the empty block.

## 1. Framework (as in constant43586371, unchanged)

A loop on m+3 letters is written as a list (its cyclic class matters). A row is (base, satellite 9, visible) with
visible = |base| (full, charge 0) or |base| - 2 (short, charge 2); head = first |base|-2 letters, tail = first
|base|-2 letters of base rotated left by visible+1; consecutive rows must satisfy tail = next head.

A block above the canonical loop d0 (m old letters, nodup) with tokens t1, t2, t3 must give (constant43586371 `BlockOK`
plus a cycle condition): closed walks of rows whose bases are permutations of t3 t2 t1 d0; a list of loops without
a row; every loop of `above3T t1 t2 t3 d0` (the L = m(m+1)(m+2) loops with old letters in the cyclic order d0) is
a row base or a loop without a row (up to rotation); the walk, written h/g times, transported from g start ports
lists every transported row once; cycles (length h = m+2, no repeated letter, letters in 10 :: alphabet) that meet
the completion of every walk from every port. `Stage.advance` and `Stage.close` (Lean, constant43586371) do the rest.
Exactness needed for `Closed.word` (R = h! rows at the top): rows + loops without a row = L in every block,
which needs the loops of the walk to be pairwise distinct.

## 2. The walk W(m), m odd, m ≥ 5

Old letters d0 (a nodup list of length m), tokens A = t1, B = t2, C = t3. Period k (0 ≤ k < m) uses
e = rot(d0, 2k) = [e0, e1] ++ mid ++ [el] (|mid| = m-3) and the four arrangements (lists of length m+2)

    w = [e1] ++ mid ++ [A, el, e0, C]        u = mid ++ [A, el, e0, e1, B]
    y = [e0, e1, B] ++ mid ++ [el, C]        v = [e1, B] ++ mid ++ [el, e0, A].

A sweep (s, T, J) is the list of rows with bases rot(s, j) ++ [T] for j = m+1, 0, 1, ..., J-1, all full except the
last (j = J-1), which is short. Period k = sweep(w, B, 2) ++ sweep(u, C, m) ++ sweep(y, A, 2) ++ sweep(v, C, 4):
3 + (m+1) + 3 + 5 = m+12 rows, 4 of them short. W(m) = period 0 ++ period 1 ++ ... ++ period m-1.
This is const_limit's W(m, 1, (A,B,C), 0) started one row later (checked literally for m ≤ 61).

## 3. Lemma 1 (closed trail)

(a) *Full row.* For |x| = m+2 the full row with base x ++ [T] has tail = drop 1 x, and every row with base
y ++ [T'] has head = take (m+1) y. Hence a full row rot(s, j) ++ [T] is followed compatibly by rot(s, j+1) ++ [T]
(take (m+1) (rot(s, j+1)) = drop 1 (rot(s, j))); for j = m+1, rot(s, m+2) = s = rot(s, 0).
(b) *Short row.* The short row with base x ++ [T] has tail = T :: take m x. The first row of a sweep (s', T') has
head = take (m+1)(rot(s', m+1)) = last(s') :: take m s'. So the last row of sweep (s, T, J) is followed compatibly by
the first row of sweep (s', T') iff last(s') = T and take m s' = take m (rot(s, J-1)).
(c) The four transitions of a period, with the explicit rotations
rot(w,1) = mid ++ [A, el, e0, C, e1], rot(u, m-1) = [e0, e1, B] ++ mid ++ [A, el], rot(y,1) = [e1, B] ++ mid ++ [el, C, e0],
rot(v, 3) = drop 1 mid ++ [el, e0, A, e1, B, mid0]:
w→u (last u = B, take m u = mid ++ [A, el, e0]), u→y (last y = C, take m y = [e0, e1, B] ++ mid),
y→v (last v = A, take m v = [e1, B] ++ mid ++ [el]), and v → w of period k+1, whose old letters are
rot(e, 2) = mid ++ [el, e0, e1] = [mid0, mid1] ++ (drop 2 mid ++ [el, e0]) ++ [e1]: last w' = C,
take m w' = drop 1 mid ++ [el, e0, A, e1].
(d) Period m equals period 0 since rot(d0, 2m) = d0. So W(m) is a closed trail.

## 4. Lemma 2 (alphabet, counts)

Every base is a rotation of s ++ [T] with s ++ [T] a permutation of e ++ [A, B, C], hence of t3 t2 t1 d0; letters
are distinct and differ from 9. |W| = m(m+12), total charge 2·4m = 8m. signed excess (rows minus charge) = m(m+4).

## 5. Lemma 3 (the loops of W are distinct)

*C-normal form.* Every base b is a rotation of X ++ [C] with X explicit (C ∉ X):

| rows of period k | X |
|---|---|
| sweep w (j = m+1, 0, 1) | a1, rot(a1, m+1), rot(u, m), with a1 = [e1] ++ mid ++ [A, el, e0, B] |
| sweep u (j = m+1, 0..m-1) | rot(u, j) |
| sweep y (j = m+1, 0, 1) | a2, rot(a2, m+1), rot(v, m), with a2 = [e0, e1, B] ++ mid ++ [el, A] |
| sweep v (j = m+1, 0, 1, 2, 3) | rot(v, j) |

So the X of the rows of period k are: all m+2 rotations of u, rotations 0 and m+1 of a1 and of a2, rotations
m, m+1, 0, 1, 2, 3 of v. Two lists P ++ [C], P' ++ [C] (no repeated letter) are rotations of each other only if
P = P'. Hence the loops of W are distinct iff these X are distinct as lists.

*Invariants.* For a list X containing A and B let gA(X) = the letter after A in X with B deleted (cyclically),
gB(X) = the letter after B in X with A deleted. Both are invariant under rotation of X. With e_i = d0[(i+2k) mod m]:

| arrangement | gA | gB | gB index - gA index |
|---|---|---|---|
| u_k | el = d0[2k-1] | e2 = d0[2k+2] | 3 |
| a1_k | el = d0[2k-1] | e1 = d0[2k+1] | 2 |
| a2_k | e0 = d0[2k] | e2 = d0[2k+2] | 2 |
| v_k | e1 = d0[2k+1] | e2 = d0[2k+2] | 1 |

(indices mod m). Suppose rot(s, j) = rot(s', j') for arrangements s of period k, s' of period k'. Then gA, gB agree,
so the index differences agree mod m; for m ≥ 5 the values 1, 2, 3 are distinct mod m, so the families agree
except possibly a1 / a2. Within one family gA gives 2k ≡ 2k' (mod m), hence k = k' (m odd, 0 ≤ k, k' < m), s = s',
and j = j' because a list without repeated letters has distinct rotations (0 ≤ j, j' < m+2).
For a1_k against a2_k' (rows with X ∈ {a1, rot(a1, m+1)} and {a2, rot(a2, m+1)}): equal gA means 2k-1 ≡ 2k' (mod m);
the last letters are B or e0_k = d0[2k] against A or el_k' = d0[2k'-1]; d0[2k] = d0[2k'-1] would give 2k ≡ 2k'-1,
and with 2k-1 ≡ 2k' this gives 2 ≡ 0 (mod m), impossible. So all m(m+12) loops of W are distinct.

## 6. Lemma 4 (above3T, the loops without a row)

Each arrangement is s = rot(Y, κ) with Y = rot(rot(d0, i) ++ [A], ι) ++ [B]:
u: (i, ι, κ) = (2k+m-1, 3, 0); a1: (2k+m-1, 2, 0); a2: (2k, 2, m-1); v: (2k+1, 1, m) (i mod m).
Hence every row base is a rotation of rot(Y, κ + j) ++ [C], an element of above3T A B C d0 (indices reduced mod m,
m+1, m+2). above3T has exactly L entries, pairwise distinct and pairwise not rotations of each other (each ends
with C; position of B gives the outer index, then the position of A, then the rotation of d0).
The loops without a row are the entries of above3T that are not rotations of a row base. By Lemma 3 the map
row → its entry is injective, so there are exactly L - m(m+12) of them.

## 7. Lemma 5 (ports)

A full row moves a completion port q to q + h - 1 ≡ q - 1, a short row to q + 1 (mod h = m+2). Over W:
-(m(m+8)) + 4m = -m(m+4) = 4 - (m+2)^2 ≡ 4 (mod m+2). Since m+2 is odd, i ↦ q + 4i (mod m+2) is a bijection of
{0..m+1}: the walk written h times, transported from port 0 alone, passes every port once (one item (W, g = 1)),
and h divides h·(signed excess) trivially. So the block's trails one level up are the h-fold walk transported once.

## 8. Lemma 6 (one cycle)

Completion of the first row r0 of W (full, base b0) at port 0 starts with the row of base 10 :: b0, whose head is
c0 = 10 :: take (m+1) b0: m+2 distinct letters containing 10. The completion of the h-fold walk from any port j
passes port 0 at the start of some lap (Lemma 5), so it contains that row; c0 meets it (SafeIncidence). One cycle
at the block's own level; extended once it costs h = m+2 loop units.

## 9. Lemma 7 (values) and the limit

Normalise a stage on a+1 letters (a = |A0|) by x = Q/a! + c/(a-1)! (charge and cycles so far) and p = P/(a-1)!
(fraction of loops still pending); R + aP = a! throughout. No seed: x = 0, p = 1. A walk block at odd a = m:
x' = x + p(8m + (m+2))/L, p' = p(L - N)/L with N = m(m+12). An empty block (even a): x' = x, p' = p. At the
close every pending loop becomes a chart: coefficient κ = x + p, cycle ratio γ = (c+P)/(a-1)! ≤ κ.

* (I1) x + (10/m0) p ≤ 10/m0 stays true: the walk step adds p[(9m+2) - (10/m0) m(m+12)]/L ≤ 0 since m ≥ m0.
* (I2) at the walk levels a = m0 + 6i, p^6 (a+1) does not increase from one to the next: p is multiplied by
  1 - N/L ≤ a/(a+1) (because (a+12)/((a+1)(a+2)) ≥ 1/(a+1)), and a^6 (a+7) ≤ (a+1)^7.

In naturals (as in Lean, `Inv` and `Arith.lean`): (I1) R + aP = a!, (I2) m0 Q + m0 a c + 10 a P ≤ 10 a!,
(I3) P^6 (a+1) ≤ (m0+1) ((a-1)!)^6. After K pairs (walk, empty) the level is a = m0 + 6K, and at the close
κ = (Q + a(c+P))/a! = (Q + ac)/a! + p with (Q + ac)/a! ≤ 10/m0 and p = aP/a!, p^6 (a+1) ≤ m0+1; γ = a(c+P)/a! ≤ κ.
With m0 > 40/δ and K > (m0+1)(4/δ)^6 (so a + 1 > (m0+1)(4/δ)^6): p ≤ δ/4 and κ ≤ δ/2 ≤ 1/2. The closed level
gives, for every n ≥ a+3 and every 2 ≤ a' ≤ n-2, words of length
F3(n) + κ(n-3)! + (a'-2)c' + (n-2-a') min(c', (n-1)!/(a'+1)!) with c' = γ (n-4)! (constant43586371 `Closed.all`,
`Closed.word`). The choice a' = ⌊(n-2)/r⌋ with r > 8/δ and n-2 ≥ 2048 r^4/δ makes the two error terms at most
(2/r + 512 r^4/(n-2))(n-3)! ≤ (δ/2)(n-3)! (Pantone's `floor_parameter_bounds`, `factorial_error_le`, as in
constant43586371's GenericBounds). Total: F3(n) + δ (n-3)! ≤ F3(n) + ε (n-3)!. ∎

## 11. Lean (`lean/SuperpermutationUpperBound43586371/Uniform/`)

| file | content |
|---|---|
| `Walk.lean` | rows, sweeps, periods `Pd`, `walk d0 A B C`; `walk_closed`, `walk_basedOn`, `walk_length`, `walk_charge` (Lemmas 1, 2) |
| `Canon.lean` | `canon` (rotation ending with a letter), `above3T` nodup / length / perm, `count_uncovered` |
| `Distinct.lean` | arrangements `arr 0..3`, invariants `key1`, `key2`, C-normal forms `canon_rowAt`, `arr_yform` |
| `WalkLoops.lean` | `Xinj`, `walk_canon_nodup`, `walk_canon_mem`, `walk_dloops_length` (Lemmas 3, 4) |
| `Ports.lean` | `walk_exit` (shift 4), `walk_orbit_perm`, `cycle0`, `walk_safe` (Lemmas 5, 6) |
| `Block.lean` | `walkData`, `walkData_ok`, `walk_safeB`, `emptyData`, `famS` (a `BlockFam` for every odd m) |
| `Arith.lean`, `Iterate.lean` | the invariants (I1)-(I3), `double_step`, `stages`, `closed_level` (Lemma 7) |
| `Bounds.lean`, `Main.lean` | `finite_of_closed`, `eventual_of_finite`, `small_coefficient`, `coefficient_tends_to_zero` |

## 10. Remarks

* Only odd levels carry a walk, so p decays like (m0/a)^{1/6}; even levels (2 start ports, 2 cycles) or the full
  R(m) families would give (m0/a)^{1/3} or ~8/a but need more proof (disjointness for R(m)).
* The numbers: m0 = 11 gives κ ≈ 0.49 after 400 levels (n ≈ 1214); the method is a limit statement, not a good
  finite bound.
