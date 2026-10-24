# Caterpillar blocks at every level: paper proof (constant43586371)

2026-10-19. Checked numerically by `../constant43586371_work/checkR.py` for m = 5..100 (logs in
`../constant43586371_work/logs/`); the values by `../constant43586371_work/vals.py`.

## 0. The block R'(m) and why it differs from the earlier family's R(m) at even m

Old letters d0 (length m, no repetition), tokens t1, t2, t3 (t1 = the letter added one level above d0).

    G(m) = { g : g ≥ 1, g ≡ 1 (mod 3), 2g ≤ m - 5 }
    walks W(m, g, σ, s):  g ∈ G(m),  σ ∈ {id, swap},  s ∈ {0} (m odd) or {0, 1} (m even)
    roles (A, B, C) = (t1, t2, t3) for σ = id, (t2, t1, t3) for σ = swap.

For odd m this is exactly the earlier family's R(m) (2 walks per g). For even m the earlier family uses all six token orders
with g ≡ 1 (mod 4); here every walk has C = t3 and both shifts s, with g ≡ 1 (mod 3). Reason: with one common
token C the disjointness proof is one invariant (section 4), while the six orders need a parity case split over
36 order pairs. The cost: R'(m) has 2|G(m)| m (m+12) rows at every m (≈ m³/3, coverage → 1/3); the earlier family's even
R(m) has ≈ 3m³/8. Value: with the shared cycles of section 6, coefficient 0.1087 at n = 100 and 0.1022 at n = 106
(the earlier family, with its cycle rule: 0.10 at n = 106).

## 1. The walk

Period offset o = s + 2k (k < P, P = m for odd m, m/2 for even m). The old letters of the period, read from
index o + 2: O = rot(d0, o + 2) = mid1 ++ q with |mid1| = m - 2 - g ≥ 2 and |q| = g + 2 ≥ 3. Four arrangements
(lists of length m + 2) and sweeps (s, T, J) as in `PROOF.md` (rows rot(s, j) ++ [T] for j = m+1, 0, ..., J-1, the
last one short):

    w = [q_last] ++ mid1 ++ [A] ++ q.dropLast ++ [C]     token B, J = 2
    u = mid1 ++ [A] ++ q ++ [B]                           token C, J = m + 1 - g
    y = q.drop 1 ++ [B] ++ mid1 ++ [q0, C]                token A, J = 2
    v = q.drop 2 ++ [B] ++ mid1 ++ [q0, q1, A]            token C, J = g + 3

3 + (m + 2 - g) + 3 + (g + 4) = m + 12 rows per period, 4 short. For g = 1, s = 0 this is `PROOF.md`'s walk.
It equals the earlier family's W(m, g, T, s) started one row later (checked for every walk of every block, m ≤ 100).

Lemma 1 (closed trail). Inside a sweep as in `PROOF.md`. The last row rot(s, J-1) ++ [T] of a sweep is followed
by the first row of the next sweep (s', T') iff last(s') = T and take m s' = take m (rot(s, J-1)):
w→u: rot(w, 1) = mid1 ++ [A] ++ q.dropLast ++ [C, q_last], take m = mid1 ++ [A] ++ q.dropLast = take m u;
u→y: rot(u, m - g) = q.drop 1 ++ [B] ++ mid1 ++ [A, q0], take m = q.drop 1 ++ [B] ++ mid1 = take m y;
y→v: rot(y, 1) = q.drop 2 ++ [B] ++ mid1 ++ [q0, C, q1], take m = take m v;
v→w': with O' = rot(O, 2) (offset o + 2): mid1' = mid1.drop 2 ++ q.take 2, q' = q.drop 2 ++ mid1.take 2, and
rot(v, g + 2) = mid1.drop 1 ++ [q0, q1, A] ++ q.drop 2 ++ [B, mid1_0]; take m of both is
mid1.drop 1 ++ [q0, q1, A] ++ q.drop 2. After P periods O returns (2P ≡ 0 mod m).

Lemma 2. Rows are permutations of t3 :: t2 :: t1 :: d0; P (m + 12) rows; charge 8P.

## 2. C-normal forms

Every base is a rotation of X ++ [C] with C ∉ X; per period (with a1 = [q_last] ++ mid1 ++ [A] ++ q.dropLast ++ [B],
a2 = q.drop 1 ++ [B] ++ mid1 ++ [q0, A]):

| family | rows | X |
|---|---|---|
| a1 | w-sweep j = m+1, 0 | a1, rot(a1, m+1) |
| u | w-sweep j = 1; u-sweep | rot(u, m); rot(u, j), j ∈ {m+1, 0, ..., m-g} |
| a2 | y-sweep j = m+1, 0 | a2, rot(a2, m+1) |
| v | y-sweep j = 1; v-sweep | rot(v, m); rot(v, j), j ∈ {m+1, 0, ..., g+2} |

## 3. Keys

For a list X over d0, A, B (no repetitions, old letters in the cyclic order d0): κ_A(X) is the i (mod m) with
"X without B, rotated to end with A" = rot(d0, i) ++ [A]; κ_B similarly. Both are invariant under rotation of X.
Relative to o:

| family | κ_A - o | κ_B - o | κ_B - κ_A |
|---|---|---|---|
| a1 | m - g | 1 | g + 1 |
| u | m - g | 2 | g + 2 |
| a2 | m + 1 - g | 2 | g + 1 |
| v | m + 2 - g | 2 | g |

## 4. Lemma 3: all rows of R'(m) are distinct

Rows are equal iff their bases are rotations of each other iff their X (all w.r.t. the same C = t3) are equal.
Let X come from (g, σ, o, f, j) and X' from (g', σ', o', f', j'). Equal X give equal κ_{t1}, κ_{t2}.
Put δ = κ_{t2} - κ_{t1} (mod m): δ = κ_B - κ_A ∈ D_g = {g, g+1, g+2} for σ = id and δ = -(κ_B - κ_A) for σ = swap.
Since 2g ≤ m - 5, D_g ⊂ [1, (m-1)/2] and -D_g ⊂ [(m+1)/2, m-1]; for g ≢ g' (both ≡ 1 mod 3) D_g ∩ D_g' = ∅.
So σ = σ', g = g' and the families have the same κ_B - κ_A. Then κ_A fixes o mod m, which fixes (s, k) (odd m:
2k ≡ 2k' with k, k' < m; even m: s + 2k ≡ s' + 2k' with both < m). Families with the same difference and the same
o are equal, except a1 / a2 (difference g + 1), which give o ≡ o' + 1; there the last letters of X are B or
d0[o] (a1) against A or d0[o' + m - g] (a2), and d0[o] = d0[o' - g] would give g ≡ -1 (mod m), impossible.
Same (g, σ, o, f): j = j' because a list without repetitions has distinct rotations (0 ≤ j < m + 2).

## 5. Lemma 4: loops without a row

Every X above is (old letters in the cyclic order d0, plus t1, t2), hence (general lemma) of the form
rot(rot(rot(d0, i) ++ [t1], j) ++ [t2], k) with i < m, j < m+1, k < m+2, so X ++ [t3] ∈ above3T. With Lemma 3:
exactly L - 2|G(m)| m (m+12) loops of above3T are not rotations of row bases.

## 6. Lemma 5 (ports) and Lemma 6 (shared cycles)

A full row moves a port by h - 1, a short row by 1 (h = m + 2); per period (m + 8)(h - 1) + 4 ≡ -2 (mod h).
Odd m: P = m periods, shift -2m ≡ 4; m + 2 odd: the walk written h times from port 0 passes every port once
(item (W, 1)). Even m: P = m/2, shift -m ≡ 2; ports 0 and 1 start the two orbits (item (W, 2), written h/2 times);
h | (h/2)·(signed excess) because the signed excess P(m + 4) is even.

Cycles: for τ ∈ {t1, t2}, i0 ∈ I, ε ∈ E: c(τ, i0, ε) = 10 :: rot(rot(d0, i0) ++ [τ], ε), with I = E = {0} for odd m
(2 cycles) and I = E = {0, 1} for even m (8 cycles). For the walk (g, σ, s) let τ = A, i0 = 0 (odd m) or
(s + g) mod 2 (even m), and k the period with o + m - g ≡ i0 (mod m) (exists: odd m since 2 is invertible; even m
since o ≡ s and i0 ≡ s - g mod 2). Its u-sweep row j = 0 (index k(m+12) + 4 of the walk) is full with base
u ++ [C]; Y = u.dropLast = mid1 ++ [A] ++ q, and q ++ mid1 ++ [A] = rot(d0, o + m - g) ++ [A], so
rot(Y, m - 1 - g + ε) = rot(rot(d0, i0) ++ [A], ε). The completed row at port p has head Y[0..p) ++ [10] ++ Y[p..],
a rotation of 10 :: rot(Y, p); at p = m - 1 - g + ε (≤ m) it lies on c(A, i0, ε).
The completion of the h-fold (h/2-fold) walk from port j completes this row at the ports j + 4t + π (j + 2t + π)
mod h, t over the passes, π the prefix shift of the row: all ports for odd m; for even m all ports ≡ j + π ≡ j
(mod 2), since every row shifts by an odd amount and the row's index is even. Choose ε ≡ j - (m-1-g) (mod 2).
So the cycles meet every trail from every port.

## 7. Lemma 7: values

Per level: N = 2|G| m (m+12) rows, charge 16|G| m, cycles (m+2)·(2 or 8) in loop units (none if G = ∅), D = L - N.
With x = Q/a! + c/(a-1)!, p = P/(a-1)!: x' = x + p (Q_b + C_b)/L, p' = p D/L; the closed level after K levels from
m0 has coefficient κ(m0, K) = x + p, computed exactly by the recursion on (R, Q, c, P) that `Stage.advance`
performs (Lean: `cntR`, `kappaR`, `gammaR`). For every n ≥ m0 + 3K + 3 and 2 ≤ a ≤ n - 2 the word has length at
most F3(n) + κ (n-3)! + (a-2)γ(n-4)! + (n-2-a) min(γ (n-4)!, (n-1)!/(a+1)!) with γ = (c+P)/(A-1)!, A = m0 + 3K.
Exact values (`../bound_R.py N`, minimised over m0, K, a): 0.3059 (N = 40), 0.2015 (60), 0.1103 (100),
0.1031 (106).

## 8. Lemma 8: the rate 9/n

For a ≥ 49: |G(a)| ≥ ⌊(a-7)/6⌋ + 1 ≥ 8 (the g = 3i+1 with 6i + 7 ≤ a), N = 2|G| a (a+12), charge 16|G| a,
cycles ≤ 8 (a+2). Hence 4N ≥ L (from 6|G| ≥ a - 6) and 2(charge + cycles)·a ≤ 17 N (from |G| ≥ 8). With
xc = c/(A-1)!: for m0 ≥ 49 and every K,
x + (17/(2 m0)) p ≤ 17/(2 m0),  p ≤ (3/4)^K,  xc ≤ 8K/m0²  (induction; the step of xc adds ≤ 8/(a(a+1))).
With a = 2 the finite bound is ≤ F3(n) + (κ + γ)(n-3)! and κ + γ = x + xc + 2p ≤ 17/(2 m0) + 2(3/4)^K + 8K/m0².
Choose L = ⌊log2 n⌋, K = 5L, m0 = n - 3 - 3K. For n ≥ 2^14: 64(15L + 3) ≤ 2^L ≤ n (induction from L = 14), so
64 m0 ≥ 63 n and 960 L ≤ n; (3/4)^{5L} ≤ (1/4)^L < 4/n² (since n < 2^{L+1}). Then
17/(2m0) ≤ 544/(63n), 8K/m0² ≤ (1/20)/n, 2(3/4)^K ≤ (1/1000)/n, total ≤ 8.69/n ≤ 9/n.
