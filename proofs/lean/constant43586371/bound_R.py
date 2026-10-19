"""bound_R.py N [m0] - the exact Lean upper bound at size N from finite_boundR (constant43586371, UniR/RMain.lean).

finite_boundR m0 K n a: for m0 >= 11, n >= m0 + 3K + 3, 2 <= a <= n - 2 there is a covering word of length at most
    ubound(kappaR m0 K, gammaR m0 K, n - 2, a)
  = F3(n) + kappa (n-3)! + (a-2) gamma (n-3)!/(n-3) + (n-2-a) min(gamma (n-3)!/(n-3), (n-1)!/(a+1)!),
with kappa, gamma computed from the count recursion cntR (Lean's definitions copied literally below).
The script minimises over m0 (K as large as allowed, which is always best) and a, unless m0 is given.
"""
import sys
from fractions import Fraction as Fr
from math import factorial as fact


def Gl(m):
    return [g for g in range(m) if g % 3 == 1 and 2 * g + 5 <= m]


def Sl(m):
    return [0] if m % 2 == 1 else [0, 1]


def Pm(m):
    return m if m % 2 == 1 else m // 2


def Dl_len(m):
    return len(Gl(m)) * 2 * len(Sl(m))


def rowsR(m):
    return Dl_len(m) * (Pm(m) * (m + 12))


def chargeR(m):
    return Dl_len(m) * (8 * Pm(m))


def ncycR(m):
    return 2 if m % 2 == 1 else 8


def cntR(m0, K):
    R, Q, c, P = 0, 0, 0, fact(m0 - 1)
    for k in range(K):
        a = m0 + 3 * k
        R, Q, c, P = ((a + 3) * ((a + 2) * ((a + 1) * R)) + P * ((a + 3) * rowsR(a)),
                      (a + 3) * ((a + 2) * ((a + 1) * Q)) + P * ((a + 3) * chargeR(a)),
                      (a + 2) * ((a + 1) * (a * c)) + P * ((a + 2) * ncycR(a)),
                      P * (a * ((a + 1) * (a + 2)) - rowsR(a)))
    return R, Q, c, P


def kappa_gamma(m0, K):
    R, Q, c, P = cntR(m0, K)
    A = m0 + 3 * K
    assert R + P * A == fact(A)
    gamma = Fr(c + P, fact(A - 1))
    return Fr(Q, fact(A)) + gamma, gamma


def ubound(kappa, gamma, m, a):
    F3 = fact(m + 2) + fact(m + 1) + fact(m)
    cc = gamma * fact(m - 1) / (m - 1)
    return F3 + kappa * fact(m - 1) + (a - 2) * cc + (m - a) * min(cc, Fr(fact(m + 1), fact(a + 1)))


def best(N, m0s):
    m = N - 2
    out = None
    for m0 in m0s:
        K = (N - 3 - m0) // 3
        if K < 0:
            continue
        kap, gam = kappa_gamma(m0, K)
        for a in range(2, m + 1):
            b = ubound(kap, gam, m, a)
            if out is None or b < out[0]:
                out = (b, m0, K, a, kap, gam)
    return out


def main():
    N = int(sys.argv[1])
    m0s = [int(sys.argv[2])] if len(sys.argv) > 2 else range(11, N - 2)
    b, m0, K, a, kap, gam = best(N, m0s)
    F3 = fact(N) + fact(N - 1) + fact(N - 2)
    print("N = %d: m0 = %d, K = %d levels (closed level on %d letters), a = %d" % (N, m0, K, m0 + 3 * K + 1, a))
    print("kappa = %.6f, gamma = %.3e" % (float(kap), float(gam)))
    print("(bound - F3(N)) / (N-3)! = %.6f   (bound has %d digits)" % (float((b - F3) / fact(N - 3)),
                                                                          len(str(int(b)))))


if __name__ == "__main__":
    main()
