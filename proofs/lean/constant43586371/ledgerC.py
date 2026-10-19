"""Ledger of the nested block levels written out part by part, exact fractions.

Selection on k symbols, completion at n = k + 1, h = n - 3.  Charge Q of a selection on k symbols multiplies by
(k - 1) under one transport (k -> k + 1); so does the number of loops without a row.  Cycles chosen at level n0
count (n - 4)!/(n0 - 4)! times at level n.  Finite bound (Pantone section 5 / Lean finite_bound, m = n - 2):
    L(n, a) = F3(n) + Q_n + h c_n + (a - 2) c_n + (n - 2 - a) min(c_n, (n-1)!/(a+1)!).
"""
from fractions import Fraction as Fr
from math import factorial as f

Q11, D11, BIG, GRP6 = 178080, 6048, 155, 288      # C on 11 symbols; long-walk cycles (n=12); (A) cycles (n=13)
A = Fr(61937, 120960)
# (Q, D, cycles, level n0 of the cycles, loops, m) per block
BLK = {"s103_old2_0": (370, 440, 4, 15, 1320, 10), "s103_old2_0@16": (370, 440, 26, 16, 1320, 10),
       "w103_0.6245_1": (320, 500, 4, 15, 1320, 10), "w103_0.4795_0": (240, 660, 4, 15, 1320, 10),
       # cycles chosen on 16 symbols (leanC/cyc16, blockcyc.py, Gurobi optimal: 20 each)
       "w103_0.6245_1@16": (320, 500, 20, 16, 1320, 10), "w103_0.4795_0@16": (240, 660, 20, 16, 1320, 10),
       "s133_0": (702, 988, 1, 18, 2730, 13), "w133_0": (598, 1105, 1, 18, 2730, 13),
       "s163_old2_0": (768, 2208, 6, 21, 4896, 16)}


def F3(n):
    return f(n) + f(n - 1) + f(n - 2)


def L(n, Qn, cn, a):
    return F3(n) + Qn + (n - 3) * cn + (a - 2) * cn + (n - 2 - a) * min(Fr(cn), Fr(f(n - 1), f(a + 1)))


def ledger(chain, verbose=True):
    """chain of block names, level j block sits above the loops without a row of level j-1 (level 1: above C.d11)
    at 14 + 3 (j - 1) symbols.  Returns (k, Q_k, c_{k+1}, parts) for the selection on k = 15 + 3 (len - 1) symbols."""
    J = len(chain)
    k = 14 + 3 * (J - 1) + 1            # selection size where the last block's empty loops are charts
    n = k + 1
    Q = Q11                              # on 11 symbols
    sym = 11
    empty = D11                          # loops without a row of the current deepest level, on `sym` symbols
    cyc = {"long walks (n=12)": BIG * f(n - 4) // f(8), "small walks (A) (n=13)": GRP6 * f(n - 4) // f(9)}
    copies = D11                         # number of copies of the next block
    for j, name in enumerate(chain):
        Qb, Db, cb, n0, loops, m = BLK[name]
        # transport three times to sym + 3: Q and empty loops multiply by (sym-1)(sym)(sym+1)
        mult = (sym - 1) * sym * (sym + 1)
        assert loops == mult, (name, loops, mult)
        Q = Q * mult + copies * Qb       # the empty loops of the previous level are replaced by blocks
        sym += 3
        assert n0 - 1 >= sym and (n0 - 4) <= n - 4
        cyc["block level %d %s: %d copies x %d cycles at n=%d" % (j + 1, name, copies, cb, n0)] = \
            copies * cb * f(n - 4) // f(n0 - 4)
        copies = copies * Db             # loops without a row of this level
    assert sym == k - 1
    Q = Q * (sym - 1)                    # one more transport; the deepest empty loops become charts (charge 0)
    cyc["charts above level %d loops without a row (z-free, n=%d)" % (J, n)] = copies
    c = sum(cyc.values())
    Qc, Cc = Fr(Q, f(n - 3)), Fr(c, f(n - 4))
    coef = Qc + Cc
    # cross-check by the value recursion of STATE section 6
    V = Fr(1)
    for name in reversed(chain):
        Qb, Db, cb, n0, loops, m = BLK[name]
        h0 = n0 - 3
        # cycles at n0 for a block on n0-1 symbols: chosen at the block's first completion level n0 = 15+3j (h0)
        # or one level later (26 at n=16 worth 26/13 per 12)
        lvl = 15 + 3 * (chain.index(name))
        w = Fr(cb * f(lvl - 4), f(n0 - 4)) * (lvl - 3)
        V = (Qb + w + Db * V) / loops
    alt = A - Fr(1, 60) * (1 - V)
    if verbose:
        print("chain %s: selection on %d symbols, n = %d" % (" + ".join(chain), k, n))
        print("  Q_%d = %d, Qcoef = Q/(n-3)! = %s" % (k, Q, Qc))
        for kk, v in cyc.items():
            print("  c part %-66s %d" % (kk, v))
        print("  c_%d = %d, Ccoef = c/(n-4)! = %s" % (n, c, Cc))
        print("  coefficient = %s = %.9f ; value recursion V1 = %s gives %s  %s" % (coef, float(coef), V, alt,
                                                                                  alt == coef))
        for nn in range(n, n + 3):
            Qn = Q * f(nn - 3) // f(n - 3)
            cn = c * f(nn - 4) // f(n - 4)
            assert Q * f(nn - 3) % f(n - 3) == 0 and c * f(nn - 4) % f(n - 4) == 0
            vals = sorted((L(nn, Qn, cn, a), a) for a in range(2, nn - 1))
            v, a = vals[0]
            print("  n = %d: Q = %d, c = %d, best a = %d, bound %s (exact %s) = %s ; a=9: %s" % (
                nn, Qn, cn, a, format(v.numerator // v.denominator, ","), v.denominator == 1, v,
                format(int(L(nn, Qn, cn, 9)), ",") if L(nn, Qn, cn, 9).denominator == 1 else L(nn, Qn, cn, 9)))
    return k, Q, c, coef, Cc


if __name__ == "__main__":
    r2 = ledger(["w103_0.6245_1", "s133_0"])
    assert r2[3] == Fr(43586371, 86486400)
    print()
    ledger(["s103_old2_0", "s133_0"])
    print()
    r2b = ledger(["s103_old2_0@16", "s133_0"])
    assert r2b[3] == Fr(3961457, 7862400) and r2b[4] == Fr(121207, 17297280)
    print()
    r2c = ledger(["w103_0.6245_1@16", "s133_0"])
    assert r2c[3] == Fr(8711159, 17297280) and r2c[4] == Fr(124711, 17297280)
    print()
    r3b = ledger(["w103_0.4795_0@16", "w133_0", "s163_old2_0"])
    assert r3b[3] == Fr(21736511, 43243200) and r3b[4] == Fr(56491, 8648640)
    print()
    r3 = ledger(["w103_0.4795_0", "w133_0", "s163_old2_0"])
    assert r3[3] == Fr(21751799, 43243200)
    print()
    ledger(["s103_old2_0@16", "w133_0", "s163_old2_0"])
    print()
    ledger(["s103_old2_0@16", "s133_0", "s163_old2_0"])


# ---------------------------------------------------------------- no seed (opt/const_limit), the Lean Stage arithmetic
# block: (nrows, nq, ncirc, nd, m) with ncirc = cycles per block in the stage's count (h * cycles at the block's own
# level, or cycles one level up), m = old letters (the block's h at its level is m + 2)
NSB = {"D73@13": (315, 126, 3, 189, 7), "B73@13": (147, 42, 6, 357, 7),
       "X103@16": (660, 240, 20, 660, 10), "W103@16": (820, 320, 20, 500, 10),
       "W133": (1625, 598, 15 * 1, 1105, 13), "W133@19": (1625, 598, 7, 1105, 13),
       "S133": (1742, 702, 15 * 1, 988, 13), "S133@19": (1742, 702, 11, 988, 13),
       "S163": (2688, 768, 18 * 6, 2208, 16), "S163@22": (2688, 768, 45, 2208, 16)}


def ledger_ns(chain, m0, verbose=True):
    """Stage(A0 with m0 letters, no rows, (m0-1)! pending loops), advance by each block, close: exactly the
    numbers of Stage.advance / Stage.close in Lean."""
    h = m0
    R, Q, c, P = 0, 0, 0, f(m0 - 1)
    for name in chain:
        nrows, nq, ncirc, nd, m = NSB[name]
        assert m == h
        R = (h + 3) * (h + 2) * (h + 1) * R + P * (h + 3) * nrows
        Q = (h + 3) * (h + 2) * (h + 1) * Q + P * (h + 3) * nq
        c = (h + 2) * (h + 1) * h * c + P * ncirc
        P = P * nd
        h += 3
    R, c = R + P * h, c + P
    assert R == f(h), (R, f(h))
    n = h + 3
    Qc, Cc = Fr(Q, f(h)), Fr(c, f(h - 1))
    if verbose:
        print("no seed, chain %s: closed on %d symbols, n = %d, R = %d! , Q = %d, c = %d" % (" + ".join(chain), h + 2, n, h, Q, c))
        print("  Qcoef %s, Ccoef %s, coefficient %s = %.9f" % (Qc, Cc, Qc + Cc, float(Qc + Cc)))
        for nn in (n, n + 1):
            Qn, cn = Q * f(nn - 3) // f(h), c * f(nn - 4) // f(h - 1)
            v, a = min((L(nn, Qn, cn, a), a) for a in range(2, nn - 1))
            print("  n = %d: best a = %d, bound %s (exact %s)" % (nn, a, format(v.numerator // v.denominator, ","), v.denominator == 1))
    return Q, c, Qc, Cc


if __name__ == "__main__":
    print()
    r = ledger_ns(["X103@16", "W133", "S163"], 10)
    assert r[0] == 39302075009433600 and r[1] == 727520258304000 and r[2] + r[3] == Fr(629507, 1441440) and r[3] == Fr(32759, 288288)
    r = ledger_ns(["D73@13", "W103@16", "S133@19"], 7)
    assert r[2] + r[3] == Fr(3853, 8736)
    r = ledger_ns(["B73@13", "X103@16", "W133@19", "S163@22"], 7)
    assert r[2] + r[3] == Fr(11117297, 27675648)
