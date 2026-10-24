"""tabs15.py (agent n7-15map) - the capacity tables for defect 15 on 7 symbols, in three tiers.  Nothing is searched here.

All tables are indexed by the exact number of holes x.
  P[s][x]  rows of a sequence with exactly s links of weight 4 (others weight 3) and x holes; P[0] = M (chains)
  PR[x]    rows of a ring with x holes

Tiers
  LEAN  the tables of the Lean proof of 5,899 (tab5899.txt, "set B"; a file of mine, not in this repository): proved upper bounds.
        M to 84, P_s to 84 - 6 s (s = 1..5), PR to 77.
  CAP   the best upper bounds computed by programs so far:
        M   caps.txt of the ring ladder (a file of mine, not in this repository; n7-cover, C and Rust; exact to 58, 61 by the referee; x + 44 at 73..75)
            lowered to the referee's exact values at 59..61
        P_s set B (the caps of lbsmall with its ladders at the top), s = 1..5
        PR  exact to 69 (lbsmall ring/pr_table72.txt = referee PR7.txt), then min(set B, M)
  LOW   values known to be ATTAINED by an object (lower bounds), -1 where nothing is known:
        M to 61 (referee M7ref61.txt), PR to 69, P_1 to 56, P_2 to 46, P_3 to 44, P_4 to 39
        (lbsmall lk/ex_row.txt, family (R), link cost at most s; lk/caps_blk_final.txt rows 1 and 4 for the part
        "(B) only" of LINKS_D14.md section 3: these are attained in family (B), which is part of (R)).
        A LOW entry of P_s is the number of rows of a linked path with link cost AT MOST s.

Beyond the last entry of a table, in tiers LEAN and CAP, the closure bounds (paper, two lines each):
  (cl1) cut a sequence after the first row at which the number of holes so far is >= a: the prefix has d holes,
        a <= d <= a + 4 (a row has at most 5 holes), and the two parts are sequences with sA + sB = s or s - 1 links:
        P_s(x) <= max_{a <= d <= a+4} max_{sA+sB in {s, s-1}} P_sA(d) + P_sB(x - d)      for every a with 1 <= a <= x - 5
  (cl2) cut at a link of weight 4 (s >= 1):  P_s(x) <= max_{sA+sB = s-1, d} P_sA(d) + P_sB(x - d)
  PR(x) <= M(x).
"""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
OPT = os.path.normpath(os.path.join(HERE, "..", "..", ".."))
XMAX = 96
SMAX = 16
NEG = -1


def read_named(fn):
    T = {}
    for line in open(fn):
        if ":" in line and not line.startswith("#"):
            k, v = line.split(":")
            T[k.strip()] = [int(x) for x in v.split()]
    return T


def ints(fn):
    return [int(x) for x in open(fn).read().split()]


def close(P, base_len):
    """extend P[s] (lists) to x = 0..XMAX for s = 0..SMAX by (cl1), (cl2).  base_len[s] = number of given entries."""
    out = [list(P[s][:base_len[s]]) if s < len(P) else [] for s in range(SMAX + 1)]
    for x in range(0, XMAX + 1):
        for s in range(0, SMAX + 1):
            if x < len(out[s]):
                continue
            assert x == len(out[s])
            best = None
            # (cl2)
            if s >= 1:
                b = 0
                for sA in range(0, s):
                    sB = s - 1 - sA
                    for d in range(0, x + 1):
                        v = out[sA][d] + out[sB][x - d]
                        if v > b:
                            b = v
                best = b
            # (cl1)
            for a in range(1, x - 4):
                b = 0
                for d in range(a, a + 5):
                    for tot in (s, s - 1):
                        if tot < 0:
                            continue
                        for sA in range(0, tot + 1):
                            v = out[sA][d] + out[tot - sA][x - d]
                            if v > b:
                                b = v
                if best is None or b < best:
                    best = b
            if best is None:          # s = 0 and x <= 6: cannot happen, the base covers it
                raise ValueError((s, x))
            out[s].append(best)
    return out


class Tier:
    def __init__(self, name, P, base_len, PR, pr_len):
        self.name = name
        self.base_len = list(base_len) + [0] * (SMAX + 1 - len(base_len))
        self.P = close(P, self.base_len)
        self.M = self.P[0]
        self.pr_len = pr_len
        self.PR = [PR[x] if x < pr_len else self.M[x] for x in range(XMAX + 1)]

    def given(self, s, x):
        return x < self.base_len[s]


def load():
    B = read_named(os.path.join(OPT, "lb", "lean", "scratchP", "tab5899.txt"))
    PB = [B["M"]] + [B["P%d" % s] for s in range(1, 6)]
    lean = Tier("LEAN", PB, [85, 79, 73, 67, 61, 55], B["PR"], 78)

    Mc = ints(os.path.join(OPT, "n7", "cover", "ladR15", "caps.txt"))
    assert len(Mc) == 85
    Mref = ints(os.path.join(OPT, "n7", "referee", "M7ref61.txt"))
    assert len(Mref) == 62 and Mref[:59] == Mc[:59]
    for x in range(59, 62):
        assert Mref[x] <= Mc[x]
        Mc[x] = Mref[x]
    for x in range(85):
        assert Mc[x] <= B["M"][x], x
    pr = ints(os.path.join(OPT, "lb", "small", "ring", "pr_table72.txt"))
    assert pr == ints(os.path.join(OPT, "n7", "referee", "PR7.txt")) and len(pr) == 70
    assert pr[:64] == B["PR"][:64]
    PRc = [pr[x] if x < 70 else min(B["PR"][x], Mc[x]) for x in range(78)]
    cap = Tier("CAP", [Mc] + PB[1:], [85, 79, 73, 67, 61, 55], PRc, 78)

    ex = {int(k): v for k, v in read_named(os.path.join(OPT, "lb", "small", "lk", "ex_row.txt")).items()}
    blk = {int(k): v for k, v in read_named(os.path.join(OPT, "lb", "small", "lk", "caps_blk_final.txt")).items()}
    low = {"M": Mref, "PR": pr,
           1: ex[1] + blk[1][47:57], 2: ex[2], 3: ex[3], 4: blk[4][:40]}
    assert len(low[1]) == 57 and low[1][47:] == [87, 88, 90, 91, 92, 94, 95, 96, 98, 99]
    for s in (1, 2, 3):
        for x, v in enumerate(ex[s]):
            assert v <= PB[s][x], (s, x)
    return lean, cap, low


def lowP(low, s, x):
    """attained rows of a linked path with link cost at most s and at most x holes (-1: nothing known)"""
    best = NEG
    for t in range(0, s + 1):
        tab = low["M"] if t == 0 else low.get(t)
        if tab is None or x < 0:
            continue
        v = tab[min(x, len(tab) - 1)]        # an object with fewer holes is an object with at most x holes
        if v > best:
            best = v
    return best


def lowPR(low, x):
    if x < 0:
        return NEG
    return low["PR"][min(x, len(low["PR"]) - 1)]


if __name__ == "__main__":
    lean, cap, low = load()
    for T in (lean, cap):
        print(T.name)
        for s in range(0, 8):
            print("  P%d given to %d; x=%d..90:" % (s, T.base_len[s] - 1, max(T.base_len[s] - 3, 0)),
                  " ".join(str(v) for v in T.P[s][max(T.base_len[s] - 3, 0):91 - 6 * s]))
        print("  PR 60..83:", " ".join(str(v) for v in T.PR[60:84]))
