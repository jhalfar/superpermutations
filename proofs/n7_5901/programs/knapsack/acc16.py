"""acc16.py TIER [nopairs] (agent n7-d16map) - the accounting of defect 16 on 7 symbols, all excess cases.

Own program (shares only the table reader tabs15.py, a copy of the map of 15).  Notation of STATE.md section 2.
  need: sum v >= 40 within sum w <= 96  (ACC16).  eps <= 2 (Lemma EPS16).
Tiers (tables of upper bounds, rows of a sequence with exactly s links and x holes; PR for rings):
  CAP  tier CAP of the map of 15 (what the coordinator's acc16_CAP.log used)
  TP   table T' of PROOF_5900: CAP + M(76) <= 120 + P_s(x) <= x + 44 + 5 s for s = 5..8, closed again (min-closure)
  D    TP + Corollary K of defect 15 (val <= 44 within weight 90, every s), closed again.  Valid when K0, K1, K2 end.
  D16  D + the kernel-alone statement of defect 16 (val <= 39 within weight 96): what is left if that were proved.
Items (value at weight).  P = table, y = holes of the object.
  kernel K_s(x)            P_s(x) - x - 5 s                      at x + 6 s
  eps 0:  Z(x), A1(x), A_q(x), B_q(x) as in PROOF_5900 3.4
  excess pieces E^g_q(y) = P_q(y) - y - 5 (q + 1 + g)            at y + 6 (q + 1 + g),   g = 1 (E), g = 2 (F)
     plain (kernel behind a dear seam; H1 with a >= 2):   E_q(y), F_q(y)
     of a cyclic component (H1 with a = 1 / H0a with dear seams): the sum of its pieces - 6 at the sum + 7:
        one piece g = 1:  A'_c(x) (c = q + 3, x = y + 1),  B'_c(x) (c = q + 2, x = y + 7)
        one piece g = 2:  A''_c(x) (c = q + 4, x = y + 1), B''_c(x) (c = q + 3, x = y + 7)
        two pieces g = 1: AA(q1,q2)(x) (x = y1 + y2 + 1),  BB(q1,q2)(x) (x = y1 + y2 + 7)
A PROFILE = kernel + multiset of eps-0 items + excess part with total g <= 2, every item of positive value
(for AA, BB: both pieces positive and the sum - 6 positive).  It SURVIVES if value >= 40 within weight 96.
Output: counts by eps (= total g of the profile), shapes, cells, piece statements, and what the statements of
defect 15 (S1..S5, Corollary K) remove.
"""
import sys
sys.dont_write_bytecode = True
from collections import defaultdict
import tabs15

NEED, W = 40, 96
XMAX, SMAX = 96, 16
BIG = -10 ** 6
TIER = sys.argv[1] if len(sys.argv) > 1 else "D"
NOPAIRS = "nopairs" in sys.argv


def reclose(P):
    """min-closure: every entry is lowered to the bounds (cl1), (cl2) of PROOF_5900 2.2 computed from earlier entries"""
    for x in range(XMAX + 1):
        for s in range(SMAX + 1):
            best = P[s][x]
            if s >= 1:
                b = 0
                for sA in range(s):
                    ra, rb = P[sA], P[s - 1 - sA]
                    for d in range(x + 1):
                        v = ra[d] + rb[x - d]
                        if v > b:
                            b = v
                if b < best:
                    best = b
            for a in range(1, x - 4):
                b = 0
                for tot in (s, s - 1):
                    if tot < 0:
                        continue
                    for sA in range(tot + 1):
                        ra, rb = P[sA], P[tot - sA]
                        for d in range(a, a + 5):
                            v = ra[d] + rb[x - d]
                            if v > b:
                                b = v
                if b < best:
                    best = b
            P[s][x] = best


def tables(tier):
    lean, cap, low = tabs15.load()
    P = [list(r[:XMAX + 1]) for r in cap.P]
    PR = list(cap.PR[:XMAX + 1])
    if tier in ("TP", "D", "D16", "LAW"):
        P[0][76] = min(P[0][76], 120)
        for s, top in ((5, 60), (6, 54), (7, 48), (8, 42)):
            for x in range(top + 1):
                P[s][x] = min(P[s][x], x + 44 + 5 * s)
    if tier in ("D", "D16", "LAW"):
        for s in range(SMAX + 1):
            for x in range(0, 90 - 6 * s + 1):
                P[s][x] = min(P[s][x], x + 44 + 5 * s)
    if tier == "LAW":          # hypothetical: the row law, a chain inside a configuration of defect 16 has at most 105 rows
        for x in range(XMAX + 1):
            P[0][x] = min(P[0][x], 105)
    if tier == "D16":
        for s in range(SMAX + 1):
            for x in range(0, 96 - 6 * s + 1):
                P[s][x] = min(P[s][x], x + 39 + 5 * s)
    if tier != "CAP":
        reclose(P)
        PR = [min(PR[x], P[0][x]) for x in range(XMAX + 1)]
    return P, PR, low


P, PR, LOW = tables(TIER)


def lowP(s, x):
    v = tabs15.lowP(LOW, s, x)
    return v if v >= 0 else None


def lowPR(x):
    v = tabs15.lowPR(LOW, x)
    return v if v >= 0 else None


# ---- items.  record: (name, kind, value, weight, cost, holes, g, pieces, lowvalue)
# pieces: list of (spec, links, wt, tableval, borrow)   spec "S" or "R"
def mk(name, kind, rows, minus, w, c, h, g, pieces, lowrows):
    v = rows - minus
    if w > W or v <= 0:
        return None
    lv = (lowrows - minus) if lowrows is not None else BIG
    return (name, kind, v, w, c, h, g, pieces, lv)


def eps0_items():
    out = []
    for x in range(7, W + 1):
        out.append(mk("Z(%d)" % x, "Z", PR[x - 7] + 1, x, x, 0, x, 0, [("R", 0, x - 7, PR[x - 7] - (x - 7), 1)], (lowPR(x - 7) or -9) + 1 if lowPR(x - 7) is not None else None))
    for x in range(1, W - 5):
        out.append(mk("A1(%d)" % x, "A1", PR[x - 1], x + 5, x + 6, 1, x, 0, [("R", 0, x - 1, PR[x - 1] - (x - 1), 1)], lowPR(x - 1)))
    for q in range(2, W // 6 + 1):
        for x in range(1, W - 6 * q + 1):
            t = q - 2
            out.append(mk("A%d(%d)" % (q, x), "A%d" % q, P[t][x - 1], x + 5 * q, x + 6 * q, q, x, 0,
                          [("S", t, x - 1 + 6 * t, P[t][x - 1] - (x - 1) - 5 * t, 1)], lowP(t, x - 1)))
    for q in range(1, W // 6 + 1):
        for x in range(7, W - 6 * q + 1):
            t = q - 1
            out.append(mk("B%d(%d)" % (q, x), "B%d" % q, P[t][x - 7] + 1, x + 5 * q, x + 6 * q, q, x, 0,
                          [("S", t, x - 7 + 6 * t, P[t][x - 7] - (x - 7) - 5 * t, 1)],
                          (lowP(t, x - 7) + 1) if lowP(t, x - 7) is not None else None))
    return [i for i in out if i]


def excess_pieces(g):
    """plain pieces E^g_q(y): (q, y, value, weight, tableval, lowvalue)"""
    out = []
    for q in range(0, SMAX + 1):
        for y in range(0, W - 6 * (q + 1 + g) + 1):
            v = P[q][y] - y - 5 * (q + 1 + g)
            if v > 0:
                lp = lowP(q, y)
                out.append((q, y, v, y + 6 * (q + 1 + g), P[q][y] - y - 5 * q, (lp - y - 5 * (q + 1 + g)) if lp is not None else BIG))
    return out


def bundles():
    """excess parts: (shape names tuple, value, weight, cost, holes, g, pieces, lowvalue)"""
    B = [((), 0, 0, 0, 0, 0, [], 0)]
    E1, E2 = excess_pieces(1), excess_pieces(2)
    single = []          # excess-1 items, for the pairs
    for g, EP, nm, a1, b1 in ((1, E1, "E", "A'", "B'"), (2, E2, "F", "A''", "B''")):
        for (q, y, v, w, tv, lv) in EP:
            pc = [("S", q, y + 6 * q, tv, 0)]
            it = (("%s%d" % (nm, q),), v, w, q + 1 + g, y, g, pc, lv, "%s%d(%d)" % (nm, q, y))
            B.append(it[:8]) if g == 2 else single.append(it)
            if v - 6 > 0 and w + 7 <= W:
                pcb = [("S", q, y + 6 * q, tv, 1)]
                ca, cb = q + 2 + g, q + 1 + g
                ia = (("%s%d" % (a1, ca),), v - 6, w + 7, ca, y + 1, g, pcb, lv - 6, "%s%d(%d)" % (a1, ca, y + 1))
                ib = (("%s%d" % (b1, cb),), v - 6, w + 7, cb, y + 7, g, pcb, lv - 6, "%s%d(%d)" % (b1, cb, y + 7))
                if g == 2:
                    B.append(ia[:8]); B.append(ib[:8])
                else:
                    single.append(ia); single.append(ib)
    for it in single:
        B.append(it[:8])
    npair = 0
    if not NOPAIRS:
        single.sort(key=lambda t: (t[0], t[8]))
        for i in range(len(single)):
            a = single[i]
            for j in range(i, len(single)):
                b = single[j]
                if a[2] + b[2] > W:
                    continue
                B.append((tuple(sorted(a[0] + b[0])), a[1] + b[1], a[2] + b[2], a[3] + b[3], a[4] + b[4], 2, a[6] + b[6], a[7] + b[7]))
                npair += 1
        # cyclic component with two dear seams of weight 5
        for i in range(len(E1)):
            (q1, y1, v1, w1, t1, l1) = E1[i]
            for j in range(i, len(E1)):
                (q2, y2, v2, w2, t2, l2) = E1[j]
                if v1 + v2 - 6 <= 0 or w1 + w2 + 7 > W:
                    continue
                pc = [("S", q1, y1 + 6 * q1, t1, 1), ("S", q2, y2 + 6 * q2, t2, 0)]
                qq = tuple(sorted((q1, q2)))
                B.append((("AA(%d,%d)" % qq,), v1 + v2 - 6, w1 + w2 + 7, q1 + q2 + 5, y1 + y2 + 1, 2, pc, l1 + l2 - 6))
                B.append((("BB(%d,%d)" % qq,), v1 + v2 - 6, w1 + w2 + 7, q1 + q2 + 4, y1 + y2 + 7, 2, pc, l1 + l2 - 6))
                npair += 2
    return B, len(E1), len(E2), npair


ITEMS0 = sorted(eps0_items(), key=lambda t: (t[1], t[0]))
KERNELS = []
for s in range(0, W // 6 + 1):
    for x in range(0, W - 6 * s + 1):
        lp = lowP(s, x)
        KERNELS.append((s, x, P[s][x] - x - 5 * s, x + 6 * s, (lp - x - 5 * s) if lp is not None else BIG))
KERNELS.sort(key=lambda k: k[3])

HB0 = [0] * (W + 1)
for w in range(1, W + 1):
    b = HB0[w - 1]
    for it in ITEMS0:
        if it[3] <= w and HB0[w - it[3]] + it[2] > b:
            b = HB0[w - it[3]] + it[2]
    HB0[w] = b
BESTK = [BIG] * (W + 1)
for w in range(W + 1):
    b = BIG
    for (s, x, vk, wk, lv) in KERNELS:
        if wk > w:
            break
        if vk + HB0[w - wk] > b:
            b = vk + HB0[w - wk]
    BESTK[w] = b

_base_cache = {}


def base_profiles(need, budget):
    """all (kernel, multiset of eps-0 items) with value >= need within weight budget:
    list of (s, x, vk, lvk, items tuple, value, weight)"""
    key = (need, budget)
    if key in _base_cache:
        return _base_cache[key]
    out = []
    cur = []

    def rec(i0, wh, vh):
        left = budget - wh
        for (s, x, vk, wk, lv) in KERNELS:
            if wk > left:
                break
            if vk + vh >= need:
                out.append((s, x, vk, lv, tuple(cur), vk + vh, wk + wh))
        for i in range(i0, len(ITEMS0)):
            it = ITEMS0[i]
            if it[3] > left:
                continue
            if vh + it[2] + BESTK[left - it[3]] < need:
                continue
            cur.append(it)
            rec(i, wh + it[3], vh + it[2])
            cur.pop()
    rec(0, 0, 0)
    _base_cache[key] = out
    return out


# ---- the statements of defect 15 as cuts on profiles.  J(pieces; V, W; B)
S15 = [("S1", ["S4", "S4"], 55, 78, 1), ("S2", ["S5", "R"], 51, 83, 1), ("S3", ["S2", "R", "R"], 57, 76, 2),
       ("S4", ["S1", "S1", "R"], 61, 71, 1), ("S5", ["S0", "S0", "R"], 62, 70, 2)]


def match_kinds(pcs, spec):
    """can the pieces (all of them) be assigned to the piece kinds of the statement?  (greedy on sorted links)"""
    if len(pcs) != len(spec):
        return False
    rs = sum(1 for p in pcs if p[0] == "R")
    if rs != sum(1 for k in spec if k == "R"):
        return False
    a = sorted(p[1] for p in pcs if p[0] == "S")
    b = sorted(int(k[1:]) for k in spec if k != "R")
    return all(x <= y for x, y in zip(a, b))


def killed15(pcs, Vtot):
    """pcs: list of (spec, links, wt, tableval, borrow).  Some subset A must have sum val >= Vtot - (table values of
    the others); it has exact weight and at most (borrowers in A) shared classes.  Killed if a statement forbids A."""
    n = len(pcs)
    tot = sum(p[3] for p in pcs)
    for mask in range(1, 1 << n):
        A = [pcs[i] for i in range(n) if mask >> i & 1]
        if len(A) < 2 or len(A) > 3:
            continue
        need = Vtot - (tot - sum(p[3] for p in A))
        wt = sum(p[2] for p in A)
        bw = sum(p[4] for p in A)
        for (nm, spec, V, Wt, Bm) in S15:
            if need >= V and wt <= Wt and bw <= Bm and match_kinds(A, spec):
                return nm
    return None


DV = {"R": (6, 7)}


def shifts(names, bundle_names):
    pass


def main():
    Bn, n1, n2, npair = bundles()
    print("=" * 100)
    print("TIER %s, defect 16: need sum v >= %d within sum w <= %d%s" % (TIER, NEED, W, "  (pairs of excess-1 items left out)" if NOPAIRS else ""))
    print("tables: max val of a sequence within weight 90: %d; within 96: %d;  chains: %s" % (
        max(k[2] for k in KERNELS if k[3] <= 90), max(k[2] for k in KERNELS), " ".join("%d:%d" % (x, P[0][x] - x) for x in range(60, 97, 4))))
    print("eps-0 hanging items of positive value: %d; plain excess pieces g=1: %d, g=2: %d; excess parts in all: %d (two-piece: %d)" % (
        len(ITEMS0), n1, n2, len(Bn), npair))
    print("HB0:", " ".join(str(v) for v in HB0))
    shapes = {}    # shape -> [profiles, max slack, example, eps, pieces, realised, survive15, example15, maxslack15]
    cells = {}     # (shape, S, u) -> [profiles, max slack, surviving the statements of 15]
    stm = {}       # (kinds, V, W, B) -> [profiles, shapes set, max slack, after 15]
    tot = [0, 0, 0]
    tot15 = [0, 0, 0]
    real = [0, 0, 0]
    kill = defaultdict(int)
    for (bnames, vb, wb, cb, hb, g, bp, lvb) in Bn:
        if wb > W or vb + BESTK[W - wb] < NEED:
            continue
        for (s, x, vk, lvk, its, val, wt) in base_profiles(NEED - vb, W - wb):
            total = val + vb
            names = sorted([i[1] for i in its] + list(bnames))
            shape = "K%d" % s + ("+" + "+".join(names) if names else "")
            S = s + cb + sum(i[4] for i in its)
            u = x + hb + sum(i[5] for i in its)
            pcs = [("S", s, x + 6 * s, vk, 0)] + [p for i in its for p in i[7]] + list(bp)
            Vt = sum(p[3] for p in pcs) - (total - NEED)      # = 40 + shifts
            Wt = sum(p[2] for p in pcs)
            bw = sum(p[4] for p in pcs)
            lowtot = lvk + lvb + sum(i[8] for i in its)
            tot[g] += 1
            isreal = lowtot >= NEED
            if isreal:
                real[g] += 1
            k15 = killed15(pcs, Vt) if len(pcs) >= 2 else None
            if k15:
                kill[k15] += 1
            else:
                tot15[g] += 1
            sh = shapes.get(shape)
            ex = "K%d(%d)" % (s, x) + "".join(" + " + i[0] for i in its) + ("" if not bnames else " + [" + ",".join(bnames) + " v%d w%d]" % (vb, wb))
            if sh is None:
                sh = shapes[shape] = [0, BIG, None, g, len(pcs), 0, 0, None, BIG]
            sh[0] += 1
            if total - NEED > sh[1]:
                sh[1] = total - NEED
                sh[2] = ex
            if isreal:
                sh[5] += 1
            if not k15:
                sh[6] += 1
                if total - NEED > sh[8]:
                    sh[8] = total - NEED
                    sh[7] = ex
            c = cells.get((shape, S, u))
            if c is None:
                c = cells[(shape, S, u)] = [0, BIG, 0]
            c[0] += 1
            if total - NEED > c[1]:
                c[1] = total - NEED
            if not k15:
                c[2] += 1
            kinds = tuple(sorted(("R" if p[0] == "R" else "S") for p in pcs))
            # statement of the profile: V = 40 + shifts, W = 96 - shifts (the same for all profiles of a shape)
            Vs = Vt
            Ws = W - (wt + wb - Wt)
            key = (kinds, Vs, Ws, bw)
            st = stm.get(key)
            if st is None:
                st = stm[key] = [0, set(), BIG, 0, [0] * 8]
            st[0] += 1
            st[1].add(shape)
            if total - NEED > st[2]:
                st[2] = total - NEED
            if not k15:
                st[3] += 1
            lk = sorted((p[1] for p in pcs if p[0] == "S"), reverse=True)
            for i, v in enumerate(lk):
                if v > st[4][i]:
                    st[4][i] = v
    print("(profiles) surviving: %d = eps 0: %d, eps 1: %d, eps 2: %d;  shapes %d, cells %d" % (sum(tot), tot[0], tot[1], tot[2], len(shapes), len(cells)))
    print("   realised piece by piece (LOW): eps 0: %d, eps 1: %d, eps 2: %d" % tuple(real))
    for g in (0, 1, 2):
        shg = [s for s in shapes if shapes[s][3] == g]
        print("   eps %d: shapes %d, by pieces: %s;  cells %d" % (g, len(shg), " ".join("%d:%d" % (n, sum(1 for s in shg if shapes[s][4] == n)) for n in range(1, 9) if any(shapes[s][4] == n for s in shg)),
                                                              sum(1 for k in cells if shapes[k[0]][3] == g)))
    print("(defect-15 statements as cuts) removed: %s;  left: %d = eps 0: %d, eps 1: %d, eps 2: %d;  shapes left %d, cells left %d" % (
        " ".join("%s:%d" % kv for kv in sorted(kill.items())), sum(tot15), tot15[0], tot15[1], tot15[2],
        sum(1 for s in shapes if shapes[s][6]), sum(1 for k in cells if cells[k][2])))
    for g in (0, 1, 2):
        shg = [s for s in shapes if shapes[s][3] == g and shapes[s][6]]
        print("   left, eps %d: shapes %d, by pieces: %s" % (g, len(shg), " ".join("%d:%d" % (n, sum(1 for s in shg if shapes[s][4] == n)) for n in range(1, 9) if any(shapes[s][4] == n for s in shg))))
    with open("shapes_D16_%s.tsv" % TIER, "w", newline="\n") as f:
        f.write("shape\teps\tpieces\tprofiles\tmax_slack\tbest_profile\trealised_LOW\tleft_after_15\tmax_slack_left\tbest_left\n")
        for sh in sorted(shapes, key=lambda k: (shapes[k][3], shapes[k][4], -shapes[k][1], k)):
            v = shapes[sh]
            f.write("%s\t%d\t%d\t%d\t%d\t%s\t%d\t%d\t%s\t%s\n" % (sh, v[3], v[4], v[0], v[1], v[2], v[5], v[6], v[8] if v[6] else "-", v[7] or "-"))
    with open("cells_D16_%s.tsv" % TIER, "w", newline="\n") as f:
        f.write("shape\tS\tu\trows_outside_loops\tloops\tprofiles\tmax_slack\tleft_after_15\n")
        for key in sorted(cells, key=lambda k: (cells[k][1], k)):
            c = cells[key]
            f.write("%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n" % (key[0], key[1], key[2], key[2] + NEED + 5 * key[1], W - key[2] - 6 * key[1], c[0], c[1], c[2]))
    with open("stmts_D16_%s.tsv" % TIER, "w", newline="\n") as f:
        f.write("pieces\tV\tW\tB\tmax_links_of_the_sequences\tprofiles\tmax_slack\tleft_after_15\tshapes\n")
        for key in sorted(stm, key=lambda k: (len(k[0]), k)):
            st = stm[key]
            ns = sum(1 for k in key[0] if k == "S")
            f.write("%s\t%d\t%d\t%d\t%s\t%d\t%d\t%d\t%s\n" % (" ".join(key[0]), key[1], key[2], key[3], ",".join(str(v) for v in st[4][:ns]),
                                                         st[0], st[2], st[3], " ".join(sorted(st[1]))))
    print("statements (pieces; V, W; B): %d;  written shapes_D16_%s.tsv, cells_D16_%s.tsv, stmts_D16_%s.tsv" % (len(stm), TIER, TIER, TIER))
    for key in sorted(stm, key=lambda k: (len(k[0]), k)):
        st = stm[key]
        ns = sum(1 for k in key[0] if k == "S")
        print("   (%s; %d, %d; %d)  links<=%s  profiles %d  slack %d  left after 15: %d  shapes %d" % (
            " ".join(key[0]), key[1], key[2], key[3], ",".join(str(v) for v in st[4][:ns]), st[0], st[2], st[3], len(st[1])))


if __name__ == "__main__":
    main()
