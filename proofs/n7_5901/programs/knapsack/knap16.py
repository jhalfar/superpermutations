# Referee n7-ref16: own knapsack of defect 16 at the level of PIECES (Lemma PIECE16), from capD.txt alone.
# A profile = kernel piece (sequence, u0 links, weight w0) + extra pieces, each with a shift (dv, dw), a flag "borrows"
# and an excess g; total g <= 2; every extra has table value - dv >= 1; sum (t - dv) + t0 >= 40; sum (w + dw) + w0 <= 96.
# Removed (Lemma SUB) by a statement J(kinds; V, W; B) on a sub-multiset A: kinds fit, sum_A w <= W, borrowers(A) <= B,
# 40 + sum dv - sum_{not in A} t >= V.
import sys, re, itertools, collections
import os
HERE = os.path.dirname(os.path.abspath(__file__))
MODE = sys.argv[1] if len(sys.argv) > 1 else "map"
rows = {}
for line in open(os.path.join(HERE, "..", "..", "table", "capD.txt")):
    k, v = line.split(":"); rows[k.strip()] = [int(x) for x in v.split()]
P = [rows[str(s)] for s in range(12)]; PR = rows["R"]
print("capD rows", len(P), "lengths", [len(r) for r in P], "ring", len(PR))
# ---- comparison with the Lean tables
txt = open(os.path.join(HERE, "..", "..", "..", "lean", "n7_5900", "LowerBounds", "KTables.lean")).read()
def lean(name):
    m = re.search(r"def " + name + r" : List[^=]*:=\s*(\[.*?\])\s*\n\s*\n", txt, re.S)
    return eval(m.group(1))
Dtab, Ttab, TRtab = lean("Dtab"), lean("Ttab"), lean("TRtab")
Tlen = [85, 79, 73, 67, 61, 61, 55, 49, 43]
bad = 0
for s in range(9):
    for x in range(0, 91 - 6 * s):
        if P[s][x] != Dtab[s][x]: bad += 1; print("DIFF D", s, x, P[s][x], Dtab[s][x])
    for x in range(Tlen[s]):
        if P[s][x] > Ttab[s][x]: print("capD above T'", s, x)
print("rows 0..8, x <= 90-6s: capD == Lean Dtab:", bad == 0, " Lean Dtab row lengths", [len(r) for r in Dtab])
print("ring row: Lean TRtab length", len(TRtab), " equal on 0..84:", PR[:85] == TRtab[:85], " first diff:", [(x, PR[x], TRtab[x]) for x in range(min(len(PR), len(TRtab))) if PR[x] != TRtab[x]][:5])
print("ring row 85..96:", PR[85:97], " chain row 85..96:", P[0][85:97], " x+44:", [x + 44 for x in range(85, 97)])
print("val cap of rows at weight 91..96 (x = w - 6s):", {s: [P[s][w - 6 * s] - (w - 6 * s) - 5 * s for w in range(91, 97)] for s in range(0, 11)})
# ---- closure (cl2 only, an upper bound) for the rows 9..16 from the rows 0..8 of the file
T = [list(P[s]) for s in range(9)]
def cl2(s, x): return max(T[a][d] + T[s - 1 - a][x - d] for a in range(s) for d in range(x + 1))
for s in range(9, 17):
    T.append([cl2(s, x) for x in range(max(0, 97 - 6 * s))])
for s in range(9, 12):
    n = min(len(T[s]), len(P[s]))
    lo = [x for x in range(n) if P[s][x] < T[s][x]]; hi = [x for x in range(n) if P[s][x] > T[s][x]]
    print("row", s, ": file below my cl2 closure at", len(lo), "levels", lo[:8], "(needs cl1 or Corollary K), above at", len(hi))
for s in range(9, 17):
    xs = range(max(0, 97 - 6 * s))
    if xs: print("row", s, "max val within weight 96 (file if present else cl2):", max((P[s][x] if s < 12 and x < len(P[s]) else T[s][x]) - x - 5 * s for x in xs),
                 " within 90:", max([(P[s][x] if s < 12 and x < len(P[s]) else T[s][x]) - x - 5 * s for x in xs if x + 6 * s <= 90] or [-99]))
def cap(s, x): return P[s][x] if s < 12 and x < len(P[s]) else T[s][x]
SMAX = 16
def sv(u, w):  # table value of a sequence with exactly u links and weight w
    x = w - 6 * u
    return cap(u, x) - x - 5 * u if x >= 0 else None
# ---- statements
if MODE == "map":
    ST = {"T1": ([7, 3], 0, 50, 84, 1), "T2": ([7], 1, 46, 89, 1), "T3": ([5], 2, 52, 82, 2), "T4": ([4, 2], 1, 56, 77, 2),
          "T5": ([3, 1, 1], 0, 60, 72, 2), "T6": ([2], 3, 58, 75, 3), "T7": ([1, 0], 2, 62, 70, 3), "T8": ([0, 0, 0], 1, 66, 65, 2),
          "T9": ([0], 4, 64, 68, 4)}
else:  # as run
    ST = {"T1": ([7, 7], 0, 50, 84, 1), "T2": ([7], 1, 46, 89, 1), "T3": ([5], 2, 52, 82, 2), "T4": ([4, 4], 1, 56, 77, 2),
          "T5": ([3, 3, 3], 0, 60, 72, 2), "T6": ([2], 3, 58, 75, 3), "T7": ([1, 0], 2, 62, 70, 3), "T8": ([0, 0, 0], 1, 66, 65, 2),
          "T9": ([0], 4, 64, 68, 4)}
ST["K"] = ([SMAX], 0, 40, 96, 0)
S15 = {"S1": ([4, 4], 0, 55, 78, 1), "S2": ([5], 1, 51, 83, 1), "S3": ([2], 2, 57, 76, 2), "S4": ([1, 1], 1, 61, 71, 1), "S5": ([0, 0], 1, 62, 70, 2)}
USE15 = len(sys.argv) > 2 and sys.argv[2] == "with15"
if USE15: ST.update(S15)
POS = not (len(sys.argv) > 3 and sys.argv[3] == "nopos")   # positivity of the extras
# ---- items: (iv, iw, kind, u, w, t, borrow, g, name)
ext = []
for H in range(0, 97):
    if H < len(PR):
        t = min(PR[H], P[0][H]) - H
        if (t - 6 >= 1 or not POS) and H + 7 <= 96: ext.append((t - 6, H + 7, "R", 0, H, t, 1, 0, "R"))
for name, dv, dw, bor, g in (("AB", 11, 13, 1, 0), ("E", 10, 12, 0, 1), ("A'", 16, 19, 1, 1), ("F", 15, 18, 0, 2), ("A''", 21, 25, 1, 2)):
    for u in range(0, SMAX + 1):
        for w in range(6 * u, 97 - dw):
            t = sv(u, w)
            if t is not None and (t - dv >= 1 or not POS): ext.append((t - dv, w + dw, "S", u, w, t, bor, g, name))
ext.sort(key=lambda e: (e[8], e[3], e[4]))
print("extra items:", collections.Counter(e[8] for e in ext))
kern = [(sv(u, w), w, u) for u in range(SMAX + 1) for w in range(6 * u, 97)]
bestK = [max(t for t, w, u in kern if w <= b) for b in range(97)]
bestX = [0] * 97   # unbounded knapsack of extras
for b in range(97):
    for e in ext:
        if e[1] <= b and e[0] > 0: bestX[b] = max(bestX[b], bestX[b - e[1]] + e[0])
print("best kernel within 96, 90, 89:", bestK[96], bestK[90], bestK[89], " best extras within 96:", bestX[96])
def fits(seq_links, nring, kinds, nr):
    if nring != nr or len(seq_links) != len(kinds): return False
    return all(a <= b for a, b in zip(sorted(seq_links, reverse=True), sorted(kinds, reverse=True)))
def removed(pieces, Vneed):
    # pieces: list of (kind, u, w, t, borrow)
    n = len(pieces); tot = sum(p[3] for p in pieces); out = []
    for mask in range(1, 1 << n):
        A = [pieces[i] for i in range(n) if mask >> i & 1]
        tA = sum(p[3] for p in A); wA = sum(p[2] for p in A); bA = sum(p[4] for p in A)
        need = Vneed - (tot - tA)
        sl = [p[1] for p in A if p[0] == "S"]; nr = sum(1 for p in A if p[0] == "R")
        for nm, (kinds, kr, V, W, B) in ST.items():
            if fits(sl, nr, kinds, kr) and wA <= W and bA <= B and need >= V: out.append((nm, mask))
    return out
stats = collections.Counter(); shapes = collections.defaultdict(collections.Counter); unrem = []; maxlink = collections.defaultdict(lambda: [0] * 4)
slack = collections.defaultdict(lambda: [99, 99])
nprof = 0
def rec(start, chosen, iv, iw, g):
    global nprof
    b = 96 - iw
    if iv + bestK[b] + bestX[b] < 40: return
    if iv + bestK[b] >= 40 or not chosen:
        for t0, w0, u0 in kern:
            if w0 <= b and t0 + iv >= 40:
                nprof += 1
                pieces = [("S", u0, w0, t0, 0)] + [(e[2], e[3], e[4], e[5], e[6]) for e in chosen]
                Vneed = 40 + sum(e[5] - e[0] for e in chosen)
                rm = removed(pieces, Vneed)
                shape = "K+" + "+".join(sorted(e[8] for e in chosen))
                eps = sum(e[7] for e in chosen)
                if not rm: unrem.append((shape, u0, w0, t0, [(e[8], e[3], e[4], e[5]) for e in chosen])); stats["UNREMOVED"] += 1; shapes[shape]["UNREMOVED"] += 1
                else:
                    names = set(r[0] for r in rm)
                    full = [r[0] for r in rm if r[1] == (1 << len(pieces)) - 1]
                    first = full[0] if full else "sub:" + sorted(names)[0]
                    stats[first] += 1; shapes[shape][first] += 1
                    stats["eps%d" % eps] += 1
                    for nm in set(full):
                        sl = sorted([p[1] for p in pieces if p[0] == "S"], reverse=True)
                        for i, x in enumerate(sl): maxlink[nm][i] = max(maxlink[nm][i], x)
                        kinds, kr, V, W, B = ST[nm]
                        slack[nm][0] = min(slack[nm][0], Vneed - V); slack[nm][1] = min(slack[nm][1], W - sum(p[2] for p in pieces))
    for j in range(start, len(ext)):
        e = ext[j]
        if g + e[7] > 2 or iw + e[1] > 96: continue
        chosen.append(e); rec(j, chosen, iv + e[0], iw + e[1], g + e[7]); chosen.pop()
rec(0, [], 0, 0, 0)
print("MODE", MODE, "with15" if USE15 else "", "positivity" if POS else "NO positivity")
print("profiles (piece level):", nprof, " by first statement:", dict(stats))
print("max links per position among the profiles a statement removes whole:", {k: v for k, v in maxlink.items()})
print("least (Vneed - V, W - weight) per statement:", dict(slack))
print("UNREMOVED:", len(unrem))
for u in unrem[:40]: print("  ", u)
sh_un = [s for s, c in shapes.items() if c["UNREMOVED"]]
print("shapes:", len(shapes), " with unremoved profiles:", sh_un[:30])
dbl = {s: dict(c) for s, c in shapes.items() if "F" in s.split("+") or "A''" in s.split("+")}
print("shapes with a double place:", dbl)
with open(os.path.join(HERE, "knap16_%s%s%s.shapes.txt") % (MODE, "_15" if USE15 else "", "" if POS else "_nopos"), "w") as f:
    for s in sorted(shapes): f.write("%s\t%s\n" % (s, dict(shapes[s])))
