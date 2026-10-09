"""summary.py N PAIRS.txt REPS.idx OUT.tsv: turn the output of neighbours into a table and a summary.

PAIRS.txt: lines "i j steps_i steps_j common direction renaming" of neighbours; REPS.idx: class and source of line i
of the word file.  OUT.tsv: class_a, class_b, differing steps, direction, renaming (symbol s of b is written as the
s-th digit).  Printed: how many classes hang together when two words count as linked if they differ in at most d
steps, for a few d, and the nearest other word of every class.
"""
import sys
from collections import Counter

n, pairs, idx, out = sys.argv[1:5]
names = [l.rstrip("\n").split("\t") for l in open(idx, encoding="utf-8")]
P = []
for l in open(pairs):
    t = l.split()
    i, j, si, sj, c = (int(x) for x in t[:5])
    assert si == sj
    P.append((si - c, i - 1, j - 1, t[5], t[6]))
m = len(names)
print("words on %s symbols: %d classes, %d of %d pairs" % (n, m, len(P), m * (m - 1) // 2))
with open(out, "w", encoding="utf-8", newline="\n") as f:
    f.write("class a\tclass b\tdiffering steps\tdirection of b\trenaming of b\n")
    for d, i, j, di, r in sorted(P, key=lambda x: (x[1], x[2])):
        f.write("%s\t%s\t%d\t%s\t%s\n" % (names[i][0], names[j][0], d, di, r))


def components(limit):
    par = list(range(m))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for d, i, j, _, _ in P:
        if d <= limit:
            par[find(i)] = find(j)
    return Counter(find(x) for x in range(m))


ds = sorted(set(d for d, *_ in P))
print("differing steps, smallest values:", ds[:12], "largest:", ds[-3:])
for limit in (1, 2, 3, 5, 10, 20, 50, 100, 200, 1000, 100000):
    c = components(limit)
    print("linked at <= %6d steps: %3d groups, sizes %s" % (limit, len(c), sorted(c.values(), reverse=True)[:12]))
near = {}
for d, i, j, _, _ in P:
    for a, b in ((i, j), (j, i)):
        if a not in near or d < near[a][0]:
            near[a] = (d, b)
print("nearest other word: differing steps -> number of classes:", sorted(Counter(v[0] for v in near.values()).items()))
if "-v" in sys.argv:
    for a in range(m):
        if a in near:
            print(names[a][0], names[a][1], "nearest", names[near[a][1]][0], near[a][0])
