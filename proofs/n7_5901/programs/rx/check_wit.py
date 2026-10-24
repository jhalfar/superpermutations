# check_wit.py WITFILE [CAPS]: checks every line "RING rows T holes H : word/len ..." from the definitions
# (PROOF_5900.md section 1): rows (e, l) = blocks e, tau2 e, ..; all blocks in pairwise different classes;
# every link exit -> next entry has weight exactly 3, also from the last row to the first; T >= 2;
# T rows and exactly H holes. With CAPS: prints whether T equals the ring row entry at H.
import sys
def ew(u, v):
    for t in range(1, 7):
        if u[t:] == v[:7 - t]:
            return t
    return 7
def tau2(w): return w[1:6] + w[0] + w[6]
def siginv(w): return w[6] + w[:6]
def cls(w):
    i = w.index('1'); return w[i:] + w[:i]
R = None
if len(sys.argv) > 2:
    for l in open(sys.argv[2]):
        if l.startswith('R:'): R = [int(x) for x in l[2:].split()]
ok = 0; res = {}
for line in open(sys.argv[1]):
    if not line.startswith('RING'): continue
    p = line.split()
    T, H = int(p[2]), int(p[4])
    rows = [(x.split('/')[0], int(x.split('/')[1])) for x in p[6:]]
    assert len(rows) == T and T >= 2, (T, H)
    seen = set(); exits = []; holes = 0
    for e, l in rows:
        assert sorted(e) == list('1234567') and 1 <= l <= 6
        w = e
        for i in range(l):
            c = cls(w); assert c not in seen, ('class twice', T, H); seen.add(c)
            last = w; w = tau2(w)
        exits.append(siginv(last)); holes += 6 - l
    assert holes == H, (holes, H)
    for i in range(T):
        assert ew(exits[i], rows[(i + 1) % T][0]) == 3, ('link', T, H, i)
    ok += 1; res[H] = T
print('rings checked:', ok)
print('H:T', ' '.join('%d:%d' % (h, res[h]) for h in sorted(res)))
if R:
    bad = [h for h in res if res[h] != R[h]]
    print('levels where the witness has fewer rows than the ring row:', bad)
