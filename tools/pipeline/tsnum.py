"""tsnum.py BASE.txt BASE_p.tsv PLAN OUT.plan: renumber the trails of a w2p13o plan (trail = piece index) to
trailsearch's numbering (trailsearch.c main: first the pieces with closes(k, 0) in piece order, i.e. R = len - 10 > 26
and the last 10 letters equal the first 10; then the other pieces).  O and S events must lie on closes(k, 0) pieces
(checked); P events keep their piece index.  Prints the pieces that are not closes(k, 0)."""
import sys, mmap

base, bp, plan, out = sys.argv[1:5]
n, h = 13, 10
P = [(int(r[1]), int(r[2])) for r in (l.split('\t') for l in open(bp))]
fb = open(base, 'rb'); B = mmap.mmap(fb.fileno(), 0, access=mmap.ACCESS_READ)
tnum, nc, notc = {}, 0, []
for k, (s, L) in enumerate(P):
    R = L - h
    if R > 2 * n and B[s + R:s + R + h] == B[s:s + h]: tnum[k] = nc; nc += 1
    else: notc.append(k)
print(f"pieces {len(P)}, closes(k,0) {nc}, others {len(notc)}: {notc}")
lines = open(plan).read().splitlines()
res = [lines[0]]; moved = 0; bad = 0
for l in lines[1:]:
    a = l.split()
    if a and a[0] in 'OS':
        t = int(a[1])
        if t not in tnum: print("event on a piece that is not closes(k,0):", l); bad += 1; res.append(l); continue
        if tnum[t] != t: moved += 1
        a[1] = str(tnum[t]); l = ' '.join(a)
    res.append(l)
open(out, 'w').write('\n'.join(res) + '\n')
print(f"events renumbered {moved}, bad {bad}; wrote {out}")
sys.exit(1 if bad else 0)
