"""unitsplit.py BASE.txt BASE.tsv PLAN OUT.plan [SPEC]

Jay Pantone's 6,747,801,272 writes the 96 W2058.1022 trails of selection N (R 3,443,055 = 7 x 491,865 and
R 383,789 = 7 x 54,827) in up to 7 segments, cut at the 7 rotation-equivalent weight-3 steps of the trail (the unit
boundaries; offsets 477,158 mod 491,865 and 13,750 mod 54,827 in the base word of selection N), and puts the segments between
D loops.  This script rewrites a plan so that every such trail is written as its unit segments, one after the other
(the word stays letter for letter the same: consecutive units overlap by the 10 letters of the weight-3 step).
segins / polish can then move every unit on its own.

SPEC: comma list of R:c:U (default "3443055:477158:491865,383789:13750:54827"); a boundary is an offset b = c mod U
whose step from the window b - 3 has weight 3 (checked).
Events: O t o gg g1 (whole trail from window o, R + 13 - gg letters), S t o len, P k.  An event of such a trail is
cut at every boundary b with o < b and b - 3 >= o inside its windows; the pieces become S events.  BASE.tsv: the
trail table of the base (type, ?, R, start), one line per trail in order."""
import sys, mmap

base, btsv, plan, out = sys.argv[1:5]
spec = sys.argv[5] if len(sys.argv) > 5 else "3443055:477158:491865,383789:13750:54827"
SP = {}
for s in spec.split(','):
    R, c, U = s.split(':'); SP[int(R)] = ([-1 if x == 'own' else int(x) for x in c.split('/')], int(U))
lines = open(plan).read().splitlines()
n = int(lines[0].split()[1])
own = {}                                   # c = own: the orbit of the trail's first cut in the plan
for l in lines[1:]:
    a = l.split()
    if a and a[0] in 'OS': own.setdefault(int(a[1]), int(a[2]))
rows = [l.split('\t') for l in open(btsv)]
TR = [(int(r[2]), int(r[3])) for r in rows]
fb = open(base, 'rb'); B = mmap.mmap(fb.fileno(), 0, access=mmap.ACCESS_READ)


def T(t, o, k):
    R, s = TR[t]; o %= R; res = b''
    while len(res) < k:
        take = min(k - len(res), R - o); res += B[s + o:s + o + take]; o = 0
    return res


def isperm(x): return len(set(x)) == n


bcache = {}; skipped = [0]
def bounds(t):
    if t in bcache: return bcache[t]
    R, _ = TR[t]; cs, U = SP[R]
    bs = []
    for c in cs:
        if c < 0: c = own[t] % U
        for k in range(R // U):
            b = (c + k * U) % R
            g = next((g for g in (1, 2, 3) if isperm(T(t, b - g, n))), 0)
            if not isperm(T(t, b, n)) or g < 2:
                if cs[0] < 0: bcache[t] = []; skipped[0] += 1; return []   # own orbit not all cuts: leave the trail
                if c == cs[0]: sys.exit(f"trail {t}: offset {b} is not a weight-2/3 step")
                skipped[0] += 1; continue      # a further offset that is no boundary in this trail
            bs.append((b, g))
    bcache[t] = sorted(bs); return bcache[t]


lines = open(plan).read().split('\n')
hdr = lines[0].split()
outl = []; nsplit = 0; nnew = 0
for l in lines[1:]:
    if not l.strip(): continue
    a = l.split()
    if a[0] in 'OS' and TR[int(a[1])][0] in SP:
        t, o = int(a[1]), int(a[2]); R = TR[t][0]
        ln = R + n - int(a[3]) if a[0] == 'O' else int(a[3])
        last = o + ln - n                      # last window, unwrapped
        cuts = []
        for b, g in bounds(t):
            for bb in (b, b + R, b + 2 * R):
                if o < bb and bb - g >= o and bb <= last: cuts.append((bb, g))
        cuts = sorted(set(cuts))
        if cuts:
            nsplit += 1
            st = o
            for bb, g in cuts:
                outl.append(f"S {t} {st % R} {bb - g - st + n}"); nnew += 1; st = bb
            outl.append(f"S {t} {st % R} {last - st + n}"); nnew += 1
            if a[0] == 'O' and int(a[4]) > 0:
                sys.stderr.write(f"note: trail {t} had a skip cut; the dropped window stays dropped (segment ends)\n")
            continue
    outl.append(l)
with open(out, 'w') as f:
    f.write(f"TRAILSEARCH-PLAN {hdr[1]} {hdr[2]} {len(outl):12d}\n")
    f.write('\n'.join(outl) + '\n')
print(f"events {len(lines) - 2} -> {len(outl)}; {nsplit} events of the W2058 trails split into {nnew} segments; "
      f"{skipped[0]} offsets of the further orbits are no boundary in their trail")
