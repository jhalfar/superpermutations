"""gen_blockB.py - write the Lean certificate of the (10,3) block of step (B).

    gen_blockB.py [BLOCK] [CYC15] [CYC16] [--out DIR]

BLOCK  the block on 14 symbols, lines "x T" (default data/s103_old2_0.txt)
CYC15  its connector cycles with z = E on 15 symbols (default data/cyc_s103_old2_0.txt)
CYC16  the cycles with z = F on 16 symbols for the block transported once (default data/cyc_t_s103_old2_0_n16.txt)

Lean letters.  The block is written above the canonical loop d0 = alph10 = [11, 8, 0, 1, ..., 7]: the old block
letter i is d0[i]; the tokens A, B, C are 12, 13, 14 (the letters added at 12, 13, 14 symbols); the distinguished
letter (D in the block file) is 9; the completion letter (E at 15 symbols, F at 16) is 10; the letter added at 15
symbols (D in the transported file) is 15.

Everything Lean checks is checked here first with functions that follow the Lean definitions (as gen_cert.py).
Output: SuperpermutationUpperBound305989/Certificate/BlockData.lean, BlockChecks.lean, BlockPorts16a.lean, BlockPorts16b.lean, BlockCert.lean.
The 4 cycles on 15 symbols (306157/604800) are checked by this script only; Lean uses the 26 on 16 symbols.
"""
import sys, os, hashlib, math

here = os.path.dirname(os.path.abspath(__file__))
c15 = os.path.join(here, 'data')
root = here
argv = sys.argv[1:]
OUT = os.path.join(here, 'SuperpermutationUpperBound305989', 'Certificate')
if '--out' in argv:
    i = argv.index('--out'); OUT = argv[i + 1]; del argv[i:i + 2]
BLOCK = argv[0] if len(argv) > 0 else os.path.join(c15, 's103_old2_0.txt')
CYC15 = argv[1] if len(argv) > 1 else os.path.join(c15, 'cyc_s103_old2_0.txt')
CYC16 = argv[2] if len(argv) > 2 else os.path.join(c15, 'cyc_t_s103_old2_0_n16.txt')
NS = 'SuperpermutationUpperBound305989'

def sha(path): return hashlib.sha256(open(path, 'rb').read()).hexdigest()
def lines(path): return [l.split() for l in open(path) if l.strip() and not l.startswith('#')]

SAT, FINAL = 9, 10
D0 = [11, 8, 0, 1, 2, 3, 4, 5, 6, 7]
ALPH13 = [14, 13, 12] + D0           # = alphabet 2 = 14 :: 13 :: alph11, alph11 = 12 :: alph10
ALPH14 = [15] + ALPH13
NUM = {str(i): D0[i] for i in range(10)}
NUM.update({'A': 12, 'B': 13, 'C': 14})
NUM15 = dict(NUM); NUM15['E'] = FINAL                 # cycles at 15 symbols
NUM16 = dict(NUM); NUM16['D'] = 15; NUM16['F'] = FINAL  # cycles at 16 symbols (transported file)

def rot(x, j): j %= len(x); return x[j:] + x[:j]
def insertLetter(x, z, j): return x[:j] + [z] + x[j:]
def head(r): return r[0][:len(r[0]) - 2]
def tail(r): return rot(r[0], r[1] + 1)[:len(r[0]) - 2]
def charge(r): return len(r[0]) - r[1]
def portTarget(r, j):
    n = len(r[0])
    return (j + (n - 2)) % (n - 1) if r[1] == n else (j + 1) % (n - 1)
def portPath(r, z, j):
    b, v = r; n = len(b)
    if v == n:
        return [(insertLetter(b, z, 0), n + 1), (insertLetter(b, z, n - 1), n + 1)] if j == 0 else [(insertLetter(b, z, j), n + 1)]
    if j < n - 2: return [(insertLetter(b, z, j), n - 1)]
    return [(insertLetter(b, z, n - 2), n - 1), (rot(b, n - 1) + [z], n - 1)]
def transRows(r, z):
    b, v = r; n = len(b)
    if v == n: return [(insertLetter(b, z, j), n + 1) for j in range(n)]
    return [(insertLetter(b, z, j), n - 1) for j in range(n - 1)] + [(rot(b, n - 1) + [z], n - 1)]
def transportWalk(rs, z, p):
    out = []
    for r in rs: out += portPath(r, z, p); p = portTarget(r, p)
    return out
def completionExit(rs, q):
    for r in rs: q = portTarget(r, q)
    return q
def orbitPorts(rs, m, p):
    out = []
    for _ in range(m): out.append(p); p = completionExit(rs, p)
    return out
def closed(rs): return all(tail(rs[i]) == head(rs[(i + 1) % len(rs)]) for i in range(len(rs)))
def excess(rs): return len(rs) - sum(charge(r) for r in rs)
def canon(x): i = x.index(min(x)); return tuple(x[i:] + x[:i])
def fullChart(x, z, s): return [(rot(x, j) + [z], len(x) + 1) for j in range(len(x))]
def above3(d):
    return [rot(rot(rot(d, i) + [12], j) + [13], k) + [14]
            for i in range(len(d)) for j in range(len(d) + 1) for k in range(len(d) + 2)]

# ---------------------------------------------------------------- the block on 14 symbols
sel = lines(BLOCK)
assert len(sel) == 1320
rows = [([NUM[c] for c in x], 13 if T == 'F' else 11) for x, T in sel if T in 'FS']
dloops = sorted([NUM[c] for c in x] for x, T in sel if T == 'D')
assert all(T in 'FSD' for _, T in sel) and len(rows) == 880 and len(dloops) == 440
by_head = {}
for i, r in enumerate(rows):
    assert tuple(head(r)) not in by_head; by_head[tuple(head(r))] = i
succ = [by_head[tuple(tail(r))] for r in rows]
assert sorted(succ) == list(range(880))
seen = [False] * 880; walks = []
for i in range(880):
    if seen[i]: continue
    w = []; j = i
    while not seen[j]: seen[j] = True; w.append(j); j = succ[j]
    k = min(range(len(w)), key=lambda t: rows[w[t]])
    walks.append([rows[t] for t in w[k:] + w[:k]])
walks.sort(key=lambda w: (-len(w), w))
for w in walks:
    assert closed(w)
    for b, v in w: assert sorted(b) == sorted(ALPH13) and v in (13, 11)
assert sum(len(w) for w in walks) == 880 and sum(charge(r) for w in walks for r in w) == 370
for d in dloops: assert sorted(d) == sorted(ALPH13)
H14 = 12
G = []      # number of start ports (gcd of the winding and 12) per walk
for w in walks:
    e = excess(w); g = math.gcd(e, H14); m = H14 // g
    assert (m * e) % H14 == 0
    ps = [q for p in range(g) for q in orbitPorts(w, m, p)]
    assert sorted(ps) == list(range(H14)), (len(w), e, g)
    G.append(g)
print('walks (rows, full, short, winding, start ports):',
      [(len(w), sum(1 for r in w if r[1] == 13), sum(1 for r in w if r[1] == 11), excess(w), g) for w, g in zip(walks, G)])

# completeness: every loop above d0 is a row base or a loop without a row, up to rotation
loc = {}
for c, w in enumerate(walks):
    for o, r in enumerate(w): loc[canon(r[0])] = (c, o)
for o, d in enumerate(dloops): loc[canon(d)] = (len(walks), o)
A3 = above3(D0)
assert len(A3) == 1320 and len(set(canon(t) for t in A3)) == 1320
ptrs = [loc[canon(t)] for t in A3]
assert len(set(ptrs)) == 1320

# ---------------------------------------------------------------- transported once: 15 symbols, completion at 16
H15 = 13
T15 = []    # the closed trails on 15 symbols that come from the walks
for w, g in zip(walks, G):
    m = H14 // g
    for p in range(g):
        W = transportWalk(w * m, 15, p)
        assert closed(W) and excess(W) % H15 == 0
        T15.append(W)
assert sorted((tuple(b), v) for W in T15 for b, v in W) == sorted(
    (tuple(b), v) for w in walks for r in w for b, v in transRows(r, 15))
charts15 = [fullChart(e, 15, SAT) for e in dloops]
allrows15 = [r for W in T15 for r in W] + [r for C in charts15 for r in C]
assert len(allrows15) == 17160 and sum(charge(r) for r in allrows15) == 4810
assert len(set(canon(b) for b, _ in allrows15)) == 17160

def cyc_index(cycles, h):
    idx = {}
    for ci, c in enumerate(cycles):
        assert len(c) == h and len(set(c)) == h and FINAL in c and SAT not in c
        for k in range(h): idx.setdefault(tuple(rot(c, k)), (ci, k))
    return idx
def pointers(W, h, idx):
    out = []
    for j in range(h):
        p = j; found = None
        for ri, r in enumerate(W):
            hit = idx.get(tuple(insertLetter(head(r), FINAL, p)))
            if hit is not None: found = (0, j, hit[0], ri, p, hit[1]); break
            p = portTarget(r, p)
        assert found is not None, 'a port is not covered'
        out.append(found)
    return out

cyc16 = [[NUM16[ch] for ch in l[0]] for l in lines(CYC16)]
assert len(cyc16) == 26
for c in cyc16: assert set(c) <= set(ALPH14) | {FINAL}
idx16 = cyc_index(cyc16, H15)
P16 = [pointers(W, H15, idx16) for W in T15]
assert sum(len(p) for p in P16) == 182

# the n = 15 alternative (306157/604800): 4 cycles for the walks written m times on 14 symbols, h = 12
cyc15 = [[NUM15[ch] for ch in l[0]] for l in lines(CYC15)]
assert len(cyc15) == 4
idx15 = cyc_index(cyc15, H14)
P15 = [pointers(w * (H14 // g), H14, idx15) for w, g in zip(walks, G)]

# ---------------------------------------------------------------- output
def L(xs): return '[' + ','.join(str(x) for x in xs) + ']'
def R(r): return '⟨%s,%d,%d⟩' % (L(r[0]), SAT, r[1])
def rows_lit(rs, ind='  '): return '[\n' + ',\n'.join(ind + R(r) for r in rs) + ']'
def pairs(ps): return '[' + ','.join('(%d,%d)' % p for p in ps) + ']'
def mptrs(ps): return '[' + ','.join('⟨%d,%d,%d,%d,%d,%d⟩' % p for p in ps) + ']'
def rel(p): return os.path.relpath(p, root).replace(os.sep, '/')
SRC = ('Generated by gen_blockB.py from\n  %s  (SHA-256 %s)\n  %s  (SHA-256 %s)\n  %s  (SHA-256 %s)'
       % (rel(BLOCK), sha(BLOCK), rel(CYC15), sha(CYC15), rel(CYC16), sha(CYC16)))
HEAD = '''
namespace %s.Certificate

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound.Certificates.CircleBase
open %s

set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option Elab.async false
''' % (NS, NS)
FOOT = '\nend %s.Certificate\n' % NS
P = NS + '.Certificate.'
def write(name, imports, doc, body):
    text = ''.join('import %s\n' % i for i in imports) + '\n/-! %s\n\n%s -/\n' % (doc, SRC) + HEAD + '\n' + body + FOOT
    with open(os.path.join(OUT, name + '.lean'), 'w', encoding='utf-8', newline='\n') as f: f.write(text)

write('BlockData', [NS + '.BlockB'],
      'The (10,3) block above the canonical loop d0 = alph10 on 14 symbols: %d closed walks of full and short rows\n'
      '(%d rows, total charge %d), each with its number of start ports, %d loops without a row, the pointers of the\n'
      '1,320 loops above d0, and the 26 connector cycles on 16 symbols.' % (len(walks), 880, 370, 440),
      'def blockItems : List (List (Row Nat) × Nat) := [\n%s]\n\n' % ',\n'.join('  (' + rows_lit(w, '    ') + ', %d)' % g for w, g in zip(walks, G)) +
      'def blockD : List (List Nat) := [\n%s]\n\n' % ',\n'.join('  ' + L(d) for d in dloops) +
      'def blockPtrs : List (Nat × Nat) := %s\n\n' % pairs(ptrs) +
      'def blockCyc16 : List (List Nat) := [\n%s]\n\n' % ',\n'.join('  ' + L(c) for c in cyc16) +
      'def blockData : BlockData where\n  items := blockItems\n  dloops := blockD\n'
      '  ptrs := blockPtrs\n  cyc := blockCyc16\n')

write('BlockChecks', [P + 'BlockData'], 'The kernel checks of the block on 14 symbols (`BlockOK`).',
      open(os.path.join(here, 'block_checks_body.lean'), encoding='utf-8').read())

SPLIT = 7    # two files of pointer checks (one file took 6.3 GB)
for part, sel_, ps in (('a', 'List.take %d blockData.trails15' % SPLIT, P16[:SPLIT]),
                       ('b', 'List.drop %d blockData.trails15' % SPLIT, P16[SPLIT:])):
    write('BlockPorts16' + part, [P + 'BlockData'],
          'Cycle pointers on 16 symbols for %d of the %d closed trails on 15 symbols that come from the block walks, all 13 ports.' % (len(ps), len(T15)),
          'def blockPorts16%s : List (List MixedPointer) := [\n%s]\n\n' % (part, ',\n'.join('  ' + mptrs(p) for p in ps)) +
          'theorem blockPorts16%s_ok : portsB blockData.cyc 13 (%s) blockPorts16%s = true := by\n  decide +kernel\n\n' % (part, sel_, part) +
          '#print axioms blockPorts16%s_ok\n' % part)

write('BlockCert', [NS + '.Fifteen', P + 'BlockChecks', P + 'BlockPorts16a', P + 'BlockPorts16b'], 'The checked block.',
      '''theorem blockData_ports : ∀ W ∈ blockData.trails15, ∃ m, PortsCovered W blockData.cyc 13 m := by
  intro W hW
  rw [← List.take_append_drop %d blockData.trails15] at hW
  rcases List.mem_append.mp hW with h | h
  · exact portsB_sound _ _ blockPorts16a_ok W h
  · exact portsB_sound _ _ blockPorts16b_ok W h

/-- The block of step (B), with its checks. -/
def blockCert : BlockCert where
  data := blockData
  ok := blockData_ok
  ports := blockData_ports

#print axioms blockData_ports
''' % SPLIT)

print('trails on 15 symbols:', len(T15), [len(W) for W in T15])
print('max pointer row (16):', max(p[3] for ps in P16 for p in ps), '; (15, script check only):', max(p[3] for ps in P15 for p in ps))
print('cycles used at 16:', len(set(p[2] for ps in P16 for p in ps)), 'of 26; at 15:', len(set(p[2] for ps in P15 for p in ps)), 'of 4')
