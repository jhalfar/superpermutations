"""gen_cert.py - write the Lean certificate files of SuperpermutationUpperBound1771/Certificate/.

    gen_cert.py [SELECTION] [CYCLES] [--out DIR]

SELECTION  the selection on 11 symbols, lines "x T"
           (default: arrange/data/n12t-selection.txt.xz of github.com/jhalfar/superpermutations)
CYCLES     the 203 connector cycles on 12 symbols
           (default: selection/data/zcycles_n12.txt of the same repository)
DIR        where the files are written (default: SuperpermutationUpperBound1771/Certificate next to this script)

The defaults are found when this script sits in proofs/lean/constant/ of that repository.  Python 3, no packages.

Everything else is derived here: the 9-symbol selection (the rows of SELECTION that start with the two newest
letters, with those letters removed), its two closed walks, the 48 groups, and all pointers.  The functions below
follow the Lean definitions (Transport.portPath, portTarget, transportWalk, Row.head, Row.tail, insertLetter, rot);
every fact that Lean will check is checked here first, so a mistake shows up in this script and not in the kernel.

Letters in Lean: 0..7 the ordinary letters of the 9-symbol selection, 9 the distinguished letter, 8 and 11 the
letters added by the two transports ('8', '9' in SELECTION), 12 the next one, 10 the completion letter ('B').
"""
import sys, os, lzma, hashlib, itertools, collections, math

here = os.path.dirname(os.path.abspath(__file__))
repo = os.path.normpath(os.path.join(here, '..', '..', '..'))
argv = sys.argv[1:]
OUT = os.path.join(here, 'SuperpermutationUpperBound1771', 'Certificate')
if '--out' in argv:
    i = argv.index('--out'); OUT = argv[i + 1]; del argv[i:i + 2]
SEL = argv[0] if len(argv) > 0 else os.path.join(repo, 'arrange', 'data', 'n12t-selection.txt.xz')
CYC = argv[1] if len(argv) > 1 else os.path.join(repo, 'selection', 'data', 'zcycles_n12.txt')
GROUPS_PER_FILE = 6; BIG_PER_FILE = 8

def sha(path): return hashlib.sha256(open(path, 'rb').read()).hexdigest()
def lines(path):
    f = lzma.open(path, 'rt') if path.endswith('.xz') else open(path)
    return [l.split() for l in f if l.strip() and not l.startswith('#')]
sel = lines(SEL); cyc = [l[0] for l in lines(CYC)]
assert len(sel) == 362880 and len(cyc) == 203

def canon(x):
    i = x.index(min(x)); return x[i:] + x[:i]
def srot(x, j): j %= len(x); return x[j:] + x[:j]
def shead(x): return x[:len(x) - 2]
def stail(x, T): return srot(x, (len(x) if T == 'F' else len(x) - 2) - 1)[2:]

def closed_walks(fs):
    """the closed trails of full / short rows (strings), each started at its smallest row"""
    by_head = {}
    for i, (x, T) in enumerate(fs):
        assert shead(x) not in by_head; by_head[shead(x)] = i
    succ = [by_head[stail(x, T)] for x, T in fs]
    seen = [False] * len(fs); out = []
    for i in range(len(fs)):
        if seen[i]: continue
        w = []; j = i
        while not seen[j]: seen[j] = True; w.append(j); j = succ[j]
        assert j == i
        k = min(range(len(w)), key=lambda t: fs[w[t]])
        out.append([fs[t] for t in w[k:] + w[:k]])
    return out

# ---------------------------------------------------------------- the structure of the selection
fs = [(x, T) for x, T in sel if T != 'D']
D11 = [x for x, T in sel if T == 'D']
walks11 = closed_walks(fs)
small = [w for w in walks11 if len(w) <= 182]
big = [w for w in walks11 if len(w) > 182]
assert len(small) == 144 and len(big) == 112 and len(D11) == 6048
def gkey(x): return canon(x.replace('7', '').replace('8', '').replace('9', ''))
groups = collections.defaultdict(lambda: {'walks': [], 'dloops': []})
for w in small:
    ks = set(gkey(x) for x, _ in w); assert len(ks) == 1
    groups[ks.pop()]['walks'].append(w)
for x in D11: groups[gkey(x)]['dloops'].append(x)
assert len(groups) == 48
gkeys = sorted(groups)
for k in gkeys:
    g = groups[k]
    g['walks'].sort(key=len); g['dloops'].sort()
    assert [len(w) for w in g['walks']] == [63, 133, 182] and len(g['dloops']) == 126
    g['d9'] = [canon(k[:i] + '7' + k[i:]) for i in range(7)]
D9 = [d for k in gkeys for d in groups[k]['d9']]
D9set = set(D9); assert len(D9set) == 336
base = [(x[2:], T) for x, T in fs if x.startswith('98') and canon(x[2:]) not in D9set]
assert len(base) == 4704
assert len(set(canon(x) for x, _ in base) | D9set) == 5040
walks9 = sorted(closed_walks(base), key=len)
assert [len(w) for w in walks9] == [2280, 2424]

# ---------------------------------------------------------------- the Lean side: rows as (base, visible)
NUM = {str(i): i for i in range(8)}; NUM['8'] = 8; NUM['9'] = 11; NUM['B'] = 10
SAT, FINAL = 9, 10
def row(x, T): b = [NUM[c] for c in x]; return (b, len(b) if T == 'F' else len(b) - 2)
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
def transportWalk(rs, z, p):
    out = []
    for r in rs: out += portPath(r, z, p); p = portTarget(r, p)
    return out
def completionExit(rs, q):
    for r in rs: q = portTarget(r, q)
    return q
def closed(rs): return all(tail(rs[i]) == head(rs[(i + 1) % len(rs)]) for i in range(len(rs)))
def excess(rs): return len(rs) - sum(charge(r) for r in rs)
def cyc_eq(a, b): return len(a) == len(b) and any(rot(a, j) == b for j in range(len(a)))

W9 = [[row(x, T) for x, T in w] for w in walks9]
for w in W9: assert closed(w) and excess(w) % 7 == 0
circles = [[NUM[c] for c in word] for word in cyc]
assert all(len(c) == 9 and len(set(c)) == 9 and FINAL in c for c in circles)
circ_index = {}
for ci, c in enumerate(circles):
    for k in range(9): circ_index.setdefault(tuple(rot(c, k)), (ci, k))

def pointers(W, h):
    """MixedPointer for every port: the first row whose boundary vertex lies on a cycle"""
    out = []
    for j in range(h):
        p = j; found = None
        for ri, r in enumerate(W):
            hit = circ_index.get(tuple(insertLetter(head(r), FINAL, p)))
            if hit is not None: found = (0, j, hit[0], ri, p, hit[1]); break
            p = portTarget(r, p)
        assert found is not None, 'a port is not covered'
        out.append(found)
    return out

# long walks on 11 symbols and their pointers
bigdata = []
allbig = set()
for iw in range(2):
    for p1 in range(7):
        W10 = transportWalk(W9[iw], 8, p1)
        assert closed(W10)
        for p2 in range(8):
            W11 = transportWalk(W10, 11, p2)
            assert closed(W11) and excess(W11) % 9 == 0
            for r in W11: allbig.add((tuple(r[0]), r[1]))
            bigdata.append((iw, p1, p2, pointers(W11, 9)))
selbig = set((tuple(row(x, T)[0]), row(x, T)[1]) for w in big for x, T in w)
assert allbig == selbig, 'the long walks are not the 9-symbol walks transported twice'

# groups
def above(d):
    return [rot(rot(d, i) + [8], j) + [11] for i in range(len(d)) for j in range(len(d) + 1)]
G = []
for k in gkeys:
    g = groups[k]
    walks = [[row(x, T) for x, T in w] for w in g['walks']]
    dloops = [[NUM[c] for c in x] for x in g['dloops']]
    d9 = [[NUM[c] for c in x] for x in g['d9']]
    for w in walks:
        assert closed(w)
        ports = [0]
        for _ in range(8): ports.append(completionExit(w, ports[-1]))
        assert sorted(ports) == list(range(9))
    loc = {}
    for c, w in enumerate(walks):
        for o, r in enumerate(w): loc[tuple(canon(r[0]))] = (c, o)
    for o, d in enumerate(dloops): loc[tuple(canon(d))] = (3, o)
    assert len(loc) == 504
    ptrs = [loc[tuple(canon(t))] for d in d9 for t in above(d)]
    assert len(ptrs) == 504 and len(set(ptrs)) == 504
    mixed = [pointers(w * 9, 9) for w in walks]
    assert sum(len(w) for w in walks) == 378 and sum(charge(r) for w in walks for r in w) == 182
    G.append((walks, dloops, d9, ptrs, mixed))

# completeness on 9 symbols
# (the rows of the two walks are listed once more in chunks of 64, so that a pointer is two short list walks)
CHUNK = 64
chunks9 = [w[i:i + CHUNK] for w in W9 for i in range(0, len(w), CHUNK)]
assert [r for ch in chunks9 for r in ch] == [r for w in W9 for r in w]
loc9 = {}
for c, ch in enumerate(chunks9):
    for o, r in enumerate(ch): loc9[tuple(canon(r[0]))] = (c, o)
D9n = [[NUM[c] for c in d] for d in D9]
for o, d in enumerate(D9n): loc9[tuple(canon(d))] = (len(chunks9), o)
assert len(loc9) == 5040
ptrs9 = {}
for a in range(1, 8):
    rest = [x for x in range(1, 8) if x != a]
    ptrs9[a] = [loc9[tuple(canon([0, a] + list(t)))] for t in itertools.permutations(rest)]

# ---------------------------------------------------------------- output
def L(xs): return '[' + ','.join(str(x) for x in xs) + ']'
def R(r): return '⟨%s,%d,%d⟩' % (L(r[0]), SAT, r[1])
def rows_lit(rs, ind='  '): return '[\n' + ',\n'.join(ind + R(r) for r in rs) + ']'
def pairs(ps): return '[' + ','.join('(%d,%d)' % p for p in ps) + ']'
def mptrs(ps): return '[' + ','.join('⟨%d,%d,%d,%d,%d,%d⟩' % p for p in ps) + ']'
SRC = ('Generated by gen_cert.py from\n'
       '  arrange/data/%s  (SHA-256 %s)\n  selection/data/%s  (SHA-256 %s)' % (
           os.path.basename(SEL), sha(SEL), os.path.basename(CYC), sha(CYC)))
HEAD = '''
namespace SuperpermutationUpperBound1771.Certificate

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound.Certificates.CircleBase
open SuperpermutationUpperBound1771

set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option Elab.async false
'''
FOOT = '\nend SuperpermutationUpperBound1771.Certificate\n'
P = 'SuperpermutationUpperBound1771.Certificate.'
os.makedirs(OUT, exist_ok=True)
modules = []
def write(name, imports, doc, body):
    text = ''.join('import %s\n' % i for i in imports) + '\n/-! %s\n\n%s -/\n' % (doc, SRC) + HEAD + '\n' + body + FOOT
    with open(os.path.join(OUT, name + '.lean'), 'w', encoding='utf-8', newline='\n') as f: f.write(text)
    modules.append(name)
def chain(names, lemma='List.forall_mem_cons'):
    return ''.join('  %s.2 ⟨%s,\n' % (lemma, n) for n in names) + '  (fun _ h => nomatch h)' + '⟩' * len(names)

for name, w in zip('AB', W9):
    write('Walk' + name, [P + 'Checks'],
          'One of the two closed walks of the selection on 9 symbols: %d rows, %d of them short.' % (len(w), sum(charge(r) for r in w) // 2),
          'def walk%s : List (Row Nat) := %s\n\n' % (name, rows_lit(w)) +
          'theorem walk%s_ok : WalkOK walk%s := by decide +kernel\n\n' % (name, name) +
          'theorem walk%s_counts : walk%s.length = %d ∧ (walk%s.map Row.charge).sum = %d := by\n  decide +kernel\n\n' % (name, name, len(w), name, sum(charge(r) for r in w)) +
          '#print axioms walk%s_ok\n#print axioms walk%s_counts\n' % (name, name))

write('Walks9', [P + 'WalkA', P + 'WalkB'], 'The selection on 9 symbols as a level.',
      '''def walks9 : List (List (Row Nat)) := [walkA, walkB]

theorem walks9_level : Level alph8 7 walks9 := by
  apply level9_of_walks
  intro w hw
  simp only [walks9, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact walkA_ok
  · exact walkB_ok

theorem walks9_rowCount : walks9.flatten.length = %d := by
  simp [walks9, walkA_counts.1, walkB_counts.1]

theorem walks9_charge : (walks9.flatten.map Row.charge).sum = %d := by
  simp [walks9, walkA_counts.2, walkB_counts.2]
''' % (sum(len(w) for w in W9), sum(charge(r) for w in W9 for r in w)))

write('Circles', [P + 'Checks'], 'The 203 connector cycles on 12 symbols (letter 10 is the completion letter).',
      'def circles11 : List (List Nat) := [\n' + ',\n'.join('  ' + L(c) for c in circles) + ']\n\n' +
      '''theorem circles11_valid : CircleFamilyValid 9 circles11 := by
  unfold CircleFamilyValid
  decide +kernel

theorem circles11_support : ∀ c ∈ circles11, ∀ a ∈ c, a ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11] := by
  decide +kernel

theorem circles11_length : circles11.length = 203 := by decide +kernel

#print axioms circles11_valid
#print axioms circles11_support
''')

gfiles = []
for f0 in range(0, 48, GROUPS_PER_FILE):
    name = 'Groups%02d' % (f0 // GROUPS_PER_FILE); gfiles.append(name)
    body = []
    for gi in range(f0, min(48, f0 + GROUPS_PER_FILE)):
        walks, dloops, d9, ptrs, mixed = G[gi]
        body.append('/-- Group %d: the 2-loops above the 9-symbol loops with the cyclic order %s of the letters 0..6. -/' % (gi, gkeys[gi]))
        body.append('def g%d : Group where\n  walks := [\n%s]\n  dloops := [\n%s]\n  d9 := %s\n' % (
            gi, ',\n'.join('    ' + rows_lit(w, '      ') for w in walks),
            ',\n'.join('    ' + L(d) for d in dloops), '[' + ', '.join(L(d) for d in d9) + ']'))
        body.append('def g%d_ptrs : List (Nat × Nat) := %s\n' % (gi, pairs(ptrs)))
        body.append('def g%d_mixed : List (List MixedPointer) := [\n%s]\n' % (gi, ',\n'.join('  ' + mptrs(m) for m in mixed)))
        body.append('theorem g%d_ok : GroupOK circles11 g%d g%d_ptrs g%d_mixed := by decide +kernel\n' % (gi, gi, gi, gi))
        body.append('#print axioms g%d_ok\n' % gi)
    write(name, [P + 'Circles'], 'Six of the 48 groups: three short closed walks, 126 loops without a row, the pointers.', '\n'.join(body))

bfiles = []
for f0 in range(0, len(bigdata), BIG_PER_FILE):
    name = 'Big%02d' % (f0 // BIG_PER_FILE); bfiles.append(name)
    body = []
    for iw, p1, p2, ptrs in bigdata[f0:f0 + BIG_PER_FILE]:
        body.append('def bigPtr_%d_%d_%d : List MixedPointer := %s\n' % (iw, p1, p2, mptrs(ptrs)))
        body.append('theorem big_%d_%d_%d : BigOK circles11 walks9 %d %d %d bigPtr_%d_%d_%d := by decide +kernel\n' % ((iw, p1, p2) * 3))
    body.append('#print axioms big_%d_%d_%d\n' % bigdata[f0][:3])
    write(name, [P + 'Walks9', P + 'Circles'], 'Cycle pointers for eight of the 112 long walks on 11 symbols.', '\n'.join(body))

write('D9', [P + 'Checks'], 'The 336 2-loops of the 9-symbol selection without a row (seven per group, in the order of the groups).',
      'def d9all : List (List Nat) := [\n' + ',\n'.join('  ' + L(d) for d in D9n) + ']\n')

write('Chunks9', [P + 'Walks9'], 'The rows of the two 9-symbol walks once more, in chunks of %d, for the pointers of the completeness check.' % CHUNK,
      'def chunks9 : List (List (Row Nat)) := [\n' + ',\n'.join('  ' + rows_lit(ch, '    ') for ch in chunks9) + ']\n\n' +
      'theorem chunks9_flatten : chunks9.flatten = walks9.flatten := by decide +kernel\n')

c9files = []
for a in range(1, 8):
    name = 'Complete9_%d' % a; c9files.append(name)
    write(name, [P + 'Chunks9', P + 'D9'],
          'Completeness on 9 symbols, the 720 orderings that start with 0, %d: each is a row of a walk or a loop without a row.' % a,
          'def ptrs9_%d : List (Nat × Nat) := %s\n\n' % (a, pairs(ptrs9[a])) +
          'theorem complete9_%d : coveredB chunks9 d9all (canonPart %d) ptrs9_%d = true := by decide +kernel\n\n#print axioms complete9_%d\n' % (a, a, a, a))

write('Groups', [P + 'D9'] + [P + g for g in gfiles], 'The 48 groups.',
      'def groups : List Group := [' + ', '.join('g%d' % i for i in range(48)) + ']\n\n' +
      'theorem groups_length : groups.length = 48 := by decide +kernel\n\n' +
      'theorem groups_d9 : groups.flatMap Group.d9 = d9all := by decide +kernel\n\n' +
      'theorem groups_facts : ∀ g ∈ groups, GroupFacts circles11 g :=\n' + chain(['g%d_ok.facts' % i for i in range(48)]) + '\n\n' +
      '#print axioms groups_facts\n')

write('Complete9', [P + 'Groups'] + [P + c for c in c9files],
      'Completeness on 9 symbols: every 2-loop is a row of a walk or one of the 336 loops without a row.',
      'def ptrs9 : Nat → List (Nat × Nat)\n' + ''.join('  | %d => ptrs9_%d\n' % (a, a) for a in range(1, 8)) + '  | _ => []\n\n' +
      'theorem complete9 {x : List Nat} (hx : x.Perm alph8) :\n'
      '    (∃ r ∈ walks9.flatten, CyclicEq r.base x) ∨ (∃ d ∈ groups.flatMap Group.d9, CyclicEq d x) := by\n'
      '  rw [← chunks9_flatten, groups_d9]\n'
      '  exact complete9_of_parts ptrs9\n    (' + chain(['complete9_%d' % a for a in range(1, 8)]).strip() + ') hx\n\n'
      '#print axioms complete9\n')

items = ', '.join('(%d, %d, %d, bigPtr_%d_%d_%d)' % ((iw, p1, p2) * 2) for iw, p1, p2, _ in bigdata)
write('Cert', [P + 'Complete9'] + [P + b for b in bfiles], 'The certificate of the selection, assembled.',
      'def bigItems : List (Nat × Nat × Nat × List MixedPointer) := [' + items + ']\n\n' +
      'theorem bigItems_ok : ∀ x ∈ bigItems, BigOK circles11 walks9 x.1 x.2.1 x.2.2.1 x.2.2.2 :=\n' +
      chain(['big_%d_%d_%d' % (iw, p1, p2) for iw, p1, p2, _ in bigdata]) + '\n\n' +
      '''theorem bigItems_complete : ∀ iw < 2, ∀ p1 < 7, ∀ p2 < 8,
    ∃ x ∈ bigItems, x.1 = iw ∧ x.2.1 = p1 ∧ x.2.2.1 = p2 := by decide +kernel

theorem big_all : ∀ iw < walks9.length, ∀ p1 < 7, ∀ p2 < 8,
    ∃ ptrs, BigOK circles11 walks9 iw p1 p2 ptrs := by
  intro iw hiw p1 hp1 p2 hp2
  obtain ⟨x, hx, h1, h2, h3⟩ := bigItems_complete iw hiw p1 hp1 p2 hp2
  have h := bigItems_ok x hx
  rw [h1, h2, h3] at h
  exact ⟨_, h⟩

/-- The certificate of the selection. -/
def cert : Cert where
  walks9 := walks9
  groups := groups
  circles := circles11
  level9 := walks9_level
  rowCount9 := walks9_rowCount
  charge9 := walks9_charge
  complete9 := fun _ hx => complete9 hx
  groupCount := groups_length
  groupFacts := groups_facts
  circles_valid := circles11_valid
  circles_support := circles11_support
  circleCount := circles11_length
  bigSafe := bigSafe_of_ptrs walks9_level big_all
''')
with open(os.path.join(OUT, 'modules.txt'), 'w', newline='\n') as f: f.write('\n'.join(modules) + '\n')
print('wrote', len(modules), 'modules:', ' '.join(modules))
print('max pointer row (long walks):', max(p[3] for _, _, _, ps in bigdata for p in ps), '; (short walks):', max(p[3] for g in G for m in g[4] for p in m))
