"""gen_blocks.py - write the Lean certificates of the nested blocks.

    gen_blocks.py NAME [NAME ...] [--out DIR]        NAME in CONF below (W103, S133, X103, W133, S163)

A block sits above the canonical loop d0 (a Lean list); the block file letters are, in order: the old letters
(d0[0], d0[1], ...), the three tokens t1 t2 t3 (the letters added one, two and three levels above d0), the
distinguished letter (Lean 9) and, in the cycle file, the completion letter (Lean 10).  The frame of the block in
Lean is `{ d0, t1, t2, t3, z }` with z the letter added one level above the block (`BlockG.lean`).

Everything Lean checks (`BlockOK`, `BlockPorts`) is checked here first with functions that follow the Lean
definitions (as gen_blockB.py of step (B)).  Output, in SuperpermutationUpperBound43586371/Certificate/:
  Block<NAME>Data.lean    the frame, walks (with start ports), loops without a row, cover pointers, cycles
  Block<NAME>Walks.lean   the walk checks (one theorem per walk)
  Block<NAME>Cover.lean   the cover of the loops above d0 (chunks of CHUNK loops, one theorem per chunk; for the
                          blocks in SPLIT each chunk is its own module Block<NAME>Cover<i>.lean)
  Block<NAME>Ports.lean   the cycle pointers of the walks written h/g times, on the completion of the block level
  Block<NAME>.lean        BlockOK, BlockPorts and the BlockCert
"""
import sys, os, hashlib, math

here = os.path.dirname(os.path.abspath(__file__))
c15 = os.path.join(here, 'data')
root = here
OUT = os.path.join(here, 'SuperpermutationUpperBound43586371', 'Certificate')
if '--out' in sys.argv:
    i = sys.argv.index('--out'); OUT = sys.argv[i + 1]; del sys.argv[i:i + 2]
NS = 'SuperpermutationUpperBound43586371'

SAT, FINAL = 9, 10
ALPH10 = [11, 8, 0, 1, 2, 3, 4, 5, 6, 7]          # Lean alph10
ALPH2 = [14, 13, 12] + ALPH10                     # Lean alphabet 2
ALPHB2 = [17, 16, 15] + ALPH2                     # Lean 17 :: 16 :: 15 :: alphabet 2
F0 = dict(d0=[1, 2, 3, 4, 5, 6, 7], d0lean='[1, 2, 3, 4, 5, 6, 7]', t=(0, 8, 11), z=12)
F1 = dict(d0=ALPH10, d0lean='alph10', t=(12, 13, 14), z=15)
F2 = dict(d0=ALPH2, d0lean='alphabet 2', t=(15, 16, 17), z=18)
F3 = dict(d0=ALPHB2, d0lean='17 :: 16 :: 15 :: alphabet 2', t=(18, 19, 20), z=21)
CONF = {
    'W103': dict(F1, file='w103_0.6245_1.txt', cyc='cyc_w103_0.6245_1.txt'),
    'S133': dict(F2, file='s133_0.txt', cyc='cyc_s133_0.txt'),
    'X103': dict(F1, file='w103_0.4795_0.txt', cyc='cyc_w103_0.4795_0.txt'),
    'W133': dict(F2, file='w133_0.txt', cyc='cyc_w133_0.txt'),
    'S163': dict(F3, file='s163_old2_0.txt', cyc='cyc_s163_old2_0_ref.txt'),
    # cycles one level up (BlockCertUp): leanB's 26 cycles on 16 symbols for the block transported once
    'S103': dict(F1, file='s103_old2_0.txt', cyc1='cyc_t_s103_old2_0_n16.txt'),
    # the same for W103 and X103, cycles chosen on 16 symbols by blockcyc.py (leanC/cyc16, 20 each, optimal)
    'W103U': dict(F1, file='w103_0.6245_1.txt', cyc1='cyc_t_w103_0.6245_1_n16.txt'),
    'X103U': dict(F1, file='w103_0.4795_0.txt', cyc1='cyc_t_w103_0.4795_0_n16.txt'),
    # no seed (opt/const_limit): (7,3) blocks above the loops of [1..7] (tokens 0, 8, 11, next letter 12, so that
    # the letters one level up are alph10), with their cycles on 13 symbols
    'D73': dict(F0, file='block_7_3_enum14_0.txt', cyc1='cyc_t_block_7_3_enum14_0_n13.txt'),
    'B73': dict(F0, file='b73_dw_0.txt', cyc1='cyc_t_b73_dw_0_n13.txt'),
    # cycles one level up for blocks already certified (their Data / OK are reused): const_limit's covers
    'S133U': dict(F2, file='s133_0.txt', cyc1='cyc_up_s133_0_alph.txt', base='S133', upch=1, psplit=2),
    'W133U': dict(F2, file='w133_0.txt', cyc1='cyc_up_w133_0_alph.txt', base='W133', upch=1, psplit=2),
    'S163U': dict(F3, file='s163_old2_0.txt', cyc1='cyc_up_s163_old2_0_alph.txt', base='S163', upch=2),
}
CHUNK = int(os.environ.get('CHUNK', '700'))       # loops per cover theorem
SPLIT = {'S163': 300}                             # blocks whose cover chunks (of this many loops) go into separate modules
DIGITS = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'


def sha(path): return hashlib.sha256(open(path, 'rb').read()).hexdigest()
def lines(path): return [l.split() for l in open(path) if l.strip() and not l.startswith('#')]
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
def closed(rs): return len(rs) > 0 and all(tail(rs[i]) == head(rs[(i + 1) % len(rs)]) for i in range(len(rs)))
def excess(rs): return len(rs) - sum(charge(r) for r in rs)
def canon(x): i = x.index(min(x)); return tuple(x[i:] + x[:i])
def above3T(a, b, c, d):
    return [rot(rot(rot(d, i) + [a], j) + [b], k) + [c]
            for i in range(len(d)) for j in range(len(d) + 1) for k in range(len(d) + 2)]


def build(name):
    cf = CONF[name]
    d0, (t1, t2, t3), z = cf['d0'], cf['t'], cf['z']
    BLOCK = os.path.join(c15, cf['file']); CYC = os.path.join(c15, cf.get('cyc', cf.get('cyc1')))
    m0 = len(d0); h = m0 + 2
    alph = [t3, t2, t1] + d0; alph1 = [z] + alph
    assert len(set(alph1)) == len(alph1) and SAT not in alph1 and FINAL not in alph1
    NUM = {DIGITS[i]: d0[i] for i in range(m0)}
    NUM.update({DIGITS[m0]: t1, DIGITS[m0 + 1]: t2, DIGITS[m0 + 2]: t3})
    DIST = DIGITS[m0 + 3]; NUMC = dict(NUM); NUMC[DIGITS[m0 + 4]] = FINAL
    sel = lines(BLOCK)
    nloops = m0 * (m0 + 1) * (m0 + 2)
    assert len(sel) == nloops, (len(sel), nloops)
    assert all(T in 'FSD' for _, T in sel)
    assert all(DIST not in x for x, _ in sel)
    rows = [([NUM[c] for c in x], len(x) if T == 'F' else len(x) - 2) for x, T in sel if T in 'FS']
    dloops = sorted([NUM[c] for c in x] for x, T in sel if T == 'D')
    by_head = {}
    for i, r in enumerate(rows):
        assert tuple(head(r)) not in by_head; by_head[tuple(head(r))] = i
    succ = [by_head[tuple(tail(r))] for r in rows]
    assert sorted(succ) == list(range(len(rows)))
    seen = [False] * len(rows); walks = []
    for i in range(len(rows)):
        if seen[i]: continue
        w = []; j = i
        while not seen[j]: seen[j] = True; w.append(j); j = succ[j]
        k = min(range(len(w)), key=lambda t: rows[w[t]])
        walks.append([rows[t] for t in w[k:] + w[:k]])
    walks.sort(key=lambda w: (-len(w), w))
    for w in walks:
        assert closed(w)
        for b, v in w:
            assert sorted(b) == sorted(alph) and len(set(b)) == len(b) and SAT not in b and v in (h + 1, h - 1) and 1 <= v <= len(b)
    nrows = sum(len(w) for w in walks); nq = sum(charge(r) for w in walks for r in w)
    for d in dloops: assert sorted(d) == sorted(alph)
    G = []
    for w in walks:
        e = excess(w); g = math.gcd(e, h); m = h // g
        assert m > 0 and (m * e) % h == 0
        ps = [q for p in range(g) for q in orbitPorts(w, m, p)]
        assert sorted(ps) == list(range(h)), (len(w), e, g)
        G.append(g)
    winfo = [(len(w), sum(1 for r in w if r[1] == h + 1), sum(1 for r in w if r[1] == h - 1), excess(w), g)
             for w, g in zip(walks, G)]
    # cover: every loop above d0 is a row base or a loop without a row, up to rotation
    loc = {}
    for c, w in enumerate(walks):
        for o, r in enumerate(w): loc[canon(r[0])] = (c, o)
    for o, d in enumerate(dloops): loc[canon(d)] = (len(walks), o)
    A3 = above3T(t1, t2, t3, d0)
    assert len(A3) == nloops and len(set(canon(t) for t in A3)) == nloops
    ptrs = [loc[canon(t)] for t in A3]
    assert len(set(ptrs)) == nloops == nrows + len(dloops)
    # one transport later: inventory of the trails
    T1 = []
    for w, g in zip(walks, G):
        m = h // g
        for p in range(g):
            W = transportWalk(w * m, z, p)
            assert closed(W) and excess(W) % (h + 1) == 0
            T1.append(W)
    assert sorted((tuple(b), v) for W in T1 for b, v in W) == sorted(
        (tuple(b), v) for w in walks for r in w for b, v in transRows(r, z))
    up = 'cyc1' in cf
    cyc1 = P1 = None
    if up:
        # cycles one level up (h + 1 ports): letter m0+3 of the transported file is z, letter m0+5 is 10
        CYC = os.path.join(c15, cf['cyc1'])
        NUM1 = dict(NUM); NUM1[DIGITS[m0 + 3]] = z; NUM1[DIGITS[m0 + 5]] = FINAL
        cyc1 = [[NUM1[ch] for ch in l[0]] for l in lines(CYC)]
        idx1 = {}
        for ci, c in enumerate(cyc1):
            assert len(c) == h + 1 and len(set(c)) == h + 1 and FINAL in c and SAT not in c and set(c) <= set(alph1) | {FINAL}
            for k in range(h + 1): idx1.setdefault(tuple(rot(c, k)), (ci, k))
        P1 = []
        for W in T1:
            o = []
            for j in range(h + 1):
                p = j; found = None
                for ri, r in enumerate(W):
                    hit = idx1.get(tuple(insertLetter(head(r), FINAL, p)))
                    if hit is not None: found = (0, j, hit[0], ri, p, hit[1]); break
                    p = portTarget(r, p)
                assert found is not None, 'a port is not covered'
                o.append(found)
            P1.append(o)
        print(name, 'cycles one level up:', len(cyc1), 'used', len(set(q[2] for o in P1 for q in o)),
              'max pointer row', max(q[3] for o in P1 for q in o))
    # cycles on the completion of the block level (h ports), pointers on the walks written h/g times
    cyc = [] if up else [[NUMC[ch] for ch in l[0]] for l in lines(CYC)]
    idx = {}
    for ci, c in enumerate(cyc):
        assert len(c) == h and len(set(c)) == h and FINAL in c and SAT not in c and set(c) <= set(alph) | {FINAL}
        for k in range(h): idx.setdefault(tuple(rot(c, k)), (ci, k))
    P = []
    for w, g in ([] if up else zip(walks, G)):
        W = w * (h // g); out = []
        for j in range(h):
            p = j; found = None
            for ri, r in enumerate(W):
                hit = idx.get(tuple(insertLetter(head(r), FINAL, p)))
                if hit is not None: found = (0, j, hit[0], ri, p, hit[1]); break
                p = portTarget(r, p)
            assert found is not None, 'a port is not covered'
            out.append(found)
        P.append(out)
    info = dict(name=name, walks=winfo, nrows=nrows, nq=nq, nd=len(dloops), ncyc=len(cyc), h=h,
                trails=len(T1), maxptr=max([p[3] for ps in P for p in ps] or [0]), cycused=len(set(p[2] for ps in P for p in ps)))
    print(info)
    write(name, cf, BLOCK, CYC, walks, G, dloops, ptrs, cyc, P, nrows, nq, info, cyc1, P1)
    return info


def write(name, cf, BLOCK, CYC, walks, G, dloops, ptrs, cyc, P, nrows, nq, info, cyc1=None, P1=None):
    def L(xs): return '[' + ','.join(str(x) for x in xs) + ']'
    def R(r): return '⟨%s,%d,%d⟩' % (L(r[0]), SAT, r[1])
    def rows_lit(rs, ind='  '): return '[\n' + ',\n'.join(ind + R(r) for r in rs) + ']'
    def pairs(ps): return '[' + ','.join('(%d,%d)' % p for p in ps) + ']'
    def mptrs(ps): return '[' + ','.join('⟨%d,%d,%d,%d,%d,%d⟩' % p for p in ps) + ']'
    def rel(p): return os.path.relpath(p, root).replace(os.sep, '/')
    SRC = ('Generated by gen_blocks.py %s from\n  %s  (SHA-256 %s)\n  %s  (SHA-256 %s)'
           % (name, rel(BLOCK), sha(BLOCK), rel(CYC), sha(CYC)))
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
    P_ = NS + '.Certificate.'
    n = name.lower()
    def out(mod, imports, doc, body):
        text = ''.join('import %s\n' % i for i in imports) + '\n/-! %s\n\n%s -/\n' % (doc, SRC) + HEAD + '\n' + body + FOOT
        with open(os.path.join(OUT, mod + '.lean'), 'w', encoding='utf-8', newline='\n') as f: f.write(text)
    if cf.get('base'):
        write_upbase(name, n, out, P_, mptrs, P1, cf, cyc1, L)
        return
    t1, t2, t3 = cf['t']
    frame = '{ d0 := %s, t1 := %d, t2 := %d, t3 := %d, z := %d }' % (cf['d0lean'], t1, t2, t3, cf['z'])
    nw = len(walks)
    body = 'def %sFrame : Frame := %s\n\n' % (n, frame)
    for i, (w, g) in enumerate(zip(walks, G)):
        body += 'def %sItem%d : List (Row Nat) × Nat := (%s, %d)\n\n' % (n, i, rows_lit(w, '  '), g)
    body += 'def %sItems : List (List (Row Nat) × Nat) := [%s]\n\n' % (n, ', '.join('%sItem%d' % (n, i) for i in range(nw)))
    body += 'def %sD : List (List Nat) := [\n%s]\n\n' % (n, ',\n'.join('  ' + L(d) for d in dloops))
    body += 'def %sPtrs : List (Nat × Nat) := %s\n\n' % (n, pairs(ptrs))
    body += 'def %sCyc : List (List Nat) := [\n%s]\n\n' % (n, ',\n'.join('  ' + L(c) for c in cyc))
    if cyc1 is not None:
        body += 'def %sCyc1 : List (List Nat) := [\n%s]\n\n' % (n, ',\n'.join('  ' + L(c) for c in cyc1))
    body += ('def %sData : BlockData where\n  items := %sItems\n  dloops := %sD\n  ptrs := %sPtrs\n  cyc := %sCyc\n'
             '  nrows := %d\n  nq := %d\n  nd := %d\n  ncyc := %d\n' % (n, n, n, n, n, nrows, nq, len(dloops), len(cyc)))
    out('Block%sData' % name, [NS + '.BlockG'],
        'Block %s above the canonical loop d0 = `%s`, tokens %d, %d, %d, next letter %d: %d closed walks of full and short\n'
        'rows (%d rows, total charge %d, start ports %s), %d loops without a row, the pointers of the %d loops above d0,\n'
        'and %d connector cycles for the completion of the block level (%d ports).'
        % (name, cf['d0lean'], t1, t2, t3, cf['z'], nw, nrows, nq, G, len(dloops), len(ptrs), len(cyc), info['h']), body)
    # walks
    body = ''
    for i in range(nw):
        body += ('theorem %sItem%d_ok : BWalkOK %sFrame %sItem%d := by\n'
                 '  unfold BWalkOK BasedOn ClosedTrail CyclicallyCompatible Row.Compatible\n  decide +kernel\n\n' % (n, i, n, n, i))
    body += ('theorem %sItems_ok : ∀ wg ∈ %sItems, BWalkOK %sFrame wg := by\n  intro wg hwg\n'
             '  simp only [%sItems, List.mem_cons, List.not_mem_nil, or_false] at hwg\n  rcases hwg with %s\n  exacts [%s]\n\n'
             % (n, n, n, n, ' | '.join(['rfl'] * nw), ', '.join('%sItem%d_ok' % (n, i) for i in range(nw))))
    body += ('theorem %sFrame_ok : %sFrame.OK := by\n  unfold Frame.OK\n  decide +kernel\n\n' % (n, n))
    body += ('theorem %sD_ok : ∀ e ∈ %sD, e.Perm %sFrame.alph := by decide +kernel\n\n' % (n, n, n))
    body += ('theorem %sRest_ok : %sData.walks.flatten.length = %sData.nrows ∧\n'
             '    (%sData.walks.flatten.map Row.charge).sum = %sData.nq ∧ %sData.dloops.length = %sData.nd ∧\n'
             '    CircleFamilyValid %sFrame.h %sData.cyc ∧ (∀ c ∈ %sData.cyc, ∀ a ∈ c, a ∈ 10 :: %sFrame.alph) ∧\n'
             '    %sData.cyc.length = %sData.ncyc := by\n  unfold CircleFamilyValid\n  decide +kernel\n\n'
             % ((n,) * 13))
    if cyc1 is not None:
        body += ('theorem %sCyc1_ok : CircleFamilyValid (%sFrame.h + 1) %sCyc1 ∧\n'
                 "    (∀ c ∈ %sCyc1, ∀ a ∈ c, a ∈ 10 :: %sFrame.alph') := by\n  unfold CircleFamilyValid\n  decide +kernel\n\n"
                 % ((n,) * 5))
    body += '#print axioms %sItems_ok\n#print axioms %sRest_ok\n' % (n, n)
    out('Block%sWalks' % name, [P_ + 'Block%sData' % name], 'The walk checks of block %s.' % name, body)
    # cover, in chunks: chunk i is ((L.drop s).drop s ...).take s
    nl = len(ptrs); s = SPLIT.get(name, CHUNK); nch = (nl + s - 1) // s
    Lexpr = 'above3T %sFrame.t1 %sFrame.t2 %sFrame.t3 %sFrame.d0' % (n, n, n, n)
    def dropped(i):
        e = '(%s)' % Lexpr
        for _ in range(i): e = '(List.drop %d %s)' % (s, e)
        return e
    def chunkdef(i):
        return 'def %sPtrs%d : List (Nat × Nat) := %s\n\n' % (n, i, pairs(ptrs[i * s:(i + 1) * s]))
    def chunkthm(i):
        return ('theorem %sCover%d : coveredB %sData.walks %sData.dloops (List.take %d %s) %sPtrs%d = true := by\n'
                '  decide +kernel\n\n' % (n, i, n, n, s, dropped(i), n, i))
    def chunk(i): return chunkdef(i) + chunkthm(i)
    split = name in SPLIT
    body = ''
    imports = [P_ + 'Block%sData' % name]
    if split:   # one module per chunk: the kernel's memory grows within a module
        for i in range(nch):
            out('Block%sCover%d' % (name, i), [P_ + 'Block%sData' % name],
                'Chunk %d of the cover of the loops above d0 for block %s (%d loops per chunk).' % (i, name, s), chunk(i))
        imports = [P_ + 'Block%sCover%d' % (name, i) for i in range(nch)]
    else:
        body = ''.join(chunkdef(i) for i in range(nch)) + ''.join(chunkthm(i) for i in range(nch))
    # assemble with forall_mem_take_drop
    def chain(i):
        if i == nch - 1:
            return 'forall_mem_of_take_eq %d (by decide +kernel) (coveredB_sound _ _ %sCover%d)' % (s, n, i)
        return 'forall_mem_take_drop %d (coveredB_sound _ _ %sCover%d) (%s)' % (s, n, i, chain(i + 1))
    body += ('theorem %sCover_ok : ∀ t ∈ %s,\n    (∃ r ∈ %sData.walks.flatten, CyclicEq r.base t) ∨ (∃ e ∈ %sData.dloops, CyclicEq e t) :=\n  %s\n\n'
             % (n, Lexpr, n, n, chain(0)))
    body += '#print axioms %sCover_ok\n' % n
    out('Block%sCover' % name, imports,
        'The cover of the %d loops above d0 for block %s, in %d chunks of at most %d loops.' % (nl, name, nch, s), body)
    print('cover chunks:', nch, 'modules:', ' '.join('Certificate/Block%sCover%d' % (name, i) for i in range(nch)) if split else '-')
    if cyc1 is not None:
        write_up(name, n, out, P_, mptrs, P1)
        return
    # ports
    body = ''
    for i in range(nw):
        body += 'def %sPorts%d : List MixedPointer := %s\n\n' % (n, i, mptrs(P[i]))
        body += ('theorem %sPorts%d_ok : PortsCovered (rep (%sFrame.h / %sItem%d.2) %sItem%d.1) %sCyc %sFrame.h %sPorts%d := by\n'
                 '  decide +kernel\n\n' % (n, i, n, n, i, n, i, n, n, n, i))
    body += ('theorem %sPorts_ok : BlockPorts %sFrame %sData := by\n  intro wg hwg\n'
             '  simp only [%sData, %sItems, List.mem_cons, List.not_mem_nil, or_false] at hwg\n  rcases hwg with %s\n  exacts [%s]\n\n'
             % (n, n, n, n, n, ' | '.join(['rfl'] * nw), ', '.join('⟨_, %sPorts%d_ok⟩' % (n, i) for i in range(nw))))
    body += '#print axioms %sPorts_ok\n' % n
    out('Block%sPorts' % name, [P_ + 'Block%sData' % name],
        'Cycle pointers for the %d walks of block %s, each written h/g times, on the completion of the block level.' % (nw, name), body)
    # cert
    body = ('theorem %sOK : BlockOK %sFrame %sData where\n  frame := %sFrame_ok\n  walks := %sItems_ok\n  dloops := %sD_ok\n'
            '  cover := %sCover_ok\n  nrows := %sRest_ok.1\n  nq := %sRest_ok.2.1\n  nd := %sRest_ok.2.2.1\n'
            '  valid := %sRest_ok.2.2.2.1\n  support := %sRest_ok.2.2.2.2.1\n  ncyc := %sRest_ok.2.2.2.2.2\n\n' % ((n,) * 13))
    body += ('/-- Block %s with its checks. -/\ndef %sCert : BlockCert where\n  F := %sFrame\n  B := %sData\n  ok := %sOK\n  ports := %sPorts_ok\n\n'
             % (name, n, n, n, n, n))
    body += '#print axioms %sCert\n' % n
    out('Block%s' % name, [P_ + 'Block%sWalks' % name, P_ + 'Block%sCover' % name, P_ + 'Block%sPorts' % name],
        'Block %s, checked.' % name, body)


UPCH = 4   # trails per module of pointer checks one level up (leanB: 7 trails took 4.4 GB)


def write_up(name, n, out, P_, mptrs, P1):
    nt = len(P1); s = UPCH; nch = (nt + s - 1) // s
    T = '(%sData.trails %sFrame)' % (n, n)
    def dropped(i):
        e = T
        for _ in range(i): e = '(List.drop %d %s)' % (s, e)
        return e
    mods = []
    for i in range(nch):
        body = 'def %sUpPtrs%d : List (List MixedPointer) := [\n%s]\n\n' % (
            n, i, ',\n'.join('  ' + mptrs(p) for p in P1[i * s:(i + 1) * s]))
        body += ('theorem %sUp%d : portsB %sCyc1 (%sFrame.h + 1) (List.take %d %s) %sUpPtrs%d = true := by\n'
                 '  decide +kernel\n\n#print axioms %sUp%d\n' % (n, i, n, n, s, dropped(i), n, i, n, i))
        out('Block%sUp%d' % (name, i), [NS + '.BlockUp', P_ + 'Block%sData' % name],
            'Cycle pointers one level up (h + 1 ports) for trails %d..%d of the %d trails of block %s.'
            % (i * s, min(nt, (i + 1) * s) - 1, nt, name), body)
        mods.append('Certificate/Block%sUp%d' % (name, i))
    def chain(i):
        if i == nch - 1:
            return "forall_mem_of_take_eq' %d (by decide +kernel) (portsB_sound _ _ %sUp%d)" % (s, n, i)
        return "forall_mem_take_drop' %d (portsB_sound _ _ %sUp%d) (%s)" % (s, n, i, chain(i + 1))
    body = ('theorem %sOK : BlockOK %sFrame %sData where\n  frame := %sFrame_ok\n  walks := %sItems_ok\n  dloops := %sD_ok\n'
            '  cover := %sCover_ok\n  nrows := %sRest_ok.1\n  nq := %sRest_ok.2.1\n  nd := %sRest_ok.2.2.1\n'
            '  valid := %sRest_ok.2.2.2.1\n  support := %sRest_ok.2.2.2.2.1\n  ncyc := %sRest_ok.2.2.2.2.2\n\n' % ((n,) * 13))
    body += ('theorem %sPorts1 : ∀ W ∈ %s, ∃ m, PortsCovered W %sCyc1 (%sFrame.h + 1) m :=\n  %s\n\n'
             % (n, T, n, n, chain(0)))
    body += ('/-- Block %s with its cycles one level up, checked. -/\ndef %sCert : BlockCertUp where\n  F := %sFrame\n'
             '  B := %sData\n  ok := %sOK\n  cyc1 := %sCyc1\n  valid1 := %sCyc1_ok.1\n  support1 := %sCyc1_ok.2\n'
             '  ports1 := %sPorts1\n\n#print axioms %sCert\n' % ((name,) + (n,) * 9))
    out('Block%s' % name, [NS + '.BlockUp', P_ + 'Block%sWalks' % name, P_ + 'Block%sCover' % name] +
        [P_ + 'Block%sUp%d' % (name, i) for i in range(nch)], 'Block %s (cycles one level up), checked.' % name, body)
    print('up modules:', ' '.join(mods))


def write_upbase(name, n, out, P_, mptrs, P1, cf, cyc1, L):
    """Cycles one level up for a block whose Data and BlockOK exist already (module Block<base>)."""
    base = cf['base']; nb = base.lower()
    nt = len(P1); s = cf.get('upch', UPCH); nch = (nt + s - 1) // s
    T = '(%sData.trails %sFrame)' % (nb, nb)
    body = 'def %sCyc1 : List (List Nat) := [\n%s]\n\n' % (n, ',\n'.join('  ' + L(c) for c in cyc1))
    body += ('theorem %sCyc1_ok : CircleFamilyValid (%sFrame.h + 1) %sCyc1 ∧\n'
             "    (∀ c ∈ %sCyc1, ∀ a ∈ c, a ∈ 10 :: %sFrame.alph') := by\n  unfold CircleFamilyValid\n  decide +kernel\n\n"
             % (n, nb, n, n, nb))
    out('Block%sCyc' % name, [NS + '.BlockUp', P_ + 'Block%sData' % base],
        'The %d cycles one level up for block %s (its data in Block%sData).' % (len(cyc1), base, base), body)
    def dropped(i):
        e = T
        for _ in range(i): e = '(List.drop %d %s)' % (s, e)
        return e
    mods = ['Certificate/Block%sCyc' % name]
    k = cf.get('psplit', 1)
    if k > 1:   # one trail per module group, its ports in k ranges (one module each)
        assert s == 1
        hh = len(P1[0]); cuts = [hh * r // k for r in range(k + 1)]
        H1 = '(%sFrame.h + 1)' % nb
        def bnd(v): return H1 if v == hh else str(v)
        trail_thms = []
        for i in range(nt):
            parts = []
            for r in range(k):
                lo, hi = cuts[r], cuts[r + 1]
                ps = [q for q in P1[i] if lo <= q[1] < hi]
                body = 'def %sUpP%d_%d : List MixedPointer := %s\n\n' % (n, i, r, mptrs(ps))
                body += ('theorem %sUp%d_%d : ∀ W ∈ List.take 1 %s, PortsRange W %sCyc1 %s %s %s %sUpP%d_%d := by\n'
                         '  decide +kernel\n\n#print axioms %sUp%d_%d\n' % (n, i, r, dropped(i), n, H1, bnd(lo), bnd(hi), n, i, r, n, i, r))
                out('Block%sUp%d_%d' % (name, i, r), [NS + '.PortsSplit', P_ + 'Block%sCyc' % name],
                    'Cycle pointers one level up for ports %d..%d of trail %d of block %s.' % (lo, hi - 1, i, base), body)
                mods.append('Certificate/Block%sUp%d_%d' % (name, i, r))
                parts.append('%sUp%d_%d' % (n, i, r))
            e = parts[0]
            for q in parts[1:]: e = '(portsRange_append %s %s)' % (e, q)
            trail_thms.append('theorem %sUpT%d : ∀ W ∈ List.take 1 %s, ∃ m, PortsCovered W %sCyc1 %s m :=\n  portsCovered_of_range %s\n\n'
                              % (n, i, dropped(i), n, H1, e))
        def chain1(i):
            if i == nt - 1:
                return "forall_mem_of_take_eq' 1 (by decide +kernel) %sUpT%d" % (n, i)
            return "forall_mem_take_drop' 1 %sUpT%d (%s)" % (n, i, chain1(i + 1))
        body = ''.join(trail_thms)
        body += ('theorem %sPorts1 : ∀ W ∈ %s, ∃ m, PortsCovered W %sCyc1 (%sFrame.h + 1) m :=\n  %s\n\n'
                 % (n, T, n, nb, chain1(0)))
        body += ('/-- Block %s with its cycles one level up, checked. -/\ndef %sCert : BlockCertUp where\n  F := %sFrame\n'
                 '  B := %sData\n  ok := %sOK\n  cyc1 := %sCyc1\n  valid1 := %sCyc1_ok.1\n  support1 := %sCyc1_ok.2\n'
                 '  ports1 := %sPorts1\n\n#print axioms %sCert\n' % (base, n, nb, nb, nb, n, n, n, n, n))
        out('Block%s' % name, [NS + '.PortsSplit', P_ + 'Block%s' % base] + [P_ + m[len('Certificate/'):] for m in mods[1:]],
            'Block %s with cycles one level up, checked.' % base, body)
        mods.append('Certificate/Block%s' % name)
        print('modules:', ' '.join(mods))
        return
    for i in range(nch):
        body = 'def %sUpPtrs%d : List (List MixedPointer) := [\n%s]\n\n' % (
            n, i, ',\n'.join('  ' + mptrs(p) for p in P1[i * s:(i + 1) * s]))
        body += ('theorem %sUp%d : portsB %sCyc1 (%sFrame.h + 1) (List.take %d %s) %sUpPtrs%d = true := by\n'
                 '  decide +kernel\n\n#print axioms %sUp%d\n' % (n, i, n, nb, s, dropped(i), n, i, n, i))
        out('Block%sUp%d' % (name, i), [P_ + 'Block%sCyc' % name],
            'Cycle pointers one level up (h + 1 ports) for trails %d..%d of the %d trails of block %s.'
            % (i * s, min(nt, (i + 1) * s) - 1, nt, base), body)
        mods.append('Certificate/Block%sUp%d' % (name, i))
    def chain(i):
        if i == nch - 1:
            return "forall_mem_of_take_eq' %d (by decide +kernel) (portsB_sound _ _ %sUp%d)" % (s, n, i)
        return "forall_mem_take_drop' %d (portsB_sound _ _ %sUp%d) (%s)" % (s, n, i, chain(i + 1))
    body = ('theorem %sPorts1 : ∀ W ∈ %s, ∃ m, PortsCovered W %sCyc1 (%sFrame.h + 1) m :=\n  %s\n\n'
            % (n, T, n, nb, chain(0)))
    body += ('/-- Block %s with its cycles one level up, checked. -/\ndef %sCert : BlockCertUp where\n  F := %sFrame\n'
             '  B := %sData\n  ok := %sOK\n  cyc1 := %sCyc1\n  valid1 := %sCyc1_ok.1\n  support1 := %sCyc1_ok.2\n'
             '  ports1 := %sPorts1\n\n#print axioms %sCert\n' % (base, n, nb, nb, nb, n, n, n, n, n))
    out('Block%s' % name, [NS + '.BlockUp', P_ + 'Block%s' % base] +
        [P_ + 'Block%sUp%d' % (name, i) for i in range(nch)], 'Block %s with cycles one level up, checked.' % base, body)
    mods.append('Certificate/Block%s' % name)
    print('modules:', ' '.join(mods))


if __name__ == '__main__':
    for nm in sys.argv[1:]:
        build(nm)
