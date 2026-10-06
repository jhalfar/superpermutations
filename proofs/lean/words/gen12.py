"""Generate the Lean certificate files for a literal superpermutation: the version for twelve symbols.

    gen12.py WORD.txt NAME [--depth D] [--bpf N] [--gpf G] [--leaves N] [--fast] [--parts-only] [--nocheck]
             [--source TEXT] [--out DIR]

WORD.txt   the word, one symbol per character (symbols are ranked in ASCII order), 8 to 16 symbols;
           a file whose name ends in .xz is decompressed
NAME       module name below Superperm, e.g. N12 -> DIR/Superperm/N12/{B000.., Tree, P000.., Main}.lean
DIR        default: the directory of this script

Python 3 with numpy.

The certificate is that of gen11.py (one table entry for every rotation class; see Superperm/Cyc.lean):
  blocks   block i is the number whose base-16 digits are the letters i*B .. i*B+B+2K-2 of the word (as far
           as the word goes), so each hex literal is a stretch of the word written backwards and
           neighbouring blocks share 2K-1 letters.  The blocks are the leaves of a binary tree of depth D.
  tables   for every arrangement p' of 0..K-1 that ENDS with K-1 one entry: a position pos (S bits) and
           above it a number r (4 bits).  The 2K-1 letters at pos are the letters r .. r+2K-2 of
           p' p' p' p'.  A part fixes the first choices of the walk (K-1, then the list t); its table
           holds the entries of its branch in lexicographic order of the rest.
What differs from gen11.py (see Superperm/TreeOk.lean and Superperm/Cyc2.lean):
  - nothing is computed on the whole word: every block file checks its own subtree with `okT` (size of the
    blocks, neighbouring blocks agree), Tree.lean joins the subtrees with `okT_node`;
  - the parts come in groups of (K-1-s)(K-2-s) = 56: a group is all parts whose list t ends with the same
    `tail` of s symbols; a part file holds G groups and checks each with `groupOKj`;
  - the script reads the word in pieces and ranks every class directly (523 million letters need about 1.5 GB).
The script needs every rotation class to be visited in one stretch, and it runs the same checks as Lean
before it writes anything.
"""
import argparse, itertools, math, os, hashlib, sys, time
import numpy as np

ap = argparse.ArgumentParser()
ap.add_argument('word'); ap.add_argument('name')
ap.add_argument('--leaves', type=int, default=720, help='largest number of leaf checks in one kernel check')
ap.add_argument('--depth', type=int, default=-1, help='depth of the block tree (default: blocks of about 8,000 letters)')
ap.add_argument('--bpf', type=int, default=512, help='blocks per Lean file (a power of two)')
ap.add_argument('--gpf', type=int, default=4, help='groups of 56 parts per Lean file')
ap.add_argument('--fast', action='store_true', help='state the part checks with partCycF (Superperm/Cyc3.lean) and convert')
ap.add_argument('--source', default='', help='one line describing where the word comes from')
ap.add_argument('--nocheck', action='store_true', help='skip the Python run of the leaf checks')
ap.add_argument('--parts-only', action='store_true', help='write only the part files and Main (the block files and Tree stay as they are)')
ap.add_argument('--out', default=os.path.dirname(os.path.abspath(__file__)), help='directory in which Superperm/NAME is written')
a = ap.parse_args()
T0 = time.time()
def log(*x): print('[%6.1fs]' % (time.time() - T0), *x, flush=True)

if a.word.endswith('.xz'):
    import lzma
    with lzma.open(a.word) as f: data = f.read()
else:
    with open(a.word, 'rb') as f: data = f.read()
sha_file = hashlib.sha256(data).hexdigest()
raw = np.frombuffer(data, np.uint8)
while raw[-1] in (10, 13): raw = raw[:-1]
L = len(raw)
sha_text = hashlib.sha256(memoryview(data)[:L]).hexdigest()
syms = np.flatnonzero(np.bincount(raw, minlength=256)); K = len(syms)
assert 8 <= K <= 16
lut = np.zeros(256, np.uint8); lut[syms] = np.arange(K, dtype=np.uint8)
w = lut[raw]; del raw, data
Kw = 2 * K - 1

# ---- runs of permutation windows, in pieces of 2^24 letters ---------------------------------------
n = L - K + 1
C = 1 << 24
fst = []; open_start = -1
for lo in range(0, n, C):
    hi = min(n, lo + C)
    seg = w[lo:hi + K - 1]
    last = np.full(len(seg), -1, np.int32)           # previous occurrence of the same letter inside seg
    for s_ in range(K):
        idx = np.flatnonzero(seg == s_)
        last[idx[1:]] = idx[:-1]
    m = last[:hi - lo].copy()
    for j in range(1, K): np.maximum(m, last[j:j + hi - lo], out=m)
    isperm = m < np.arange(hi - lo, dtype=np.int32)  # window lo+i is a permutation
    dd = np.diff(np.concatenate(([1 if open_start >= 0 else 0], isperm.view(np.int8), [0])))
    st = np.flatnonzero(dd == 1) + lo; en = np.flatnonzero(dd == -1) + lo
    if open_start >= 0: st = np.concatenate(([open_start], st))
    if len(en) and en[-1] == hi and hi < n:          # a run that goes on in the next piece
        open_start = int(st[-1]); st = st[:-1]; en = en[:-1]
    else: open_start = -1
    fst.append(st[en - st >= K].astype(np.int64))    # a run of K windows: 2K-1 letters with period K
    del last, m, isperm, dd, st, en, seg
fstarts = np.concatenate(fst); del fst

# ---- parameters -----------------------------------------------------------------------------------
S = max(1, (L - 1).bit_length()); Se = S + 4         # bits of a position, of a table entry
mS = 2 ** S - 1; mW = 2 ** (4 * Kw) - 1
M = 1 + 16 ** K + 16 ** (2 * K) + 16 ** (3 * K)
K1 = K - 1
s1 = 0                                               # length of t
while math.factorial(K1 - s1) > a.leaves: s1 += 1
free = K1 - s1                                       # symbols the walk arranges
F = math.factorial(free)
stride = Se * math.factorial(free - 1) if free >= 1 else 0
J = min(2, s1); s0 = s1 - J                          # a group: all t with the same last s0 symbols
d = a.depth
if d < 0:
    d = 0
    while L > 8000 * 2 ** d: d += 1
B = -(-L // 2 ** d)
assert Kw <= B
h0 = 4 * B * 2 ** (d - 1) if d >= 1 else 4 * B
nb = 2 ** d
bpf = min(a.bpf, nb)
assert bpf & (bpf - 1) == 0
nbfiles = nb // bpf; db = bpf.bit_length() - 1        # depth of the subtree of one block file

def prefixes(K, s):
    """the order of LiteralSuperperm.prefixes"""
    if s == 0: return [[]]
    return [[x] + pre for pre in prefixes(K, s - 1) for x in range(K) if x not in pre]
def ext(u, j):
    """u with j more symbols in front, in the order of LiteralSuperperm.prefixes"""
    if j == 0: return [u]
    return [[x] + t for t in ext(u, j - 1) for x in range(K1) if x not in t]
tails = prefixes(K1, s0)
ngroups = len(tails); gsize = len(ext(tails[0], J))
nparts = ngroups * gsize
assert nparts * F == math.factorial(K1)

# ---- the table entry of every class, at the place where the walk meets the class ------------------
def part_index(t):
    """index of the lists t (rows) in the order tails x ext: the last symbol counts most"""
    idx = np.zeros(len(t), np.int64)
    for i in range(s1 - 1, -1, -1):
        idx = idx * (K1 - (s1 - 1 - i)) + t[:, i] - (t[:, i + 1:] < t[:, i:i + 1]).sum(axis=1)
    return idx
def leaf_index(q):
    """lexicographic rank of the arrangements q (rows)"""
    idx = np.zeros(len(q), np.int64)
    for i in range(free):
        idx = idx * (free - i) + (q[:, i + 1:] < q[:, i:i + 1]).sum(axis=1)
    return idx
allt = [t for u in tails for t in ext(u, J)]
assert (part_index(np.array(allt, dtype=np.int64).reshape(nparts, s1)) == np.arange(nparts)).all()
PERM = np.array(list(itertools.permutations(range(free))), dtype=np.int64).reshape(-1, free)   # lexicographic
assert (leaf_index(PERM) == np.arange(F)).all()

entries = np.full(nparts * F, -1, np.int64)
for hi in range(len(fstarts), 0, -(1 << 20)):        # backwards, so that the first stretch of a class is kept
    p = fstarts[max(0, hi - (1 << 20)):hi][::-1]
    win = w[p[:, None] + np.arange(K)].astype(np.int64)
    idx = (win == K1).argmax(axis=1)
    Pp = np.take_along_axis(win, (idx[:, None] - np.arange(K)) % K, axis=1)   # the rotation that ends with K-1, backwards
    assert (Pp[:, 0] == K1).all()
    flat = part_index(Pp[:, 1:1 + s1]) * F + leaf_index(Pp[:, 1 + s1:])
    entries[flat] = p | ((K1 - idx) << S)            # the window at p is that rotation rotated by r = K-1-idx
del fstarts
missing = int((entries < 0).sum())
assert missing == 0, '%d of %d rotation classes are not visited in one stretch' % (missing, len(entries))
log('K=%d L=%d: %d rotation classes, each with a stretch of %d letters' % (K, L, len(entries), Kw))

def table(k):
    """the table of part k: the entries of its branch in the order of the walk"""
    tb = 0
    for i, e in enumerate(entries[k * F:(k + 1) * F].tolist()): tb |= e << (Se * i)
    return tb

log('S=%d groups=%d parts/group=%d leaves/part=%d depth=%d block=%d stride=%d' % (
    S, ngroups, gsize, F, d, B, stride))

# ---- output helpers -------------------------------------------------------------------------------
outdir = os.path.join(a.out, 'Superperm', a.name)
os.makedirs(outdir, exist_ok=True)
for fn in os.listdir(outdir):
    if fn.endswith('.lean') and (not a.parts_only or fn.startswith('P') or fn == 'Main.lean'): os.remove(os.path.join(outdir, fn))
ns = 'LiteralSuperperm.' + a.name
args = '%d %d %d %d %d %d %d %d tree %d' % (K, Kw, L, S, mS, mW, M, h0, stride)
okargs = '%d %d %d' % (B, Kw, mW)

def lit(x): return '0x%x' % x
def tname(p): return 't' + ''.join('_%d' % x for x in p) if p else 't_all'
def pname(p): return 'p' + ''.join('_%d' % x for x in p) if p else 'p_all'
def plist(p): return '[' + ', '.join(str(x) for x in p) + ']'
def write(fn, text):
    if a.parts_only and not (fn.startswith('P') or fn == 'Main.lean'): return
    with open(os.path.join(outdir, fn), 'w', newline='\n', encoding='utf-8') as f: f.write(text)
def chain(names, tail, lemma):
    return ''.join(f'  {lemma}.2 ⟨{n},\n' for n in names) + '  ' + tail + '⟩' * len(names)
def bal(terms):
    """a balanced WT term over the given subterms"""
    if len(terms) == 1: return terms[0]
    mid = len(terms) // 2
    return '(WT.node %s %s)' % (bal(terms[:mid]), bal(terms[mid:]))

# ---- the blocks: checked as Lean checks them, and written -----------------------------------------
HEX = np.frombuffer(b'0123456789abcdef', np.uint8)
def stretch(lo, hi):                                 # letters lo..hi-1 as a hex literal (backwards); beyond the word: 0
    lo = min(lo, L); hi = min(hi, L)
    return HEX[w[lo:hi][::-1]].tobytes().decode() if lo < hi else '0'
bval = []
for j in range(nbfiles):
    lo = j * bpf
    body = [f'import Superperm.TreeOk', '',
            f'/-! Generated by gen12.py.  {a.source}',
            f'Blocks {lo} to {lo + bpf - 1} of {nb}: block `i` holds the letters `{B} * i` to `{B} * i + {B + Kw - 1}` of the word',
            f'(as far as the word goes; blocks beyond its end are 0), letter `j` of the block as base-16 digit `j`, so each literal is a',
            f'stretch of the word written backwards.  `s{j}` is the subtree over these blocks; `s{j}_ok` is the kernel check',
            f'that it has depth {db}, that no block is longer than {B + Kw} letters, and that neighbouring blocks agree on the',
            f'{Kw} letters they share. -/', '',
            f'namespace {ns}', 'open LiteralSuperperm', '']
    for i in range(lo, lo + bpf):
        hx = stretch(i * B, (i + 1) * B + Kw)
        bval.append(int(hx, 16))
        body.append(f'def b{i} : Nat := 0x{hx}')
    body += ['', f'def s{j} : WT := ' + bal([f'(WT.leaf b{i})' for i in range(lo, lo + bpf)]), '',
             f'theorem s{j}_ok : okT {okargs} {db} s{j} = true := by decide +kernel', '', f'end {ns}']
    write('B%03d.lean' % j, '\n'.join(body) + '\n')
del w
# LiteralSuperperm.okT: every leaf below 16^(B+Kw); the digits above B of a leaf are the lowest Kw digits of the next
for i in range(nb):
    assert bval[i] >> (4 * (B + Kw)) == 0
    assert i == nb - 1 or bval[i] >> (4 * B) == bval[i + 1] & mW, 'blocks %d and %d disagree' % (i, i + 1)
log('%d blocks written and checked' % nb)

def oknode(lo, hi, dd):
    """theorems for the nodes above the block files; returns (term, name of its okT theorem)"""
    if hi - lo == 1: return 's%d' % lo, 's%d_ok' % lo
    mid = (lo + hi) // 2
    tl, nl = oknode(lo, mid, dd - 1); tr, nr = oknode(mid, hi, dd - 1)
    term = '(WT.node %s %s)' % (tl, tr); name = 'ok_%d_%d' % (dd, lo)
    toplines.append(f'theorem {name} : okT {okargs} {dd} {term} = true :=\n  okT_node {nl} {nr} (by decide +kernel)')
    return term, name
toplines = []
tterm, tok = oknode(0, nbfiles, d)
bimports = '\n'.join(['import Superperm.TreeOk'] + [f'import Superperm.{a.name}.B%03d' % j for j in range(nbfiles)])
nl = '\n'
write('Tree.lean', f'''{bimports}

/-! Generated by gen12.py.  {a.source}
The word has {L} symbols over {K} letters.  SHA-256 of the file: {sha_file}
(of the text without the line end: {sha_text}).
`tree` is the tree of the {nb} blocks of {B} (+{Kw}) letters, `W` the number it spells (`valT`, a definition the
kernel never evaluates): symbol `i` of the word (from the left, letters ranked 0..{K-1}) is base-16 digit `i` of `W`.
`tree_ok` joins the checks of the {nbfiles} block files: the tree has depth {d}, no block is longer than {B + Kw}
letters, and neighbouring blocks agree on the {Kw} letters they share.  By `okT_sound` the tree is then
`build {B} {Kw} {d} W`. -/

namespace {ns}
open LiteralSuperperm

def tree : WT := {tterm}

def W : Nat := valT {B} {d} tree

{nl.join(toplines)}

theorem tree_ok : okT {okargs} {d} tree = true := {tok}

end {ns}
''')

# ---- the same leaf checks as Lean -----------------------------------------------------------------
def mktree(lo, hi):
    if hi - lo == 1: return bval[lo]
    mid = (lo + hi) // 2
    return (mktree(lo, mid), mktree(mid, hi))
tree = mktree(0, nb)
def getT(t, h, q):
    """LiteralSuperperm.getT"""
    while isinstance(t, tuple):
        if h <= q: t = t[1]; q -= h
        else: t = t[0]
        h >>= 1
    return t >> q
def leaf(c, tbl):
    """LiteralSuperperm.leafCyc"""
    p = tbl & mS
    return p + Kw <= L and (getT(tree, h0, 4 * p) & mW) == (((c * M) >> (4 * ((tbl >> S) & 15))) & mW)
def go(r, rem, c, tbl, stride):
    """LiteralSuperperm.go"""
    if r == 0: return leaf(c, tbl)
    for x in rem:
        if not go(r - 1, [y for y in rem if y != x], c * 16 + x, tbl, stride // (r - 1) if r > 1 else 0): return False
        tbl >>= stride
    return True
def check_part(t, tbl):
    """LiteralSuperperm.partCyc"""
    pre = [K1] + t
    rem = [x for x in range(K) if x not in pre]
    c = 0
    for x in pre: c = c * 16 + x
    return go(K - len(pre), rem, c, tbl, stride)

# ---- the part files -------------------------------------------------------------------------------
PART = 'partCycF' if a.fast else 'partCyc'
pimports = [f'import Superperm.Cyc3' if a.fast else 'import Superperm.Cyc2', f'import Superperm.{a.name}.Tree']
npdone = 0
files = list(range(-(-ngroups // a.gpf)))
for f in files:
    gs = range(f * a.gpf, min(ngroups, (f + 1) * a.gpf))
    body = pimports + ['',
            f'/-! Generated by gen12.py: tables and kernel checks for the groups {gs[0]} to {gs[-1]}, each {gsize} branches of {math.factorial(free)} rotation classes.',
            f'A group is all branches whose list ends with the same tail (`tails g`); `group g_ok` checks that the group has',
            f'a branch for every way of putting {J} more symbols in front of the tail. -/', '',
            '-- one declaration at a time on one thread: the memory of each kernel check is given back before the next',
            'set_option Elab.async false', '',
            f'namespace {ns}', 'open LiteralSuperperm', '']
    for g in gs:
        ps = ext(tails[g], J)
        for p in ps:
            assert p == allt[npdone]
            t = table(npdone)
            if not a.nocheck: assert check_part(p, t), p
            body.append(f'def {tname(p)} : Nat := {lit(t)}')
            body.append(f'theorem {pname(p)} : {PART} {args} {plist(p)} {tname(p)} = true := by decide +kernel')
            body.append('')
            npdone += 1
        body.append(f'def items{g} : List (List Nat × Nat) := [' + ', '.join(f'({plist(p)}, {tname(p)})' for p in ps) + ']')
        body.append('')
        if a.fast:
            body.append(f'theorem items{g}_okF : ∀ x ∈ items{g}, {PART} {args} x.1 x.2 = true :=')
            body.append(chain([pname(p) for p in ps], '(fun _ h => nomatch h)', 'List.forall_mem_cons'))
            body.append('')
            body.append(f'theorem items{g}_ok : ∀ x ∈ items{g}, partCyc {args} x.1 x.2 = true :=')
            body.append(f'  fun x hx => (partCycF_eq ..).symm.trans (items{g}_okF x hx)')
        else:
            body.append(f'theorem items{g}_ok : ∀ x ∈ items{g}, partCyc {args} x.1 x.2 = true :=')
            body.append(chain([pname(p) for p in ps], '(fun _ h => nomatch h)', 'List.forall_mem_cons'))
        body.append('')
        body.append(f'def tails{g} : List (List Nat) := [{plist(tails[g])}]')
        body.append(f'theorem group{g}_ok : groupOKj {K1} {J} tails{g} items{g} = true := by decide +kernel')
        body.append('')
    body.append(f'end {ns}')
    write('P%03d.lean' % f, '\n'.join(body) + '\n')
    if f % 20 == 0: log('part file %d of %d' % (f, len(files)))
assert npdone == nparts

# ---- Main -----------------------------------------------------------------------------------------
GT = 'List (List (List Nat) × List (List Nat × Nat))'
sub = [list(range(i, min(ngroups, i + 30))) for i in range(0, ngroups, 30)]
lines = []
for i, gl in enumerate(sub):
    lines.append(f'def groupsA{i} : {GT} := [' + ', '.join(f'(tails{g}, items{g})' for g in gl) + ']')
    lines.append(f'theorem groupsA{i}_ok : ∀ g ∈ groupsA{i}, ∀ x ∈ g.2, partCyc {args} x.1 x.2 = true :=')
    lines.append(chain([f'items{g}_ok' for g in gl], '(fun _ h => nomatch h)', 'List.forall_mem_cons'))
    lines.append(f'theorem groupsA{i}_complete : ∀ g ∈ groupsA{i}, groupOKj {K1} {J} g.1 g.2 = true :=')
    lines.append(chain([f'group{g}_ok' for g in gl], '(fun _ h => nomatch h)', 'List.forall_mem_cons'))
    lines.append('')
allgroups = ''.join(f'groupsA{i} ++ (' for i in range(len(sub))) + '[]' + ')' * len(sub)
imports = '\n'.join(['import Superperm.Cyc2'] + [f'import Superperm.{a.name}.P%03d' % f for f in files])
hyps = ' '.join(['(by decide)'] * 9) + ' tree_ok (by decide)'
write('Main.lean', f"""{imports}

/-! Generated by gen12.py.  {a.source}
A word of {L} symbols over {K} letters that contains every permutation.
Every computation is a kernel reduction (`decide +kernel`): no `native_decide`. -/

-- one declaration at a time on one thread: the memory of each kernel check is given back before the next
set_option Elab.async false

namespace {ns}
open LiteralSuperperm SuperpermutationBounds

/-! The {nparts} branches of the walk (first choices {K1} and then {s1} more) in {ngroups} groups of {gsize}; the tail of a
group is the last {s0} choices of its branches.  The groups are listed in pieces of 30. -/

{nl.join(lines)}
def groups : {GT} := {allgroups}

theorem groups_ok : ∀ g ∈ groups, ∀ x ∈ g.2, partCyc {args} x.1 x.2 = true :=
{chain([f'groupsA{i}_ok' for i in range(len(sub))], '(fun _ h => nomatch h)', 'List.forall_mem_append')}

theorem groups_complete : ∀ g ∈ groups, groupOKj {K1} {J} g.1 g.2 = true :=
{chain([f'groupsA{i}_complete' for i in range(len(sub))], '(fun _ h => nomatch h)', 'List.forall_mem_append')}

theorem tails_complete : tailsComplete {K1} {s0} groups = true := by decide +kernel

/-- The literal word. -/
def word : List (Fin {K}) := wordOf {K} {L} W (by decide)

theorem word_length : word.length = {L} := wordOf_length _ _ _ _

theorem word_covers : Covers word :=
  covers_of_cyc_ok {hyps} groups groups_ok
    tails_complete groups_complete

theorem hasWord : HasWord {K} {L} := ⟨word, word_covers, word_length.le⟩

end {ns}
""")
mods = ['B%03d' % j for j in range(nbfiles)] + ['Tree'] + ['P%03d' % f for f in files] + ['Main']
with open(os.path.join(outdir, 'modules.txt'), 'w', newline='\n') as f: f.write('\n'.join(mods) + '\n')
log('K=%d L=%d S=%d parts=%d leaves/part=%d partfiles=%d block=%d depth=%d blockfiles=%d stride=%d sha256(file)=%s' % (
    K, L, S, nparts, math.factorial(free), len(files), B, d, nbfiles, stride, sha_file))
