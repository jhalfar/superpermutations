"""Generate the Lean certificate files for a literal superpermutation, one table entry per rotation class.

    gen11.py WORD.txt NAME [--depth D] [--bpf N] [--leaves N] [--per-file P] [--source TEXT] [--out DIR]

WORD.txt   the word, one symbol per character (symbols are ranked in ASCII order), 8 to 16 symbols;
           a file whose name ends in .xz is decompressed
NAME       module name below Superperm, e.g. N11 -> DIR/Superperm/N11/{B000.., Tree, P000.., Main}.lean
DIR        default: the directory of this script

Python 3 with numpy.

The certificate (see Superperm/Cyc.lean and Superperm/Literal.lean):
  blocks   block i is the number whose base-16 digits are the letters i*B .. i*B+B+2K-2 of the word (as far
           as the word goes), so each hex literal is a stretch of the word written backwards and
           neighbouring blocks share 2K-1 letters.  The blocks are the leaves of a binary tree of depth D.
  tables   for every arrangement p' of 0..K-1 that ENDS with K-1 one entry: a position pos (S bits) and
           above it a number r (4 bits).  The 2K-1 letters at pos are the letters r .. r+2K-2 of
           p' p' p' p'; they contain all K rotations of p'.  The walk fixes the first choices
           (K-1, then the list t) per part; the table of a part holds the entries of its branch in
           lexicographic order of the rest.  (The walk builds an arrangement from its last letter.)
The script needs every rotation class to be visited in one stretch (true for the words of 9, 10 and 11
symbols used here), and it runs the same checks as Lean before it writes anything.
"""
import argparse, itertools, math, os, hashlib, sys, time
import numpy as np

ap = argparse.ArgumentParser()
ap.add_argument('word'); ap.add_argument('name')
ap.add_argument('--leaves', type=int, default=720, help='largest number of leaf checks in one kernel check')
ap.add_argument('--depth', type=int, default=-1, help='depth of the block tree (default: blocks of about 10,000 letters)')
ap.add_argument('--bpf', type=int, default=128, help='blocks per Lean file (a power of two)')
ap.add_argument('--per-file', type=int, default=56, help='parts per Lean file')
ap.add_argument('--source', default='', help='one line describing where the word comes from')
ap.add_argument('--nocheck', action='store_true', help='skip the Python run of the leaf checks')
ap.add_argument('--out', default=os.path.dirname(os.path.abspath(__file__)), help='directory in which Superperm/NAME is written')
a = ap.parse_args()
T0 = time.time()
def log(*x): print('[%6.1fs]' % (time.time() - T0), *x, flush=True)

def read_word(path):
    """the bytes of a word file; a file whose name ends in .xz is decompressed first"""
    if path.endswith('.xz'):
        import lzma
        with lzma.open(path) as f: return f.read()
    with open(path, 'rb') as f: return f.read()

data = read_word(a.word)
raw = data.strip()
sha_file = hashlib.sha256(data).hexdigest(); sha_text = hashlib.sha256(raw).hexdigest()
syms = sorted(set(raw)); K = len(syms); L = len(raw)
assert 8 <= K <= 16
lut = np.zeros(256, np.uint8)
for i, c in enumerate(syms): lut[c] = i
w = lut[np.frombuffer(raw, np.uint8)]
Kw = 2 * K - 1

# ---- runs of permutation windows ------------------------------------------------------------------
last = np.full(L, -1, np.int32)                      # index of the previous occurrence of the same letter
for s_ in range(K):
    idx = np.flatnonzero(w == s_)
    last[idx[1:]] = idx[:-1]
n = L - K + 1
m = last[:n].copy()
for j in range(1, K): np.maximum(m, last[j:j + n], out=m)
isperm = m < np.arange(n, dtype=np.int32)            # window i is a permutation
del last, m
dd = np.diff(np.concatenate(([0], isperm.view(np.int8), [0])))
starts = np.flatnonzero(dd == 1); lens = np.flatnonzero(dd == -1) - starts
del dd, isperm
fstarts = starts[lens >= K]                          # a run of K windows: 2K-1 letters with period K
codes = np.empty(len(fstarts), np.int64); rs = np.empty(len(fstarts), np.int64)
for lo in range(0, len(fstarts), 1 << 20):
    p = fstarts[lo:lo + (1 << 20)]
    win = w[p[:, None] + np.arange(K)].astype(np.int64)
    idx = (win == K - 1).argmax(axis=1)
    can = np.take_along_axis(win, (idx[:, None] + 1 + np.arange(K)) % K, axis=1)   # the rotation that ends with K-1
    codes[lo:lo + len(p)] = (can << (4 * np.arange(K))).sum(axis=1)                # its code: letter j is digit j
    rs[lo:lo + len(p)] = K - 1 - idx                                               # window = rotation by r
order = np.argsort(codes, kind='stable')
cs = codes[order]
keep = np.concatenate(([True], cs[1:] != cs[:-1]))
ccode = cs[keep]; cpos = fstarts[order][keep].astype(np.int64); cr = rs[order][keep]
assert len(ccode) == math.factorial(K - 1), \
    'only %d of %d rotation classes are visited in one stretch' % (len(ccode), math.factorial(K - 1))
log('K=%d L=%d: %d rotation classes, each with a stretch of %d letters' % (K, L, len(ccode), Kw))

# ---- parameters -----------------------------------------------------------------------------------
S = max(1, (L - 1).bit_length()); Se = S + 4         # bits of a position, of a table entry
mS = 2 ** S - 1; mW = 2 ** (4 * Kw) - 1
M = 1 + 16 ** K + 16 ** (2 * K) + 16 ** (3 * K)
K1 = K - 1
s1 = 0                                               # length of t
while math.factorial(K1 - s1) > a.leaves: s1 += 1
free = K1 - s1                                       # symbols the walk arranges
stride = Se * math.factorial(free - 1) if free >= 1 else 0
d = a.depth
if d < 0:
    d = 0
    while L > 10000 * 2 ** d: d += 1
B = -(-L // 2 ** d)
h0 = 4 * B * 2 ** (d - 1) if d >= 1 else 4 * B
centry = cpos | (cr << S)

def prefixes(K, s):
    """the order of LiteralSuperperm.prefixes"""
    if s == 0: return [[]]
    return [[x] + pre for pre in prefixes(K, s - 1) for x in range(K) if x not in pre]

PERM = np.array(list(itertools.permutations(range(free))), dtype=np.int64).reshape(-1, free)   # lexicographic
def table(t):
    """entries of the branch K-1, t: arrangement P' = [K-1] + t + q, code = sum P'[i] * 16^(K-1-i)"""
    rest = np.array([x for x in range(K1) if x not in t], dtype=np.int64)
    c0 = 0
    for x in [K1] + t: c0 = c0 * 16 + x
    q = rest[PERM]
    c = (q << (4 * (free - 1 - np.arange(free)))).sum(axis=1) + (c0 << (4 * free))
    k = np.searchsorted(ccode, c)
    assert (ccode[k] == c).all()
    tb = 0
    for i, e in enumerate(centry[k].tolist()): tb |= e << (Se * i)
    return tb

pres = prefixes(K1, s1)
tabs = [table(t) for t in pres]
log('S=%d parts=%d leaves/part=%d depth=%d block=%d stride=%d' % (S, len(pres), math.factorial(free), d, B, stride))

# ---- the blocks -----------------------------------------------------------------------------------
HEX = np.frombuffer(b'0123456789abcdef', np.uint8)
wrev_hex = HEX[w[::-1]].tobytes().decode()           # the word backwards, as hex digits
def stretch(lo, hi):                                 # letters lo..hi-1 as a hex literal (backwards); beyond the word: 0
    lo = min(lo, L); hi = min(hi, L)
    return wrev_hex[L - hi:L - lo] if lo < hi else '0'
nb = 2 ** d
bhex = [stretch(i * B, (i + 1) * B + Kw if i < nb - 1 else L) for i in range(nb)]
bval = [int(x, 16) for x in bhex]
Wn = int(wrev_hex, 16)                               # the word as a number

# ---- the same checks as Lean ----------------------------------------------------------------------
def mktree(lo, hi):
    if hi - lo == 1: return bval[lo]
    mid = (lo + hi) // 2
    return (mktree(lo, mid), mktree(mid, hi))
tree = mktree(0, nb)
def unb(t, h):
    """LiteralSuperperm.unb"""
    if not isinstance(t, tuple): return t
    return unb(t[0], h >> 1) | (unb(t[1], h >> 1) << h)
def chkT(dd, t, x):
    """LiteralSuperperm.chkT"""
    if dd == 0: return (not isinstance(t, tuple)) and t == x
    if not isinstance(t, tuple): return False
    dd -= 1
    return chkT(dd, t[0], x & ((1 << (4 * (B * 2 ** dd + Kw))) - 1)) and chkT(dd, t[1], x >> (4 * (B * 2 ** dd)))
assert unb(tree, h0) == Wn, 'the tree does not spell the word'
assert chkT(d, tree, Wn)
log('tree checked')

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
if not a.nocheck:
    for t, tb in zip(pres, tabs): assert check_part(t, tb), t
    log('all parts checked in Python')

# ---- output ---------------------------------------------------------------------------------------
outdir = os.path.join(a.out, 'Superperm', a.name)
os.makedirs(outdir, exist_ok=True)
for fn in os.listdir(outdir):
    if fn.endswith('.lean'): os.remove(os.path.join(outdir, fn))
ns = 'LiteralSuperperm.' + a.name
args = '%d %d %d %d %d %d %d %d tree %d' % (K, Kw, L, S, mS, mW, M, h0, stride)

def lit(x): return '0x%x' % x
def tname(p): return 't' + ''.join('_%d' % x for x in p) if p else 't_all'
def pname(p): return 'p' + ''.join('_%d' % x for x in p) if p else 'p_all'
def plist(p): return '[' + ', '.join(str(x) for x in p) + ']'
def write(fn, text):
    with open(os.path.join(outdir, fn), 'w', newline='\n', encoding='utf-8') as f: f.write(text)
def chain(names, tail, lemma):
    return ''.join(f'  {lemma}.2 ⟨{n},\n' for n in names) + '  ' + tail + '⟩' * len(names)
def bal(terms):
    """a balanced WT term over the given subterms"""
    if len(terms) == 1: return terms[0]
    mid = len(terms) // 2
    return '(WT.node %s %s)' % (bal(terms[:mid]), bal(terms[mid:]))

bpf = min(a.bpf, nb)
assert bpf & (bpf - 1) == 0
nbfiles = nb // bpf
for j in range(nbfiles):
    lo = j * bpf
    body = [f'import Superperm.Literal', '',
            f'/-! Generated by gen11.py.  {a.source}',
            f'Blocks {lo} to {lo + bpf - 1} of {nb}: block `i` holds the letters `{B} * i` to `{B} * i + {B + Kw - 1}` of the word',
            f'(as far as the word goes; blocks beyond its end are 0), letter `j` of the block as base-16 digit `j`, so each literal is a',
            f'stretch of the word written backwards.  `s{j}` is the subtree over these blocks. -/', '',
            f'namespace {ns}', 'open LiteralSuperperm', '']
    for i in range(lo, lo + bpf): body.append(f'def b{i} : Nat := 0x{bhex[i]}')
    body += ['', f'def s{j} : WT := ' + bal([f'(WT.leaf b{i})' for i in range(lo, lo + bpf)]), '', f'end {ns}']
    write('B%03d.lean' % j, '\n'.join(body) + '\n')

bimports = '\n'.join(['import Superperm.Cyc'] + [f'import Superperm.{a.name}.B%03d' % j for j in range(nbfiles)])
write('Tree.lean', f'''{bimports}

/-! Generated by gen11.py.  {a.source}
The word has {L} symbols over {K} letters.  SHA-256 of the file: {sha_file}
(of the text without the line end: {sha_text}).
`tree` is the tree of the {nb} blocks of {B} (+{Kw}) letters, `W` the number it spells: symbol `i` of the word
(from the left, letters ranked 0..{K-1}) is base-16 digit `i` of `W`.  `tree_ok` is the kernel check that
`tree` is `build {B} {Kw} {d} W`; in particular neighbouring blocks agree on the {Kw} letters they share. -/

namespace {ns}
open LiteralSuperperm

def tree : WT := {bal([f's{j}' for j in range(nbfiles)])}

def W : Nat := unb tree {h0}

theorem tree_ok : chkT {B} {Kw} {d} tree W = true := by decide +kernel

end {ns}
''')

files = []
for fi in range(0, len(pres), a.per_file):
    k = fi // a.per_file
    files.append(k)
    ps = pres[fi:fi + a.per_file]; ts = tabs[fi:fi + a.per_file]
    body = [f'import Superperm.{a.name}.Tree', '',
            f'/-! Generated by gen11.py: tables and kernel checks for {len(ps)} branches of {math.factorial(free)} rotation classes. -/', '',
            '-- one declaration at a time on one thread: the memory of each kernel check is given back before the next',
            'set_option Elab.async false', '',
            f'namespace {ns}', 'open LiteralSuperperm', '']
    for p, t in zip(ps, ts):
        body.append(f'def {tname(p)} : Nat := {lit(t)}')
        body.append(f'theorem {pname(p)} : partCyc {args} {plist(p)} {tname(p)} = true := by decide +kernel')
        body.append('')
    body.append(f'def items{k} : List (List Nat × Nat) := [' + ', '.join(f'({plist(p)}, {tname(p)})' for p in ps) + ']')
    body.append('')
    body.append(f'theorem items{k}_ok : ∀ x ∈ items{k}, partCyc {args} x.1 x.2 = true :=')
    body.append(chain([pname(p) for p in ps], '(fun _ h => nomatch h)', 'List.forall_mem_cons'))
    body.append('')
    body.append(f'end {ns}')
    write('P%03d.lean' % k, '\n'.join(body) + '\n')

imports = '\n'.join(f'import Superperm.{a.name}.P%03d' % k for k in files)
hyps = '(by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) tree_ok (by decide)'
tailpart = f"""
/-- The literal word. -/
def word : List (Fin {K}) := wordOf {K} {L} W (by decide)

theorem word_length : word.length = {L} := wordOf_length _ _ _ _
"""
head = f"""/-! Generated by gen11.py.  {a.source}
A word of {L} symbols over {K} letters that contains every permutation.
Every computation is a kernel reduction (`decide +kernel`): no `native_decide`. -/"""
if len(pres) <= 1000:
    allitems = ''.join(f'items{k} ++ (' for k in files) + '[]' + ')' * len(files)
    deep = 'set_option maxRecDepth 8192 in\n' if len(files) > 16 else ''
    write('Main.lean', f"""{imports}

{head}

namespace {ns}
open LiteralSuperperm SuperpermutationBounds

/-- The {len(pres)} branches of the walk (first choices {K1} and then {s1} more) with their tables. -/
def items : List (List Nat × Nat) := {allitems}

{deep}theorem items_ok : ∀ x ∈ items, partCyc {args} x.1 x.2 = true :=
{chain([f'items{k}_ok' for k in files], '(fun _ h => nomatch h)', 'List.forall_mem_append')}

theorem items_complete : itemsComplete {K1} {s1} items = true := by decide +kernel
{tailpart}
theorem word_covers : Covers word :=
  covers_of_cyc {hyps} items items_ok
    (hpre_of_itemsComplete items_complete)

theorem hasWord : HasWord {K} {L} := ⟨word, word_covers, word_length.le⟩

end {ns}
""")
else:
    # many branches: completeness is checked group by group (Superperm/Groups.lean); a group is one file
    per_tail = K1 - (s1 - 1)
    assert a.per_file % per_tail == 0, 'a file must hold whole groups of %d branches' % per_tail
    lines = []
    for k in files:
        ps = pres[k * a.per_file:(k + 1) * a.per_file]
        tails = [p[1:] for p in ps[::per_tail]]
        assert [[x] + t for t in tails for x in range(K1) if x not in t] == ps
        lines.append(f'def tails{k} : List (List Nat) := [' + ', '.join(plist(t) for t in tails) + ']')
        lines.append(f'theorem group{k}_ok : groupOK {K1} tails{k} items{k} = true := by decide +kernel')
    groups = ', '.join(f'(tails{k}, items{k})' for k in files)
    nl = '\n'
    write('Main.lean', f"""{imports}

{head}

-- one declaration at a time on one thread: the memory of each kernel check is given back before the next
set_option Elab.async false

namespace {ns}
open LiteralSuperperm SuperpermutationBounds

/-! The {len(pres)} branches of the walk (first choices {K1} and then {s1} more) in {len(files)} groups;
`tails k` are the last {s1 - 1} choices of the branches of group `k`. -/

{nl.join(lines)}

def groups : List (List (List Nat) × List (List Nat × Nat)) := [{groups}]

set_option maxRecDepth 8192 in
theorem groups_ok : ∀ g ∈ groups, ∀ x ∈ g.2, partCyc {args} x.1 x.2 = true :=
{chain([f'items{k}_ok' for k in files], '(fun _ h => nomatch h)', 'List.forall_mem_cons')}

set_option maxRecDepth 8192 in
theorem groups_complete : ∀ g ∈ groups, groupOK {K1} g.1 g.2 = true :=
{chain([f'group{k}_ok' for k in files], '(fun _ h => nomatch h)', 'List.forall_mem_cons')}

theorem tails_complete : tailsComplete {K1} {s1 - 1} groups = true := by decide +kernel
{tailpart}
theorem word_covers : Covers word :=
  covers_of_cyc_groups {hyps} groups groups_ok
    tails_complete groups_complete

theorem hasWord : HasWord {K} {L} := ⟨word, word_covers, word_length.le⟩

end {ns}
""")
mods = ['B%03d' % j for j in range(nbfiles)] + ['Tree'] + ['P%03d' % k for k in files] + ['Main']
with open(os.path.join(outdir, 'modules.txt'), 'w', newline='\n') as f: f.write('\n'.join(mods) + '\n')
log('K=%d L=%d S=%d parts=%d leaves/part=%d files=%d block=%d depth=%d blockfiles=%d stride=%d sha256(file)=%s' % (
    K, L, S, len(pres), math.factorial(free), len(files), B, d, nbfiles, stride, sha_file))
