"""Generate the Lean certificate files for a literal superpermutation.

    gen.py WORD.txt NAME [--leaves N] [--block B] [--per-file P] [--source TEXT] [--out DIR]

WORD.txt   the word, one symbol per character (any alphabet; symbols are ranked in ASCII order);
           a file whose name ends in .xz is decompressed
NAME       module name below Superperm, e.g. N7 -> DIR/Superperm/N7/{Word,P000,...,Main}.lean
DIR        default: the directory of this script

Python 3, no packages.

The certificate (see Superperm/Literal.lean):
  W        the word as one number, symbol i = base-16 digit i (so the hex literal is the word reversed)
  tables   for every arrangement q of 0..K-1 the position pos (S bits) at which the window of the
           word, read backwards, is q.  The walk fixes the first s choices (`pre`) per part; the table
           of a part holds the (K-s)! entries of its branch, in lexicographic order of the rest.
The script runs the same check as Lean before it writes anything.
"""
import argparse, itertools, math, os, hashlib

ap = argparse.ArgumentParser()
ap.add_argument('word'); ap.add_argument('name')
ap.add_argument('--leaves', type=int, default=720, help='largest number of permutations in one kernel check (default 720: about 100 MB and 1 s)')
ap.add_argument('--block', type=int, default=262144, help='digits per leaf of the word tree (a leaf lookup copies half a block on average; each tree level costs about 0.06 ms per permutation)')
ap.add_argument('--chunk', type=int, default=65536, help='hex digits per literal of the word (Lean reads a numeral in quadratic time)')
ap.add_argument('--per-file', type=int, default=56, help='parts per Lean file')
ap.add_argument('--source', default='', help='one line describing where the word comes from')
ap.add_argument('--out', default=os.path.dirname(os.path.abspath(__file__)), help='directory in which Superperm/NAME is written')
a = ap.parse_args()

def read_word(path):
    """the bytes of a word file; a file whose name ends in .xz is decompressed first"""
    if path.endswith('.xz'):
        import lzma
        with lzma.open(path) as f: return f.read()
    with open(path, 'rb') as f: return f.read()

raw = read_word(a.word).decode().strip()
syms = sorted(set(raw)); K = len(syms); L = len(raw)
assert K <= 16
rank = {c: i for i, c in enumerate(syms)}
w = [rank[c] for c in raw]
sha = hashlib.sha256(raw.encode()).hexdigest()

# first position of every permutation window, keyed by the reversed window
pos = {}
for i in range(L - K + 1):
    win = tuple(w[i:i + K])
    if len(set(win)) == K:
        q = win[::-1]
        if q not in pos: pos[q] = i
assert len(pos) == math.factorial(K), 'not a superpermutation: %d of %d' % (len(pos), math.factorial(K))

S = max(1, (L - 1).bit_length())                 # bits per table entry
s = 0
while math.factorial(K - s) > a.leaves: s += 1
B = a.block
d = 0
while B * 2 ** d < L: d += 1
mS = 2 ** S - 1; mK = 2 ** (4 * K) - 1
stride = S * math.factorial(K - s - 1) if K - s >= 1 else 0
W = int(''.join('%x' % x for x in reversed(w)), 16)   # = sum of w[i] * 16^i

def prefixes(K, s):
    """the order of LiteralSuperperm.prefixes"""
    if s == 0: return [[]]
    return [[x] + pre for pre in prefixes(K, s - 1) for x in range(K) if x not in pre]

def table(pre):
    rest = [x for x in range(K) if x not in pre]
    t = 0
    for i, r in enumerate(itertools.permutations(rest)):
        t |= pos[tuple(pre) + r] << (S * i)
    return t

def build(dd, x):
    """LiteralSuperperm.build"""
    if dd == 0: return x
    h = B * 2 ** (dd - 1)
    return (build(dd - 1, x & (2 ** (4 * (h + K)) - 1)), build(dd - 1, x >> (4 * h)))

def get(dd, t, p):
    """LiteralSuperperm.get"""
    while dd > 0:
        dd -= 1
        h = B * 2 ** dd
        if p + 1 <= h: t = t[0]
        else: t = t[1]; p -= h
    return t >> (4 * p)

tree = build(d, W)

def check_part(pre, tbl):
    """LiteralSuperperm.part, line by line"""
    def go(r, rem, c, tbl, stride):
        if r == 0:
            p = tbl & mS
            return p + K <= L and (get(d, tree, p) & mK) == c
        for x in rem:
            if not go(r - 1, [y for y in rem if y != x], c * 16 + x, tbl, stride // (r - 1) if r > 1 else 0): return False
            tbl >>= stride
        return True
    rem = [x for x in range(K) if x not in pre]
    c = 0
    for x in pre: c = c * 16 + x
    return go(K - len(pre), rem, c, tbl, stride)

pres = prefixes(K, s)
tabs = [table(p) for p in pres]
for p, t in zip(pres, tabs):
    assert check_part(p, t), p

outdir = os.path.join(a.out, 'Superperm', a.name)
os.makedirs(outdir, exist_ok=True)
for fn in os.listdir(outdir):
    if fn.endswith('.lean'): os.remove(os.path.join(outdir, fn))
ns = 'LiteralSuperperm.' + a.name
args = '%d %d %d %d %d %d W %d' % (K, L, mS, mK, B, d, stride)

def lit(x): return '0x%x' % x
def tname(p): return 't' + ''.join('_%d' % x for x in p) if p else 't_all'
def pname(p): return 'p' + ''.join('_%d' % x for x in p) if p else 'p_all'
def plist(p): return '[' + ', '.join(str(x) for x in p) + ']'

def write(fn, text):
    with open(os.path.join(outdir, fn), 'w', newline='\n', encoding='utf-8') as f: f.write(text)

def chain(names, tail, lemma):
    return ''.join(f'  {lemma}.2 ⟨{n},\n' for n in names) + '  ' + tail + '⟩' * len(names)

if L <= a.chunk:
    wdef = 'def W : Nat := ' + lit(W)
else:
    cm = 16 ** a.chunk - 1
    chunks = [(W >> (4 * a.chunk * i)) & cm for i in range((L + a.chunk - 1) // a.chunk)]
    assert sum(c << (4 * a.chunk * i) for i, c in enumerate(chunks)) == W
    wdef = ('/-- The word in pieces of %d digits, lowest first. -/\ndef chunks : List Nat := [\n  ' % a.chunk
            + ',\n  '.join(lit(c) for c in chunks) + ']\n\n'
            + 'def W : Nat := chunks.foldr (fun c acc => Nat.lor c (Nat.shiftLeft acc %d)) 0' % (4 * a.chunk))

write('Word.lean', f'''import Superperm.Literal

/-! Generated by gen.py.  {a.source}
The word has {L} symbols over {K} letters (SHA-256 of the text, without line end: {sha}).
`W` is the word as a number: symbol `i` (from the left, letters ranked 0..{K-1}) is base-16 digit `i`,
so the literal below is the word written backwards. -/

namespace {ns}

{wdef}

end {ns}
''')

files = []
for fi in range(0, len(pres), a.per_file):
    k = fi // a.per_file
    mod = 'P%03d' % k
    files.append(k)
    ps = pres[fi:fi + a.per_file]; ts = tabs[fi:fi + a.per_file]
    body = [f'import Superperm.{a.name}.Word', '',
            f'/-! Generated by gen.py: position tables and kernel checks for {len(ps)} branches of {math.factorial(K - s)} permutations. -/', '',
            '-- one declaration at a time on one thread: the memory of each kernel check is given back before the next',
            'set_option Elab.async false', '',
            f'namespace {ns}', 'open LiteralSuperperm', '']
    for p, t in zip(ps, ts):
        body.append(f'def {tname(p)} : Nat := {lit(t)}')
        body.append(f'theorem {pname(p)} : part {args} {plist(p)} {tname(p)} = true := by decide +kernel')
        body.append('')
    body.append(f'def items{k} : List (List Nat × Nat) := [' + ', '.join(f'({plist(p)}, {tname(p)})' for p in ps) + ']')
    body.append('')
    body.append(f'theorem items{k}_ok : ∀ x ∈ items{k}, part {args} x.1 x.2 = true :=')
    body.append(chain([pname(p) for p in ps], '(fun _ h => nomatch h)', 'List.forall_mem_cons'))
    body.append('')
    body.append(f'end {ns}')
    write(mod + '.lean', '\n'.join(body) + '\n')

imports = '\n'.join(f'import Superperm.{a.name}.P%03d' % k for k in files)
tailpart = f"""
/-- The literal word. -/
def word : List (Fin {K}) := wordOf {K} {L} W (by decide)

theorem word_length : word.length = {L} := wordOf_length _ _ _ _
"""
if len(pres) <= 1000:
    allitems = ''.join(f'items{k} ++ (' for k in files) + '[]' + ')' * len(files)
    deep = 'set_option maxRecDepth 8192 in\n' if len(files) > 16 else ''   # the proof of items_ok is nested once per file
    write('Main.lean', f"""{imports}

/-! Generated by gen.py.  {a.source}
A word of {L} symbols over {K} letters that contains every permutation.
Every computation is a kernel reduction (`decide +kernel`): no `native_decide`. -/

namespace {ns}
open LiteralSuperperm SuperpermutationBounds

/-- The {len(pres)} branches of the walk (first {s} choices) with their position tables. -/
def items : List (List Nat × Nat) := {allitems}

{deep}theorem items_ok : ∀ x ∈ items, part {args} x.1 x.2 = true :=
{chain([f'items{k}_ok' for k in files], '(fun _ h => nomatch h)', 'List.forall_mem_append')}

theorem items_complete : itemsComplete {K} {s} items = true := by decide +kernel
{tailpart}
theorem word_covers : Covers word :=
  covers_of_parts (by decide) (by decide) (by decide) (by decide) items items_ok
    (hpre_of_itemsComplete items_complete)

theorem hasWord : HasWord {K} {L} := ⟨word, word_covers, word_length.le⟩

end {ns}
""")
else:
    # many branches: completeness is checked group by group (Superperm/Groups.lean); a group is one file
    per_tail = K - (s - 1)
    assert a.per_file % per_tail == 0, 'a file must hold whole groups of %d branches' % per_tail
    lines = []
    for k in files:
        ps = pres[k * a.per_file:(k + 1) * a.per_file]
        tails = [p[1:] for p in ps[::per_tail]]
        assert [[x] + t for t in tails for x in range(K) if x not in t] == ps
        lines.append(f'def tails{k} : List (List Nat) := [' + ', '.join(plist(t) for t in tails) + ']')
        lines.append(f'theorem group{k}_ok : groupOK {K} tails{k} items{k} = true := by decide +kernel')
    groups = ', '.join(f'(tails{k}, items{k})' for k in files)
    nl = '\n'
    write('Main.lean', f"""import Superperm.Groups
{imports}

/-! Generated by gen.py.  {a.source}
A word of {L} symbols over {K} letters that contains every permutation.
Every computation is a kernel reduction (`decide +kernel`): no `native_decide`. -/

-- one declaration at a time on one thread: the memory of each kernel check is given back before the next
set_option Elab.async false

namespace {ns}
open LiteralSuperperm SuperpermutationBounds

/-! The {len(pres)} branches of the walk (first {s} choices) in {len(files)} groups; `tails k` are the
last {s - 1} choices of the branches of group `k`. -/

{nl.join(lines)}

def groups : List (List (List Nat) × List (List Nat × Nat)) := [{groups}]

set_option maxRecDepth 8192 in
theorem groups_ok : ∀ g ∈ groups, ∀ x ∈ g.2, part {args} x.1 x.2 = true :=
{chain([f'items{k}_ok' for k in files], '(fun _ h => nomatch h)', 'List.forall_mem_cons')}

set_option maxRecDepth 8192 in
theorem groups_complete : ∀ g ∈ groups, groupOK {K} g.1 g.2 = true :=
{chain([f'group{k}_ok' for k in files], '(fun _ h => nomatch h)', 'List.forall_mem_cons')}

theorem tails_complete : tailsComplete {K} {s - 1} groups = true := by decide +kernel
{tailpart}
theorem word_covers : Covers word :=
  covers_of_groups (by decide) (by decide) (by decide) (by decide) groups groups_ok
    tails_complete groups_complete

theorem hasWord : HasWord {K} {L} := ⟨word, word_covers, word_length.le⟩

end {ns}
""")
with open(os.path.join(outdir, 'modules.txt'), 'w', newline='\n') as f:
    f.write('\n'.join(['Word'] + ['P%03d' % k for k in files] + ['Main']) + '\n')
print('K=%d L=%d S=%d split=%d parts=%d leaves/part=%d files=%d block=%d depth=%d stride=%d sha256=%s' % (
    K, L, S, s, len(pres), math.factorial(K - s), len(files), B, d, stride, sha))
