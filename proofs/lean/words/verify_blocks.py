"""Check that the block literals of a generated certificate spell a given word file.

    verify_blocks.py NAME WORD.txt [DIR]

Reads DIR/Superperm/NAME/B*.lean and Tree.lean (DIR: by default the directory of this script; nothing of
gen11.py is used): the blocks `b0, b1, …`, the block length B, the number of shared letters and the word
length from the `chkT`, `partCyc` lines.  Block i, read backwards, must be the letters B*i .. B*i+B+Kw-1 of
the word (as far as the word goes; '0' beyond it), with the letters of the file ranked in ASCII order.
Prints the SHA-256 of the file.

A file whose name ends in .xz is decompressed.  Python 3, no packages.
"""
import sys, os, re, glob, hashlib
name, wordfile = sys.argv[1], sys.argv[2]
here = sys.argv[3] if len(sys.argv) > 3 else os.path.dirname(os.path.abspath(__file__))
d = os.path.join(here, 'Superperm', name)
tree = open(os.path.join(d, 'Tree.lean'), encoding='utf-8').read()
B, Kw, depth = map(int, re.search(r'chkT (\d+) (\d+) (\d+) tree W = true', tree).groups())
main = open(os.path.join(d, 'Main.lean'), encoding='utf-8').read()
K, L = map(int, re.search(r'theorem hasWord : HasWord (\d+) (\d+)', main).groups())
blocks = {}
for fn in sorted(glob.glob(os.path.join(d, 'B*.lean'))):
    for m in re.finditer(r'^def b(\d+) : Nat := 0x([0-9a-f]+)$', open(fn, encoding='utf-8').read(), re.M):
        blocks[int(m.group(1))] = m.group(2)
assert sorted(blocks) == list(range(2 ** depth)), 'blocks missing'
if wordfile.endswith('.xz'):
    import lzma
    data = lzma.open(wordfile).read()
else:
    data = open(wordfile, 'rb').read()
raw = data.strip()
syms = sorted(set(raw))
assert len(syms) == K and len(raw) == L, (len(syms), len(raw))
tr = bytes.maketrans(bytes(syms), b'0123456789abcdef'[:K])
word = raw.translate(tr).decode()
for i in range(2 ** depth):
    want = word[B * i:B * i + B + Kw][::-1] or '0'
    assert blocks[i] == want, 'block %d differs' % i
# the leaves of `tree` are b0, b1, … in this order
order = []
for fn in sorted(glob.glob(os.path.join(d, 'B*.lean'))):
    s = open(fn, encoding='utf-8').read()
    order += [int(x) for x in re.findall(r'WT\.leaf b(\d+)', s[s.index('def s'):])]
assert order == list(range(2 ** depth)), 'leaves out of order'
subs = [int(x) for x in re.findall(r'\bs(\d+)\b', tree[tree.index('def tree'):tree.index('def W')])]
assert subs == list(range(len(glob.glob(os.path.join(d, 'B*.lean'))))), 'subtrees out of order'
print('%s: %d blocks of %d (+%d) letters spell the %d letters over %d symbols of %s' % (name, 2 ** depth, B, Kw, L, K, wordfile))
print('SHA-256 of the file%s: %s' % (' (decompressed)' if wordfile.endswith('.xz') else '', hashlib.sha256(data).hexdigest()))
