"""Check that the number W of a certificate written by gen.py spells a given word file.

    verify_word.py NAME WORD.txt [DIR]

Reads DIR/Superperm/NAME/Word.lean and Main.lean (DIR: by default the directory of this script; nothing of
gen.py is used).  W is either one hexadecimal literal or a list `chunks` of literals that Lean joins,
lowest first, each shifted by the number of bits named in the definition of W.  With the letters of the file
ranked in ASCII order, letter i of the word (from the left) must be base-16 digit i of W, and W must have no
digit beyond the length of the word.  Prints the SHA-256 of the file.

A file whose name ends in .xz is decompressed.  Python 3, no packages.
"""
import sys, os, re, hashlib
name, wordfile = sys.argv[1], sys.argv[2]
here = sys.argv[3] if len(sys.argv) > 3 else os.path.dirname(os.path.abspath(__file__))
d = os.path.join(here, 'Superperm', name)
text = open(os.path.join(d, 'Word.lean'), encoding='utf-8').read()
main = open(os.path.join(d, 'Main.lean'), encoding='utf-8').read()
K, L = map(int, re.search(r'def word : List \(Fin (\d+)\) := wordOf \1 (\d+) W ', main).groups())

one = re.search(r'^def W : Nat := 0x([0-9a-f]+)$', text, re.M)
if one:
    W = int(one.group(1), 16)
else:
    shift = int(re.search(r'^def W : Nat := chunks\.foldr \(fun c acc => Nat\.lor c \(Nat\.shiftLeft acc (\d+)\)\) 0$',
                          text, re.M).group(1))
    body = text[text.index('def chunks : List Nat := [') + len('def chunks : List Nat := ['):text.index(']\n\ndef W')]
    chunks = [int(x, 16) for x in re.findall(r'0x([0-9a-f]+)', body)]
    assert re.fullmatch(r'(\s*0x[0-9a-f]+,?)*\s*', body), 'unexpected text in the list of chunks'
    W = 0
    for c in reversed(chunks):                       # foldr: the last chunk is the innermost
        assert c < (1 << shift), 'a chunk is longer than the shift'
        W = c | (W << shift)

if wordfile.endswith('.xz'):
    import lzma
    data = lzma.open(wordfile).read()
else:
    data = open(wordfile, 'rb').read()
raw = data.strip()
syms = sorted(set(raw))
assert len(syms) == K and len(raw) == L, (len(syms), len(raw))
tr = bytes.maketrans(bytes(syms), b'0123456789abcdef'[:K])
want = int(raw.translate(tr).decode()[::-1], 16)     # letter i is digit i, so the literal is the word backwards
assert W == want, 'W does not spell the word'
print('%s: W spells the %d letters over %d symbols of %s' % (name, L, K, wordfile))
print('SHA-256 of the file%s: %s' % (' (decompressed)' if wordfile.endswith('.xz') else '', hashlib.sha256(data).hexdigest()))
