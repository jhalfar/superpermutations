"""check_n6.py [LIST] - checks the list of minimal superpermutations on 6 symbols (default: minimal-6-872.txt.xz next to
this file; .xz, .gz or plain text, one word per line, letters 1-6).

For every line: length 872, letters 1-6, starts with 123456 (one word per class under relabelling), all 720
permutations occur as windows.  Then it prints the counts that README.md gives: distinct words, words with a repeated
permutation, palindromes, classes under relabelling and reversal, and the SHA-256 of the unpacked list.
It checks that each word is a superpermutation of length 872; that the list is complete is the claim of README.md and
is not something this script can check.  Python 3, standard library only, about 15 seconds."""
import gzip
import hashlib
import lzma
import os
import sys
from itertools import permutations

N, LEN = 6, 872
PERMS = {''.join(p) for p in permutations('123456')}
path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), 'minimal-6-872.txt.xz')
opener = lzma.open if path.endswith('.xz') else gzip.open if path.endswith('.gz') else open
with opener(path, 'rb') as f:
    data = f.read()
sha = hashlib.sha256(data).hexdigest()
words = data.decode('ascii').split('\n')
if words and words[-1] == '':
    words.pop()


def canon(w):
    m = {c: str(i + 1) for i, c in enumerate(w[:N])}
    return ''.join(m[c] for c in w)


bad = rep = 0
for w in words:
    if len(w) != LEN or set(w) - set('123456') or not w.startswith('123456'):
        bad += 1
        continue
    seen = {}
    for i in range(LEN - N + 1):
        x = w[i:i + N]
        if x in PERMS:
            seen[x] = seen.get(x, 0) + 1
    if len(seen) != 720:
        bad += 1
    elif any(v > 1 for v in seen.values()):
        rep += 1
S = set(words)
pal = sum(1 for w in words if w == w[::-1])
classes = {min(w, canon(w[::-1])) for w in S}
print(f"lines {len(words)}, distinct {len(S)}, bad {bad}, with a repeated permutation {rep}, palindromes {pal}, "
      f"classes under relabelling and reversal {len(classes)}")
print(f"sha256 {sha}")
ok = bad == 0 and len(S) == len(words) == 45116 and rep == 40 and pal == 0 and len(classes) == 22560 \
    and sha == '6683584162fbb8acbefeebf46c50c136b4613c0b110e9ef0c1192def74358b5f'
print("OK: the counts of README.md" if ok else "MISMATCH")
sys.exit(0 if ok else 1)
