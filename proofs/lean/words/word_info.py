"""What check_word.sh needs to know about a word before anything is generated.

    word_info.py WORD.txt

WORD.txt   the word, one symbol per character (symbols are ranked in ASCII order); white space at the ends
           is ignored; a file whose name ends in .xz is decompressed

Prints one "key=value" line each for:
  symbols        the number K of different symbols
  letters        the length L of the word
  sha256         SHA-256 of the file (after decompression)
  classes        (K-1)!, the number of rotation classes of permutations
  classes_full   how many of them the word visits in one stretch: K windows in a row that are permutations,
                 that is 2K-1 letters of period K, which contain all K rotations of the class
  permutations   how many different permutations occur.  If every class has a full run this is K! and is not
                 counted again.  Otherwise it is counted when K <= 10, and "unknown" is printed when K > 10.

A word is a superpermutation exactly if permutations = K!.  The method of Superperm/Cyc.lean needs
classes_full = classes.  Python 3 with numpy; the script needs about three times the size of the word in memory.
"""
import hashlib, math, sys
import numpy as np

sys.stdout.reconfigure(newline='\n')
path = sys.argv[1]
if path.endswith('.xz'):
    import lzma
    with lzma.open(path) as f: data = f.read()
else:
    with open(path, 'rb') as f: data = f.read()
sha = hashlib.sha256(data).hexdigest()
raw = np.frombuffer(data, np.uint8)
lo, hi = 0, len(raw)
while hi > lo and raw[hi - 1] in (9, 10, 13, 32): hi -= 1
while lo < hi and raw[lo] in (9, 10, 13, 32): lo += 1
raw = raw[lo:hi]
L = len(raw)
syms = np.flatnonzero(np.bincount(raw, minlength=256)); K = len(syms)
print('symbols=%d' % K); print('letters=%d' % L); print('sha256=%s' % sha)
if K < 2 or K > 16 or L < K:
    print('classes=0'); print('classes_full=0'); print('permutations=unknown')
    sys.exit(0)
lut = np.zeros(256, np.uint8); lut[syms] = np.arange(K, dtype=np.uint8)
w = lut[raw]; del raw, data
FACT = [math.factorial(i) for i in range(K + 1)]

def is_perm(seg, count):
    """for the first `count` positions of seg: is the window of K letters a permutation"""
    last = np.full(len(seg), -1, np.int32)           # previous occurrence of the same letter inside seg
    for s in range(K):
        idx = np.flatnonzero(seg == s)
        last[idx[1:]] = idx[:-1]
    m = last[:count].copy()
    for j in range(1, K): np.maximum(m, last[j:j + count], out=m)
    return m < np.arange(count, dtype=np.int32)

def rank(win):
    """lexicographic rank of each row of win (rows are arrangements of the same letters)"""
    r = np.zeros(len(win), np.int64); width = win.shape[1]
    for i in range(width - 1):
        r += (win[:, i + 1:] < win[:, i:i + 1]).sum(axis=1) * FACT[width - 1 - i]
    return r

# ---- runs of permutation windows, in pieces of 2^22 windows ----------------------------------------
n = L - K + 1
C = 1 << 22
full = np.zeros(FACT[K - 1], np.bool_)               # rotation classes with a full run
seen = np.zeros(FACT[K], np.bool_) if K <= 10 else None
run = 0                                              # length of the run that ends just before this piece
for a in range(0, n, C):
    b = min(n, a + C)
    p = is_perm(w[a:b + K - 1], b - a)
    if seen is not None:
        pos = np.flatnonzero(p) + a
        for c in range(0, len(pos), 1 << 18):
            q = pos[c:c + (1 << 18)]
            seen[rank(w[q[:, None] + np.arange(K)].astype(np.int8))] = True
    # run length ending at each position: positions where the K-th window of a run ends
    idx = np.arange(b - a, dtype=np.int64)
    start = np.where(p, 0, idx + 1)                  # last non-permutation position + 1 ...
    np.maximum.accumulate(start, out=start)
    length = np.where(p, idx - start + 1 + np.where(start == 0, run, 0), 0)
    ends = np.flatnonzero(length >= K) + a           # a full run ends here: windows ends-K+1 .. ends
    for c in range(0, len(ends), 1 << 18):
        q = ends[c:c + (1 << 18)]
        win = w[q[:, None] + np.arange(K)].astype(np.int64)
        shift = (win == K - 1).argmax(axis=1)        # rotate so that the letter K-1 comes last
        can = np.take_along_axis(win, (shift[:, None] + 1 + np.arange(K - 1)) % K, axis=1)
        full[rank(can.astype(np.int8))] = True
    run = int(length[-1]) if len(length) else 0
nfull = int(full.sum())
print('classes=%d' % FACT[K - 1]); print('classes_full=%d' % nfull)
if nfull == FACT[K - 1]: print('permutations=%d' % FACT[K])
elif seen is not None: print('permutations=%d' % int(seen.sum()))
else: print('permutations=unknown')
