"""rotations.py N WORD [--classes] [--write DIR]: the words obtained by reading the path of a word as a closed path.

The permutations of WORD in order of first occurrence form a path.  Joining its last permutation to its first costs
c letters (the closing step).  Cutting the closed path at a step of weight x gives a word of length L + c - x.
Printed: c, the number of steps of every weight, and for the cuts with x >= c the number of words and of classes
(renaming of the symbols and reversal, with --classes).  --write DIR writes the canonical hashes of the classes
with x = c, the word itself included, to DIR/rotations-N-LENGTH.sha256.
"""
import hashlib
import lzma
import os
import sys
from collections import Counter

SYM = "123456789abcdef"


def read(path):
    data = lzma.open(path).read() if path.endswith(".xz") else open(path, "rb").read()
    return data.decode("ascii").strip()


def relabel(v):
    m = {}
    out = []
    for c in v:
        if c not in m:
            m[c] = SYM[len(m)]
        out.append(m[c])
    return "".join(out)


def key(v):
    return min(hashlib.sha256(relabel(v).encode()).hexdigest(), hashlib.sha256(relabel(v[::-1]).encode()).hexdigest())


n, w = int(sys.argv[1]), read(sys.argv[2])
seen = set()
P = []
pos = []
for i in range(len(w) - n + 1):
    p = w[i:i + n]
    if len(set(p)) == n and p not in seen:
        seen.add(p)
        P.append(p)
        pos.append(i)
wt = [pos[i + 1] - pos[i] for i in range(len(P) - 1)]
close = next(k for k in range(1, n + 1) if P[-1][k:] == P[0][:n - k])
print("length", len(w), "permutations", len(P), "closing step", close, "steps", sorted(Counter(wt).items()))
better = [i for i, x in enumerate(wt) if x > close]
same = [i for i, x in enumerate(wt) if x == close]
print("cuts that give a shorter word:", len(better), "; cuts that give the same length:", len(same))
if "--classes" in sys.argv or "--write" in sys.argv:
    def word(i):                      # cut at step i: start at P[i+1], end at P[i]
        seq = P[i + 1:] + P[:i + 1]
        out = [seq[0]]
        for a, b in zip(seq, seq[1:]):
            k = next(k for k in range(1, n + 1) if a[k:] == b[:n - k])
            out.append(b[n - k:])
        return "".join(out)
    cls = {}
    for i in same:
        v = word(i)
        assert len(v) == len(w)
        cls.setdefault(key(v), v)
    cls.setdefault(key(w), w)
    print("classes of the same length, the word itself included:", len(cls))
    if "--write" in sys.argv:
        d = sys.argv[sys.argv.index("--write") + 1]
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "rotations-%d-%d.sha256" % (n, len(w))), "w", newline="\n") as f:
            for k in sorted(cls):
                f.write(k + "\n")
