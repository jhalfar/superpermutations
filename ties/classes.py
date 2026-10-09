"""classes.py LIST.tsv OUT.tsv: check record-length words and sort them into classes.

LIST.tsv: n <tab> source label <tab> path (a text file with one word, or the same compressed with xz).
For every word: length, whether it contains all n! permutations, how many windows are a permutation seen before
(repeats), the histogram of the steps between first occurrences (weight 1, 2, 3, ...), the histogram of the lengths
of maximal runs of weight-1 steps, and the SHA-256 of the two canonical forms (symbols renamed in order of first
appearance, for the word and for its reverse).  Two words are in one class if one is the other after renaming
symbols and, possibly, reversal: the class key is the smaller of the two hashes.
"""
import hashlib
import lzma
import math
import sys
from collections import Counter


def read(path):
    data = lzma.open(path).read() if path.endswith(".xz") else open(path, "rb").read()
    return data.decode("ascii").strip()


def relabel(w):
    m = {}
    out = []
    for c in w:
        if c not in m:
            m[c] = "123456789abcdef"[len(m)]
        out.append(m[c])
    return "".join(out)


def study(w, n):
    seen = set()
    last = None
    repeats = 0
    steps = Counter()
    runs = Counter()
    run = 0
    for i in range(len(w) - n + 1):
        p = w[i:i + n]
        if len(set(p)) != n:
            continue
        if p in seen:
            repeats += 1
            continue
        seen.add(p)
        if last is not None:
            d = i - last
            steps[d] += 1
            if d == 1:
                run += 1
            else:
                runs[run] += 1
                run = 0
        last = i
    runs[run] += 1
    return len(seen), repeats, steps, runs


def hist(c):
    return " ".join("%d:%d" % (k, c[k]) for k in sorted(c))


rows = []
for line in open(sys.argv[1], encoding="utf-8"):
    if not line.strip() or line.startswith("#"):
        continue
    n, label, path = line.rstrip("\n").split("\t")
    n = int(n)
    w = read(path)
    assert len(set(w)) == n, path
    perms, repeats, steps, runs = study(w, n)
    f = hashlib.sha256(relabel(w).encode()).hexdigest()
    r = hashlib.sha256(relabel(w[::-1]).encode()).hexdigest()
    rows.append([n, len(w), "yes" if perms == math.factorial(n) else "NO", min(f, r),
                 "same" if f == r else ("fwd" if f < r else "rev"), repeats, hist(steps), hist(runs),
                 hashlib.sha256(w.encode()).hexdigest(), label, path])
    print(n, len(w), perms == math.factorial(n), min(f, r), label, flush=True)
ids = {}
with open(sys.argv[2], "w", encoding="utf-8", newline="\n") as out:
    out.write("n\tlength\tall permutations\tclass\tclass key\tread\trepeats\tsteps weight:count\t"
              "weight-1 runs length:count\tsha256 of the file word\tsource\tpath\n")
    for t in rows:
        key = (t[0], t[1], t[3])
        ids.setdefault(key, "%d-%d-%03d" % (t[0], t[1], 1 + sum(1 for q in ids if q[:2] == key[:2])))
        out.write("\t".join(str(x) for x in t[:3] + [ids[key]] + t[3:]) + "\n")
print(len(rows), "words,", len(ids), "classes")
