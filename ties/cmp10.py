"""cmp10.py A B: steps of two words on 10 symbols that differ, both words in canonical form (four combinations of
reading directions)."""
import lzma
import sys


def read(path):
    data = lzma.open(path).read() if path.endswith(".xz") else open(path, "rb").read()
    return data.decode("ascii").strip()


def relabel(w):
    m = {}
    return "".join(m.setdefault(c, "123456789ab"[len(m)]) for c in w)


def steps(w, n=10):
    seen = set()
    last = None
    out = {}
    for i in range(len(w) - n + 1):
        p = w[i:i + n]
        if len(set(p)) != n or p in seen:
            continue
        seen.add(p)
        if last is not None:
            out[last] = (p, i - li)
        last = p
        li = i
    return out


a, b = read(sys.argv[1]), read(sys.argv[2])
for na, wa in (("A forward", relabel(a)), ("A reversed", relabel(a[::-1]))):
    A = steps(wa)
    for nb, wb in (("B forward", relabel(b)), ("B reversed", relabel(b[::-1]))):
        B = steps(wb)
        common = sum(1 for p, q in B.items() if p in A and A[p][0] == q[0])
        print(na, nb, "steps", len(A), len(B), "common", common, flush=True)
        if common > len(B) // 2:
            da = sorted(A[p][1] for p in A if p not in B or B[p][0] != A[p][0])
            db = sorted(B[p][1] for p in B if p not in A or A[p][0] != B[p][0])
            print(" steps only in A:", len(da), "weights", da[:60])
            print(" steps only in B:", len(db), "weights", db[:60])
        del B
    del A
