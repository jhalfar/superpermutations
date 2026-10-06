"""Python mirror of Superperm8/KCode.lean and KSearch.lean (same arithmetic, same order of children).
Used to check the definitions against opt/lb/small/affine_check.py (node counts) and to plan the cut of the
search into parts for the kernel (plan.py imports this file).

usage: ksim.py A Cc Bd fuel      prints the result of fsearch, the number of calls of fsearchK and the depth profile
"""
import sys
sys.setrecursionlimit(100000)

def rotF(c): return ((c // 8 % 262144) * 8 + c // 2097152) * 8 + c % 8
def rotR(c): return (c % 2097152) * 8 + c // 2097152
def cmask(c): return c & (c >> 1) & (c >> 2) & 2396745
def ccanon(c):
    m = cmask(c)
    return (c * (2097152 // m)) % 16777216 + c // (8 * m)
def cidxV(v): return (v // 64 % 32768) * 2 + (1 if (v // 8 % 8) < (v % 8) else 0)
def cidx(c): return cidxV(ccanon(c))
def bmask(nx): return nx & (nx >> 1) & (nx >> 2) & 299593
def btarget(last): return 6 if last == 7 else 7
def bcanon(c):
    top, last = c // 8, c % 8
    m = bmask((top ^ (btarget(last) * 299593)) ^ 2097151)
    return ((top * (262144 // m)) % 2097152 + top // (8 * m)) * 8 + last
def bidxV(v): return (v // 512 % 4096) * 16 + (8 if (v // 64 % 8) < (v // 8 % 8) else 0) + v % 8
def bidx(c): return bidxV(bcanon(c))
def sixCodes(c):
    base = (c // 8 % 32768) * 512; x = c // 2097152; y = c // 262144 % 8; z = c % 8
    return [base + x*64 + y*8 + z, base + x*64 + z*8 + y, base + y*64 + x*8 + z,
            base + y*64 + z*8 + x, base + z*64 + x*8 + y, base + z*64 + y*8 + x]
def bit(S, i): return (S >> i) & 1 == 1
def setBit(S, i): return S | (1 << i)

def rowAcc(mk, kmax, C0, n, i, k, sc, Cacc, acc):
    """returns a Python list: the Lean list, head first"""
    if n == 0:
        return acc
    ci = cidx(sc)
    def omit():
        if 1 <= i and k + 1 <= kmax:
            return rowAcc(mk, kmax, C0, n - 1, i + 1, k + 1, rotF(sc), Cacc, acc)
        return acc
    if bit(C0, ci):
        return omit()
    C2 = setBit(Cacc, ci)
    rest = rowAcc(mk, kmax, C0, n - 1, i + 1, k, rotF(sc), C2, omit())
    if 6 - i + k <= kmax:
        return [mk(6 - i + k, sc, C2)] + rest
    return rest

def childrenAt(A, Cc, st, qc, acc):
    uc, B, C, s = st
    return rowAcc(lambda ch, sc, C2: (sc, setBit(B, bidx(qc)), C2, s + A - Cc * ch),
                  (s + A - 1) // Cc, C, 7, 0, 0, qc, C, acc)

def children(A, Cc, st):
    uc, B, C, s = st
    acc = []
    for qc in reversed(sixCodes(uc)):          # List.foldr
        if not bit(B, bidx(qc)):
            acc = childrenAt(A, Cc, st, qc, acc)
    return acc

IDC = 342391
def rootChildren(A, Cc): return childrenAt(A, Cc, (0, 0, 0, 0), IDC, [])

class Search:
    def __init__(self, A, Cc, Bd):
        self.A, self.Cc, self.Bd = A, Cc, Bd
        self.calls = 0
        self.per_depth = {}
    def found(self, fuel, st, depth=1):
        """fsearchK with the leaf `true`"""
        self.calls += 1
        self.per_depth[depth] = self.per_depth.get(depth, 0) + 1
        if fuel == 0:
            return True
        if self.Bd < st[3]:
            return True
        for c in children(self.A, self.Cc, st):
            if self.found(fuel - 1, c, depth + 1):
                return True
        return False
    def fsearch(self, fuel):
        for c in rootChildren(self.A, self.Cc):
            if self.found(fuel, c):
                return True
        return False

def self_test():
    """the two walk tests of KCode.lean (cTest_all, bTest_all), and that the indices separate classes and blocks"""
    import itertools
    def code(p):
        c = 0
        for a in p: c = c * 8 + a
        return c
    cls, blk = {}, {}
    for p in itertools.permutations(range(8)):
        c = code(p)
        v = ccanon(c); rots = [c]
        for _ in range(7): rots.append(rotR(rots[-1]))
        assert v // 2097152 == 7 and v in rots
        w = bcanon(c); frots = [c]
        for _ in range(6): frots.append(rotF(frots[-1]))
        assert w // 2097152 == btarget(c % 8) and w in frots
        cls.setdefault(cidx(c), set()).add(min(rots))
        blk.setdefault(bidx(c), set()).add(min(frots))
    assert all(len(s) == 1 for s in cls.values()) and len(cls) == 5040, len(cls)
    assert all(len(s) == 1 for s in blk.values()) and len(blk) == 5760, len(blk)
    assert max(cls) < 65536 and max(blk) < 65536
    print("self test passed: 5040 class indices, 5760 block indices, all below 65536")

if __name__ == "__main__":
    if sys.argv[1] == "selftest":
        self_test(); sys.exit()
    A, Cc, Bd, fuel = (int(x) for x in sys.argv[1:5])
    S = Search(A, Cc, Bd)
    r = S.fsearch(fuel)
    print(f"fsearch {A} {Cc} {Bd} {fuel} = {str(r).lower()}; calls of fsearchK: {S.calls}; deepest: {max(S.per_depth)} rows")
    print("root children:", len(rootChildren(A, Cc)))
