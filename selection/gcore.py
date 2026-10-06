"""gcore.py - selections with rows of any visible length: step, port rule, closed trails, completion, transport.

The one library of this directory.  Every builder and every solver here takes the step, the port permutation, the
number of closed trails, the literal completion, the transport and the file format from this file.  The three
checkers (check2.py, check12.py, gcover.py) deliberately do not import it.

Vocabulary (Pantone's paper, sections 2 to 4; the README has the same list):
  letters   K letters 0 .. K-1 and a distinguished letter s (k = K + 1 symbols).  Completion adds a letter z and
            gives pieces on n = K + 2 symbols.  h = n - 3 = K - 1 is the length of the end words of a slice.
  2-loop    a cyclic order of the K letters (the distinguished letter is always s here); there are (K-1)! of them.
            In this file a 2-loop is a tuple that starts with the letter 0 ("loop").
  row       the slice chosen in a 2-loop: (x, v) is the slice S(x, s; v) that starts at the rotation x of the loop
            and runs through v of its K cyclic classes (the "visible" classes).  v = K is Pantone's full slice,
            v = K - 2 his short slice, v = 1 .. K-3 are the rows of other visible lengths.  v = K - 1 is not used:
            the next row would lie in the same loop.  A row costs its deficit K - v; Q is the sum of the deficits.
  loop without a row   v = 0: a left-over loop.  Completion repairs all its K classes; it gives one closed trail
            of K slices, a "small trail".  Program output also says "D loop" or "detached loop".
  state     an ordering x of the K letters: the rotation of its loop at which a row starts.
  step      the row that follows (x, v) starts at the state
                G_K(x) = x[1 .. K-2] x[0] x[K-1]                    (full)
                G_v(x) = x[v+1 ..] x[.. v-2] x[v] x[v-1]            (v <= K - 2)
            A step exchanges two cyclically adjacent letters.  A selection is balanced when its rows are closed
            under the step; the rows then fall into closed walks, and the closed trails are forced.
  completion   (section 3 of the paper, written for any v)
                inserted slices   (x with z in front of x[j], s, v + [j < v] classes),   j = 0 .. K-1
                repair slices     (rot(x, i) s, z, K + 1 classes),                       i = v .. K-1
            A loop L without a row: the K repair slices (rot(L, i) s, z, K + 1), i = 0 .. K-1.
            All slices together cover every cyclic class on n symbols once; there are K! + Q of them.
  ports     the K inserted slices of a row are indexed by the gap j of z.  Slice K-1 is always entered from inside
            the row, so a row has the K - 1 entry ports 0 .. K-2.  A trail that enters a row at port j enters the
            next row at port pi_v(j):
                full:        j -> j - 1 mod (K-1)
                v <= K-2:    j -> j + K-v-1 (j < v),    v -> K-v-2,    j -> j - v - 1 (j > v)
            The closed trails of a closed walk after completion are the cycles of the product of its pi_v.  For
            walks of full and short rows that number is gcd(K - 1, f - t), f full and t short rows.
  transport (section 4): a full row, a short row and a loop without a row have a transport to K + 1 letters.  A row
            of another length has none (transport_search.py), so a selection with such rows serves one n only.
  block     the loops above a left-over loop D of a selection on m letters: all cyclic orders of m + r letters whose
            "old" letters 0 .. m-1 stand in the cyclic order D; r letters are "added".  A row of a block solution
            never exchanges two old letters, so it never leaves the block.
  floor     Q + (closed trails after completion), a lower limit for what the selection costs above F3(n) + n - 4.

File format of a selection or of a block solution: one line per 2-loop, "x v": x = the state as K characters of the
alphabet 0123456789AB.., v = the number of visible classes, 0 for a loop without a row (x is then the rotation that
starts with 0).  The letters F, S, D are read for v = K, K - 2, 0.  Lines that start with # are comments.  Pantone's
construction-input.txt is read as well (row type 0 = full, 2 = short).

usage:    python gcore.py --test               the port rule against the literal endpoint graph of the completion,
                                               on 120 random selections with rows of all lengths (K = 5, 6, 7)
          python gcore.py FILE [--literal]     Q, loops without a row, closed walks and their closed trails of a
                                               whole selection; with --literal also the closed trails counted in
                                               the endpoint graph of all slices of the completion
          (a block solution is not a whole selection: use lit_block.py for one)
inputs:   FILE as above.
outputs:  text on standard output.
needs:    Python 3.  No other package.
cost:     measured here on one thread: --test 5 s; the 10-symbol selection of n = 11 (40,320 loops) with
          --literal 3 s and 0.2 GB.  Selections on 11 symbols and more: use check2.py or check12.py.
"""
import math
import random
import sys
from collections import Counter

ALPH = "0123456789ABCDEFGHIJ"


def canon(x):
    """The 2-loop of the state x: the rotation of x that starts with the letter 0."""
    i = x.index(0)
    return x[i:] + x[:i]


def gstep(x, v):
    """The step: the state at which the row after the row (x, v) starts.  For a full row the last letter of x jumps
    forward over x[0]; for v <= K - 2 the letters x[v-1] and x[v] are exchanged and the next row starts v + 1
    places later."""
    K = len(x)
    if v == K:
        return x[1:K - 1] + (x[0], x[K - 1])
    return x[v + 1:] + x[:v - 1] + (x[v], x[v - 1])


_PORT = {}


def port(v, K):
    """The port permutation pi_v of a row with v visible classes, as a tuple p with p[j] = pi_v(j), j = 0 .. K-2:
    a trail that enters the row at port j (the inserted slice with z in gap j) enters the next row at port p[j].
    Kept in a table; the assertion checks that it is a permutation."""
    key = (v, K)
    if key not in _PORT:
        if v == K:
            p = [(j - 1) % (K - 1) for j in range(K - 1)]
        else:
            p = [j + K - v - 1 if j < v else (K - v - 2 if j == v else j - v - 1) for j in range(K - 1)]
        assert sorted(p) == list(range(K - 1))
        _PORT[key] = tuple(p)
    return _PORT[key]


def read_gsel(path):
    """Read a selection or a block solution ("x v" lines; F, S, D are read for K, K - 2, 0).
    Returns a dict  loop -> (x, v);  for a loop without a row x is the loop itself.  The order of the dict is the
    order of the file."""
    sel = {}
    K = None
    for line in open(path):
        if line.startswith("#") or not line.strip():
            continue
        a, ty = line.split()[:2]
        x = tuple(ALPH.index(c) for c in a)
        K = len(x)
        if ty in ("F", "S", "D"):
            v = {"F": K, "S": K - 2, "D": 0}[ty]
        else:
            v = int(ty)
        assert canon(x) not in sel
        sel[canon(x)] = (x if v else canon(x), v)
    return sel


def read_any(path):
    """Read Pantone's construction-input.txt (header CIRCLE4380V1, then "x type" with type 0 = full, 2 = short; the
    connector cycles at its end are not read) or a file in the format of read_gsel."""
    if open(path).read(12) == "CIRCLE4380V1":
        tok = open(path).read().split()
        nrow = int(tok[1])
        sel = {}
        p = 3
        for _ in range(nrow):
            x = tuple(ALPH.index(c) for c in tok[p])
            K = len(x)
            sel[canon(x)] = (x, K if tok[p + 1] == "0" else K - 2)
            p += 2
        return sel
    return read_gsel(path)


def write_gsel(path, sel, comment=""):
    """Write a selection, one line per loop in increasing order of the loops.  When every row is full or short the
    letters F, S, D are written instead of the numbers (the first line says so).  `comment` becomes comment lines."""
    K = len(next(iter(sel)))
    fs = all(v in (0, K, K - 2) for (x, v) in sel.values())
    with open(path, "w", newline="\n") as f:
        f.write("# selection on k = %d symbols (K = %d letters, distinguished letter %s): x v  "
                "(v visible classes; %d full, %d short, 0 = loop without a row)%s\n" % (
                    K + 1, K, ALPH[K], K, K - 2, "; F/S/D notation" if fs else ""))
        for c in comment.split("\n"):
            if c:
                f.write("# " + c + "\n")
        for L in sorted(sel):
            x, v = sel[L]
            if fs:
                f.write("".join(ALPH[c] for c in x) + " " + {0: "D", K: "F", K - 2: "S"}[v] + "\n")
            else:
                f.write("".join(ALPH[c] for c in x) + " %d\n" % v)


def walks(sel):
    """The closed walks of a selection: follow the step from every row.  Returns (list of walks, each a list of
    states in order; dict state -> v of all rows).  Fails when a step leads to a state that is not the chosen row
    of its loop (the selection is not balanced) or when a walk does not close."""
    chosen = {x: v for (x, v) in sel.values() if v}
    seen = set()
    out = []
    for x0 in chosen:
        if x0 in seen:
            continue
        w, x = [], x0
        while x not in seen:
            assert x in chosen, "walk leaves the selection"
            seen.add(x)
            w.append(x)
            x = gstep(x, chosen[x])
        assert x == x0, "not closed"
        out.append(w)
    return out, chosen


def cycles_of(p):
    """Number of cycles of the permutation p (a list with p[i] = image of i)."""
    seen = [False] * len(p)
    c = 0
    for i in range(len(p)):
        if not seen[i]:
            c += 1
            j = i
            while not seen[j]:
                seen[j] = True
                j = p[j]
    return c


def walk_trails(w, chosen, K):
    """Number of closed trails that the closed walk w gives after completion: the cycles of the product of the port
    permutations of its rows, taken in the order of the walk."""
    p = list(range(K - 1))
    for x in w:
        q = port(chosen[x], K)
        p = [q[j] for j in p]
    return cycles_of(p)


def exact(sel, detail=False):
    """The numbers of a selection: (Q + D + walk trails, Q + D, walk trails, number of walks, Q, D), where D is the
    number of loops without a row and "walk trails" the closed trails of all walks after completion (port rule).
    The first entry is the floor Q + closed trails.  With detail also a Counter of (loops, Q, trails) per walk."""
    K = len(next(iter(sel)))
    ws, chosen = walks(sel)
    D = sum(1 for (x, v) in sel.values() if v == 0)
    Q = sum(K - v for v in chosen.values())
    tr = 0
    st = Counter()
    for w in ws:
        c = walk_trails(w, chosen, K)
        tr += c
        if detail:
            st[(len(w), sum(K - chosen[x] for x in w), c)] += 1
    r = (Q + D + tr, Q + D, tr, len(ws), Q, D)
    return (r, st) if detail else r


def report(sel, title=""):
    """Print the numbers of a whole selection (it must have all (K-1)! loops) and return exact(sel)."""
    K = len(next(iter(sel)))
    N = math.factorial(K - 1)
    assert len(sel) == N
    r, st = exact(sel, detail=True)
    vs = Counter(v for (x, v) in sel.values())
    print("%sK = %d (%d loops): Q = %d, D = %d, walk trails = %d (%d walks); floor Q + trails = %d = %.6f x %d" % (
        title, K, N, r[4], r[5], r[2], r[3], r[0], r[0] / N, N))
    print("   rows by visible length:", dict(sorted(vs.items(), reverse=True)))
    for key in sorted(st, reverse=True)[:16]:
        print("   %5d walk(s): %6d loops, Q %6d, %d trails" % ((st[key],) + key))
    return r


# ---------------------------------------------------------------- transport (Pantone, section 4)
def transport_row(x, v):
    """The states of the K rows that the row (x, v) has after one transport to K + 1 letters (new letter w = K),
    in the order of the gap j = 0 .. K-1 of w.  Full row (v = K): w in front of x[j].  Short row (v = K - 2),
    x = u a b: the same, except that u a w b is replaced by its rotation b u a w.  The rows above are full,
    respectively short, again.  For a loop without a row (v = 0) the K results are the K loops above it, each
    again without a row (take canon of each).  Rows of other lengths have no transport."""
    K = len(x)
    assert v in (0, K, K - 2), "a row with %d of %d visible classes has no transport" % (v, K)
    w = K
    out = []
    for j in range(K):
        y = x[:j] + (w,) + x[j:]
        if v == K - 2 and j == K - 1:
            y = (x[-1],) + x[:-1] + (w,)
        out.append(y)
    return out


def transport(sel):
    """One transport of a whole selection of full and short rows and loops without a row: dict loop -> (x, v) on
    K + 1 letters.  Q, the number of loops without a row and the number of walk trails are all multiplied by K
    relative to (K-1)!, so the floor constant does not change."""
    out = {}
    for L, (x, v) in sel.items():
        for y in transport_row(x, v):
            c = canon(y)
            assert c not in out
            out[c] = (y, v + 1) if v else (c, 0)
    return out


# ---------------------------------------------------------------- blocks
def block_loops(m, r):
    """The loops of the (m, r) block: all cyclic orders of the K = m + r letters whose old letters 0 .. m-1 stand
    in the cyclic order (0 1 .. m-1), in increasing order.  There are (K-1)!/(m-1)! of them."""
    K = m + r
    base = [tuple(range(m))]
    for t in range(m, K):
        nb = []
        for c in base:
            for j in range(1, len(c) + 1):
                nb.append(c[:j] + (t,) + c[j:])
        base = nb
    loops = sorted(set(canon(c) for c in base))
    assert len(loops) == math.factorial(K - 1) // math.factorial(m - 1)
    return loops


# ---------------------------------------------------------------- literal completion: endpoint graph
def literal_trails(sel):
    """The closed trails of the completion, counted literally: every inserted and repair slice is written down with
    its head (first h letters of its word) and its tail (last h letters), each head must occur once and each tail
    must be the head of exactly one slice, and the cycles of "slice -> the slice whose head is its tail" are
    counted.  Does not use port().  Returns (closed trails, number of slices)."""
    K = len(next(iter(sel)))
    z, s = K + 1, K
    h = K - 1
    nxt = {}
    indeg = Counter()

    def rot(y, j):
        """y rotated left by j places"""
        j %= len(y)
        return y[j:] + y[:j]
    for L, (x, v) in sel.items():
        b = x
        if v:
            for j in range(K):
                y = b[:j] + (z,) + b[j:]
                vv = v + (1 if j < v else 0)
                head = y[:h]
                tail = ((s,) + rot(y, vv - 1))[-h:]
                assert head not in nxt
                nxt[head] = tail
                indeg[tail] += 1
        for j in range(v, K):
            y = rot(b, j) + (s,)
            head = y[:h]
            tail = ((z,) + rot(y, K))[-h:]
            assert head not in nxt
            nxt[head] = tail
            indeg[tail] += 1
    assert all(indeg[a] == 1 for a in nxt) and len(indeg) == len(nxt), "endpoint graph not balanced"
    seen = set()
    c = 0
    for a in nxt:
        if a not in seen:
            c += 1
            while a not in seen:
                seen.add(a)
                a = nxt[a]
    return c, len(nxt)


def random_gsel(K, rnd, tries=2000):
    """A random balanced selection with rows of all lengths, for the self-test: random closed walks through
    distinct loops are grown step by step; a walk is kept when it returns to its first state.  All other loops
    stay without a row."""
    N = math.factorial(K - 1)
    sel = {}
    used = set()
    VS = [K] + list(range(1, K - 1))
    import itertools
    loops = [(0,) + p for p in itertools.permutations(range(1, K))]
    for _ in range(tries):
        L = rnd.choice(loops)
        if L in used:
            continue
        r = rnd.randrange(K)
        x0 = L[r:] + L[:r]
        path = [(x0, None)]
        on = {L}
        x = x0
        ok = False
        for _step in range(rnd.randrange(2, 3 * K)):
            vs = VS[:]
            rnd.shuffle(vs)
            for v in vs:
                y = gstep(x, v)
                if y == x0:
                    path[-1] = (x, v)
                    ok = True
                    break
            if ok:
                break
            for v in vs:
                y = gstep(x, v)
                if canon(y) not in on and canon(y) not in used:
                    path[-1] = (x, v)
                    path.append((y, None))
                    on.add(canon(y))
                    x = y
                    break
            else:
                break
        if ok:
            for (x, v) in path:
                sel[canon(x)] = (x, v)
                used.add(canon(x))
    for L in loops:
        if L not in sel:
            sel[L] = (L, 0)
    assert len(sel) == N
    return sel


def test_ports():
    """Self-test: on 40 random selections for each of K = 5, 6, 7 the closed trails by the port rule (exact) must
    equal the closed trails of the literal endpoint graph, and the number of slices must be K! + Q."""
    rnd = random.Random(5)
    for K in (5, 6, 7):
        for rep in range(40):
            sel = random_gsel(K, rnd)
            r = exact(sel)
            lit, nsl = literal_trails(sel)
            assert nsl == math.factorial(K) + r[4], (nsl, r)
            assert lit == r[2] + r[5], ("port formula disagrees with the literal endpoint graph", K, rep, lit, r)
        print("K = %d: 40 random selections, port formula = literal endpoint graph (last: Q %d, D %d, walk trails %d, %d walks)" % (
            K, r[4], r[5], r[2], r[3]))


if __name__ == "__main__":
    if sys.argv[1] == "--test":
        test_ports()
    else:
        sel = read_any(sys.argv[1])
        report(sel)
        if "--literal" in sys.argv:
            print("literal endpoint graph: %d closed trails, %d slices" % literal_trails(sel))
