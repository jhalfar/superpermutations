"""The n = 8 words of Pantone's completion: loops, rows, selections, slices, closed trails, walks.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

The letters 6 and 7 are fixed (6 is Pantone's distinguished letter s, 7 the completion letter z).  A loop is a cyclic
order of 012345 (120 loops), written as the rotation that starts with 0.  A state is one of the 720 orderings of
012345; the state x belongs to the loop canon(x).  A selection gives every loop either a row (x, v), x a state of the
loop and v = 1 .. 6, or no row, written (loop, 0).  A row of length v costs 6 - v letters; Q is the sum.

The row (x, v) leads to the state gstep(x, v) of another loop, so the rows form closed walks.  A selection is
balanced when x -> gstep(x, v) maps the chosen states one to one onto the chosen states.

Every option is written as slices (strings of letters 0..7):
  row (x, v):     i_j = spell(x with 7 inserted before x[j], 6, v + [j < v]),   j = 0 .. 5
                  r_i = spell(rot(x, i) + 6, 7, 7),                             i = v .. 5
  no row (L, 0):  r_i = spell(rot(L, i) + 6, 7, 7),                             i = 0 .. 5
A selection has 720 + Q slices.  Two slices overlap by at most 5 letters, and by exactly 5 only along the closed
trails (each slice has exactly one successor and one predecessor of overlap 5).  A word that writes every slice
once, each joined to the previous one with overlap ov, has 46,085 + Q + J letters, J = sum of (5 - ov).
"""
import itertools
import math

K = 6
S_LETTER = 6
Z_LETTER = 7
BASE_LENGTH = 46085          # 8! + 7! + 6! + 5: the length of a word with Q = 0 and J = 0
ALPHABET = "01234567"


def canon(x):
    """the loop of a state: the rotation that starts with 0."""
    i = x.index(0)
    return x[i:] + x[:i]


def rot(x, j):
    j %= len(x)
    return x[j:] + x[:j]


def gstep(x, v):
    """the state at which the row after (x, v) starts."""
    if v == K:
        return x[1:K - 1] + (x[0], x[K - 1])
    return x[v + 1:] + x[:v - 1] + (x[v], x[v - 1])


STATES = list(itertools.permutations(range(K)))
LOOPS = sorted(set(canon(x) for x in STATES))
LOOP_STATES = {L: [x for x in STATES if canon(x) == L] for L in LOOPS}
VALUES = (1, 2, 3, 4, 5, 6)


def port(v):
    """how a row of length v permutes the K - 1 = 5 strands of a walk (Pantone's port rule)."""
    if v == K:
        return [(j - 1) % (K - 1) for j in range(K - 1)]
    return [j + K - v - 1 if j < v else (K - v - 2 if j == v else j - v - 1) for j in range(K - 1)]


PORT = {v: port(v) for v in VALUES}


def spell(b, d, m):
    """the slice S(b, d; m) as a string: m cyclic classes of b + d, d the letter that moves."""
    s = b + (d,) + b
    for t in range(m - 1):
        s += rot(b, t)[:1] + (d,) + rot(b, t + 1)
    return "".join(map(str, s))


_SLICES = {}


def option_slices(x, v):
    """[(name, string)] of the option (x, v); v = 0 means no row (x is then the loop)."""
    key = (x, v)
    if key not in _SLICES:
        out = []
        if v == 0:
            for i in range(K):
                out.append(("r%d" % i, spell(rot(x, i) + (S_LETTER,), Z_LETTER, 7)))
        else:
            for j in range(K):
                out.append(("i%d" % j, spell(x[:j] + (Z_LETTER,) + x[j:], S_LETTER, v + (1 if j < v else 0))))
            for i in range(v, K):
                out.append(("r%d" % i, spell(rot(x, i) + (S_LETTER,), Z_LETTER, 7)))
        _SLICES[key] = out
    return _SLICES[key]


def fmt(x):
    return "".join(map(str, x))


def parse_state(s):
    if len(s) != K or sorted(s) != list("012345"):
        raise ValueError("not an ordering of 012345: %r" % s)
    return tuple(int(c) for c in s)


# ---------------------------------------------------------------- selections

def read_selection(path):
    """read a selection file: one line per loop, "x v" (x a state, v = 0 .. 6); # starts a comment.
    Returns dict loop -> (x, v), with x = loop when v = 0.  Raises ValueError if the file is not a balanced
    selection of all 120 loops."""
    sel = {}
    with open(path) as f:
        for no, line in enumerate(f, 1):
            line = line.split("#")[0].strip()
            if not line:
                continue
            parts = line.split()
            if len(parts) < 2:
                raise ValueError("%s:%d: expected 'x v'" % (path, no))
            x = parse_state(parts[0])
            v = int(parts[1])
            if not 0 <= v <= K:
                raise ValueError("%s:%d: v must be 0 .. 6" % (path, no))
            L = canon(x)
            if L in sel:
                raise ValueError("%s:%d: loop %s appears twice" % (path, no, fmt(L)))
            sel[L] = (x, v) if v else (L, 0)
    check_selection(sel)
    return sel


def check_selection(sel):
    missing = [L for L in LOOPS if L not in sel]
    if missing:
        raise ValueError("%d loops are missing, e.g. %s" % (len(missing), fmt(missing[0])))
    if not balanced(sel):
        raise ValueError("the selection is not balanced: the rows do not form closed walks")


def write_selection(path, sel, comments=()):
    with open(path, "w", newline="\n") as f:
        for c in comments:
            f.write("# %s\n" % c)
        for L in LOOPS:
            x, v = sel[L]
            f.write("%s %d\n" % (fmt(x), v))


def balanced(sel):
    chosen = [x for x, v in sel.values() if v]
    image = [gstep(x, v) for x, v in sel.values() if v]
    return len(set(image)) == len(image) and set(image) == set(chosen)


def q_of(sel):
    return sum(K - v for x, v in sel.values() if v)


def rowless(sel):
    return sum(1 for x, v in sel.values() if not v)


def walks(sel):
    """the closed walks of the rows: lists of rows (x, v) in walk order."""
    nxt = {x: gstep(x, v) for x, v in sel.values() if v}
    vof = {x: v for x, v in sel.values() if v}
    seen = set()
    out = []
    for x0 in sorted(nxt):
        if x0 in seen:
            continue
        w = []
        u = x0
        while u not in seen:
            seen.add(u)
            w.append((u, vof[u]))
            u = nxt[u]
        out.append(w)
    return out


def port_trails(rows):
    """number of closed trails of a closed walk (list of row lengths v): cycles of the product of the port maps,
    plus one closed 2-slice trail for each row of length 5."""
    p = list(range(K - 1))
    for v in rows:
        p = [PORT[v][j] for j in p]
    seen = [False] * (K - 1)
    c = 0
    for i in range(K - 1):
        if not seen[i]:
            c += 1
            j = i
            while not seen[j]:
                seen[j] = True
                j = p[j]
    return c + sum(1 for v in rows if v == 5)


def slices(sel):
    """keys [(loop, name)] and strings of all slices of the selection, loops in sorted order."""
    keys, strs = [], []
    for L in LOOPS:
        x, v = sel[L]
        for name, s in option_slices(x, v):
            keys.append((L, name))
            strs.append(s)
    return keys, strs


def trail_cycles(strs):
    """the closed trails: cycles of the overlap-5 successor map.  Returns (list of cycles of slice indices, succ)."""
    pre = {}
    for i, s in enumerate(strs):
        pre.setdefault(s[:5], []).append(i)
    succ = []
    for i, s in enumerate(strs):
        js = [j for j in pre.get(s[-5:], ()) if j != i]
        if len(js) != 1:
            raise ValueError("slice %d has %d successors of overlap 5" % (i, len(js)))
        succ.append(js[0])
    if sorted(succ) != list(range(len(strs))):
        raise ValueError("the overlap-5 successors are not a permutation")
    seen = [False] * len(strs)
    cycles = []
    for i in range(len(strs)):
        if seen[i]:
            continue
        c = []
        u = i
        while not seen[u]:
            seen[u] = True
            c.append(u)
            u = succ[u]
        cycles.append(c)
    return cycles, succ


def max_overlap(a, b, cap=7):
    for k in range(min(cap, len(a) - 1, len(b) - 1), 0, -1):
        if a[-k:] == b[:k]:
            return k
    return 0


def assemble(strs, order, overlaps=None):
    """write the slices strs[order[0]], strs[order[1]], ... joined with the given overlaps (default: the largest).
    Returns (word, list of the overlaps used)."""
    parts = [strs[order[0]]]
    used = []
    for t in range(1, len(order)):
        a, b = strs[order[t - 1]], strs[order[t]]
        k = max_overlap(a, b) if overlaps is None else overlaps[t - 1]
        if a[len(a) - k:] != b[:k]:
            raise ValueError("slices %d and %d do not overlap by %d letters" % (t - 1, t, k))
        used.append(k)
        parts.append(b[k:])
    return "".join(parts), used


# ---------------------------------------------------------------- checks of a word

def read_word(path):
    with open(path) as f:
        w = f.read().strip()
    bad = set(w) - set(ALPHABET)
    if bad:
        raise ValueError("%s: letters other than 0-7: %s" % (path, "".join(sorted(bad))[:20]))
    return w


def windows(w, n=8):
    """start positions of the windows of n letters that are permutations."""
    return [i for i in range(len(w) - n + 1) if len(set(w[i:i + n])) == n]


def check_word(w, deletions=True):
    """returns a dict: length, windows, distinct permutations, missing, and (deletions=True) the number of letters
    that can be deleted with every permutation still present."""
    n = 8
    pos = windows(w, n)
    count = {}
    for i in pos:
        p = w[i:i + n]
        count[p] = count.get(p, 0) + 1
    res = {"length": len(w), "windows": len(pos), "distinct": len(count), "missing": math.factorial(n) - len(count)}
    if deletions and res["missing"] == 0:
        isperm = [False] * len(w)
        for i in pos:
            isperm[i] = True
        deletable = 0
        for p in range(len(w)):
            lost = {}
            for i in range(max(0, p - n + 1), min(p, len(w) - n) + 1):
                if isperm[i]:
                    q = w[i:i + n]
                    lost[q] = lost.get(q, 0) + 1
            gone = {q for q, c in lost.items() if count[q] == c}
            if gone:
                v = w[max(0, p - n + 1):p] + w[p + 1:p + n]
                for i in range(len(v) - n + 1):
                    gone.discard(v[i:i + n])
            if not gone:
                deletable += 1
        res["deletable"] = deletable
    return res
