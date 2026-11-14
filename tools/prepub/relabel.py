"""relabel.py BASE WORD [OUT]      (exit 1 if OUT is given and no map exists)
   relabel.py --back MAP REV IN OUT   (undo: IN in the base's labelling -> OUT in the word's labelling)
Is WORD made of the closed trails of BASE up to a relabelling of the letters (and reversal)?
Pieces are split at window gaps >= 4 (as trailsearch.c); a closed piece is a cyclic word of length R = len - h.
For every closed trail of WORD it looks for a base trail and a letter map that turns one into a rotation of the
other; it reports the map(s) consistent with all trails, and writes WORD under the map to OUT if one exists."""
import sys


def load(p):
    s = open(p).read().replace('\r', '').replace('\n', '')
    return [int(c, 16) for c in s]


def pieces(w, n):
    pos = []
    for i in range(len(w) - n + 1):
        if len(set(w[i:i + n])) == n:
            pos.append(i)
    out, st, prev = [], pos[0], pos[0]
    for p in pos[1:]:
        if p - prev >= 4:
            out.append((st, prev + n - st))
            st = p
        prev = p
    out.append((st, prev + n - st))
    return out


def closed_trails(w, n):
    h = n - 3
    tr, op = [], []
    for s, l in pieces(w, n):
        R = l - h
        if R > 2 * n and w[s + R:s + R + h] == w[s:s + h]:
            tr.append(tuple(w[s:s + R]))
        else:
            op.append((s, l))
    return tr, op


def find_map(a, b, n):
    """letter maps m with m(a) = a rotation of b (len equal)"""
    R = len(a)
    if R != len(b):
        return []
    res = []
    bb = b + b
    for r in range(R):
        m = [-1] * n
        inv = [-1] * n
        ok = True
        for i in range(R):
            x, y = a[i], bb[r + i]
            if m[x] < 0 and inv[y] < 0:
                m[x] = y
                inv[y] = x
            elif m[x] != y:
                ok = False
                break
        if ok:
            res.append(tuple(m))
    return res


def back(m, rev, src, dst):
    """undo the map: dst = word whose image (reversal rev, then letters m) is src"""
    s = load(src)
    inv = [0] * len(m)
    for a, b in enumerate(m):
        inv[b] = a
    w = [inv[c] for c in s]
    if rev:
        w = w[::-1]
    open(dst, 'w', newline='\n').write(''.join('0123456789ABCDEF'[c] for c in w) + '\n')


def main():
    if sys.argv[1] == '--back':  # relabel.py --back MAP(e.g. 03451267) REV(0/1) IN OUT
        back([int(c, 16) for c in sys.argv[2]], sys.argv[3] == '1', sys.argv[4], sys.argv[5])
        return
    base, word = load(sys.argv[1]), load(sys.argv[2])
    n = max(base) + 1
    bt, bo = closed_trails(base, n)
    wt, wo = closed_trails(word, n)
    print(f"base: {len(bt)} closed trails, lengths {sorted(len(t) for t in bt)}; open pieces {len(bo)}")
    print(f"word: {len(wt)} closed trails, lengths {sorted(len(t) for t in wt)}; open pieces {len(wo)} "
          f"(lengths {[l for _, l in wo]})")
    best = None
    for rev in (False, True):
        w2 = word[::-1] if rev else word
        wt2, _ = closed_trails(w2, n)
        cands = None
        # start from the longest word trail
        for t in sorted(wt2, key=len, reverse=True):
            ms = set()
            for b in bt:
                if len(b) == len(t):
                    ms.update(find_map(list(t), list(b), n))
            cands = ms if cands is None else cands & ms
            if not cands:
                break
        print(f"reversal {rev}: maps consistent with all word trails: {sorted(cands) if cands else 'none'}")
        if cands and best is None:
            best = (rev, sorted(cands)[0])
    if best and len(sys.argv) > 3:
        rev, m = best
        w2 = word[::-1] if rev else word
        open(sys.argv[3], 'w', newline='\n').write(''.join('0123456789ABCDEF'[m[c]] for c in w2) + '\n')
        print(f"wrote {sys.argv[3]} (reversal {rev}, map {m})")
        print(f"MAP {''.join('0123456789ABCDEF'[c] for c in m)} REV {int(rev)}")
    elif len(sys.argv) > 3:
        sys.exit(1)


main()
