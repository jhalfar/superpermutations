#!/usr/bin/env python
"""gen12.py - selection with full and short rows -> completion -> base word, trail by trail; and the junction rules
of the base word, which geng.py imports from here (plain_vertex, clean_join, TOTXT).

Two uses.  geng.py is the generator for every selection in this package and uses this file as a module only.  Run as
a program, this file is the earlier generator for selections that have only full rows, short rows and loops without a
row.  On such a selection it writes the same base word as geng.py (compared on the n = 10 selection); in the table it
names a trail of a walk W<rows>.<short rows> where geng.py writes W<rows>.<Q>.

usage: gen12.py SEL OUT_BASE.txt [--table FILE] [--order small-first|file] [--maxrot M]

Input
  SEL    a selection on K + 1 symbols (K letters 0 .. K-1, distinguished letter K), one line per loop (Pantone's
         2-loop): "x type" with type F (full row), S (short row) or D (loop without a row, called detached in the
         messages of this program); or the older format "x followed by the distinguished letter", then
         full | short | detached.  The completion adds the letter z = K + 1; the word is on n = K + 2 symbols.

Output
  OUT_BASE.txt  the base word: every closed trail once, as one closed piece written from one of its vertices
                (R + h letters, h = n - 3).  Consecutive pieces overlap in the largest overlap of their h-words,
                which must be at most h - 1, and no permutation window may lie across a junction.  A trail is
                written from the first of its vertices that joins cleanly to the word so far; a trail with no such
                vertex waits until a later place fits.
  --table       one line per trail in the order written: kind, slices, R, offset of its piece in the word.

Nothing but the selection (one row per loop) and one trail at a time is held in memory.
Measured (one thread):  n = 10: 1 s, 0.03 GB.
"""
import argparse
import collections
import math
import sys
import time

ALPH = "0123456789ABCDEF"
TOTXT = bytes(ALPH.encode()) + bytes(range(16, 256))


def rot(x, j):
    j %= len(x)
    return x[j:] + x[:j]


def read_sel(path):
    """the rows of a selection as (x, s, v): x the ordering of the K letters, s = K the distinguished letter,
    v the number of cyclic classes (K full, K - 2 short, -1 = loop without a row)"""
    rows = []
    for line in open(path):
        if line.startswith("#") or not line.strip():
            continue
        p = line.split()
        x = tuple(ALPH.index(c) for c in p[0])
        ty = p[1]
        if ty in ("full", "short", "detached"):
            K = len(x) - 1
            assert x[-1] == K
            x = x[:K]
            ty = {"full": "F", "short": "S", "detached": "D"}[ty]
        K = len(x)
        rows.append((x, K, {"F": K, "S": K - 2, "D": -1}[ty]))
    return rows


def head(r):
    b, s, v = r
    return b[:len(b) - 2]


def tail(r):
    b, s, v = r
    return rot(b, v + 1)[:len(b) - 2]


def sel_walks(rows):
    """the closed walks of the rows: the row after a row is the one whose head is its tail"""
    by_head = {}
    for i, r in enumerate(rows):
        assert head(r) not in by_head, "a head word with out-degree > 1"
        by_head[head(r)] = i
    seen, out = bytearray(len(rows)), []
    for i in range(len(rows)):
        if seen[i]:
            continue
        w, j = [], i
        while not seen[j]:
            seen[j] = 1
            w.append(rows[j])
            j = by_head[tail(rows[j])]
        assert j == i, "selection is not a union of closed walks"
        out.append(w)
    return out


def ins(x, z, j):
    return x[:j] + (z,) + x[j:]


def port_path(r, z, j):
    """slices on n symbols that carry port j of the old slice r from its head to its tail (Pantone, section 3)"""
    b, s, v = r
    L = len(b)
    if v == L:                                   # full: K slices, port 0 takes two of them
        if j == 0:
            return [(ins(b, z, 0), s, L + 1), (ins(b, z, L - 1), s, L + 1)]
        return [(ins(b, z, j), s, L + 1)]
    if j < L - 2:                                # short: lifted slices, the last port also the two repair slices
        return [(ins(b, z, j), s, v + (1 if j < v else 0))]
    return [(ins(b, z, L - 2), s, v + (1 if L - 2 < v else 0)),
            (rot(b, L - 2) + (s,), z, L + 1), (rot(b, L - 1) + (s,), z, L + 1),
            (ins(b, z, L - 1), s, v + (1 if L - 1 < v else 0))]


def trails_of_walk(walk, z):
    """generator: the closed trails of the completion of one walk, each as a generator of slices"""
    K = len(walk[0][0])
    H = K - 1
    m = len(walk)
    step = [(H - 1 if r[2] == K else 1) for r in walk]
    done = bytearray(H)                          # ports seen at walk position 0
    for p0 in range(H):
        if done[p0]:
            continue
        labels = []
        i, p = 0, p0
        while True:
            if i == 0:
                done[p] = 1
            labels.append((i, p))
            p = (p + step[i]) % H
            i += 1
            if i == m:
                i = 0
            if i == 0 and p == p0:
                break
        yield [sl for (i, p) in labels for sl in port_path(walk[i], z, p)]


def spell(trail, n):
    """cyclic word (bytes, R letters) of a trail and the offsets of its slice starts"""
    h = n - 3
    parts = []
    offs = []
    off = 0
    prev_tail = None
    for (b, s, v) in trail:
        bb = bytes(b)
        if prev_tail is not None:
            assert bb[:h] == prev_tail, "tail / head mismatch"
        d = bb + bb
        sb = bytes((s,))
        offs.append(off)
        # the slice word is  b s b, then for t = 0..v-2: b[t] s rot(b, t+1);  the trail takes it without its last
        # h letters (they are the head of the next slice)
        w = [bb, sb, bb]
        for t in range(v - 1):
            w.append(d[t:t + 1])
            w.append(sb)
            w.append(d[t + 1:t + n])
        ws = b"".join(w)
        assert len(ws) == 2 * n - 1 + (v - 1) * (n + 1)
        prev_tail = ws[-h:]
        parts.append(ws[:-h])
        off += len(ws) - h
    c = b"".join(parts)
    assert c[:h] == prev_tail, "trail is not closed"
    return c, offs


def plain_vertex(c, r, n):
    """the step into offset r is a plain weight-3 step: the two cyclic windows before r are no permutations (at a
    vertex reached over a duplicated window the piece of R + h letters would lose that window)"""
    R = len(c)
    for q in (r - 1, r - 2):
        w = c[q:q + n] if 0 <= q and q + n <= R else bytes(c[(q + i) % R] for i in range(n))
        if len(set(w)) == n:
            return False
    return True


def clean_join(tailw, piece, n):
    """largest overlap k of the h-words; ok if k <= h - 1 and no permutation window lies across the junction"""
    h = n - 3
    e, s = tailw[-h:], piece[:h]
    k = 0
    for q in range(h, 0, -1):
        if e[-q:] == s[:q]:
            k = q
            break
    if k >= h:
        return k, False
    j = tailw[-(n - 1):] + piece[k:k + n - 1]
    lt = min(len(tailw), n - 1)
    for i in range(len(j) - n + 1):
        if i + n <= lt or i >= lt - k:
            continue
        if len(set(j[i:i + n])) == n:
            return k, False
    return k, True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sel")
    ap.add_argument("out")
    ap.add_argument("--table")
    ap.add_argument("--order", default="small-first")
    ap.add_argument("--maxrot", type=int, default=200)
    a = ap.parse_args()
    t0 = time.time()
    rows = read_sel(a.sel)
    K = len(rows[0][0])
    n = K + 2
    h = n - 3
    z = K + 1
    det = [r for r in rows if r[2] < 0]
    live = [r for r in rows if r[2] >= 0]
    walks = sel_walks(live)
    tshort = sum(1 for r in live if r[2] == K - 2)
    print("selection on %d symbols: %d loops, short %d, detached %d, walks %d (%.0fs)" % (
        K + 1, len(rows), tshort, len(det), len(walks), time.time() - t0), flush=True)

    def all_trails():
        """(kind, list of slices); small trails first"""
        if a.order == "small-first":
            for r in det:
                x, s = r[0], r[1]
                yield "D", [(rot(x, i) + (s,), z, K + 1) for i in range(K)]
            order = sorted(range(len(walks)), key=lambda i: len(walks[i]))
        else:
            order = range(len(walks))
        for wi in order:
            w = walks[wi]
            tt = sum(1 for r in w if r[2] == K - 2)
            kind = "W%d.%d" % (len(w), tt)
            for tr in trails_of_walk(w, z):
                yield kind, tr
        if a.order != "small-first":
            for r in det:
                x, s = r[0], r[1]
                yield "D", [(rot(x, i) + (s,), z, K + 1) for i in range(K)]

    fo = open(a.out, "wb")
    ft = open(a.table, "w") if a.table else None
    total = 0
    tailw = b""
    waiting = []                                  # (kind, nslices, cyclic word, offsets)
    ntr = nsl = sumR = 0
    kinds = collections.Counter()
    sizes = collections.Counter()
    maxwait = 0

    def try_write(kind, nslices, c, offs):
        nonlocal total, tailw
        R = len(c)
        cc = c + c[:n + h]
        for r in offs[:a.maxrot]:
            if not plain_vertex(c, r, n):
                continue
            if total == 0:
                k, ok = 0, True
            else:
                k, ok = clean_join(tailw, cc[r:r + n + h], n)
            if ok:
                piece = c[r:] + c[:r] + cc[r:r + h]
                fo.write(piece[k:].translate(TOTXT))
                if ft:
                    ft.write("%s\t%d\t%d\t%d\n" % (kind, nslices, R, total - k))
                total += len(piece) - k
                tailw = piece[-(n + h):]
                return True
        return False

    for kind, tr in all_trails():
        c, offs = spell(tr, n)
        ntr += 1
        nsl += len(tr)
        sumR += len(c)
        kinds[kind] += 1
        sizes[len(c)] += 1
        if not try_write(kind, len(tr), c, offs):
            waiting.append((kind, len(tr), c, offs))
            maxwait = max(maxwait, len(waiting))
        elif waiting:
            again = True
            while again and waiting:
                again = False
                for q in range(len(waiting)):
                    if try_write(*waiting[q]):
                        waiting.pop(q)
                        again = True
                        break
        if ntr % 1000 == 0:
            print("  trails %d, slices %d, letters %d, waiting %d (%.0fs)" % (ntr, nsl, total, len(waiting), time.time() - t0), flush=True)
    assert not waiting, "%d trails could not be placed" % len(waiting)
    fo.write(b"\n")
    fo.close()
    if ft:
        ft.close()
    F3 = math.factorial(n) + math.factorial(n - 1) + math.factorial(n - 2)
    visits = (sumR - nsl) // (n + 1)
    print("n = %d: trails %d, slices %d (= (n-2)! + %d), sum R %d = F3 + %d, class visits %d ((n-1)! = %d)" % (
        n, ntr, nsl, nsl - math.factorial(n - 2), sumR, sumR - F3, visits, math.factorial(n - 1)))
    print("base word %d letters -> %s; most trails waiting at once %d (%.0fs)" % (total, a.out, maxwait, time.time() - t0))
    small = sum(c for R, c in sizes.items() if R <= 3000)
    print("trails with R <= 3000: %d; larger: %d; R histogram (R: count), 12 most frequent: %s" % (
        small, ntr - small, sorted(sizes.items(), key=lambda kv: -kv[1])[:12]))
    print("largest R: %s" % sorted(sizes.items(), reverse=True)[:6])
    kk = collections.Counter()
    for kd, c in kinds.items():
        kk[kd] += c
    print("trails by walk (W loops.short, D = detached loop): %s" % sorted(kk.items(), key=lambda kv: -kv[1])[:14])


if __name__ == "__main__":
    main()
