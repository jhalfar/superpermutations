#!/usr/bin/env python
"""geng.py - selection with rows of any length -> check, completion, closed trails, base word.

usage: geng.py SEL [OUT_BASE.txt] [--table TSV] [--noliteral] [--maxrot M]

Input
  SEL    a selection on K + 1 symbols: K letters 0 .. K-1 and the distinguished letter s = K.  One line per loop
         (Pantone's 2-loop: a cyclic order of the K letters), "x v":
           x   the ordering of the K letters at which the row of the loop starts.  A row is the slice the selection
               takes from the loop, Pantone's S(x, s; v).
           v   the number of cyclic classes of the row: K full, K - 2 short, 1 .. K - 3 a row of another length,
               0 = loop without a row (a left-over loop; x is then the rotation that starts with 0).
         F / S / D are accepted for K / K - 2 / 0.  Lines that start with # are comments.
         The completion adds the letter z = K + 1; the word is on n = K + 2 symbols, written 0-9 then A-F.
         Trails are joined on words of h = n - 3 = K - 1 letters.

Output
  OUT_BASE.txt  the base word: every closed trail once, as one piece written from one of its vertices, R + h
                letters (R = length of the cyclic word of the trail).  It is a superpermutation, not a short one.
  TSV           one line per trail in the order written: kind, number of slices, R, offset of its piece in the
                base word.  kind D = the trail of a loop without a row, W<rows>.<Q> = a trail of a closed walk with
                that many rows and that Q.  A plan names the trails by their line number in this table (from 0).
  stdout        the checks below and the counts.

What is checked and how
  loops      every cyclic order of the K letters occurs on exactly one line
  balance    for every row (x, v) the state G_v(x) = step(x, v) is the x of the line of its loop, and that line is
             a row; every row has exactly one predecessor.  The rows then fall into closed walks.
  slices     the completion of a row (x, v):
               inserted slices ( ins(x, z, j), s, v + [j < v] ), j = 0 .. K-1
               repair slices   ( rot(x, i) s, z, K + 1 ),        i = v .. K-1
             the completion of a loop without a row: its K repair slices (one closed trail by themselves)
  trails     (1) LITERAL: the graph "slice -> the slice whose head is its tail" is built from the slices alone;
                 every head must occur once and every tail must be a head; the closed trails are its cycles
             (2) PORT RULE: walk by walk, with port_path and port_perm below
             the two families must be equal as cyclic sequences of slices.  --noliteral does only (2): the literal
             graph holds one dictionary entry per slice (3.8 million at n = 12, 41.7 million at n = 13).
  counts     Q = sum of (K - v) over the rows, slices = K! + Q, sum R = F3(n) + Q with F3(n) = n! + (n-1)! + (n-2)!,
             class visits = (n-1)!
  That the base word contains every permutation is not checked here: run a checker on the word.

The base word is assembled with the junction rules of gen12.py (functions plain_vertex and clean_join): a trail is
written from the first of its slice heads (at most --maxrot of them are tried, default 300) that is a plain vertex
and joins cleanly to the word so far; a trail with no such head waits until a later place fits.

Measured (one thread):  n = 10: 1 s, 0.03 GB.   n = 11: 4 s, 0.10 GB.   n = 12: 40 to 60 s, 0.74 GB.
                        n = 13 with --noliteral: 3 to 7 minutes, 2.0 GB.
"""
import argparse
import collections
import math
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen12 as G          # only clean_join, plain_vertex, TOTXT (the junction rules of the base word)

ALPH = "0123456789ABCDEF"


def rot(b, j):
    j %= len(b)
    return b[j:] + b[:j]


def ins(x, z, j):
    """x with the letter z in front of x[j]"""
    return x[:j] + z + x[j:]


def step(x, v, K):
    """G_v(x): the state at which the row after the row (x, v) starts.  The letters at positions v - 1 and v are
    exchanged and the next row starts v + 1 places later (full row: v = K)."""
    if v == K:
        return x[1:K - 1] + x[0:1] + x[K - 1:K]
    return x[v + 1:] + x[:v - 1] + x[v:v + 1] + x[v - 1:v]


def slices_of_row(x, v, K, sb, zb):
    """the completion of the row (x, v): K inserted slices, then K - v repair slices.  A slice is (b, d, c): b an
    ordering of n - 1 letters, d its distinguished letter, c its number of cyclic classes."""
    out = [(ins(x, zb, j), sb, v + (1 if j < v else 0)) for j in range(K)]
    out += [(rot(x, i) + sb, zb, K + 1) for i in range(v, K)]
    return out


def head(sl, h):
    return sl[0][:h]


def tail(sl, h):
    return rot(sl[0], sl[2] + 1)[:h]


def port_path(x, v, j, K, sb, zb):
    """slices passed by a trail that enters the row (x, v) at port j (ports 0 .. K-2: the place of z in the head)"""
    def I(q):
        return (ins(x, zb, q), sb, v + (1 if q < v else 0))
    if v == K:
        return [I(0), I(K - 1)] if j == 0 else [I(j)]
    if j != v:
        return [I(j)]
    return [I(v)] + [(rot(x, i) + sb, zb, K + 1) for i in range(v, K)] + [I(K - 1)]


def port_perm(v, j, K):
    """the port at which a trail that entered the row (x, v) at port j enters the next row of the walk"""
    if v == K:
        return (j - 1) % (K - 1)
    if j < v:
        return j + K - v - 1
    if j == v:
        return K - v - 2
    return j - v - 1


def spell(trail, n):
    """the cyclic word of a closed trail (bytes, R letters) and the offsets at which its slices start.  The word of
    a slice (b, d, c) is  b d b, then for t = 0 .. c-2: b[t] d rot(b, t+1);  the trail takes it without its last h
    letters, which are the head of the next slice."""
    h = n - 3
    parts, offs = [], []
    off = 0
    prev = None
    for (b, d, c) in trail:
        if prev is not None:
            assert b[:h] == prev, "tail / head mismatch"
        dd = b + b
        w = [b, d, b]
        for t in range(c - 1):
            w.append(dd[t:t + 1])
            w.append(d)
            w.append(dd[t + 1:t + n])
        ws = b"".join(w)
        assert len(ws) == 2 * n - 1 + (c - 1) * (n + 1)
        prev = ws[-h:]
        offs.append(off)
        parts.append(ws[:-h])
        off += len(ws) - h
    cyc = b"".join(parts)
    assert cyc[:h] == prev, "trail is not closed"
    return cyc, offs


def canon_seq(seq):
    i = min(range(len(seq)), key=lambda q: seq[q])
    return tuple(seq[i:] + seq[:i])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sel")
    ap.add_argument("out", nargs="?")
    ap.add_argument("--table")
    ap.add_argument("--noliteral", action="store_true")
    ap.add_argument("--maxrot", type=int, default=300)
    a = ap.parse_args()
    t0 = time.time()
    rows = []
    for line in open(a.sel):
        if line.startswith("#") or not line.strip():
            continue
        p = line.split()
        x = bytes(ALPH.index(ch) for ch in p[0])
        K = len(x)
        if p[1] in ("full", "short", "detached"):          # an older format: x followed by s, then a word
            x = x[:-1]
            K = len(x)
            v = {"full": K, "short": K - 2, "detached": 0}[p[1]]
        else:
            v = {"F": K, "S": K - 2, "D": 0}[p[1]] if p[1] in ("F", "S", "D") else int(p[1])
        rows.append((x, v))
    K = len(rows[0][0])
    n, h = K + 2, K - 1
    sb, zb = bytes((K,)), bytes((K + 1,))
    assert all(len(x) == K and sorted(x) == list(range(K)) for x, v in rows), "a line is not an ordering of the K letters"
    assert all(0 <= v <= K and v != K - 1 for x, v in rows), "a visible length outside 0 .. K, or K - 1"

    def canon(x):
        i = x.index(0)
        return x[i:] + x[:i]

    # ---- loops: one line per cyclic order
    byloop = {}
    for x, v in rows:
        c = canon(x)
        assert c not in byloop, "a loop on two lines"
        byloop[c] = (x, v)
    nl = math.factorial(K - 1)
    print("K = %d (n = %d, h = %d): lines %d, distinct loops %d, (K-1)! = %d -> every loop exactly once: %s" % (
        K, n, h, len(rows), len(byloop), nl, len(byloop) == nl == len(rows)))
    vh = collections.Counter(v for x, v in rows)
    print("lines by visible length: %s" % dict(sorted(vh.items())))
    # ---- balance: the row after every row is the row of its loop
    bad = 0
    nxt = {}
    pred = collections.Counter()
    for x, v in rows:
        if v == 0:
            continue
        y = step(x, v, K)
        ly = byloop.get(canon(y))
        if ly is None or ly[0] != y or ly[1] == 0:
            bad += 1
        nxt[x] = y
        pred[y] += 1
    nrow = sum(1 for x, v in rows if v > 0)
    print("balance: rows %d, rows whose next state is not the row of its loop: %d, rows with a number of predecessors other than 1: %d" % (
        nrow, bad, sum(1 for x, v in rows if v > 0 and pred[x] != 1)))
    if bad:
        print("SELECTION DOES NOT CHECK")
        return 1
    # ---- the closed walks of rows
    vof = {x: v for x, v in rows}
    walks = []
    seen = set()
    for x0, v0 in rows:
        if v0 == 0 or x0 in seen:
            continue
        wk = []
        x = x0
        while x not in seen:
            seen.add(x)
            wk.append((x, vof[x]))
            x = nxt[x]
        assert x == x0
        walks.append(wk)
    Q = sum(K - v for x, v in rows if v > 0)
    F3 = math.factorial(n) + math.factorial(n - 1) + math.factorial(n - 2)
    wh = collections.Counter((len(wk), sum(K - v for x, v in wk)) for wk in walks)
    print("closed walks %d; (rows, Q of the walk) x count: %s" % (len(walks), sorted(wh.items(), reverse=True)[:30]))
    print("Q = %d; expected slices K! + Q = %d, sum R = F3 + Q = %d" % (Q, math.factorial(K) + Q, F3 + Q))
    # ---- (1) literal graph, from the slices alone: head -> tail
    import hashlib

    def fingerprint(heads):
        """a closed trail as the cyclic sequence of the heads of its slices, started at the smallest head"""
        i = min(range(len(heads)), key=lambda q: heads[q])
        return (len(heads), hashlib.blake2b(b"".join(heads[i:] + heads[:i]), digest_size=12).digest())

    litfp = None
    if not a.noliteral:
        nexthead = {}
        dup = 0
        for x, v in rows:
            sls = [(rot(x, i) + sb, zb, K + 1) for i in range(K)] if v == 0 else slices_of_row(x, v, K, sb, zb)
            for sl in sls:
                hd = sl[0][:h]
                if hd in nexthead:
                    dup += 1
                nexthead[hd] = tail(sl, h)
        nlit = len(nexthead)
        miss = sum(1 for t in nexthead.values() if t not in nexthead)
        print("literal graph: slices %d, heads used twice %d, tails that are no head %d" % (nlit + dup, dup, miss), flush=True)
        assert dup == 0 and miss == 0, "the slices do not form closed trails"
        litfp = collections.Counter()
        while nexthead:
            h0, t = nexthead.popitem()
            cyc = [h0]
            while t != h0:
                cyc.append(t)
                t = nexthead.pop(t)
            litfp[fingerprint(cyc)] += 1
        print("literal graph: closed trails %d (%.0fs)" % (sum(litfp.values()), time.time() - t0), flush=True)

    # ---- (2) port rule, trail by trail: first the loops without a row in the order of the file, then the walks,
    #          shortest first
    perwalk = collections.Counter()

    def port_trails():
        for x, v in rows:
            if v == 0:
                yield "D", [(rot(x, i) + sb, zb, K + 1) for i in range(K)]
        for wk in sorted(walks, key=len):
            m = len(wk)
            kind = "W%d.%d" % (m, sum(K - v for x, v in wk))
            done = bytearray(K - 1)                # ports already used at the first row of the walk
            cnt = 0
            for p0 in range(K - 1):
                if done[p0]:
                    continue
                sl = []
                i, p = 0, p0
                while True:
                    if i == 0:
                        done[p] = 1
                    x, v = wk[i]
                    sl += port_path(x, v, p, K, sb, zb)
                    p = port_perm(v, p, K)
                    i += 1
                    if i == m:
                        i = 0
                    if i == 0 and p == p0:
                        break
                yield kind, sl
                cnt += 1
            perwalk[kind, cnt] += 1

    # ---- words: every trail is spelled and written into the base word as one closed piece
    sumR = nsl = ntr = 0
    sizes = collections.Counter()
    kinds = collections.Counter()
    prtfp = collections.Counter()
    fo = open(a.out, "wb") if a.out else None
    ft = open(a.table, "w") if a.table else None
    total = 0
    tailw = b""
    waiting = []                                   # trails that had no fitting head yet

    def try_write(kind, nslices, c, offs):
        nonlocal total, tailw
        cc = c + c[:n + h]
        for r in offs[:a.maxrot]:
            if not G.plain_vertex(c, r, n):
                continue
            if total == 0:
                k, ok = 0, True
            else:
                k, ok = G.clean_join(tailw, cc[r:r + n + h], n)
            if ok:
                piece = c[r:] + c[:r] + cc[r:r + h]
                fo.write(piece[k:].translate(G.TOTXT))
                if ft:
                    ft.write("%s\t%d\t%d\t%d\n" % (kind, nslices, len(c), total - k))
                total += len(piece) - k
                tailw = piece[-(n + h):]
                return True
        return False

    for kind, sl in port_trails():
        ntr += 1
        nsl += len(sl)
        if litfp is not None:
            prtfp[fingerprint([q[0][:h] for q in sl])] += 1
        c, offs = spell(sl, n)
        assert len(c) == sum((n + 1) * q[2] + 1 for q in sl)
        sumR += len(c)
        sizes[len(c)] += 1
        kinds[kind] += 1
        if fo:
            if not try_write(kind, len(sl), c, offs):
                waiting.append((kind, len(sl), c, offs))
            elif waiting:
                again = True
                while again and waiting:
                    again = False
                    for q in range(len(waiting)):
                        if try_write(*waiting[q]):
                            waiting.pop(q)
                            again = True
                            break
    assert not waiting, "%d trails could not be placed" % len(waiting)
    if fo:
        fo.write(b"\n")
        fo.close()
    if ft:
        ft.close()
    print("port rule: trails %d (loops without a row %d, walk trails %d); slices %d" % (ntr, vh[0], ntr - vh[0], nsl))
    print("port rule: (walk kind, trails per walk) x walks: %s" % sorted(perwalk.items(), key=lambda kv: -kv[1])[:30])
    if litfp is not None:
        print("trails of the port rule equal the cycles of the literal graph (as cyclic sequences of slices): %s" % (litfp == prtfp))
        assert litfp == prtfp, "port rule and literal graph disagree"
        assert nsl == nlit
    visits = (sumR - nsl) // (n + 1)
    print("n = %d: trails %d, slices %d (= K! + %d), sum R %d = F3 + %d, class visits %d ((n-1)! = %d)" % (
        n, ntr, nsl, nsl - math.factorial(K), sumR, sumR - F3, visits, math.factorial(n - 1)))
    small = sum(c for kd, c in kinds.items() if kd == "D")
    print("trails by kind: %s" % sorted(kinds.items(), key=lambda kv: -kv[1])[:20])
    print("R histogram, most frequent: %s; largest: %s" % (sorted(sizes.items(), key=lambda kv: -kv[1])[:6], sorted(sizes.items(), reverse=True)[:4]))
    if fo:
        print("base word %d letters -> %s (%.0fs)" % (total, a.out, time.time() - t0))
    return 0


if __name__ == "__main__":
    sys.exit(main())
