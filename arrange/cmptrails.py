#!/usr/bin/env python
"""cmptrails.py - do two base words consist of the same closed trails?

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: cmptrails.py WORD_A.txt WORD_B.txt n

Each word is cut into pieces as the search programs cut a base word: a piece is a maximal run of permutation windows
at most 3 letters apart, and a piece whose first letters come again after R letters is a closed trail.  Pieces that
are not closed are chained by their end words (a trail written in several segments).  Every closed trail is then
turned into a canonical rotation of its cyclic word, and the two words are compared as multisets of these cyclic
words.  Where the trails start, how the pieces are ordered and how they overlap plays no part.

Prints for each word its letters, windows, closed trails, pieces that are not closed, sum R and the number of
distinct trails; then whether the two sets are identical.  If they are, a fingerprint of the set is printed
(SHA-256 over the sorted SHA-256 values of the canonical cyclic words); if not, the trails that only one word has,
by R.

I used it to compare the base word of a second generator with the base word of the first: for the n = 11 pieces
the two give the same 880 closed trails (the selection of the first n = 11 record on other pieces).

Needs: Python 3.  The word is scanned letter by letter in Python.  Time and memory, measured at n = 11
(two words of 44 million letters): 60 s and 1.90 GB; 4 s at n = 10.
"""
import collections
import hashlib
import sys

ALPH = "0123456789ABCDEF"
_FROMTXT = bytes((ALPH.index(chr(c)) if chr(c) in ALPH else 255) for c in range(256))


def parse_base(W, n):
    """the cutting of a base word: pieces = maximal runs of permutation windows with steps of at most 3 letters; a
    piece is a closed trail when its first h + ex letters come again after R letters (ex = 0, 1, 2: it was written
    from a cut at a step of weight 3, 2 or 1).  Returns (list of (start, length, R or 0), number of windows)."""
    h = n - 3
    L = len(W)
    cnt = [0] * 16
    distinct = 0
    pos = []
    for i in range(L):
        c = W[i]
        cnt[c] += 1
        if cnt[c] == 1:
            distinct += 1
        if i >= n:
            c = W[i - n]
            cnt[c] -= 1
            if cnt[c] == 0:
                distinct -= 1
        if i >= n - 1 and distinct == n:
            pos.append(i - n + 1)
    pcs = []
    st = pos[0]
    prev = pos[0]
    for p in pos[1:]:
        if p - prev >= 4:
            pcs.append((st, prev + n - st))
            st = p
        prev = p
    pcs.append((st, prev + n - st))
    out = []
    for s, l in pcs:
        cl = 0                           # cyclic length R if the piece is a whole trail (cut at gap 3, 2 or 1)
        for ex in (0, 1, 2):
            R = l - h - ex
            if R > 2 * n and W[s + R:s + R + h + ex] == W[s:s + h + ex]:
                cl = R
                break
        out.append((s, l, cl))
    return out, len(pos)


def canon(cyc, n):
    """canonical rotation of a cyclic word (bytes)"""
    b = bytes(cyc)
    d = b + b
    R = len(b)
    key = bytes(range(n))                 # rotations that start with the window 0 1 .. n-1 if there is one
    cands = []
    i = d.find(key)
    while 0 <= i < R:
        cands.append(i)
        i = d.find(key, i + 1)
    if not cands:
        best = min(d[i:i + n] for i in range(R))
        cands = [i for i in range(R) if d[i:i + n] == best]
    return min(d[i:i + R] for i in cands)


def trails_of_word(W, n):
    """canonical cyclic words of the closed pieces of a word; None entries for pieces that are not closed"""
    h = n - 3
    pcs, nw = parse_base(W, n)
    out = []
    opens = []
    for s, l, cl in pcs:
        if cl:
            out.append(canon(W[s:s + cl], n))
        else:
            opens.append((s, l))
    # open pieces: chains whose h-words match (a trail written in several segments)
    used = [False] * len(opens)
    for a in range(len(opens)):
        if used[a]:
            continue
        chain = [a]
        used[a] = True
        head = W[opens[a][0]:opens[a][0] + h]
        while True:
            s, l = opens[chain[-1]]
            tail = W[s + l - h:s + l]
            if tail == head:
                break
            nx = [b for b in range(len(opens)) if not used[b] and W[opens[b][0]:opens[b][0] + h] == tail]
            if not nx:
                chain = None
                break
            chain.append(nx[0])
            used[nx[0]] = True
        if chain is None:
            out.append(None)
            continue
        c = bytearray()
        for b in chain:
            s, l = opens[b]
            c += W[s:s + l - h]
        out.append(canon(c, n))
    return out, nw


def load_text(path):
    """the word in a file as letter values"""
    t = open(path, "rb").read().strip()
    return bytearray(t.translate(_FROMTXT))


a, b, n = sys.argv[1], sys.argv[2], int(sys.argv[3])
out = []
for path in (a, b):
    W = load_text(path)
    tr, nw = trails_of_word(W, n)
    op = sum(1 for t in tr if t is None)
    tr = [t for t in tr if t is not None]
    print("%s: %d letters, %d permutation windows, %d closed trails (%d pieces not closed), sum R %d, distinct %d" % (
        path, len(W), nw, len(tr), op, sum(len(t) for t in tr), len(set(tr))))
    out.append(tr)
A, B = collections.Counter(out[0]), collections.Counter(out[1])
print("identical as sets of cyclic words: %s" % (A == B))
if A != B:
    oa, ob = A - B, B - A
    print("only in the first: %d trails, R %s" % (sum(oa.values()),
        sorted(collections.Counter(len(t) for t in oa.elements()).items())[:20]))
    print("only in the second: %d trails, R %s" % (sum(ob.values()),
        sorted(collections.Counter(len(t) for t in ob.elements()).items())[:20]))
else:
    hsh = hashlib.sha256(b"\n".join(sorted(hashlib.sha256(t).hexdigest().encode() for t in A))).hexdigest()
    print("fingerprint of the trail set (sha256 over the sorted sha256 of the canonical cyclic words): %s" % hsh)
