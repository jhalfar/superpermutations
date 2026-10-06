#!/usr/bin/env python
"""applyplan.py - write the word of a plan.

usage: applyplan.py BASE.txt BASE.tsv PLAN OUT.txt

Input
  BASE.txt  a base word of geng.py (or gen12.py): every closed trail once, as one closed piece written from a vertex
  BASE.tsv  its table (--table): trail t = line t (from 0), columns kind, slices, R, offset of the piece
  PLAN      text.  First line "TRAILSEARCH-PLAN n baselen nevents"; then one event per line, in the order in which
            the pieces are written:
              P t             the piece of trail t as it stands in the base word (R + h letters, h = n - 3)
              O t start g g1  trail t cut open at offset `start` of its cyclic word and written as one piece of
                              R + n - g letters: the g - 1 cyclic windows before `start` are left out.  g = 3 is a
                              cut at a vertex (a weight-3 step, no cost), g = 2 a cut at a weight-2 step (one
                              letter more).  g1 > 0 marks a cut that leaves out a permutation which occurs a
                              second time elsewhere (the second number says where in the gap it lies).  Only t,
                              start and g are used here.
              S t st len      a segment: len letters of trail t from offset st (a trail written in two segments
                              has two S lines)
Output
  OUT.txt   the word, one line.  Consecutive events are joined with the largest overlap of at most h letters (the
            last k letters of one piece = the first k of the next).
  stdout    the number of events, the number of different trails used, the length.

The base word is mapped, not read into memory.  Nothing is searched: the program only writes what the plan says, so
its output has to be checked as a word (coverage of all permutations), which is done by separate programs.
The program asserts that the plan was made for this base word (baselen) and that the number of events is nevents.

Measured (one thread):  n = 10 and n = 11: below 1 s, 0.02 GB.   n = 12: 1 s, 0.02 GB (base word in the file cache).
                        n = 13: 16 s, 0.05 GB.
"""
import mmap
import sys


def main():
    basep, tsvp, planp, outp = sys.argv[1:5]
    tab = [l.split("\t") for l in open(tsvp)]
    R = [int(t[2]) for t in tab]
    st = [int(t[3]) for t in tab]
    f = open(basep, "rb")
    W = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
    lines = open(planp).read().split("\n")
    hdr = lines[0].split()
    assert hdr[0] == "TRAILSEARCH-PLAN"
    n = int(hdr[1])
    h = n - 3
    blen = int(hdr[2])
    assert blen == len(W) - (1 if W[len(W) - 1:len(W)] == b"\n" else 0), "plan is for another base word"

    def cyc(t, pos, ln):
        """ln letters of the cyclic word of trail t from offset pos"""
        r = R[t]
        pos %= r
        a = st[t]
        out = []
        while ln > 0:
            m = min(ln, r - pos)
            out.append(W[a + pos:a + pos + m])
            ln -= m
            pos = 0
        return b"".join(out)

    fo = open(outp, "wb")
    total = 0
    tail = b""
    nev = 0
    seen = bytearray(len(R))
    for l in lines[1:]:
        p = l.split()
        if not p:
            continue
        if p[0] == "P":
            t = int(p[1])
            piece = cyc(t, 0, R[t] + h)
        elif p[0] == "O":
            t, s0, g = int(p[1]), int(p[2]), int(p[3])
            piece = cyc(t, s0, R[t] + n - g)
        else:
            t, s0, ln = int(p[1]), int(p[2]), int(p[3])
            piece = cyc(t, s0, ln)
        seen[t] = 1
        k = 0
        if nev:                                    # the join: largest overlap with the end of the word so far
            for q in range(h, 0, -1):
                if tail[-q:] == piece[:q]:
                    k = q
                    break
        fo.write(piece[k:])
        total += len(piece) - k
        tail = piece[-h:]
        nev += 1
    fo.write(b"\n")
    fo.close()
    assert nev == int(hdr[3])
    print("wrote %s: %d events, %d of %d trails, length %d" % (outp, nev, sum(seen), len(R), total))


if __name__ == "__main__":
    main()
