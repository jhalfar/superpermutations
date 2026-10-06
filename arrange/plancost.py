#!/usr/bin/env python
"""plancost.py - the length of a plan and what every kind of trail costs in it.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: plancost.py BASE.txt BASE.tsv PLAN

  BASE.txt  base word written by gen12.py, geng.py or gen13.py (mapped, not read into memory)
  BASE.tsv  its table: kind, slices, R, offset of the piece; trail t is line t
  PLAN      a plan on that base word

Read-only.  Nothing is loaded and no word is written: the plan is priced from the h-letter words at the two ends of
every event (h = n - 3), which are read from the base word.

Events of a plan:
  P k             piece k of the base word as it is written there
  O t start g g1  trail t cut at the window that starts at offset `start` of its piece; g is the weight of the step
                  that is cut (3: no cost, 2: one letter); g1 > 0 marks a cut that drops a repeated permutation
  S t st len      len letters of trail t from offset st (a trail written in several segments)
Cost of an event: its cut costs 3 - g letters.  Cost of a join: h minus the largest overlap of the last h letters of
one event with the first h letters of the next.  Every join is charged half to each of its two events.  A trail
written in m segments repeats h letters m - 1 times; these letters are counted as cost of the trail.  Then
    length = h + sum R + (cuts) + (joins) + (letters repeated by extra segments).

Prints: the number of events and trails, the length of the plan and its excess over h + sum R; the number of joins
of every cost; a table with one line per kind of trail (trails, cost, cost per trail), the kinds taken from the first
column of the table; and for the eight most frequent kinds the costs of the joins that follow an event of that kind.
The length printed here is the length of the word that the plan rebuilds to; for the start plans of n = 11 and
n = 12 I rebuilt the words and the lengths agree (43,931,105 and 522,739,939).

Kinds.  D is a small trail (printed as "detached", with its R).  W<loops>.<number> is a trail of a walk of the
selection with that many loops (the second number is the count of short rows for gen12.py and gen13.py, and Q of
the walk for geng.py).  Walks of at most 12 loops are listed one by one with R; walks of more than 100 loops are put
into three groups by their number of loops (101 to 300, 301 to 2000, more than 2000).

Needs: Python 3.  Time and memory, measured: below 1 s and 0.02 GB at n = 11 (800 events) and at n = 12 (3,648
events); 1 s and 0.05 GB at n = 13 (23,808 events).

Words.  In the names of the code an "opening" is a cut and a "detached" trail is a small trail.
"""
import collections
import mmap
import sys

ALPH = b"0123456789ABCDEF"


def main():
    basep, tsvp, planp = sys.argv[1:4]
    tab = [l.split("\t") for l in open(tsvp)]
    kind = [t[0] for t in tab]
    R = [int(t[2]) for t in tab]
    st = [int(t[3]) for t in tab]
    f = open(basep, "rb")
    W = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
    n = max(W[:4096]) - 48 + 1 if max(W[:4096]) < 65 else max(W[:4096]) - 55 + 1
    h = n - 3

    def cyc(t, pos, ln):
        """ln letters of trail t from offset pos, read around the closed trail"""
        pos %= R[t]
        a = st[t] + pos
        if pos + ln <= R[t]:
            return W[a:a + ln]
        return W[a:st[t] + R[t]] + W[st[t]:st[t] + ln - (R[t] - pos)]

    def label(t):
        """the name under which trail t is counted: its kind, with R for small trails and for walks of at most 12 loops"""
        k = kind[t]
        if k == "D":
            return "detached (R %d)" % R[t]
        m = int(k[1:].split(".")[0])
        if m <= 12:
            return "walk %s, R %d" % (k[1:], R[t])
        return "walk %s" % k[1:] if R[t] < 10 ** 9 else k

    # ---- events: (trail, first h letters, last h letters, cost of the cut or None for a segment, letters written)
    lines = open(planp).read().split("\n")
    hdr = lines[0].split()
    assert hdr[0] == "TRAILSEARCH-PLAN" and int(hdr[1]) == n
    ev = []
    for l in lines[1:]:
        p = l.split()
        if not p:
            continue
        if p[0] == "P":
            t = int(p[1])
            ev.append((t, cyc(t, 0, h), cyc(t, 0, h), 0, R[t] + h))
        elif p[0] == "O":
            # the piece starts at offset s0 and ends with the window that lies g letters before s0
            t, s0, g, g1 = int(p[1]), int(p[2]), int(p[3]), int(p[4])
            ev.append((t, cyc(t, s0, h), cyc(t, s0 - g + 3, h), 3 - g, R[t] + h + 3 - g))
        else:
            t, s0, ln = int(p[1]), int(p[2]), int(p[3])
            ev.append((t, cyc(t, s0, h), cyc(t, s0 + ln - h, h), None, ln))
    total = sum(e[4] for e in ev)
    cost = collections.defaultdict(float)
    cnt = collections.Counter()
    seglen = collections.Counter()
    nev = collections.Counter()
    joins = collections.Counter()
    jk = collections.defaultdict(collections.Counter)
    for i, (t, S, E, D, ln) in enumerate(ev):
        nev[t] += 1
        seglen[t] += ln
    # ---- joins: largest overlap of the end of an event with the start of the next, half the cost to each side
    for i in range(len(ev) - 1):
        e, s = ev[i][2], ev[i + 1][1]
        k = 0
        for q in range(h, 0, -1):
            if e[-q:] == s[:q]:
                k = q
                break
        d = h - k
        total -= k
        joins[d] += 1
        cost[ev[i][0]] += d / 2.0
        cost[ev[i + 1][0]] += d / 2.0
        jk[label(ev[i][0])][d] += 1
    for t in nev:
        cost[t] += seglen[t] - R[t] - h          # cost of the cut, and h letters more for every extra segment
    sumR = sum(R)
    print("plan %s: %d events, %d trails (%d in more than one event); length %d = h + sum R + %d" % (
        planp, len(ev), len(nev), sum(1 for t in nev if nev[t] > 1), total, total - h - sumR))
    print("joins by cost: %s" % dict(sorted(joins.items())))
    agg = collections.defaultdict(lambda: [0, 0.0])
    for t in nev:
        a = agg[label(t)]
        a[0] += 1
        a[1] += cost[t]
    # group the big walks
    grp = collections.defaultdict(lambda: [0, 0.0])
    for lab, (c, x) in agg.items():
        g = lab
        if lab.startswith("walk "):
            m = int(lab[5:].split(".")[0])
            if m > 2000:
                g = "trails of walks of more than 2000 loops"
            elif m > 300:
                g = "trails of walks of 301 to 2000 loops"
            elif m > 100:
                g = "trails of walks of 101 to 300 loops"
        grp[g][0] += c
        grp[g][1] += x
    tot = sum(x for c, x in grp.values())
    print("%-52s %7s %10s %8s" % ("kind", "trails", "cost", "per trail"))
    for g, (c, x) in sorted(grp.items(), key=lambda kv: -kv[1][0]):
        print("%-52s %7d %10.1f %8.3f" % (g, c, x, x / c))
    print("%-52s %7d %10.1f %8.3f   (half a join is missing at each end of the word)" % ("all", len(nev), tot,
        tot / len(nev)))
    print("outgoing joins by cost, per kind of the event before the join:")
    for lab in sorted(jk, key=lambda l: -sum(jk[l].values()))[:8]:
        print("   %-28s %s" % (lab, dict(sorted(jk[lab].items()))))


if __name__ == "__main__":
    main()
