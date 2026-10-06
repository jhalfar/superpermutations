"""sanity test of the search (e4) of check9m.py: the same search with single conditions dropped must find solutions.
usage: test_e4.py BASE"""
import itertools
import sys

src = open(__file__.replace("test_e4.py", "check9m.py")).read().split("# ------------------------------------------------------------------ (e4)")[0]
exec(src)
rows = []
for z in np.nonzero((nin > 0) & (nout > 0))[0].tolist():
    rows.append((int(ct[BC[Z[z]]]), eL[int(np.nonzero(tin[:, z])[0][0])], sL[int(np.nonzero(tout[z])[0][0])], int(BC[Z[z]])))
set_of_start = {c[0]: sets.index(c[2]) for c in chains}
set_of_end = {c[1]: sets.index(c[2]) for c in chains}
rot = {}
for c in chains:
    rot.setdefault(sets.index(c[2]), []).append((c[0], c[1]))
link = set()
for i, j in arcs[8].tolist():
    if i in set_of_end and j in set_of_start:
        link.add((i, j))
by_trail = {t: [i for i, s_ in enumerate(sets) if t in s_] for t in small_t}
covers = []


def cover(chosen, covered):
    rest = [t for t in small_t if t not in covered]
    if not rest:
        covers.append(tuple(chosen)); return
    t = min(rest, key=lambda x: sum(1 for i in by_trail[x] if not (sets[i] & covered)))
    for i in by_trail[t]:
        if not (sets[i] & covered):
            cover(chosen + [i], covered | sets[i])


cover([], frozenset())


def search(need_all_big=True, same_trail=True, min_size=None, links_free=False, max_links=99):
    sols = 0; cases = 0
    for cov in covers:
        Kc = len(cov)
        loc = {s_: i for i, s_ in enumerate(cov)}
        cand = [r for r in rows if set_of_end[r[1]] in loc and set_of_start[r[2]] in loc]
        lo = len(big_t) if min_size is None else min_size
        for size in range(lo, Kc):
            for U in itertools.combinations(cand, size):
                if need_all_big and len(set(r[0] for r in U)) < len(big_t):
                    continue
                tail, head = {}, {}
                good = True
                for r in U:
                    a, b = loc[set_of_end[r[1]]], loc[set_of_start[r[2]]]
                    if a in tail or b in head:
                        good = False; break
                    tail[a] = r; head[b] = r
                if not good:
                    continue
                opts = []
                for i, s_ in enumerate(cov):
                    opts.append([c for c in rot[s_] if (i not in tail or c[1] == tail[i][1]) and (i not in head or c[0] == head[i][2])])
                if any(not o for o in opts):
                    continue
                cases += 1
                reach = set((1 << i, i, c) for i in range(Kc) if i not in head for c in opts[i])
                for mask in range(1, 1 << Kc):
                    for i in range(Kc):
                        if not (mask >> i) & 1:
                            continue
                        for c in opts[i]:
                            if (mask, i, c) not in reach:
                                continue
                            for j in range(Kc):
                                if (mask >> j) & 1 or (i in tail) != (j in head):
                                    continue
                                for c2 in opts[j]:
                                    if i in tail:
                                        g = (tail[i][0] == head[j][0]) or not same_trail
                                    else:
                                        g = links_free or ((c[1], c2[0]) in link)
                                    if g:
                                        reach.add((mask | (1 << j), j, c2))
                if any(k[0] == (1 << Kc) - 1 and k[1] not in tail for k in reach):
                    sols += 1
    return cases, sols


say("as in check9m (e4):                                  cases %d, solvable %d" % search())
say("entry and exit of a block on any two big trails:     cases %d, solvable %d" % search(same_trail=False))
say("not every big trail needed (U of size >= 1):         cases %d, solvable %d" % search(need_all_big=False, min_size=1))
say("no big trail at all (U empty, 7 links W = 8):        cases %d, solvable %d" % search(need_all_big=False, min_size=0)[:2])
say("any link allowed between chains (W = 8 not needed):  cases %d, solvable %d" % search(links_free=True))
# how many links W = 8 between chains of one cover
tot = 0
for cov in covers[:3]:
    cs = [c for s_ in cov for c in rot[s_]]
    tot = sum(1 for a in cs for b in cs if (a[1], b[0]) in link)
    say("cover %s: pairs (chain, chain) with a W = 8 link: %d of %d" % (cov, tot, len(cs) ** 2))
