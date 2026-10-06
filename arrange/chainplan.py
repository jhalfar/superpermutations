#!/usr/bin/env python
"""chainplan.py - the start plan of a piece set: the small trails written in chains.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: chainplan.py BASE.txt BASE.tsv DP.plan OUT.plan [--stats-only] [--time SEC]

  BASE.txt  base word written by gen12.py or geng.py: every closed trail once, as one piece
  BASE.tsv  its table, one line per trail in the order written: kind, slices, R, offset of the piece.  Trail t is
            line t.  Kind D marks a small trail: the closed trail that the completion makes of a loop without a row.
  DP.plan   any plan on BASE that writes every trail once (I use the plan of the fixed-order pass run on the base
            word as it is: recut BASE.txt OUT.txt --co-skip --time 0).  Only its header and its events of the other
            trails are used.
  OUT.plan  the chained plan: first the small trails, chain after chain, then the events of the other trails as in
            DP.plan, in the same order.

What it does.  A loop without a row is a cyclic order x of the K = n - 2 letters of the selection.  Its small trail
has K vertices, one per letter m of x: the word "x without m, read from the letter after m" (h = n - 3 letters), and
the trail can be cut there at no cost.  An F-orbit (c, m) is the K - 1 loops x_0 .. x_{K-2} that come from a cyclic
order c of the other K - 1 letters by putting m after c_j.  The trail of x_j cut at its vertex without m is the word
v_j = c_{j+1} c_{j+2} .. c_j, and v_{j+1} is v_j rotated by one letter.  So two loops that are consecutive in one
F-orbit join at cost 1 (overlap h - 1), each trail written once from that vertex.  A trail has one cut, so a chain of
three or more trails stays inside one F-orbit.  linkcheck.py confirms on all cuts, weight-2 steps included, that no
other pair of small trails joins at cost 1.

  1. Links.  All pairs (x_j, x_{j+1}) of loops without a row, in every F-orbit.
  2. Chains.  The largest set of links in which every loop uses links of one F-orbit only, and a whole orbit keeps
     at least one link unused (a chain is a path, not a ring).  This is an integer program, solved by Gurobi.  The
     number of links is exact when the status printed is 2 (optimal).  The number of units, chains and single
     trails together, is then the smallest possible: trails minus links.  The program prints that number as
     "chains"; the line after it gives the chains by length and the single trails.
  3. Order.  The chains and the single trails are the units.  After a unit that ends with the word E, the next
     unit is an unused one whose first word overlaps E most (overlaps h - 1 down to 3; a single trail may start at
     any of its K vertices); if nothing overlaps, the first unused unit.  This order is greedy, a heuristic.

What the output is good for.  The plan is a starting point for the local passes.  Its units are fewest possible;
its order of units and the cuts of the other trails are not optimised.  Which optimal set of links the solver
returns depends on the solver and its version, and the order of the units depends on that set, so another version
can give a plan of another length with the same number of units.  The lengths in the README are those of Gurobi
13.0.3 with two threads.

Prints the statistics of the links (how many neighbours a loop has, how long the runs of consecutive loops are in
the orbits), the number of links used with the solver's status and bound, the chain lengths, and the number of
events written.  The length of the plan is printed by plancost.py.

Needs: Python 3 and Gurobi (gurobipy) with a licence that allows the size of the model: one binary variable per
link and per (loop, orbit) pair that a link uses.  Measured: 3,500 variables and 3,272 constraints for the 672
small trails of the n = 11 piece set, 17,136 and 14,112 for the 2,352 small trails of the n = 12 piece set, 63,360
and 56,208 for a piece set with 8,448 small trails.  The licence that comes with the PyPI package stops at 2,000
variables, so it is too small for all of them.
Time and memory, measured (two threads): n = 11 below 1 s, 0.04 GB; n = 12 1 s, 0.06 GB.  The base word is mapped,
not read.

Words.  The text printed by the program and the names in the code use older words: a "detached loop" is a loop
without a row, an "opening" is a cut, a "slice" is one of the K equal parts of a small trail (it starts at a vertex).
"""
import argparse
import collections
import mmap
import sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("base")
    ap.add_argument("tsv")
    ap.add_argument("dpplan")
    ap.add_argument("out")
    ap.add_argument("--stats-only", action="store_true")
    ap.add_argument("--time", type=float, default=300)
    a = ap.parse_args()
    tab = [l.split("\t") for l in open(a.tsv)]
    kind = [t[0] for t in tab]
    R = [int(t[2]) for t in tab]
    st = [int(t[3]) for t in tab]
    f = open(a.base, "rb")
    W = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
    # n from the largest letter in the first 4096 letters of the word (letters are 0-9, A-F)
    mx = max(W[:4096])
    n = (mx - 48 if mx < 65 else mx - 55) + 1
    h = n - 3
    K = n - 2
    D = [t for t in range(len(tab)) if kind[t] == "D"]      # the small trails
    sl = R[D[0]] // K                      # letters per slice
    assert all(R[t] == sl * K for t in D)

    def canon(x):
        """the cyclic word x read from its smallest letter"""
        i = x.index(min(x))
        return x[i:] + x[:i]

    # ---- the loop of every small trail and the words of its K vertices.  The piece of a small trail starts at a
    # vertex, the other vertices follow at multiples of sl letters; the letter after the first h letters of the
    # piece is the letter that the first vertex leaves out.
    loop, verts = {}, {}
    for t in D:
        vs = [W[st[t] + sl * q:st[t] + sl * q + h] for q in range(K)]
        m0 = W[st[t] + h:st[t] + h + 1]
        x = canon(vs[0] + m0)
        assert len(set(x)) == K
        assert x not in loop
        loop[x] = t
        verts[t] = vs
    # ---- F-orbits: every loop lies in K of them, one for each of its letters taken as the mobile letter m
    orb = collections.defaultdict(dict)    # (m, c) -> {j: trail}
    where = collections.defaultdict(list)  # trail -> [(orbit key, j)]
    for x, t in loop.items():
        for i in range(K):
            m = x[i:i + 1]
            c = x[i + 1:] + x[:i]          # read from the letter after m
            cc = canon(c)
            # m sits after the last letter of c, i.e. after cc[j]
            j = cc.index(c[-1:])
            orb[m, cc][j] = t
            where[t].append(((m, cc), j))
    # ---- links, and the statistics that are printed
    nbr = collections.Counter()
    runs = collections.Counter()
    links = []                             # (orbit key, j): x_j and x_{j+1} both detached
    for key, d in orb.items():
        for j in d:
            if (j + 1) % (K - 1) in d:
                links.append((key, j))
        js = sorted(d)
        if len(js) == K - 1:
            runs["whole orbit"] += 1
        else:
            for j in js:
                if (j - 1) % (K - 1) not in d:
                    ln = 1
                    while (j + ln) % (K - 1) in d:
                        ln += 1
                    runs[ln] += 1
    deg = collections.Counter()
    for (key, j) in links:
        deg[orb[key][j]] += 1
        deg[orb[key][(j + 1) % (K - 1)]] += 1
    dd = collections.Counter(deg[t] // 2 for t in D)      # every neighbouring pair lies in two orbits
    print("detached loops %d; F-orbits that contain some: %d; neighbouring pairs %d" % (len(D), len(orb),
        len(links) // 2))
    print("number of detached neighbours of a detached loop (of %d possible): %s" % (K, dict(sorted(dd.items()))))
    print("runs of consecutive detached loops inside the F-orbits (length: count; every loop is counted in %d orbits): %s" % (
        K, dict(sorted(runs.items(), key=lambda kv: str(kv[0])))))
    # ---- largest set of links, one orbit per loop.  p[link] = 1: the link is used; u[trail, orbit] = 1: the trail
    # is cut at its vertex of that orbit.  A link needs both its trails cut in its orbit; a trail has one cut; an
    # orbit of which all K - 1 loops are without a row keeps one link unused.
    import gurobipy as gp
    from gurobipy import GRB
    mdl = gp.Model("chains", env=gp.Env(params={"OutputFlag": 0}))
    mdl.Params.OutputFlag = 0
    mdl.Params.Threads = 2
    mdl.Params.TimeLimit = a.time
    p = {lk: mdl.addVar(vtype=GRB.BINARY, obj=-1.0) for lk in links}
    u = {}
    for (key, j) in links:
        for t in (orb[key][j], orb[key][(j + 1) % (K - 1)]):
            if (t, key) not in u:
                u[t, key] = mdl.addVar(vtype=GRB.BINARY)
            mdl.addConstr(p[key, j] <= u[t, key])
    byt = collections.defaultdict(list)
    for (t, key), v in u.items():
        byt[t].append(v)
    for t, vs in byt.items():
        if len(vs) > 1:
            mdl.addConstr(gp.quicksum(vs) <= 1)
    for key, d in orb.items():
        if len(d) == K - 1:
            mdl.addConstr(gp.quicksum(p[key, j] for j in range(K - 1)) <= K - 2)
    mdl.optimize()
    used = [lk for lk in links if p[lk].X > 0.5]
    print("largest set of cost-1 links with one F-orbit per loop: %d (status %d, bound %.0f) -> %d chains for %d trails" % (
        len(used), mdl.Status, -mdl.ObjBound, len(D) - len(used), len(D)))
    # ---- chains: in every orbit the maximal runs of used links; every trail of a chain is cut at its vertex
    # without the mobile letter of the orbit
    byo = collections.defaultdict(set)
    for (key, j) in used:
        byo[key].add(j)
    chains = []                            # list of [(trail, vertex index q)]
    inchain = set()
    for key, js in byo.items():
        d = orb[key]
        m = key[0]
        for j in sorted(js):
            if (j - 1) % (K - 1) in js:
                continue
            ch = [j]
            while ch[-1] in js:
                ch.append((ch[-1] + 1) % (K - 1))
            ev = []
            for jj in ch:
                t = d[jj]
                q = [i for i in range(K) if m not in verts[t][i]]
                assert len(q) == 1
                ev.append((t, q[0]))
                inchain.add(t)
            for (t1, q1), (t2, q2) in zip(ev, ev[1:]):
                assert verts[t1][q1][1:] == verts[t2][q2][:h - 1]      # the join of cost 1
            chains.append(ev)
    singles = [t for t in D if t not in inchain]
    print("chain lengths (length: count): %s; single trails %d" % (
        dict(sorted(collections.Counter(len(c) for c in chains).items())), len(singles)))
    if a.stats_only:
        return
    # ---- greedy order of the units by overlap.  A piece cut at a vertex starts and ends with the word of that
    # vertex, so the last word of a unit is the vertex word of its last trail.
    units = chains + [[(t, None)] for t in singles]
    heads = collections.defaultdict(list)  # prefix -> [(unit, q)]
    for ui, un in enumerate(units):
        t, q = un[0]
        for qq in ([q] if q is not None else range(K)):
            w = verts[t][qq]
            for k in range(h - 1, 2, -1):
                heads[w[:k]].append((ui, qq))
    done = bytearray(len(units))
    seq = []
    cur = 0
    q0 = units[0][0][1] if units[0][0][1] is not None else 0
    left = len(units)
    ptr = 0
    while True:
        done[cur] = 1
        left -= 1
        un = units[cur]
        if un[0][1] is None:
            un = [(un[0][0], q0)]
        seq += un
        if not left:
            break
        E = verts[un[-1][0]][un[-1][1]]
        nx = None
        for k in range(h - 1, 2, -1):
            for (ui, qq) in heads.get(E[-k:], ()):
                if not done[ui]:
                    nx = (ui, qq)
                    break
            if nx:
                break
        if nx is None:
            while done[ptr]:
                ptr += 1
            nx = (ptr, units[ptr][0][1] if units[ptr][0][1] is not None else 0)
        cur, q0 = nx
    assert len(seq) == len(D) and len({t for t, q in seq}) == len(D)
    # ---- the plan: the small trails in this order, each cut at a vertex (weight-3 step, nothing dropped), then
    # the events of DP.plan that are not small trails
    lines = open(a.dpplan).read().split("\n")
    hdr = lines[0].split()
    rest = []
    dset = set(D)
    for l in lines[1:]:
        pp = l.split()
        if pp and int(pp[1]) not in dset:
            rest.append(l)
    with open(a.out, "w", newline="\n") as fo:
        fo.write("TRAILSEARCH-PLAN %s %s %d\n" % (hdr[1], hdr[2], len(seq) + len(rest)))
        for t, q in seq:
            fo.write("O %d %d 3 0\n" % (t, sl * q))
        for l in rest:
            fo.write(l + "\n")
    print("wrote %s: %d events (%d detached trails in %d units, then %d events of %s)" % (a.out, len(seq) + len(rest),
        len(seq), len(units), len(rest), a.dpplan))


if __name__ == "__main__":
    main()
