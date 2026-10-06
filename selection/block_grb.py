"""block_grb.py - the block above a left-over loop, rows of any visible length, solutions invariant under a group.

The (m, r) block: the loops are the cyclic orders of K = m + r letters whose old letters 0 .. m-1 stand in the
cyclic order (0 1 .. m-1); the r added letters are called tokens in this program.  A row may not exchange two old
letters.  This program writes a row as (u, d): state u and deficit d = K - v (d = 0 full, d = 2 short, d = 3 ..
K-1 the other visible lengths; "no slice" in its output is a loop without a row).

Only solutions invariant under a group of relabellings are looked for, and the programme is written on the orbits:
    --sym old    rotation of the old letters (order m)        --sym tok    cyclic shift of the tokens (order r)
    --sym swap   exchange of the first two tokens             --sym none   no symmetry
    (several names separated by commas generate a larger group; it must act freely on the loops)
A SEGMENT (u, d, j) is a row with deficit d >= 2 at the state orbit u followed by j - 1 full rows.
    every loop orbit lies in exactly one segment or has no row;   segments chain (flow at every state orbit);
    minimise  Q + D  =  sum of the deficits + loops without a row.
With --links the objective is Q + D + P * (D - links): a link joins two loops without a row whose small trails
meet at one letter (a letter of one has stepped forward over its neighbour, not two old letters); a loop uses the
links of one moving letter only.  D - links counts the paths of small trails; in the quotient this count is an
upper limit of the true one.
After the optimum the solution pool is asked for ALL solutions within --slack of it (PoolSearchMode 2).  When the
solver ends with status optimal and the pool is not full, the list is complete, and the program says so.  Every
pool solution is then lifted to the block and measured exactly: its walks and their closed trails by the port rule
(gcore.py), the fewest paths of its small trails by a second integer programme (min_paths), and
    priced = Q + D + P * paths + sum over walks (wa + wb * closed trails).
The distinct profiles are printed, cheapest first, and the first --keep are written.

What it gave (each line is about the solutions invariant under the group named, and about nothing else):
    block    rows          invariant under      min Q + D   status                     options
    (7, 2)   all lengths   nothing required     49          optimal; 336 solutions     --sym none --slack 0
    (7, 2)   all lengths   rotation             56          optimal (56 = no rows)     --sym old --slack 0
    (7, 3)   full, short   rotation             308         optimal; 6 solutions       --sym old --maxd 2 --slack 0
    (7, 3)   all lengths   rotation             301         optimal; 12 solutions      --sym old --slack 0
    (7, 3)   all lengths   rotation x shift     336         optimal; 6 solutions       --sym old,tok --slack 0
    (7, 3)   all lengths   shift of the tokens  300 found   bound 258, not optimal     --sym tok --slack 0 --time 240
The first five lines are runs that end with status optimal and a complete list (seconds each).  The last line is
quoted from the log of a run of 240 s on three threads.  With --slack 28 the third line lists the 54 full / short
solutions with Q + D up to 336, in 5 profiles.
The block of the transportable 11-symbol selection (data/block_7_3_c.txt) is one of the 6 solutions with 308:
they all have Q 182, 126 loops without a row and three walks with one closed trail each.  The block of the
n = 12 selection (data/block_7_3_n12.txt) was the cheapest profile of
    python block_grb.py 7 3 --sym old --links --no6 --P 2.9 --slack 10 --pool 400 --time 300 --threads 3 --out X
which ended by the time limit: best found, not proved optimal (model objective 396 against a bound of 338).

usage:    python block_grb.py m r [--sym old] [--maxd D] [--slack S] [--pool N] [--time SEC] [--threads T]
                 [--seed S] [--cutoff C] [--start FILE] [--focus F] [--links] [--no6] [--lazywalks]
                 [--P 4] [--wa 2.6] [--wb 1.3] [--out PREFIX] [--keep 3] [--verbose]
          --maxd     largest deficit of a row (2 = full and short rows only)
          --slack    list all solutions within this much of the optimum (in units of Q + D of the whole block)
          --cutoff   only solutions with Q + D at most this
          --start    a block solution used as a start for the solver
          --no6      forbid the walks of six rows "short, full, short, full, short, full" of three adjacent tokens
          --lazywalks  price every closed walk inside the model by rows added during the search (worked with
                     the group of order 21; with the shift of the tokens alone it made the result worse)
inputs:   none (--start: a block solution).
outputs:  text; --out PREFIX: PREFIX_0.txt .. block solutions ("x T" lines with T = F, S, D or the number of
          visible classes; LF line ends).
needs:    Python 3, gcore.py, Gurobi with its Python package gurobipy.
          Gurobi needs a full licence: academic licences are free, and the size-limited licence that
          comes with the package is too small for these models.
cost:     measured here on two threads: (7, 2) --sym none --slack 0: 11 s; (7, 3) --sym old --slack 0: 12 s;
          (7, 3) --sym old --maxd 2 --slack 0: 1 s; all under 0.2 GB.  The run that found the block of n = 12
          logged 301 s and 1.0 GB.
"""
import argparse
import time
from collections import Counter

import gurobipy as gp
from gurobipy import GRB

from gcore import ALPH, canon, gstep, port, cycles_of, walks, block_loops
from gcore import read_gsel as read_xv


# ------------------------------------------------- the deficit notation of this program on top of gcore.py
def nxt(x, d):
    """The state after a row of deficit d at the state x (d = 0: full row): the step of gcore.py."""
    return gstep(x, len(x) - d)


def moved_pair(x, d):
    """The two letters that the step of a row (x, d) exchanges."""
    K = len(x)
    return x[K - d - 1], x[(K - d) % K]


def gwalks(sel):
    """The closed walks of a block solution  loop -> (x, d)  (d = K: no row), as lists of (x, d) in order."""
    K = len(next(iter(sel)))
    ws, chosen = walks({L: (x, K - d) for L, (x, d) in sel.items()})
    return [[(x, K - chosen[x]) for x in w] for w in ws]


def walk_trails(K, w):
    """Closed trails of the closed walk w (list of (x, d)) after completion: cycles of the port product."""
    P = list(range(K - 1))
    for (x, d) in w:
        q = port(K - d, K)
        P = [q[p] for p in P]
    return cycles_of(P)


def read_gsel(path):
    """Read a block solution as dict loop -> (x, d), d = K for a loop without a row."""
    sel = read_xv(path)
    K = len(next(iter(sel)))
    return {L: (x, K - v) for L, (x, v) in sel.items()}


def write_gsel(path, sel, comment=""):
    """Write a block solution  loop -> (x, d): "x T" per loop with T = F (full), S (short), D (no row) or the
    number of visible classes of a row of another length."""
    K = len(next(iter(sel)))
    with open(path, "w", newline="\n") as f:
        f.write("# selection on k = %d symbols (K = %d letters, distinguished letter %s): x T; T = F full, S short, D no slice, "
                "or the number v of visible classes of the slice S(x, s; v)\n" % (K + 1, K, ALPH[K]))
        for c in comment.split("\n"):
            if c:
                f.write("# " + c + "\n")
        for L in sorted(sel):
            x, d = sel[L]
            f.write("".join(ALPH[c] for c in x) + " " + ("F" if d == 0 else "S" if d == 2 else "D" if d == K else str(K - d)) + "\n")


def min_paths(dl, m_, K, tlimit=60):
    """The fewest paths of small trails of a block solution: (loops without a row) minus the largest number of
    links, by an integer programme.  dl = the loops without a row.  A link (L, c) joins L and the loop in which the
    letter c has stepped forward over its successor (not two old letters), when both have no row: their small
    trails then meet at one letter.  A loop uses the links of one moving letter only; a closed cycle of links (a
    whole orbit) loses one link.  Returns (paths, 1 if the solver proved it else 0)."""
    if not dl:
        return 0, 1
    dset = set(dl)
    mod = gp.Model()
    mod.Params.OutputFlag = 0
    mod.Params.Threads = 2
    mod.Params.TimeLimit = tlimit
    link, use = {}, {}
    for L in dl:
        for i, c in enumerate(L):
            j = (i + 1) % K
            if c < m_ and L[j] < m_:
                continue
            y = list(L)
            y[i], y[j] = y[j], y[i]
            M = canon(tuple(y))
            if M not in dset:
                continue
            p = mod.addVar(vtype=GRB.BINARY, obj=-1.0)
            link[L, c] = (p, M)
            for X in (L, M):
                if (X, c) not in use:
                    use[X, c] = mod.addVar(vtype=GRB.BINARY)
                mod.addConstr(p <= use[X, c])
    if not link:
        return len(dl), 1
    by = {}
    for (X, c), u in use.items():
        by.setdefault(X, []).append(u)
    for us in by.values():
        mod.addConstr(gp.quicksum(us) <= 1)
    seen = set()
    for (L, c) in list(link):
        if (L, c) in seen:
            continue
        orb, X = [], L
        while (X, c) in link and (X, c) not in seen:
            seen.add((X, c))
            orb.append((X, c))
            X = link[X, c][1]
        if X == L and len(orb) > 1:
            mod.addConstr(gp.quicksum(link[k_][0] for k_ in orb) <= len(orb) - 1)
    mod.optimize()
    nl = int(round(-mod.ObjVal))
    return len(dl) - nl, (1 if mod.Status == GRB.OPTIMAL else 0)


def main():
    """Build the model on the orbits, solve, read the pool, lift and measure every solution, print the profiles."""
    ap = argparse.ArgumentParser()
    ap.add_argument("m", type=int)
    ap.add_argument("r", type=int)
    ap.add_argument("--sym", default="old")
    ap.add_argument("--maxd", type=int, default=-1)
    ap.add_argument("--slack", type=float, default=0.0, help="in block units (Q + D)")
    ap.add_argument("--pool", type=int, default=2000)
    ap.add_argument("--time", type=float, default=600)
    ap.add_argument("--threads", type=int, default=2)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--P", type=float, default=4.0)
    ap.add_argument("--wa", type=float, default=2.6)
    ap.add_argument("--wb", type=float, default=1.3)
    ap.add_argument("--cutoff", type=float, default=-1, help="only solutions with Q + D at most this (block units)")
    ap.add_argument("--out")
    ap.add_argument("--keep", type=int, default=3)
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--start", help="a block solution (general format) used as MIP start")
    ap.add_argument("--focus", type=int, default=0)
    ap.add_argument("--links", action="store_true", help="objective Q + D + P * (D - links), links in the quotient")
    ap.add_argument("--no6", action="store_true", help="forbid the six-row walks of three adjacent tokens")
    ap.add_argument("--lazywalks", action="store_true", help="price every closed walk (wa + wb * trails) in the model, by lazy rows")
    a = ap.parse_args()
    m_, r = a.m, a.r
    K = m_ + r
    loops = block_loops(m_, r)
    lset = set(loops)
    # the group generated by the relabellings named in --sym, and the representatives of its orbits
    gens = []
    for name in [x for x in a.sym.split(",") if x]:
        if name == "old":
            gens.append(tuple([(i + 1) % m_ for i in range(m_)] + list(range(m_, K))))
        elif name == "tok":
            gens.append(tuple(list(range(m_)) + [m_ + (i + 1) % r for i in range(r)]))
        elif name == "swap":
            gens.append(tuple(list(range(m_)) + [m_ + 1, m_] + list(range(m_ + 2, K))))
    G = {tuple(range(K))}
    frontier = list(G)
    while frontier:
        nf = []
        for g in frontier:
            for h in gens:
                x = tuple(h[c] for c in g)
                if x not in G:
                    G.add(x)
                    nf.append(x)
        frontier = nf
    G = sorted(G)
    scale = len(G)
    rep_state = lambda x: min(tuple(g[c] for c in x) for g in G)
    rep_loop = lambda L: min(canon(tuple(g[c] for c in L)) for g in G)
    lorb = sorted({rep_loop(L) for L in loops})
    assert len(lorb) * scale == len(loops)
    states = [rep_state(A[rot:] + A[:rot]) for A in lorb for rot in range(K)]
    old = lambda c: c < m_
    maxd = a.maxd if a.maxd >= 0 else K - 1
    DS = [d for d in range(2, K) if d <= maxd]
    mod = gp.Model("block_grb")
    mod.Params.OutputFlag = 1 if a.verbose else 0
    mod.Params.Threads = a.threads
    mod.Params.Seed = a.seed
    mod.Params.TimeLimit = a.time
    # segment variables (u, d, j): a row of deficit d at the state orbit u, then j - 1 full rows
    sv = {}
    seg_end = {}
    cover = {A: [] for A in lorb}
    inflow = {v: [] for v in states}
    outflow = {v: [] for v in states}
    t0 = time.time()
    for u in states:
        for d in DS:
            p, q = moved_pair(u, d)
            if old(p) and old(q):
                continue
            x = nxt(u, d)
            sts = [u]
            orbs = [rep_loop(canon(u))]
            j = 1
            while True:
                # the segment with j rows ends here: the next segment starts at x
                e = rep_state(x)
                v = mod.addVar(vtype=GRB.BINARY, obj=float(d))
                sv[u, d, j] = (v, list(sts))
                seg_end[u, d, j] = e
                for A in orbs:
                    cover[A].append(v)
                outflow[u].append(v)
                inflow[e].append(v)
                # extend by a full row at x
                p, q = moved_pair(x, 0)
                A = rep_loop(canon(x))
                if (old(p) and old(q)) or A in orbs or j >= K - 1:
                    break
                sts.append(x)
                orbs.append(A)
                x = nxt(x, 0)
                j += 1
    # det[A]: the loop orbit A has no row
    det = {A: mod.addVar(vtype=GRB.BINARY, obj=1.0 + (a.P if a.links else 0.0)) for A in lorb}
    if a.links:
        # binary links in the quotient (invariant under the group, so the model's path count is an upper bound of the
        # exact one; every pool solution is priced again with the exact count)
        link, use = {}, {}
        outl = {A: [] for A in lorb}
        inl = {A: [] for A in lorb}
        for A in lorb:
            for i, c in enumerate(A):
                jj = (i + 1) % K
                if old(c) and old(A[jj]):
                    continue
                yy = list(A)
                yy[i], yy[jj] = yy[jj], yy[i]
                cy = canon(tuple(yy))
                B = rep_loop(cy)
                gB = next(g for g in G if canon(tuple(g[q] for q in cy)) == B)
                cB = gB[c]
                p = mod.addVar(vtype=GRB.BINARY, obj=-a.P)
                link[A, c] = (p, B, cB)
                outl[A].append(p)
                inl[B].append(p)
                for (X, cc) in ((A, c), (B, cB)):
                    if (X, cc) not in use:
                        use[X, cc] = mod.addVar(vtype=GRB.BINARY)
                    mod.addConstr(p <= use[X, cc])
        byl = {}
        for (X, cc), u_ in use.items():
            byl.setdefault(X, []).append(u_)
        for X, us in byl.items():
            mod.addConstr(gp.quicksum(us) <= det[X])
        for A in lorb:
            if outl[A]:
                mod.addConstr(gp.quicksum(outl[A]) <= det[A])
            if inl[A]:
                mod.addConstr(gp.quicksum(inl[A]) <= det[A])
        seenL = set()
        for (A, c) in list(link):
            if (A, c) in seenL:
                continue
            orb, X, cc = [], A, c
            while (X, cc) in link and (X, cc) not in seenL:
                seenL.add((X, cc))
                orb.append((X, cc))
                _p, X, cc = link[X, cc]
            if (X, cc) == (A, c):
                mod.addConstr(gp.quicksum(link[k_][0] for k_ in orb) <= len(orb) - 1)
    # optional: no closed walk of three segments "short, full" (six rows)
    if a.no6:
        n6 = 0
        for (u, d, j) in list(sv):
            if d != 2 or j != 2:
                continue
            e1 = rep_state(nxt(nxt(u, 2), 0))
            if (e1, 2, 2) not in sv:
                continue
            e2 = rep_state(nxt(nxt(e1, 2), 0))
            if (e2, 2, 2) not in sv or rep_state(nxt(nxt(e2, 2), 0)) != u:
                continue
            ks = {(u, 2, 2), (e1, 2, 2), (e2, 2, 2)}
            if u == min(u, e1, e2):
                mod.addConstr(gp.quicksum(sv[k_][0] for k_ in ks) <= len(ks) - 1)
                n6 += 1
        print("six-row walks (three short + three full) forbidden: %d" % n6, flush=True)
    # cover: every loop orbit in one segment or without a row.  Flow at every state orbit
    for A in lorb:
        mod.addConstr(gp.quicksum(cover[A]) + det[A] == 1)
    for v in states:
        if inflow[v] or outflow[v]:
            mod.addConstr(gp.quicksum(inflow[v]) == gp.quicksum(outflow[v]))
    if a.cutoff >= 0:
        mod.addConstr(gp.quicksum(float(k_[1]) * v for k_, (v, _s) in sv.items()) + gp.quicksum(det.values()) <= a.cutoff / scale + 1e-6)
    print("m = %d, r = %d, K = %d, group order %d: %d loop orbits, %d segments (deficits %s), built in %.0f s" % (
        m_, r, K, scale, len(lorb), len(sv), DS, time.time() - t0), flush=True)
    if a.start:
        st = read_gsel(a.start)
        on = set()
        for w in gwalks(st):
            ds = [d for x, d in w]
            i0 = next(i for i, d in enumerate(ds) if d)
            w = w[i0:] + w[:i0]
            i = 0
            while i < len(w):
                j = 1
                while i + j < len(w) and w[i + j][1] == 0:
                    j += 1
                on.add((rep_state(w[i][0]), w[i][1], j))
                i += j
        miss = [k_ for k_ in on if k_ not in sv]
        print("start: %d segments, %d not in the model" % (len(on), len(miss)), flush=True)
        for k_, (v, _s) in sv.items():
            v.Start = 1 if k_ in on else 0
        for A in lorb:
            det[A].Start = 1 if st[A][1] == K else 0
    # the solution pool: all solutions within --slack of the optimum
    mod.Params.MIPFocus = a.focus
    mod.Params.PoolSearchMode = 2
    mod.Params.PoolSolutions = a.pool
    mod.Params.PoolGapAbs = a.slack / scale + 1e-6
    mod.Params.PoolGap = 1e9
    if a.lazywalks:
        mod.Params.LazyConstraints = 1
        ZN = 4000
        zv = [mod.addVar(lb=0.0, obj=1.0) for _ in range(ZN)]
        seen_w = {}
        skeys = list(sv)
        svars = [sv[k_][0] for k_ in skeys]

        def cb(model, where):
            """for every new solution: find its closed walks in the quotient, price each walk not seen before
            exactly (lifted), and add the row that makes the model pay that price when the walk is chosen"""
            if where != GRB.Callback.MIPSOL:
                return
            vals = model.cbGetSolution(svars)
            on = {k_[0]: k_ for k_, x_ in zip(skeys, vals) if x_ > 0.5}
            done = set()
            for u0 in on:
                if u0 in done:
                    continue
                cyc, u = [], u0
                while u not in done:
                    done.add(u)
                    cyc.append(on[u])
                    u = seg_end[on[u]]
                key = frozenset(cyc)
                if key not in seen_w:
                    # lift: follow the actual states until the start state comes back
                    rows, x = [], u0
                    while True:
                        (_u, d_, j_) = on[rep_state(x)]
                        rows.append((x, d_))
                        x = nxt(x, d_)
                        for _ in range(j_ - 1):
                            rows.append((x, 0))
                            x = nxt(x, 0)
                        if x == u0:
                            break
                    nq = sum(k_[2] for k_ in cyc)
                    mlt = len(rows) // nq
                    g_ = walk_trails(K, rows)
                    price = (scale // mlt) * (a.wa + a.wb * g_) / scale          # per orbit
                    if len(seen_w) >= ZN:
                        continue
                    seen_w[key] = (len(seen_w), price)
                idx, price = seen_w[key]
                model.cbLazy(zv[idx] >= price * (gp.quicksum(sv[k_][0] for k_ in cyc) - (len(cyc) - 1)))
        mod.optimize(cb)
        print("lazy walk rows: %d distinct walks priced" % len(seen_w), flush=True)
    else:
        mod.optimize()
    if mod.SolCount == 0:
        print("no solution; status %d, bound %.2f (block units %.1f)" % (mod.Status, mod.ObjBound, mod.ObjBound * scale))
        return
    nsol = mod.SolCount
    print("status %d: optimum of the model objective = %.1f (bound %.1f) in block units; pool: %d solutions within %.0f (pool size %d) -> %s; %.0f s" % (
        mod.Status, mod.ObjVal * scale, mod.ObjBound * scale, nsol, a.slack, a.pool,
        "list COMPLETE" if (mod.Status == GRB.OPTIMAL and nsol < a.pool) else "list NOT proved complete", time.time() - t0), flush=True)
    # every pool solution is lifted to the block and measured exactly; equal measurements form a profile
    prof = {}
    cache = {}
    for kk in range(nsol):
        mod.Params.SolutionNumber = kk
        if mod.PoolObjVal > mod.ObjVal + a.slack / scale + 1e-6:
            continue
        mval = mod.PoolObjVal * scale
        sel = {}
        for (u, d, j), (v, sts) in sv.items():
            if v.Xn > 0.5:
                for i, x0 in enumerate(sts):
                    for g in G:
                        x = tuple(g[c] for c in x0)
                        assert canon(x) not in sel
                        sel[canon(x)] = (x, d if i == 0 else 0)
        dl = tuple(sorted(L for L in loops if L not in sel))
        for L in dl:
            sel[L] = (L, K)
        ws = gwalks(sel)
        Q = sum(d for (x, d) in sel.values() if d < K)
        if dl not in cache:
            cache[dl] = min_paths(list(dl), m_, K)
        paths, exact = cache[dl]
        wl = [(len(w), sum(d for x, d in w), walk_trails(K, w)) for w in ws]
        wp = sum(a.wa + a.wb * g_ for (_l, _q, g_) in wl)
        tr = sum(g_ for (_l, _q, g_) in wl)
        priced = Q + len(dl) + a.P * paths + wp
        dd = tuple(sorted(Counter(d for (x, d) in sel.values()).items()))
        key = (round(priced, 1), Q, len(dl), paths, exact, tr, tuple(sorted(wl, reverse=True)), dd)
        prof.setdefault(key, []).append(sel)
        if a.links:
            assert mval >= Q + len(dl) + a.P * paths - 1e-4, "the model value is below the exact one"
    print("%d distinct profiles.  priced = Q + D + %.1f * paths + walks (%.1f + %.1f per trail).  Columns: priced | Q | D | paths | "
          "walk trails | floor Q + D + trails | walks (loops, Q, trails) | rows by deficit | count" % (len(prof), a.P, a.wa, a.wb))
    for i, key in enumerate(sorted(prof)[:40]):
        priced, Q, nd, paths, exact, tr, wl, dd = key
        print("  %6.1f | %3d | %3d | %2d%s | %2d | %3d | %s | %s | x %d" % (
            priced, Q, nd, paths, "" if exact else "?", tr, Q + nd + tr, list(wl)[:6], dict(dd), len(prof[key])))
        if a.out and i < a.keep:
            write_gsel("%s_%d.txt" % (a.out, i), prof[key][0],
                       "block_grb.py m=%d r=%d sym=%s: priced(P=%.1f) %.1f, Q %d, loops without slice %d in %d paths, walks %s" % (
                           m_, r, a.sym, a.P, priced, Q, nd, paths, list(wl)))


if __name__ == "__main__":
    main()
