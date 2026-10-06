"""gblock.py - the block above a left-over loop as an integer programme, rows of any visible length, no symmetry.

The (m, r) block: the loops are the cyclic orders of K = m + r letters whose old letters 0 .. m-1 stand in the
cyclic order (0 1 .. m-1); a row may not exchange two old letters, so every walk stays inside the block.  This is
the closed sub-problem above one loop without a row of a selection on m letters, after r letters have been added.

    variables   y[x, v] = 1: the loop of the state x has the row (x, v)        (all K rotations x, all v)
                det[L]  = 1: the loop L has no row
                link    = 1: two loops without a row that follow each other in the F-orbit of an added letter
                             (their small trails join at one letter) are put into the same chain;
                             a loop uses the orbit of one added letter only, a whole orbit loses one link
    cover       every loop: exactly one row or no row;     flow: a row leads to a state that carries a row
    no walk of full rows only (it costs what its loops cost without rows)
    minimise    Q + cD * D + cC * (chains of loops without a row),   Q = sum of (K - v),  D = loops without a row,
                chains = D - links

The solution pool is asked for all solutions within --gap of the optimum.  Every pool solution is then measured
exactly: the closed trails of each of its walks by the port rule (gcore.py), and
    priced = Q + D + cC * chains + cW * (walk trails).
The first solution in the order of (priced, Q, D, chains, walk trails, walks) is written to --out.

Results for the (7, 2) block of n = 11 (56 loops; every line "optimal" by the solver, status 2):
    cC = 0:           Q + D = 49      (56 = no rows at all is the optimum when only full and short rows are allowed)
    cC = 1:           55              (Q 29, 22 loops without a row in 4 chains)
    cC = 2, 2.6, 3:   Q 38, 14 loops without a row in 3 chains, one walk of 42 rows with 2 closed trails;
                      this is the block of the n = 11 selection (data/block_7_2_n11.txt), and the command
                          python gblock.py 7 2 --cC 2 --pool 3000 --gap 1.01 --time 200 --threads 1 --out FILE
                      writes that file again, byte for byte (objective 58, bound 58; 20 s on one thread here).

usage:    python gblock.py m r [--cD 1] [--cC 0] [--cW 1] [--maxD n] [--minD n] [--maxQ n] [--vset 9,7,..]
                           [--whole] [--time SEC] [--pool P] [--gap G] [--threads T] [--seed S] [--list N]
                           [--out FILE] [--verbose]
          --vset   the visible lengths that are allowed (default K and K-2 .. 1)
          --whole  loops without a row only in whole F-orbits of the last added letter
          --list   how many distinct pool solutions are printed
inputs:   none.
outputs:  text: status, objective and bound of the solver, then the distinct pool solutions with their exact
          numbers; --out FILE: the first one as a block solution ("x v" lines, LF line ends).
needs:    Python 3, gcore.py, Gurobi with its Python package gurobipy.
          Gurobi needs a full licence: academic licences are free, and the size-limited licence that
          comes with the package is too small for these models.
cost:     measured here: (7, 2), 1,680 row variables: 20 s on one thread, 0.05 GB.  For the (7, 3) block (504
          loops) there is block_grb.py, for the (7, 4) block gsegip.py.
"""
import argparse
import time

import gurobipy as gp
from gurobipy import GRB

from gcore import ALPH, canon, gstep, port, cycles_of, block_loops


def evaluate(K, rows):
    """The closed walks of a pool solution, measured exactly.  rows: dict state -> v of its rows.  Returns one
    triple (number of rows, Q of the walk, closed trails after completion by the port rule) per walk, largest
    first.  Fails when the rows are not closed under the step."""
    seen = set()
    out = []
    for x0 in rows:
        if x0 in seen:
            continue
        p = list(range(K - 1))
        x = x0
        n = q_ = 0
        while x not in seen:
            seen.add(x)
            v = rows[x]
            pv = port(v, K)
            p = [pv[j] for j in p]
            n += 1
            q_ += K - v
            x = gstep(x, v)
            assert x in rows, "not closed"
        assert x == x0
        out.append((n, q_, cycles_of(p)))
    return sorted(out, reverse=True)


def main():
    """Build the model, solve it with a solution pool, measure every pool solution, print and write the best."""
    ap = argparse.ArgumentParser()
    ap.add_argument("m", type=int)
    ap.add_argument("r", type=int)
    ap.add_argument("--cD", type=float, default=1.0)
    ap.add_argument("--cC", type=float, default=0.0)
    ap.add_argument("--cW", type=float, default=1.0)
    ap.add_argument("--maxD", type=int, default=-1)
    ap.add_argument("--minD", type=int, default=-1)
    ap.add_argument("--maxQ", type=int, default=-1)
    ap.add_argument("--time", type=float, default=120)
    ap.add_argument("--pool", type=int, default=200)
    ap.add_argument("--gap", type=float, default=0.0)
    ap.add_argument("--vset", default="")
    ap.add_argument("--threads", type=int, default=2)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--list", type=int, default=12)
    ap.add_argument("--out")
    ap.add_argument("--whole", action="store_true", help="loops without a row only in whole F-orbits of an added letter")
    ap.add_argument("--verbose", action="store_true")
    a = ap.parse_args()
    m_, r = a.m, a.r
    K = m_ + r
    VS = [int(s) for s in a.vset.split(",")] if a.vset else [K] + list(range(K - 2, 0, -1))
    loops = block_loops(m_, r)
    LS = set(loops)
    t0 = time.time()
    mod = gp.Model("gblock")
    mod.Params.OutputFlag = 1 if a.verbose else 0
    mod.Params.TimeLimit = a.time
    mod.Params.Threads = a.threads
    mod.Params.Seed = a.seed
    # variables y[x, v]: a row of every length v at every state x of every loop, when its step stays in the block
    yv = {}
    cover = {L: [] for L in loops}
    inflow, outflow = {}, {}
    for L in loops:
        for rr in range(K):
            x = L[rr:] + L[:rr]
            for v in VS:
                s = gstep(x, v)
                if canon(s) not in LS:
                    continue
                var = mod.addVar(vtype=GRB.BINARY)
                yv[x, v] = var
                cover[L].append(var)
                outflow.setdefault(x, []).append(var)
                inflow.setdefault(s, []).append(var)
    # det[L]: the loop has no row.  Cover: one row or none per loop.  Flow: a row leads to a state that carries a row
    det = {L: mod.addVar(vtype=GRB.BINARY) for L in loops}
    for L in loops:
        mod.addConstr(gp.quicksum(cover[L]) + det[L] == 1)
        for rr in range(K):
            x = L[rr:] + L[:rr]
            mod.addConstr(gp.quicksum(inflow.get(x, [])) == gp.quicksum(outflow.get(x, [])))
    done = set()
    for L in loops:                                   # no closed walk of full rows only
        for rr in range(K):
            x = L[rr:] + L[:rr]
            if x in done:
                continue
            orb = [x]
            y = gstep(x, K)
            while y != x:
                orb.append(y)
                y = gstep(y, K)
            done.update(orb)
            if all((o, K) in yv for o in orb):
                mod.addConstr(gp.quicksum(yv[o, K] for o in orb) <= len(orb) - 1)
    # F-orbits of the added letters: lists of loops in gap order
    orbits = []
    for t in range(m_, K):
        seen = set()
        for L in loops:
            if L in seen:
                continue
            i = L.index(t)
            x = L[i + 1:] + L[:i + 1]                 # t last: full steps move t through the gaps
            orb = []
            y = x
            while True:
                orb.append(canon(y))
                y = gstep(y, K)
                if y == x:
                    break
            seen.update(orb)
            orbits.append((t, orb))
    # links between loops without a row that follow each other in an orbit; a loop uses the orbit of one added letter
    link = {}
    use = {(L, t): mod.addVar(vtype=GRB.BINARY) for L in loops for t in range(m_, K)}
    for L in loops:
        mod.addConstr(gp.quicksum(use[L, t] for t in range(m_, K)) <= 1)
    for oi, (t, orb) in enumerate(orbits):
        n = len(orb)
        lv = []
        for i in range(n):
            A, B = orb[i], orb[(i + 1) % n]
            var = mod.addVar(vtype=GRB.BINARY)
            link[oi, i] = var
            lv.append(var)
            for X in (A, B):
                mod.addConstr(var <= det[X])
                mod.addConstr(var <= use[X, t])
        mod.addConstr(gp.quicksum(lv) <= n - 1)
        if a.whole and t == K - 1:
            for i in range(n - 1):
                mod.addConstr(det[orb[i]] == det[orb[i + 1]])
    # the objective, and the optional limits on D and Q
    Q = gp.quicksum((K - v) * var for (x, v), var in yv.items())
    D = gp.quicksum(det.values())
    NLk = gp.quicksum(link.values())
    if a.maxD >= 0:
        mod.addConstr(D <= a.maxD)
    if a.minD >= 0:
        mod.addConstr(D >= a.minD)
    if a.maxQ >= 0:
        mod.addConstr(Q <= a.maxQ)
    mod.setObjective(Q + a.cD * D + a.cC * (D - NLk), GRB.MINIMIZE)
    # the solution pool: all solutions within --gap of the optimum
    mod.Params.PoolSolutions = a.pool
    mod.Params.PoolSearchMode = 2
    mod.Params.PoolGap = 1e9
    mod.Params.PoolGapAbs = a.gap + 1e-6
    mod.optimize()
    print("m = %d, r = %d, K = %d: %d loops, %d arcs, rows %s; objective Q + %.2f D + %.2f chains" % (
        m_, r, K, len(loops), len(yv), VS, a.cD, a.cC))
    if mod.SolCount == 0:
        print("no solution, status", mod.Status)
        return
    print("status %d, objective %.2f, bound %.2f, %d pool solutions, %.0f s" % (
        mod.Status, mod.ObjVal, mod.ObjBound, mod.SolCount, time.time() - t0), flush=True)
    # every pool solution is measured exactly (closed trails by the port rule) and priced
    res = []
    for kk in range(mod.SolCount):
        mod.Params.SolutionNumber = kk
        rows = {x: v for (x, v), var in yv.items() if var.Xn > 0.5}
        nd = sum(1 for L in loops if det[L].Xn > 0.5)
        nl = sum(1 for var in link.values() if var.Xn > 0.5)
        ws = evaluate(K, rows)
        q_ = sum(w[1] for w in ws)
        tr = sum(w[2] for w in ws)
        priced = q_ + nd + a.cC * (nd - nl) + a.cW * tr
        res.append((priced, q_, nd, nd - nl, tr, tuple(ws), kk))
    res.sort()
    seenk = set()
    shown = 0
    for (priced, q_, nd, ch, tr, ws, kk) in res:
        key = (q_, nd, ch, ws)
        if key in seenk:
            continue
        seenk.add(key)
        print("   priced %.2f: Q %d, D %d in %d chains, walk trails %d, floor %d; walks (loops, Q, trails): %s" % (
            priced, q_, nd, ch, tr, q_ + nd + tr, list(ws)))
        shown += 1
        if shown >= a.list:
            break
    print("   distinct (Q, D, chains, walks) in the pool: %d" % len({(r_[1], r_[2], r_[3], r_[5]) for r_ in res}))
    if a.out:
        kk = res[0][6]
        mod.Params.SolutionNumber = kk
        sel = {L: (L, 0) for L in loops}
        for (x, v), var in yv.items():
            if var.Xn > 0.5:
                sel[canon(x)] = (x, v)
        with open(a.out, "w") as f:
            f.write("# block m = %d, r = %d (K = %d): x v ; gblock.py: priced %.2f, Q %d, D %d in %d chains, walk trails %d; walks %s\n" % (
                m_, r, K, res[0][0], res[0][1], res[0][2], res[0][3], res[0][4], list(res[0][5])))
            for L in loops:
                x, v = sel[L]
                f.write("".join(ALPH[c] for c in x) + " %d\n" % v)
        print("   wrote", a.out)


if __name__ == "__main__":
    main()
