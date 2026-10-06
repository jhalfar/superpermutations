"""gregion.py - connect the walk of a block to a big walk around it; assemble the n = 11 selection from connections.

After gapply.py every one of the 48 blocks of the 10-symbol selection has its own small walk (2 closed trails),
and each of the 14 big walks of Pantone's selection still gives 8 closed trails.  When a block is solved again
together with the loops around it, so that its rows lie on a big walk, that big walk comes out with 2 closed trails
instead of 8 and the block has no walk trail of its own.  A "connection" is the list of rows changed by one such
solution; connections are kept in JSON files:  {"blocks": [cyclic order D of each connected block],
"changes": [[old x, old v, new x, new v], ...]}.

  Assembly (no solver):
      python gregion.py multi BASE FALLBACK OUT CONN.json [CONN.json ...] --walks 0:0
    reads BASE as gapply.py does, applies the connections, puts the block solution FALLBACK above every other
    left-over loop, writes OUT, and counts the closed trails once more in the literal endpoint graph of the
    completion (the program fails unless that count and the number of slices agree with the port rule).
    The n = 11 selection is
      python gregion.py multi construction-input.txt data/block_7_2_n11.txt OUT \
             data/connect_n11_a.json data/connect_n11_b.json --walks 0:0
    (10 blocks connected, 38 with the plain block solution; 800 closed trails; 3 s, 0.2 GB).

  Search (integer programme, one per try):
      python gregion.py multi BASE FALLBACK UNUSED --fullring --walks 0:7 --json NEW.json [options]
    For every big walk in --walks the free blocks are sorted by the number of their neighbour loops that lie on
    that walk, and the first --tries of them are solved: region = the block and its ring (with --fullring all
    loops one exchange away from the block, otherwise only those on the walk).
        variables as in gblock.py for the loops of the region; the parts of walks outside the region are
        contracted into jumps (entry state, product of the port permutations, exit state) and stay fixed
        minimise   Q + D + cC * (chains of loops without a row inside the block)
        subject to Q + D of the region at most its present value + --gap, and at least one row that leads from
        the block into the ring or back (only through ring loops of the target walk)
    Pool solutions are measured exactly (port rule, jumps included) and priced
        (change of Q + D) + cC * chains + cB * (change of the trails of walks that leave the region)
                                        + cW * (trails of walks inside the region);
    the cheapest one that lowers the trails by at least 6 (--mintrail -6) is applied, and the next walk is
    solved on the changed selection.  With --json the changed rows are written as a connection and no selection.
    Options: --walks a:b or a list i,j,..   --tries N (4)   --skip N   --time SEC (120)   --threads T (1)
             --gap G (14)   --pool P (300)   --poolgap G (3)   --mintrail T (-6)   --good P (-0.5: stop trying
             blocks for this walk once a solution is priced at most P)   --cC 2.7 --cB 1.86 --cW 2.2   --m 7
             --pre A.json,B.json  apply these connections before searching.

  What is found and what is not: the two connection files of the n = 11 selection were found by an earlier state
  of this search, which took the blocks in a fixed stride instead of by neighbour count:
      ... --fullring --walks 0:7  --json a.json --time 240 --gap 8 --pool 60 --poolgap 2      (and --walks 7:14)
  The 10 connections together cost 86 more in Q than the plain block solution in those blocks, leave the number
  of loops without a row as it is, and save 80 closed trails.  Nothing here is proved optimal: only a few blocks
  were tried for each walk, and for four of the fourteen big walks no connection was found then.
  The search as it stands here does not find the two files again.  Run for the first big walk with the same
  limits (--walks 0:1 --tries 4; 5 minutes) it tried four blocks: two had no solution within the gap and two gave
  Q + D + 4 with 4 closed trails fewer, which --mintrail -6 does not accept.  So the two files are checked, not
  found again: the assembly counts the closed trails literally, and the three checkers pass on the result.

inputs:   BASE = construction-input.txt, FALLBACK = a (7, 2) block solution, connection files.
outputs:  OUT (selection, "x v" lines, LF) or the JSON file; text on standard output.
needs:    Python 3 and gcore.py; the search also needs Gurobi with its Python package gurobipy.
          Gurobi needs a full licence: academic licences are free, and the size-limited licence that
          comes with the package is too small for these models.
cost:     measured here: assembly 3 s, 0.2 GB.  Search: a region has 350 loops with --fullring; four tries
          for one walk took 5 minutes on one thread, 0.1 GB.
"""
import math
import sys
import time
from collections import defaultdict

from gcore import ALPH, canon, gstep, port, cycles_of, read_any, read_gsel, write_gsel, walks, exact, report, literal_trails


def arg(name, default, typ=str):
    """Value of the command-line option `name`, or the default."""
    return typ(sys.argv[sys.argv.index(name) + 1]) if name in sys.argv else default


def neighbours(L):
    """The K loops that differ from the loop L by the exchange of two cyclically adjacent letters."""
    K = len(L)
    out = []
    for i in range(K):
        y = list(L)
        j = (i + 1) % K
        y[i], y[j] = y[j], y[i]
        out.append(canon(tuple(y)))
    return out


def load_base(path):
    """Read the base selection and turn its walks of full rows only into loops without a row."""
    sel = read_any(path)
    K = len(next(iter(sel)))
    ws, chosen = walks(sel)
    for w in ws:
        if all(chosen[x] == K for x in w):
            for x in w:
                sel[canon(x)] = (canon(x), 0)
    return sel, K


def blocks_of(sel, m):
    """The blocks: loops without a row, grouped by the cyclic order of their old letters 0 .. m-1.
    Returns dict D -> list of loops, in increasing order of D."""
    bl = defaultdict(list)
    for L, (x, v) in sel.items():
        if v == 0:
            y = tuple(c for c in L if c < m)
            i = y.index(0)
            bl[y[i:] + y[:i]].append(L)
    return dict(sorted(bl.items()))


def txt(x):
    """A state or loop as text."""
    return "".join(ALPH[c] for c in x)


def solve_region(sel, K, m_, blockset, free, cC, cB, cW, cross, gap, tlim, threads, pool, poolgap, quiet=False, ring_ok=None):
    """Solve the loops of `free` again while the rest of the selection `sel` stays as it is.
    blockset = the loops of the block (chains of loops without a row are counted there), free = block + ring,
    cross = least number of rows that lead from the block out of it or back, ring_ok = the ring loops such rows
    may use, gap = how far Q + D of the region may rise, pool / poolgap = size and width of the solution pool.
    Walks that pass through the region are cut into the stretches inside and the stretches outside; an outside
    stretch becomes a jump (product of its port permutations, state where it comes back in) and is fixed.
    Returns the pool solutions, cheapest first, as (priced change, (change of Q + D, loops without a row, chains,
    change of the trails of walks that leave the region, trails of walks inside, inside walks as (rows, trails)),
    {loop: (x, v)} for all loops of `free`)."""
    import gurobipy as gp
    from gurobipy import GRB
    VS = [K] + list(range(K - 2, 0, -1))
    # the walks as they are: a walk outside the region is counted; any other is cut into its stretches
    # outside the region, which become jumps
    cur = exact(sel)
    ws, chosen = walks(sel)
    tr_fixed = 0
    jump = {}
    for w in ws:
        inside = [canon(x) in free for x in w]
        if not any(inside):
            p = list(range(K - 1))
            for x in w:
                q = port(chosen[x], K)
                p = [q[j] for j in p]
            tr_fixed += cycles_of(p)
            continue
        n = len(w)
        i0 = inside.index(True)
        i = 0
        while i < n:
            idx = (i0 + i) % n
            if inside[idx]:
                i += 1
                continue
            start = w[idx]
            p = list(range(K - 1))
            while not inside[(i0 + i) % n]:
                x = w[(i0 + i) % n]
                q = port(chosen[x], K)
                p = [q[j] for j in p]
                i += 1
            jump[start] = (tuple(p), w[(i0 + i) % n])
    # the programme on the loops of the region: rows y[x, v] whose step stays in the region or leads to the
    # start of a jump; det[L] = no row
    t0 = time.time()
    m = gp.Model()
    m.Params.OutputFlag = 0
    m.Params.TimeLimit = tlim
    m.Params.Threads = threads
    yv = {}
    cover = {L: [] for L in free}
    inflow, outflow = {}, {}
    for L in free:
        for r in range(K):
            x = L[r:] + L[:r]
            for v in VS:
                s = gstep(x, v)
                if canon(s) not in free and s not in jump:
                    continue
                var = m.addVar(vtype=GRB.BINARY)
                yv[x, v] = var
                cover[L].append(var)
                outflow.setdefault(x, []).append(var)
                inflow.setdefault(s, []).append(var)
    det = {L: m.addVar(vtype=GRB.BINARY) for L in free}
    for L in free:
        m.addConstr(gp.quicksum(cover[L]) + det[L] == 1)
    # flow: a state at which a jump comes back has one unit of inflow from outside; every jump is entered once
    ext_in = {nx for (p_, nx) in jump.values()}
    for L in free:
        for r in range(K):
            x = L[r:] + L[:r]
            m.addConstr(gp.quicksum(inflow.get(x, [])) + (1 if x in ext_in else 0) == gp.quicksum(outflow.get(x, [])))
    for s in jump:
        m.addConstr(gp.quicksum(inflow.get(s, [])) == 1)
    # no closed walk of full rows only
    done = set()
    for L in free:
        for r in range(K):
            x = L[r:] + L[:r]
            if x in done:
                continue
            orb = [x]
            y = gstep(x, K)
            while y != x:
                orb.append(y)
                y = gstep(y, K)
            done.update(orb)
            if all((o, K) in yv for o in orb):
                m.addConstr(gp.quicksum(yv[o, K] for o in orb) <= len(orb) - 1)
    # chains of loops without a row inside the block, as in gblock.py
    link = []
    use = {(L, t): m.addVar(vtype=GRB.BINARY) for L in blockset for t in range(m_, K)}
    for L in blockset:
        m.addConstr(gp.quicksum(use[L, t] for t in range(m_, K)) <= 1)
    for t in range(m_, K):
        seen = set()
        for L in sorted(blockset):
            if L in seen:
                continue
            i = L.index(t)
            x = L[i + 1:] + L[:i + 1]
            orb = []
            y = x
            while True:
                orb.append(canon(y))
                y = gstep(y, K)
                if y == x:
                    break
            seen.update(orb)
            lv = []
            for i in range(len(orb)):
                A, B = orb[i], orb[(i + 1) % len(orb)]
                var = m.addVar(vtype=GRB.BINARY)
                lv.append(var)
                for X in (A, B):
                    m.addConstr(var <= det[X])
                    m.addConstr(var <= use[X, t])
            m.addConstr(gp.quicksum(lv) <= len(orb) - 1)
            link += lv
    # Q + D of the region, its limit, the rows that must lead from the block into the ring or back
    QD = gp.quicksum((K - v) * var for (x, v), var in yv.items()) + gp.quicksum(det.values())
    cur_in = sum(K - sel[L][1] if sel[L][1] else 1 for L in free)
    m.addConstr(QD <= cur_in + gap)
    if cross:
        m.addConstr(gp.quicksum(var for (x, v), var in yv.items()
                                if (canon(x) in blockset) != (canon(gstep(x, v)) in blockset)) >= cross)
    if ring_ok is not None:
        bad = []
        for (x, v), var in yv.items():
            a_, b_ = canon(x), canon(gstep(x, v))
            if (a_ in blockset) != (b_ in blockset):
                r_ = b_ if a_ in blockset else a_
                if r_ not in ring_ok:
                    bad.append(var)
        m.addConstr(gp.quicksum(bad) == 0)
    m.setObjective(QD + cC * (gp.quicksum(det.values()) - gp.quicksum(link)), GRB.MINIMIZE)
    for (x, v), var in yv.items():
        var.Start = 1 if chosen.get(x) == v else 0
    m.Params.PoolSolutions = pool
    m.Params.PoolSearchMode = 2
    m.Params.PoolGap = 1e9
    m.Params.PoolGapAbs = poolgap
    m.optimize()
    if not quiet:
        print("status %d, objective %.2f (bound %.2f), present Q + D of the region %d, %d pool solutions, %.0f s" % (
            m.Status, m.ObjVal if m.SolCount else float("nan"), m.ObjBound, cur_in, m.SolCount, time.time() - t0), flush=True)
    # every pool solution is measured exactly: follow its rows, and the jumps through the fixed stretches
    res = []
    for kk in range(m.SolCount):
        m.Params.SolutionNumber = kk
        new = {key_[0]: key_[1] for key_, var in yv.items() if var.Xn > 0.5}
        nd = sum(1 for L in free if det[L].Xn > 0.5)
        nl = sum(1 for var in link if var.Xn > 0.5)
        seen = set()
        tb = ts = 0
        ok = True
        nsmall = []
        for x0 in new:
            if x0 in seen:
                continue
            p = list(range(K - 1))
            x = x0
            big = False
            cnt = 0
            while True:
                seen.add(x)
                cnt += 1
                v = new[x]
                q = port(v, K)
                p = [q[j] for j in p]
                s = gstep(x, v)
                if s in jump:
                    q, s = jump[s]
                    p = [q[j] for j in p]
                    big = True
                if s == x0:
                    break
                if s not in new or s in seen:
                    ok = False
                    break
                x = s
            if not ok:
                break
            c = cycles_of(p)
            if big:
                tb += c
            else:
                ts += c
                nsmall.append((cnt, c))
        if not ok:
            continue
        q_ = sum(K - v for v in new.values())
        dq = q_ + nd - cur_in
        priced = dq + cC * (nd - nl) + cB * (tr_fixed + tb - cur[2]) + cW * ts
        rows = {L: (L, 0) for L in free}
        for x, v in new.items():
            rows[canon(x)] = (x, v)
        res.append((priced, (dq, nd, nd - nl, tr_fixed + tb - cur[2], ts, tuple(sorted(nsmall))), rows))
    res.sort(key=lambda r: (r[0], r[1]))
    return res


def multi():
    """The driver: search for connections walk by walk (when --walks names walks), or apply connection files;
    then either write the changed rows as a connection (--json) or assemble and check the selection."""
    sel, K = load_base(sys.argv[2])
    fb = read_gsel(sys.argv[3])
    out = sys.argv[4]
    m_ = arg("--m", 7, int)
    cC, cB, cW = arg("--cC", 2.7, float), arg("--cB", 1.86, float), arg("--cW", 2.2, float)
    bl = blocks_of(sel, m_)
    keys = list(bl)
    report(sel, "base: ")
    # the big walks; each is remembered by up to 50 of its states that lie in no block and in no ring
    ws, chosen = walks(sel)
    big = [w for w in ws if len(w) > 200]
    allblock = {L for b in bl.values() for L in b}
    ringall = {M for L in allblock for M in neighbours(L)}
    reps = [[x for x in w if canon(x) not in ringall][:50] for w in big]
    print("%d big walks, %d blocks" % (len(big), len(keys)), flush=True)
    crossed = []
    if "--pre" in sys.argv:
        import json
        for jf in arg("--pre", "").split(","):
            T = json.load(open(jf))
            for (ox, ov, nx, nv) in T["changes"]:
                o = tuple(ALPH.index(a) for a in ox)
                nw = tuple(ALPH.index(a) for a in nx)
                assert sel[canon(o)] == (o, ov), "a changed row does not match the base"
                sel[canon(o)] = (nw, nv)
            crossed += [tuple(ALPH.index(a) for a in k) for k in T["blocks"]]
        walks(sel)
        print("applied %s: %d blocks already connected" % (arg("--pre", ""), len(crossed)), flush=True)
    # the search, one big walk at a time, on the selection as changed so far
    wspec = arg("--walks", "0:%d" % len(big))
    wlist = [int(t) for t in wspec.split(",")] if "," in wspec or ":" not in wspec else list(range(*[int(t) for t in wspec.split(":")]))
    base0 = dict(sel)
    for wi in wlist:
        ws, chosen = walks(sel)
        wid = {x: i for i, w in enumerate(ws) for x in w}
        target = wid[next(x for x in reps[wi] if x in chosen)]
        okw = False
        cands = []
        tried = set()
        order = []
        for key in keys:
            if key in crossed:
                continue
            blockset = set(bl[key])
            ring = {M for L in blockset for M in neighbours(L)} - blockset
            order.append((-sum(1 for M in ring if sel[M][1] and wid[sel[M][0]] == target), key))
        order.sort()
        print("walk %d: ring loops on this walk per free block: %s" % (wi, [-c for c, k in order][:16]), flush=True)
        skip = arg("--skip", 0, int)
        for attempt in range(arg("--tries", 4, int)):
            if skip + attempt >= len(order) or order[skip + attempt][0] == 0:
                break
            key = order[skip + attempt][1]
            tried.add(key)
            blockset = set(bl[key])
            ring = {M for L in blockset for M in neighbours(L)} - blockset
            ringw = {M for M in ring if sel[M][1] and wid[sel[M][0]] == target}
            free = blockset | ring if "--fullring" in sys.argv else blockset | ringw
            res = solve_region(sel, K, m_, blockset, free, cC, cB, cW, 1, arg("--gap", 14.0, float),
                               arg("--time", 120.0, float), arg("--threads", 1, int), arg("--pool", 300, int),
                               arg("--poolgap", 3.0, float), quiet=True, ring_ok=ringw)
            nall = len(res)
            from collections import Counter as _C
            hist = dict(sorted(_C((r[1][0], r[1][3]) for r in res).items()))
            res = [r for r in res if r[1][3] <= arg("--mintrail", -6, int)]
            if not res:
                print("walk %d: block %s, region %d loops (%d on the walk): %d solutions, (Q + D change, trail change): %s" % (
                    wi, txt(key), len(free), len(ringw), nall, hist), flush=True)
                continue
            r = res[0]
            print("walk %d: block %s: priced %.2f, Q + D %+d, D %d in %d chains" % (wi, txt(key), r[0], r[1][0], r[1][1], r[1][2]), flush=True)
            cands.append((r[0], key, r, len(free)))
            if r[0] <= arg("--good", -0.5, float):
                break
        if cands:
            cands.sort(key=lambda c: c[0])
            _p, key, r, nfree = cands[0]
            for L, row in r[2].items():
                sel[L] = row
            walks(sel)
            crossed.append(key)
            print("walk %d (%d rows): block %s, region %d loops: priced %.2f, Q + D %+d, D %d in %d chains, "
                  "trails of the walk %+d, inside walks %s" % (wi, len(big[wi]), txt(key), nfree, r[0], r[1][0], r[1][1],
                                                              r[1][2], r[1][3], list(r[1][5])), flush=True)
            okw = True
        if not okw:
            print("walk %d: left as it is" % wi, flush=True)
    # write the rows that were changed as a connection file
    if "--json" in sys.argv:
        import json
        ch = [[txt(base0[L][0]), base0[L][1], txt(sel[L][0]), sel[L][1]] for L in sorted(sel) if sel[L] != base0[L]]
        json.dump({"blocks": [txt(k) for k in crossed], "changes": ch}, open(arg("--json", None), "w"))
        print("wrote %s: %d rows changed, %d blocks" % (arg("--json", None), len(ch), len(crossed)))
        return
    # assembly: apply the connection files named on the command line
    for jf in sys.argv[5:]:
        if jf.endswith(".json"):
            import json
            T = json.load(open(jf))
            for (ox, ov, nx, nv) in T["changes"]:
                o = tuple(ALPH.index(a) for a in ox)
                nw = tuple(ALPH.index(a) for a in nx)
                assert sel[canon(o)] == (o, ov), "a changed row does not match the base"
                sel[canon(o)] = (nw, nv)
            crossed += [tuple(ALPH.index(a) for a in k) for k in T["blocks"]]
    walks(sel)
    # the block solution FALLBACK in every block that is not connected
    nfb = 0
    for key in keys:
        if key in crossed:
            continue
        phi = list(key) + list(range(m_, K))
        for L, (x, v) in fb.items():
            y = tuple(phi[c] for c in x)
            c = canon(y)
            assert sel[c][1] == 0
            sel[c] = (y if v else c, v)
        nfb += 1
    print("%d blocks connected to a big walk, %d blocks with the fallback solution" % (len(crossed), nfb))
    r1 = report(sel, "result: ")
    write_gsel(out, sel, "gregion.py multi %s + %s: floor %d = Q %d + D %d + walk trails %d" % (
        sys.argv[2], sys.argv[3], r1[0], r1[4], r1[5], r1[2]))
    lit, nsl = literal_trails(sel)
    print("literal endpoint graph: %d closed trails (formula %d), %d slices (K! + Q = %d)" % (
        lit, r1[2] + r1[5], nsl, math.factorial(K) + r1[4]))
    assert lit == r1[2] + r1[5] and nsl == math.factorial(K) + r1[4]
    print("wrote", out)


if __name__ == "__main__":
    {"multi": multi}[sys.argv[1]]()
