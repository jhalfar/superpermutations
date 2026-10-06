"""gsegip.py - the block above a left-over loop as an integer programme over segments, with a neighbourhood search.

This found the (7, 4) block of the n = 13 selection.  The (m, r) block: the loops are the cyclic orders of
K = m + r letters whose old letters 0 .. m-1 stand in the cyclic order (0 1 .. m-1); a row may not exchange two old
letters.  Rows have any visible length v; this program speaks of the cost d = K - v of a row (d = 2 is Pantone's
short row).  In the picture of a walk: a step exchanges two adjacent letters; after a full row the same letter moves
on; after a row of cost d the letter d places behind the one that has just moved starts to move.

Only solutions invariant under a group of relabellings are looked for (--sym old: rotation of the old letters;
tok: cyclic shift of the added letters; swap: exchange of the first two of them), and the programme is written on
the orbits (quot.py):
    SEGMENT (u, d, j)   a row of cost d >= 2 at the state orbit u, followed by j - 1 full rows
    CHAIN (--chains)    loops without a row that follow each other in the orbit of one moving letter: their small
                        trails join at one letter each; one column per run of such loops
    minimise   sum of d over the segments + sum over the chains (loops + P) + (1 + P) per single loop without a row
               = Q + D + P * (chains and single loops)
    cover      every loop orbit lies in exactly one segment or chain, or is a single loop without a row
    flow       a segment ends at the state where another starts
    lazily     a closed walk W with Q_W + (closed trails of W) >= (rows of W) is forbidden: it costs at least what
               its loops cost without rows.  Closed trails by the port rule of gcore.py.

Ways to run it:
  --lp          the linear relaxation only.  Columns that meet a loop orbit twice are kept then, so the value is a
                lower bound of Q + D for every selection of the block, invariant or not (average a selection over
                the group).  (7, 4): 1,376.2 with rows of all lengths (--dmax 10), 1,403.6 with full and short rows.
                The bound is weak: for the (7, 3) block it gives 182 and 189, where the optima under rotation
                are 301 and 308.
  (default)     branch and bound until --time.  For the (7, 3) block this proves, in seconds, the optima under
                rotation 308 (--dmax 2) and 301 (--dmax 9), the values of block_grb.py, and 476 for Q + D + 3 x
                chains (--dmax 2 --P 3 --chains).  For the (7, 4) block it does not get anywhere: the first runs
                stood at a gap of 45 to 52 % at the root.
  --lns N       neighbourhood search from --start (lns_part.py): N rounds; a round frees a region of loop orbits,
                fixes the chosen columns outside it, and solves the rest for --sub seconds below the present value.
                --frac: size of a region as a part of all loop orbits.  A solution is accepted when
                    Q + D + P * (chains and single loops) + wt * (closed trails of walks) + wu * (walks)
                goes down (--wt, --wu; neither term is in the programme unless --zprice).
  --zprice      (with --lns) the price wt per closed trail and wu per walk inside the programme: one price variable
                per walk met so far, bound to the walk when it first appears.
  --arcs 2|3    (with --chains) joins of cost 2 (and 3) between the end of one chain and the start of another as
                columns: two units become one, the join costs 2 or 3 instead of 1 and one P is saved.
  --norel SEC   the no-relaxation heuristic of the solver instead of branch and bound.
  --fwd         only steps in which an added letter moves forward.
  --minj, --maxj   shortest and longest segment;   --dmax D   largest cost of a row (default 2).
  --heur, --nodemethod, --cuts   passed to the solver;   --focus F (1);   --seed S;   --threads T;   --verbose.

The block of the n = 13 selection (data/block_7_4_n13.txt).  It is the end of a chain of --lns runs that began at
the transported (7, 3) block (Q 1,820, 1,260 loops without a row, floor 3,110): first with --dmax 4, then
--dmax 6, with P between 0.6 and 2.6, about an hour in all.  The last two stages can be run again from the data
files:
    python gsegip.py 7 4 --dmax 6 --P 2.6 --wt 3.5 --chains --lns 2000 --sub 50 --frac 0.3 --time 100 --threads 1
           --seed 101 --start data/block_7_4_step1.txt --out OUT          (writes data/block_7_4_step2.txt)
    python gsegip.py 7 4 --dmax 6 --P 4.5 --wt 1 --wu 4.5 --zprice --chains --lns 2000 --sub 60 --frac 0.35
           --time 100 --threads 1 --seed 91 --start data/block_7_4_step2.txt --out OUT
                                                                          (writes data/block_7_4_n13.txt)
On the machine used here both write their file again byte for byte (Gurobi 13.0, one thread, 100 s each, 0.5 GB;
the gain comes in the fourth and in the fifth round).  The round that finds the second file ends by its time
limit of 60 s, so on another machine the result of that stage can differ.  step1 is the solution with the lowest
floor that the chain met (2,875); step2 has fewer chains (84 against 98; floor 2,901).  The second stage is the
first with the prices of the walks inside the programme; it rearranges two walks, 24 closed trails become 20, and
Q and the loops without a row stay (floor 2,897).  Left running, it found one more block after 70 rounds (Q 2,863,
168 loops without a row in 49 chains, 8 closed trails), which was not used.  Runs with --arcs found none better.
Nothing about the (7, 4) block is proved optimal: the only bound is the 1,376.2 above.

usage:    python gsegip.py m r [options above] [--sym old] [--P p] [--chains] [--time SEC] [--start FILE]
                               [--out FILE]
inputs:   --start: a block solution ("x v" lines, see gcore.py) whose segments are all among the columns.
outputs:  text: the model size, then one line per accepted solution (Q, D, chains, walks, closed trails, floor =
          Q + D + trails, objective, rows by visible length, the largest walks as (rows, Q, trails) x count);
          --out: the best solution so far, rewritten at every improvement ("x v" lines, LF line ends).
needs:    Python 3, gcore.py, quot.py, lns_part.py, Gurobi with its Python package gurobipy.
          Gurobi needs a full licence: academic licences are free, and the size-limited licence that
          comes with the package is too small for these models.
cost:     measured here on one thread: (7, 4) --dmax 6 --chains: 158,400 segment and 26,184 chain columns, built in
          8 s, 0.5 GB, each of the two stages above 100 s; --lp --dmax 10: 6 s, 0.5 GB; the (7, 3) optima: 1 s
          (--dmax 2) and 18 s (--dmax 9).
"""
import itertools
import sys
import time
from collections import Counter, defaultdict

import gurobipy as gp
from gurobipy import GRB

from gcore import canon, gstep, read_gsel, write_gsel, walks, walk_trails
from quot import Quot


def arg(k, d):
    """Value of the command-line option k, converted to the type of the default d; a flag when d is a bool."""
    if k not in sys.argv:
        return d
    if isinstance(d, bool):
        return True
    return type(d)(sys.argv[sys.argv.index(k) + 1])


def gevaluate(sel):
    """The numbers of a block solution  loop -> (x, v), as a dict: Q, D (loops without a row), nwalks, trails
    (closed trails of all walks after completion, port rule), floor = Q + D + trails, stat = Counter of (rows, Q,
    trails) per walk, per = list of (walk, its Q, its trails), chosen = state -> v, rows = Counter of v."""
    K = len(next(iter(sel)))
    ws, chosen = walks(sel)
    D = sum(1 for (x, v) in sel.values() if v == 0)
    Qc = sum(K - v for v in chosen.values())
    tr = 0
    stat = Counter()
    per = []
    for w in ws:
        c = walk_trails(w, chosen, K)
        qw = sum(K - chosen[x] for x in w)
        tr += c
        stat[(len(w), qw, c)] += 1
        per.append((w, qw, c))
    return dict(K=K, Q=Qc, D=D, nwalks=len(ws), trails=tr, floor=Qc + D + tr, stat=stat, per=per, chosen=chosen,
                rows=Counter(v for v in chosen.values()))


def main():
    """Build the columns and the programme on the orbits, then run one of the modes of the header."""
    m, r = int(sys.argv[1]), int(sys.argv[2])
    sym = arg("--sym", "old"); tl = arg("--time", 300.0); threads = arg("--threads", 2)
    fwd = arg("--fwd", False); lp = arg("--lp", False); P = arg("--P", 0.0)
    start = arg("--start", ""); out = arg("--out", ""); focus = arg("--focus", 1); seed = arg("--seed", 1)
    chains_on = arg("--chains", False)
    t0 = time.time()
    Q = Quot(m, r, sym)
    K = Q.K
    maxj = arg("--maxj", K - 1); minj = arg("--minj", 1); dmax = arg("--dmax", 2)
    n = len(Q.loops)
    mdl = gp.Model("gsegip")
    mdl.Params.OutputFlag = 0
    mdl.Params.Threads = threads
    mdl.Params.Seed = seed
    vt = GRB.CONTINUOUS if lp else GRB.BINARY
    # segment columns (u, d, j): a row of cost d at the state orbit u, then j - 1 full rows
    cover = {A: [] for A in Q.lorb}
    inflow, outflow = defaultdict(list), defaultdict(list)
    col = {}
    for u in Q.states:
        for d in range(2, dmax + 1):
            v_ = K - d
            a_, b_ = u[v_ - 1], u[v_]                      # exchanged: a_ moves forward over b_
            if a_ < m and b_ < m:
                continue
            if fwd and a_ < m:
                continue
            visited = {canon(u)}
            cnt = Counter([Q.lrep[canon(u)][0]])
            x = gstep(u, v_)
            for j in range(1, maxj + 1):
                if not lp and max(cnt.values()) > 1:
                    break
                if j >= minj:
                    var = mdl.addVar(vtype=vt, ub=1, obj=float(d))
                    col[u, d, j] = var
                    for A, c in cnt.items():
                        cover[A].append((c, var))
                    outflow[u].append(var)
                    inflow[Q.rep_state(x)].append(var)
                if (x[-1] < m and x[0] < m) or canon(x) in visited or (fwd and x[-1] < m):
                    break
                visited.add(canon(x))
                cnt[Q.lrep[canon(x)][0]] += 1
                x = gstep(x, K)
    # det[A]: a single loop orbit without a row.  Chain columns: runs of loops without a row that follow each
    # other in the orbit of one moving letter (in the quotient such an orbit is a path or a cycle)
    det = {A: mdl.addVar(vtype=vt, ub=1, obj=1.0 + P) for A in Q.lorb}
    chain = {}
    chport = {}                    # chain column -> (first loop orbit, index of its mover), (last loop orbit, index)
    if P > 0 and chains_on:
        nxt = {}
        for A in Q.lorb:
            for i in range(K):
                lk = Q.link(A, i)
                if lk is not None:
                    nxt[A, i] = lk
        hasprev = set(nxt.values())
        seqs = []
        seen = set()
        for key in nxt:
            if key in hasprev or key in seen:
                continue
            seq, k = [key], key
            seen.add(key)
            while k in nxt:
                k = nxt[k]
                seen.add(k)
                seq.append(k)
            seqs.append((seq, False))
        for key in nxt:
            if key in seen:
                continue
            seq, k = [], key
            while k not in seen:
                seen.add(k)
                seq.append(k)
                k = nxt[k]
            assert k == key
            seqs.append((seq, True))
        for seq, cyc in seqs:
            loops_ = [k[0] for k in seq]
            L = len(loops_)
            if cyc:
                for ln in range(2, L):
                    for s0 in range(L):
                        ch = tuple(loops_[(s0 + q) % L] for q in range(ln))
                        if len(set(ch)) == ln and ch not in chain:
                            chain[ch] = None
                            chport[ch] = (seq[s0], seq[(s0 + ln - 1) % L])
                if len(set(loops_)) == L:
                    i0 = loops_.index(min(loops_))
                    chain[tuple(loops_[i0:] + loops_[:i0])] = None
                    chport[tuple(loops_[i0:] + loops_[:i0])] = (seq[i0], seq[(i0 - 1) % L])
            else:
                for ln in range(2, L + 1):
                    for s0 in range(L - ln + 1):
                        ch = tuple(loops_[s0:s0 + ln])
                        if len(set(ch)) == ln and ch not in chain:
                            chain[ch] = None
                            chport[ch] = (seq[s0], seq[s0 + ln - 1])
        for ch in chain:
            var = mdl.addVar(vtype=vt, ub=1, obj=len(ch) + P)
            chain[ch] = var
            for A in ch:
                cover[A].append((1, var))
    # cheap joins between chains: the last small trail of a chain (opened after its mover; a single loop: after any
    # letter) is followed by the first small trail of another chain whose word overlaps in K - 1 - cost letters.
    # Two units become one: the join costs `cost` instead of 1 and one unit price P is saved.
    arcv, arccost = {}, {}
    amax = arg("--arcs", 0)
    if amax >= 2 and chain:
        ends_at, starts_at = defaultdict(list), defaultdict(list)
        for ch, var in chain.items():
            sk, ek = chport[ch]
            starts_at[sk].append(var)
            ends_at[ek].append(var)
        aout, ain = defaultdict(list), defaultdict(list)
        for A in Q.lorb:
            for i in range(K):
                c = A[i]
                w = A[i + 1:] + A[:i]
                for cst in range(2, amax + 1):
                    rest = w[cst:]
                    for perm in itertools.permutations(w[:cst] + (c,)):
                        m1 = perm[-1]
                        y2 = canon((m1,) + rest + perm[:-1])
                        if y2 == A or y2 not in Q.lset:
                            continue
                        B, hi = Q.lrep[y2]
                        key = ((A, i), (B, B.index(Q.G[hi][m1])))
                        if key in arcv:
                            continue
                        var = mdl.addVar(vtype=vt, ub=1, obj=float(cst - 1) - P)
                        arcv[key] = var
                        arccost[key] = cst
                        aout[key[0]].append(var)
                        ain[key[1]].append(var)
        for nd, vs in aout.items():
            mdl.addConstr(gp.quicksum(vs) <= gp.quicksum(ends_at.get(nd, [])) + det[nd[0]])
        for nd, vs in ain.items():
            mdl.addConstr(gp.quicksum(vs) <= gp.quicksum(starts_at.get(nd, [])) + det[nd[0]])
        for A in Q.lorb:
            outs = [(i, aout[A, i]) for i in range(K) if (A, i) in aout]
            ins = [(i, ain[A, i]) for i in range(K) if (A, i) in ain]
            if len(outs) > 1:
                mdl.addConstr(gp.quicksum(v for i, vs in outs for v in vs) <= 1)
            if len(ins) > 1:
                mdl.addConstr(gp.quicksum(v for i, vs in ins for v in vs) <= 1)
            if outs and ins:
                for i, vs in outs:
                    other = [v for i2, vs2 in ins if i2 != i for v in vs2]
                    if other:
                        mdl.addConstr(gp.quicksum(vs) + gp.quicksum(other) <= 1)
        print("joins of cost 2..%d between chains: %d variables (cycles of chains are cut in the search)" % (amax, len(arcv)), flush=True)
    # cover and flow
    for A in Q.lorb:
        mdl.addConstr(gp.quicksum(c * x for c, x in cover[A]) + det[A] == 1)
    for v in set(inflow) | set(outflow):
        mdl.addConstr(gp.quicksum(inflow.get(v, [])) == gp.quicksum(outflow.get(v, [])))
    print("m = %d r = %d sym = %s%s, rows of cost 0 and 2..%d: %d loops, %d loop orbits, %d segment columns, %d chain columns; P = %.2f (%.0fs)" % (
        m, r, sym, " forward-token only" if fwd else "", dmax, n, len(Q.lorb), len(col), len(chain), P, time.time() - t0), flush=True)
    # mode --lp: the linear relaxation, by the barrier method
    if lp:
        mdl.Params.Method = 2
        mdl.Params.Crossover = 0
        mdl.optimize()
        print("LP: in-model objective >= %.3f of %d loops = %.5f per loop  (loops without a row %.2f)  (%.0fs)" % (
            mdl.ObjVal * Q.scale, n, mdl.ObjVal * Q.scale / n,
            Q.scale * (sum(v.X for v in det.values()) + sum(len(ch) * v.X for ch, v in chain.items())), time.time() - t0))
        return

    def to_sel(val):
        """lift a solution of the programme (val = value of a variable) to the block: dict loop -> (x, v)"""
        yt = {}
        for (u, d, j), var in col.items():
            if val(var) > 0.5:
                yt[u] = K - d
                x = gstep(u, K - d)
                for _ in range(j - 1):
                    yt[Q.rep_state(x)] = K
                    x = gstep(x, K)
        sel = Q.lift(yt)
        return {L: ((x, ty) if ty != "D" else (L, 0)) for L, (x, ty) in sel.items()}

    def segkeys(w, chosen):
        """the segment columns (u, d, j) in the quotient that the closed walk w is made of"""
        keys = set()
        L = len(w)
        for i, x in enumerate(w):
            if chosen[x] != K:
                j = 1
                while chosen[w[(i + j) % L]] == K:
                    j += 1
                keys.add((Q.rep_state(x), K - chosen[x], j))
        return keys

    # the best solution seen by the callbacks
    best = {"obj": None, "sel": None, "txt": ""}
    ncut = [0]

    def cb(model, where):
        """branch and bound: a new solution with a walk that costs at least its number of rows gets a lazy cut
        for every such walk; any other new solution is recorded and written when it is the best so far"""
        if where == GRB.Callback.MIPSOL:
            val = lambda x: model.cbGetSolution(x)
            sel = to_sel(val)
            st = gevaluate(sel)
            bad = [(w, qw, c) for (w, qw, c) in st["per"] if qw + c >= len(w)]
            if bad:
                seen = set()
                for (w, qw, c) in bad:
                    keys = frozenset(segkeys(w, st["chosen"]))
                    if keys in seen:
                        continue
                    seen.add(keys)
                    vs = [col[k] for k in keys]
                    model.cbLazy(gp.quicksum(vs) <= len(vs) - 1)
                    ncut[0] += 1
            else:
                nch = Q.scale * (sum(1 for ch, p in chain.items() if val(p) > 0.5) + sum(1 for A, p in det.items() if val(p) > 0.5))
                obj = st["Q"] + st["D"] + P * nch
                if best["obj"] is None or obj < best["obj"] - 1e-6:
                    best.update(obj=obj, sel=sel)
                    best["txt"] = "Q %d D %d chains %d walks %d trails %d floor %d obj %.1f | rows %s | %s" % (
                        st["Q"], st["D"], nch, st["nwalks"], st["trails"], st["floor"], obj,
                        dict(sorted(st["rows"].items(), reverse=True)), sorted(st["stat"].items(), reverse=True)[:4])
                    print("   solution: %s | cuts %d | %.0fs" % (best["txt"], ncut[0], time.time() - t0), flush=True)
                    if out:
                        write_gsel(out, sel, "gsegip.py m=%d r=%d sym=%s%s dmax=%d P=%.2f: %s" % (m, r, sym, " fwd" if fwd else "", dmax, P, best["txt"]))

    # the start solution: its segments, its chains (longest first) and its single loops as start values
    if start:
        s0 = read_gsel(start)
        ws, chosen = walks(s0)
        on = set()
        for w in ws:
            on |= segkeys(w, chosen)
        miss = [k for k in on if k not in col]
        print("start %s: %d segments in the quotient, %d not among the columns" % (start, len(on), len(miss)), flush=True)
        if not miss:
            for k, var in col.items():
                var.Start = 1 if k in on else 0
            isd = {A: s0[A][1] == 0 for A in Q.lorb}
            taken = set()
            onch = set()
            for ch in sorted(chain, key=len, reverse=True):
                if all(isd[A] and A not in taken for A in ch):
                    taken.update(ch)
                    onch.add(ch)
            for ch, var in chain.items():
                var.Start = 1 if ch in onch else 0
            for A in Q.lorb:
                det[A].Start = 1 if (isd[A] and A not in taken) else 0
    mdl.Params.LazyConstraints = 1
    mdl.Params.MIPFocus = focus
    for k_, d_ in (("--heur", 0.05), ("--nodemethod", -1), ("--cuts", -1)):
        if k_ in sys.argv:
            setattr(mdl.Params, {"--heur": "Heuristics", "--nodemethod": "NodeMethod", "--cuts": "Cuts"}[k_], arg(k_, d_))
    # mode --lns: the neighbourhood search of lns_part.py
    if arg("--lns", 0) > 0:
        assert start and not miss, "--lns needs a start whose segments are all among the columns"
        from lns_part import run_lns
        run_lns(dict(mdl=mdl, Q=Q, K=K, m=m, col=col, chain=chain, det=det, arcv=arcv, arccost=arccost, gstep=gstep, gevaluate=gevaluate, to_sel=to_sel,
                     segkeys=segkeys, write_gsel=write_gsel, P=P, s0=s0, out=out, t0=t0, tl=tl, nlns=arg("--lns", 0),
                     sub=arg("--sub", 30.0), frac=arg("--frac", 0.5), seed=seed, wt=arg("--wt", 0.0), wu=arg("--wu", 0.0), zprice=arg("--zprice", False), verbose=arg("--verbose", False),
                     tag="gsegip.py m=%d r=%d sym=%s%s dmax=%d P=%.2f" % (m, r, sym, " fwd" if fwd else "", dmax, P)))
        return
    # mode --norel
    norel = arg("--norel", 0.0)
    if norel > 0:
        # no lazy constraints: Gurobi's no-relaxation heuristic from the start; solutions with a bad walk are skipped
        wt_, wu_ = arg("--wt", 0.0), arg("--wu", 0.0)
        nbad = [0]

        def cb3(model, where):
            """no-relaxation heuristic: solutions with a bad walk are skipped (no cut is added), the others are
            recorded and written when they are the best so far"""
            if where == GRB.Callback.MIPSOL:
                val = lambda x: model.cbGetSolution(x)
                sel = to_sel(val)
                st = gevaluate(sel)
                if any(qw + c >= len(w) for (w, qw, c) in st["per"]):
                    nbad[0] += 1
                    return
                nch = Q.scale * (sum(1 for ch, p in chain.items() if val(p) > 0.5) + sum(1 for A, p in det.items() if val(p) > 0.5))
                obj = st["Q"] + st["D"] + P * nch
                objB = obj + wt_ * st["trails"] + wu_ * st["nwalks"]
                if best["obj"] is None or objB < best["obj"] - 1e-6:
                    best.update(obj=objB, sel=sel)
                    best["txt"] = "Q %d D %d chains %d walks %d trails %d floor %d obj %.1f objB %.1f | rows %s | %s" % (
                        st["Q"], st["D"], nch, st["nwalks"], st["trails"], st["floor"], obj, objB,
                        dict(sorted(st["rows"].items(), reverse=True)), sorted(st["stat"].items(), reverse=True)[:4])
                    print("   solution: %s | skipped (bad walk) %d | %.0fs" % (best["txt"], nbad[0], time.time() - t0), flush=True)
                    if out:
                        write_gsel(out, sel, "gsegip.py m=%d r=%d sym=%s%s dmax=%d P=%.2f norel: %s" % (m, r, sym, " fwd" if fwd else "", dmax, P, best["txt"]))
        mdl.Params.LazyConstraints = 0
        mdl.Params.NoRelHeurTime = norel
        mdl.Params.TimeLimit = norel + 20
        mdl.Params.OutputFlag = 1
        mdl.Params.DisplayInterval = 60
        mdl.optimize(cb3)
        print("no-relaxation heuristic: best %s" % best["txt"])
        return
    # default mode: branch and bound with the lazy cuts of cb
    mdl.Params.TimeLimit = tl
    mdl.Params.OutputFlag = 1
    mdl.Params.DisplayInterval = 30
    mdl.optimize(cb)
    print("status %d; in-model objective best %s, bound %.1f (x group order; %d loops); lazy cuts %d  (%.0fs)" % (
        mdl.Status, ("%.1f" % (mdl.ObjVal * Q.scale)) if mdl.SolCount else "-", mdl.ObjBound * Q.scale, n, ncut[0], time.time() - t0))
    print("best: %s" % best["txt"])


if __name__ == "__main__":
    main()
