"""lns_part.py - the neighbourhood search of gsegip.py (imported there; it works on the objects of gsegip.main()).

One round: a region of loop orbits is drawn, every chosen column that does not touch the region is fixed, the
programme is solved for `sub` seconds with a cutoff just below the present value, and the best solution found is
taken when
    Q + D + P * (chains and single loops) + (cost of the joins between chains) + wt * (closed trails) + wu * (walks)
goes down.  Regions are of two kinds, drawn at random (one ball to two towers):
    ball    the loop orbits within a growing distance of a random one (neighbours = one exchange of adjacent
            letters that does not exchange two old letters)
    tower   one added letter t is chosen; the loop orbits are grouped by what remains when t is deleted; a ball of
            such groups is taken, each with all its loops (the letter t in every gap)
Lazy cuts found in a round (bad walks, cycles of chains) are added to the programme for all later rounds.
With zprice the walks carry their price inside the programme: every walk met gets a price variable; a solution that
was refused only because its walks had no price yet is handed back to the solver with the prices paid.

needs:    Python 3, gcore.py, Gurobi (see gsegip.py).  Not a program of its own.
"""
import random
import time
from collections import defaultdict

import gurobipy as gp
from gurobipy import GRB

from gcore import canon


def run_lns(env):
    """The search.  env: dict of the objects of gsegip.main() (the programme mdl, the quotient Q, the columns col,
    chain, det, arcv, the functions gstep, gevaluate, to_sel, segkeys, write_gsel, and the options)."""
    mdl, Q, K, m, col, chain, det = env["mdl"], env["Q"], env["K"], env["m"], env["col"], env["chain"], env["det"]
    gstep, gevaluate, to_sel, segkeys, write_gsel = env["gstep"], env["gevaluate"], env["to_sel"], env["segkeys"], env["write_gsel"]
    P, s0, out, t0, tl = env["P"], env["s0"], env["out"], env["t0"], env["tl"]
    nlns, sub, frac, seed, verbose, tag = env["nlns"], env["sub"], env["frac"], env["seed"], env["verbose"], env["tag"]
    wu = env.get("wu", 0.0)          # ... + wu * walks
    wt = env.get("wt", 0.0)          # acceptance: in-model objective + wt * walk trails must improve as well
    rng = random.Random(seed)
    allvars = list(col.items()) + [(("c",) + ch, v) for ch, v in chain.items()] + [(("d", A), v) for A, v in det.items()]
    loops_of = {}
    for (u, d, j), var in col.items():
        ls = [Q.lrep[canon(u)][0]]
        x = gstep(u, K - d)
        for _ in range(j - 1):
            ls.append(Q.lrep[canon(x)][0])
            x = gstep(x, K)
        loops_of[u, d, j] = ls
    for ch in chain:
        loops_of[("c",) + ch] = list(ch)
    for A in det:
        loops_of["d", A] = [A]
    adj = defaultdict(set)
    for A in Q.lorb:
        for i in range(K):
            lk = Q.link(A, i)
            if lk is not None:
                adj[A].add(lk[0])
                adj[lk[0]].add(A)

    def region():
        """draw a region: (its kind as text, the set of loop orbits that are freed)"""
        want = int(frac * len(Q.lorb) * rng.uniform(0.7, 1.3))
        kind = rng.choice(["ball", "tower", "tower"])
        if kind == "ball":
            fr = [rng.choice(Q.lorb)]
            R = set(fr)
            while len(R) < want and fr:
                nf = []
                rng.shuffle(fr)
                for a_ in fr:
                    for b_ in adj[a_]:
                        if b_ not in R and len(R) < want:
                            R.add(b_)
                            nf.append(b_)
                fr = nf
            return kind, R
        tok = rng.randrange(m, K)

        def proj(A):
            """the loop orbit A with the added letter tok deleted (letters above it renumbered)"""
            return tuple((c if c < tok else c - 1) for c in A if c != tok)
        groups = defaultdict(list)
        for A in Q.lorb:
            groups[proj(A)].append(A)
        gadj = defaultdict(set)
        for A in Q.lorb:
            for B in adj[A]:
                if proj(A) != proj(B):
                    gadj[proj(A)].add(proj(B))
        fr = [rng.choice(list(groups))]
        G_ = set(fr)
        while len(G_) * (K - 1) < want and fr:
            nf = []
            rng.shuffle(fr)
            for a_ in fr:
                bs = list(gadj[a_])
                rng.shuffle(bs)
                for b_ in bs:
                    if b_ not in G_ and len(G_) * (K - 1) < want:
                        G_.add(b_)
                        nf.append(b_)
            fr = nf
        return kind + "-" + "abcd"[tok - m], {A for g_ in G_ for A in groups[g_]}

    mdl.update()
    cur = {key: (1 if 0.5 < var.Start < 1.5 else 0) for key, var in allvars}
    st0 = gevaluate(s0)
    nch0 = Q.scale * sum(1 for key, on in cur.items() if on and key[0] in ("c", "d"))
    curobj = st0["Q"] + st0["D"] + P * nch0
    curB = curobj + wt * st0["trails"] + wu * st0["nwalks"]
    print("start: Q %d D %d chains %d walks %d trails %d floor %d obj %.1f" % (
        st0["Q"], st0["D"], nch0, st0["nwalks"], st0["trails"], st0["floor"], curobj), flush=True)
    cuts_all = []
    holder = {}
    varlist = [v for k, v in allvars]
    arcv, arccost = env.get("arcv", {}), env.get("arccost", {})
    arckeys = list(arcv)
    arcvars = [arcv[k] for k in arckeys]
    arc_cuts = []
    cur_aon = set()
    zprice = env.get("zprice", False)
    priced = {}                       # frozenset of column keys of a walk (all its lifts) -> (z variable, price / group order)
    newpriced = {}
    spares = []

    def walk_groups(st):
        """column set -> price of all lifted walks made of these quotient columns: wt per trail + wu per walk"""
        g = defaultdict(float)
        for (w, qw, c) in st["per"]:
            g[frozenset(segkeys(w, st["chosen"]))] += wt * c + wu
        return g

    cur_keys = set()
    if zprice:
        for key, price in walk_groups(st0).items():
            z = mdl.addVar(lb=0.0, obj=1.0)
            vs = [col[k] for k in key]
            mdl.addConstr(z >= (price / Q.scale) * (gp.quicksum(vs) - (len(vs) - 1)))
            priced[key] = (z, price / Q.scale)
            cur_keys.add(key)
        mdl.update()

    def cb2(model, where):
        """for a new solution: cut bad walks; cut cycles of chains; give unpriced walks a price variable; record
        the solution when it is the best of this round.  At a node: hand back a recorded solution whose walks
        have just been priced."""
        if where == GRB.Callback.MIPSOL:
            vals = model.cbGetSolution(varlist)
            vmap = {id(v): x for v, x in zip(varlist, vals)}
            sel = to_sel(lambda v: vmap[id(v)])
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
                    cuts_all.append(keys)
                return
            nch = Q.scale * sum(1 for (k, v), x in zip(allvars, vals) if x > 0.5 and k[0] in ("c", "d"))
            obj = st["Q"] + st["D"] + P * nch
            aon = []
            if arcvars:
                avals = model.cbGetSolution(arcvars)
                aon = [k for k, x in zip(arckeys, avals) if x > 0.5]
            if aon:
                chain_of = {}
                for (k, v), x in zip(allvars, vals):
                    if x > 0.5 and k[0] == "c":
                        for A in k[1:]:
                            chain_of[A] = k
                    elif x > 0.5 and k[0] == "d":
                        chain_of[k[1]] = k
                nx = {chain_of[e[0][0]]: (chain_of[e[1][0]], e) for e in aon}
                seen_c = set()
                cyc = False
                for k0 in list(nx):
                    if k0 in seen_c:
                        continue
                    path, k = [], k0
                    while k in nx and k not in seen_c:
                        seen_c.add(k)
                        path.append(nx[k][1])
                        k = nx[k][0]
                    if k == k0 and path:
                        model.cbLazy(gp.quicksum(arcv[e] for e in path) <= len(path) - 1)
                        arc_cuts.append(path)
                        cyc = True
                if cyc:
                    return
                obj += Q.scale * sum(arccost[k] - 1 - P for k in aon)
            groups = walk_groups(st)
            newc = 0
            if zprice:
                for key, price in groups.items():
                    if key in priced or key in newpriced or not spares:
                        continue
                    z = spares.pop()
                    vs = [col[k] for k in key]
                    model.cbLazy(z >= (price / Q.scale) * (gp.quicksum(vs) - (len(vs) - 1)))
                    newpriced[key] = (z, price / Q.scale)
                    newc += 1
            objB = obj + sum(groups.values())
            if objB < holder.get("objB", 1e18) - 1e-6:
                holder.update(obj=obj, objB=objB, vals={k: (1 if x > 0.5 else 0) for (k, v), x in zip(allvars, vals)}, sel=sel, st=st,
                              nch=nch, keys=set(groups), injected=(newc == 0), aon=set(aon))
        elif where == GRB.Callback.MIPNODE and zprice and holder and not holder.get("injected") and holder["objB"] < env_cur["B"] - 1e-6:
            # a solution that was refused only because its walks had no price yet: hand it back with the prices paid
            model.cbSetSolution(varlist, [holder["vals"][k] for k, v in allvars])
            zv, zx = [], []
            for key, (z, coef) in list(priced.items()) + list(newpriced.items()):
                zv.append(z)
                zx.append(coef if key in holder["keys"] else 0.0)
            for z in spares:
                zv.append(z)
                zx.append(0.0)
            model.cbSetSolution(zv, zx)
            if arcvars:
                model.cbSetSolution(arcvars, [1.0 if k in holder["aon"] else 0.0 for k in arckeys])
            model.cbUseSolution()
            holder["injected"] = True

    env_cur = {"B": curB}
    mdl.Params.OutputFlag = 0
    nadded = 0
    nadded_arc = 0
    txt = ""
    for it in range(nlns):
        if time.time() - t0 > tl:
            break
        kind, R = region()
        nfix = 0
        for key, var in allvars:
            if cur[key] and not any(A in R for A in loops_of[key]):
                var.LB = 1
                nfix += 1
            else:
                var.LB = 0
            var.Start = cur[key]
        for keys in cuts_all[nadded:]:
            vs = [col[k] for k in keys]
            mdl.addConstr(gp.quicksum(vs) <= len(vs) - 1)
        nadded = len(cuts_all)
        for path in arc_cuts[nadded_arc:]:
            mdl.addConstr(gp.quicksum(arcv[e] for e in path) <= len(path) - 1)
        nadded_arc = len(arc_cuts)
        for k, v in arcv.items():
            v.Start = 1 if k in cur_aon else 0
        if zprice:
            for key, (z, coef) in newpriced.items():
                vs = [col[k] for k in key]
                mdl.addConstr(z >= coef * (gp.quicksum(vs) - (len(vs) - 1)))
                priced[key] = (z, coef)
            newpriced.clear()
            while len(spares) < 80:
                spares.append(mdl.addVar(lb=0.0, obj=1.0))
            mdl.update()
            for key, (z, coef) in priced.items():
                z.Start = coef if key in cur_keys else 0.0
            for z in spares:
                z.Start = 0.0
        mdl.Params.TimeLimit = sub
        mdl.Params.Cutoff = ((curB if zprice else curobj) - 0.5) / Q.scale
        env_cur["B"] = curB
        holder.clear()
        mdl.optimize(cb2)
        msg = "it %d %s region %d fixed %d: status %d" % (it, kind, len(R), nfix, mdl.Status)
        if holder and holder["objB"] < curB - 1e-6:
            curobj = holder["obj"]
            curB = holder["objB"]
            cur = holder["vals"]
            cur_keys = holder["keys"]
            cur_aon = holder.get("aon", set())
            st = holder["st"]
            txt = "Q %d D %d chains %d walks %d trails %d floor %d obj %.1f objB %.1f | rows %s | %s" % (
                st["Q"], st["D"], holder["nch"], st["nwalks"], st["trails"], st["floor"], curobj, curB,
                dict(sorted(st["rows"].items(), reverse=True)), sorted(st["stat"].items(), reverse=True)[:4])
            print("%s | %s | joins between chains %d (x group order) | cuts %d priced walks %d | %.0fs" % (
                msg, txt, len(cur_aon), len(cuts_all), len(priced) + len(newpriced), time.time() - t0), flush=True)
            if out:
                write_gsel(out, holder["sel"], "%s: %s" % (tag, txt))
        elif verbose:
            print("%s no gain | %.0fs" % (msg, time.time() - t0), flush=True)
    print("best: %s" % txt)
