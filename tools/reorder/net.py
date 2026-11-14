"""net.py: persistent exact solver of the maximum-overlap order of word pieces (maximum-weight path cover), used by
cutlns2.py.  Same model as the solve() of the first version (cutlns.py, not published), kept in one Gurobi LP across rounds so that a round only changes the
pieces it splits or merges and re-solves from the previous basis.

Model.  Vertices: piece slots (a slot is a piece (ps, pe) of the word; slots are switched on and off, never deleted),
nodes (one per pair (k, string of k letters) that is a suffix of some slot's last n-1 letters or a prefix of some
slot's first n-1 letters) and the hub H.  Columns of slot i: A_k end(i) -> node(suffix_k) weight k, B_k
node(prefix_k) -> start(i) weight 0 (k = 1 .. n-1), C end(i) -> H, D H -> start(i).  Rows: out of end(i) = 1, into
start(i) = 1 (both 0 when the slot is off, its columns then have upper bound 0), node rows in = out.
Subtour cuts: for a vertex set X without H, the columns leaving X sum to >= 1 (valid for every order whenever X holds
a slot that is on; the right-hand side is 0 when it holds none).  When a slot is added later, its B columns from
nodes in X are added to the cut, so every cut stays exactly "flow out of X >= 1"."""
import time
import numpy as np
import scipy.sparse as sp
from scipy.sparse.csgraph import connected_components
import gurobipy as gp
from gurobipy import GRB


class Net:
    def __init__(self, n, env, threads=2, miptime=60, lpit=40, log=None, fthr=(0.3, 0.5, 0.7), stallmax=0,
                 mipparams=(), k0=4):
        self.fthr = fthr; self.stallmax = stallmax; self.mipparams = [p for p in mipparams if p]
        self.n = n; self.m_ = n - 1
        self.SH = [4 * (self.m_ - k) for k in range(n)]
        self.MK = [(1 << (4 * k)) - 1 for k in range(n)]
        self.env = env; self.threads = threads; self.miptime = miptime; self.lpit = lpit; self.log = log
        md = gp.Model(env=env)
        md.Params.Threads = threads; md.Params.Method = 1; md.Params.Presolve = 0
        md.ModelSense = GRB.MAXIMIZE
        self.md = md
        self.slot = {}; self.skey = []; self.act = []; self.S = []; self.E = []
        self.rend = []; self.rst = []; self.scols = []; self.sA = []; self.sB = []; self.scut = []
        self.node = {}; self.nrow = []; self.nB = []; self.ncut = []
        self.vars = []; self.tail = []; self.head = []; self.obj = []
        self.cuts = []; self.cslots = []; self.cnodes = []; self.cact = []
        self.nact = 0
        self.k0 = min(k0, n); self.pre = [dict() for _ in range(n)]; self.suf = [dict() for _ in range(n)]
        self.sC = []; self.sD = []; self.sDo = []; self.darc = {}

    # vertex code: slot s -> 2s, node t -> 2t+1, hub -> -1
    def _node(self, code):
        t = self.node.get(code)
        if t is None:
            t = len(self.nrow); self.node[code] = t
            self.nrow.append(self.md.addLConstr(gp.LinExpr(), GRB.EQUAL, 0.0))
            self.nB.append([]); self.ncut.append([])
        return t

    def add(self, key, S, E):
        """switch on the slot of piece key = (ps, pe) with first/last n-1 letters S, E (packed); returns its id.
        Overlaps k < k0 go through nodes, overlaps >= k0 are direct arcs end(i) -> start(j) (i != j) of weight
        the largest such overlap."""
        s = self.slot.get(key)
        if s is not None:
            if not self.act[s]: self._on(s)
            return s
        s = len(self.skey); self.slot[key] = s; self.skey.append(key); self.act.append(True)
        self.S.append(S); self.E.append(E); self.nact += 1
        md = self.md; k0 = self.k0
        re = md.addLConstr(gp.LinExpr(), GRB.EQUAL, 1.0); rs = md.addLConstr(gp.LinExpr(), GRB.EQUAL, 1.0)
        self.rend.append(re); self.rst.append(rs); self.scut.append([])
        cols = []; Acol = []; Bcol = []
        self.scols.append(cols); self.sA.append(Acol); self.sB.append(Bcol); self.sDo.append([])
        newv = []
        for k in range(1, k0):
            t = self._node((k << 52) | (E & self.MK[k]))
            newv.append((k, gp.Column([1.0, 1.0], [re, self.nrow[t]]), 2 * s, 2 * t + 1, "A", t))
            t2 = self._node((k << 52) | (S >> self.SH[k]))
            cc = [self.cuts[c] for c in self.ncut[t2]]
            newv.append((0, gp.Column([1.0, -1.0] + [1.0] * len(cc), [rs, self.nrow[t2]] + cc), 2 * t2 + 1, 2 * s,
                         "B", t2))
        newv.append((0, gp.Column([1.0], [re]), 2 * s, -1, "C", 0))
        newv.append((0, gp.Column([1.0], [rs]), -1, 2 * s, "D", 0))
        # direct arcs
        outk = {}; ink = {}
        for k in range(k0, self.n):
            for j in self.pre[k].get(E & self.MK[k], ()): outk[j] = k
            for i in self.suf[k].get(S >> self.SH[k], ()): ink[i] = k
        for k in range(k0, self.n):
            self.pre[k].setdefault(S >> self.SH[k], []).append(s)
            self.suf[k].setdefault(E & self.MK[k], []).append(s)
        for j, k in outk.items():
            newv.append((k, gp.Column([1.0, 1.0], [re, self.rst[j]]), 2 * s, 2 * j, "Do", j))
        for i, k in ink.items():
            cc = [self.cuts[c] for c in self.scut[i]]
            newv.append((k, gp.Column([1.0, 1.0] + [1.0] * len(cc), [self.rend[i], rs] + cc), 2 * i, 2 * s, "Di", i))
        for ob, col, ta, he, kind, aux in newv:
            v = md.addVar(lb=0.0, ub=1.0, obj=float(ob), column=col)
            j = len(self.vars); self.vars.append(v); self.tail.append(ta); self.head.append(he); self.obj.append(ob)
            cols.append(j)
            if kind == "A": Acol.append(j)
            elif kind == "B": Bcol.append(j); self.nB[aux].append(j)
            elif kind == "C": self.sC.append(j)
            elif kind == "D": self.sD.append(j)
            elif kind == "Do": self.sDo[s].append(j); self.scols[aux].append(j); self.darc[(s, aux)] = j
            else: self.sDo[aux].append(j); self.scols[aux].append(j); self.darc[(aux, s)] = j
        return s

    def _on(self, s):
        self.act[s] = True; self.nact += 1
        vs = [self.vars[j] for j in self.scols[s]]
        self.md.setAttr("UB", vs, [1.0] * len(vs))
        self.rend[s].RHS = 1.0; self.rst[s].RHS = 1.0
        for c in self.scut[s]:
            self.cact[c] += 1
            if self.cact[c] == 1: self.cuts[c].RHS = 1.0

    def off(self, s):
        if not self.act[s]: return
        self.act[s] = False; self.nact -= 1
        vs = [self.vars[j] for j in self.scols[s]]
        self.md.setAttr("UB", vs, [0.0] * len(vs))
        self.rend[s].RHS = 0.0; self.rst[s].RHS = 0.0
        for c in self.scut[s]:
            self.cact[c] -= 1
            if self.cact[c] == 0: self.cuts[c].RHS = 0.0

    def _addcut(self, slots, nodes):
        Xs = set(slots); Xn = set(nodes)
        cols = self._cutcols(Xs, Xn)
        na = sum(1 for s in Xs if self.act[s])
        c = self.md.addLConstr(gp.LinExpr([1.0] * len(cols), [self.vars[j] for j in cols]), GRB.GREATER_EQUAL,
                               1.0 if na else 0.0)
        cid = len(self.cuts); self.cuts.append(c); self.cslots.append(list(Xs)); self.cnodes.append(list(Xn))
        self.cact.append(na)
        for s in Xs: self.scut[s].append(cid)
        for t in Xn: self.ncut[t].append(cid)

    def _comps(self, val, thr=1e-6):
        """components of the arcs with x > thr that miss the hub and hold a slot, and whose outflow (all arcs) is
        < 1 (always true for thr ~ 0): list of (slots, nodes)."""
        if len(self.tail) != getattr(self, "_nt", -1):
            self._tl = np.asarray(self.tail); self._hd = np.asarray(self.head); self._nt = len(self.tail)
        tl = self._tl; hd = self._hd
        V = 2 * max(len(self.skey), len(self.nrow)) + 2; H = V - 1
        on = val > thr
        a = np.where(tl[on] < 0, H, tl[on]); b = np.where(hd[on] < 0, H, hd[on])
        g = sp.coo_matrix((np.ones(len(a)), (a, b)), shape=(V, V))
        nk, lab = connected_components(g, directed=False)
        used = np.zeros(V, bool); used[a] = True; used[b] = True
        hl = lab[H]
        out = []
        sl = np.flatnonzero(np.asarray(self.act))
        cs = np.unique(lab[2 * sl])
        cs = cs[cs != hl]
        if len(cs) == 0: return out
        vv = np.flatnonzero(np.isin(lab, cs) & used)
        order = np.argsort(lab[vv], kind="stable"); vv = vv[order]; lv = lab[vv]
        brk = np.flatnonzero(np.diff(lv)) + 1
        for grp in np.split(vv, brk):
            out.append(([int(v // 2) for v in grp if v % 2 == 0], [int(v // 2) for v in grp if v % 2 == 1]))
        out = [o for o in out if o[0]]
        if thr > 1e-5:
            keep = []
            for sl, nd in out:
                if val[self._cutcols(sl, nd)].sum() < 1 - 1e-4: keep.append((sl, nd))
            out = keep
        return out

    def solve(self, warm, noise=0.0, rng=None):
        """warm: the current order as a list of slot ids (all slots that are on).  Returns (order of slot ids,
        overlap, info).  noise > 0: every arc of positive weight gets + uniform [0, noise) for this solve (ties
        break differently); the LP-bound shortcut and the MIP cutoff are off, the caller judges the true length."""
        if noise > 0:
            ob0 = np.asarray(self.obj, dtype=float)
            pos = np.flatnonzero(ob0 > 0)
            nz = ob0.copy(); nz[pos] += rng.random(len(pos)) * noise
            self.md.setAttr("Obj", self.vars, nz.tolist())
        try:
            return self._solve(warm, noise)
        finally:
            if noise > 0: self.md.setAttr("Obj", self.vars, ob0.tolist())

    def _solve(self, warm, noise):
        md = self.md; t0 = time.time(); it = 0; ncut = 0; capped = False; prev = None; lpi = []; self.stall = 0
        while True:
            md.optimize(); lpi.append((int(md.IterCount), round(md.Runtime, 2)))
            if md.Status != GRB.OPTIMAL: raise RuntimeError(f"LP status {md.Status}")
            it += 1
            val = np.asarray(md.getAttr("X", self.vars))
            ob = md.ObjVal
            frac = np.abs(val - np.round(val)).max()
            if prev is not None and ob > prev - 1e-6 and frac > 1e-6:
                self.stall += 1
                if self.stall > self.stallmax: capped = True; break
            else: self.stall = 0
            prev = ob
            bad = self._comps(val)
            if not bad and frac > 1e-6:
                for thr in self.fthr:
                    bad = self._comps(val, thr)
                    if bad: break
            if not bad: break
            for sl, nd in bad: self._addcut(sl, nd); ncut += 1
            if it >= self.lpit: capped = True; break
        tlp = time.time() - t0
        status = "lp"
        Sw = np.asarray([self.S[q] for q in warm], np.int64); Ew = np.asarray([self.E[q] for q in warm], np.int64)
        cur = int(ovl(Ew[:-1], Sw[1:], self.n, self.MK, self.SH).sum())
        keepwarm = False
        if (frac > 1e-6 or capped) and noise == 0 and np.floor(md.ObjVal + 1e-6) <= cur:
            status = "lpbound"; keepwarm = True   # the LP bound proves that no order beats the current one
        elif frac > 1e-6 or capped:
            status = "mip"
            cp = md.copy()
            cv = cp.getVars()
            cp.setAttr("VType", cv, [GRB.BINARY] * len(cv))
            cp.Params.LazyConstraints = 1; cp.Params.TimeLimit = self.miptime; cp.Params.MIPGap = 0
            cp.Params.Presolve = -1; cp.Params.Method = -1; cp.Params.Cutoff = cur + 0.5 if noise == 0 else -GRB.INFINITY
            for kv in self.mipparams:
                k_, v_ = kv.split("="); cp.setParam(k_, float(v_) if "." in v_ else int(v_))
            if noise > 0: cp.setAttr("Start", cv, self._start(warm).tolist())
            lc = [0]; lazy = []

            def cb(model, where):
                if where != GRB.Callback.MIPSOL: return
                v = np.asarray(model.cbGetSolution(cv))
                for sl, nd in self._comps(v, 0.5):  # integer solution: support = x > 0.5 (values within IntFeasTol must not hide a subtour)
                    cols = self._cutcols(sl, nd); lazy.append((sl, nd))
                    model.cbLazy(gp.LinExpr([1.0] * len(cols), [cv[j] for j in cols]) >= 1); lc[0] += 1

            cp.optimize(cb); self.mipinfo = (round(cp.Runtime, 2), int(cp.NodeCount))
            ncut += lc[0]
            if cp.SolCount == 0:
                keepwarm = True
                status = "mip_nobetter" if cp.Status in (GRB.CUTOFF, GRB.INFEASIBLE, GRB.OPTIMAL) else f"mip_{cp.Status}_none"
            else:
                val = np.asarray(cp.getAttr("X", cv))
                status = "mip_opt" if cp.Status == GRB.OPTIMAL else f"mip_{cp.Status}_gap{cp.MIPGap:.1e}"
            cp.dispose()
            for sl, nd in lazy: self._addcut(sl, nd)
        if keepwarm:
            return list(warm), float(cur), dict(P=self.nact, it=it, cuts=ncut, st=status, tlp=round(tlp, 2),
                                               tsolve=round(time.time() - t0, 2), lpi=lpi, bound=round(md.ObjVal, 2),
                                               cur=cur, mip=getattr(self, 'mipinfo', None) if status != 'lpbound' else None,
                                               ncuts=len(self.cuts), slots=len(self.skey))
        objv = float(np.asarray(self.obj) @ np.round(val))
        try:
            order = self._euler(val)
        except RuntimeError as e:   # keep the current order (feasible) and say so
            order = list(warm); status = f"euler_fail({e})"
        return order, objv, dict(P=self.nact, it=it, cuts=ncut, st=status, tlp=round(tlp, 2),
                                 tsolve=round(time.time() - t0, 2), lpi=lpi, mip=getattr(self, 'mipinfo', None) if status != 'lp' else None, ncuts=len(self.cuts), slots=len(self.skey))

    def _cutcols(self, slots, nodes):
        Xs = set(slots); Xn = set(nodes); cols = []
        hd = self.head
        for s in Xs:
            for j in self.sA[s]:
                if (hd[j] - 1) // 2 not in Xn: cols.append(j)
            for j in self.sDo[s]:
                if hd[j] // 2 not in Xs: cols.append(j)
            cols.append(self.sC[s])
        for t in Xn:
            for j in self.nB[t]:
                if hd[j] // 2 not in Xs: cols.append(j)
        return cols

    def _start(self, warm):
        w = np.zeros(len(self.vars))
        S = np.asarray([self.S[s] for s in warm], np.int64); E = np.asarray([self.E[s] for s in warm], np.int64)
        o = ovl(E[:-1], S[1:], self.n, self.MK, self.SH)
        for q in range(len(warm) - 1):
            a, b, k = warm[q], warm[q + 1], int(o[q])
            if k >= self.k0: w[self.darc[(a, b)]] = 1
            elif k > 0: w[self.sA[a][k - 1]] = 1; w[self.sB[b][k - 1]] = 1
            else: w[self.sC[a]] = 1; w[self.sD[b]] = 1
        w[self.sD[warm[0]]] = 1; w[self.sC[warm[-1]]] = 1
        return w

    def _euler(self, val):
        on = np.flatnonzero(val > 0.5)
        tl = self.tail; hd = self.head
        out = {}
        for j in on: out.setdefault(tl[j], []).append(hd[j])
        stack = [-1]; circ = []
        while stack:
            v = stack[-1]
            lst = out.get(v)
            if lst: stack.append(lst.pop())
            else: circ.append(stack.pop())
        circ.reverse()
        order = [v // 2 for v in circ if v >= 0 and v % 2 == 0]
        if len(order) != self.nact or len(set(order)) != self.nact or not all(self.act[s] for s in order):
            raise RuntimeError(f"circuit: {len(order)} slots, {self.nact} on")
        return order


def ovl(E, S, n, MK, SH):
    r = np.zeros(len(E), np.int64)
    for k in range(1, n):
        r = np.where((E & MK[k]) == (S >> SH[k]), k, r)
    return r
