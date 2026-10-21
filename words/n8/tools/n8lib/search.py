"""Parallel tempering over selections, every candidate priced by the integer programme of openings.py.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

State: a balanced selection.  Energy: Q + J of its best word (openings.py, or price.py with model "slices"), so the
word has 46,085 + energy letters.

Move: a region of r loops (a breadth first ball in the graph "a row of one loop can lead to the other") is chosen
at random, every loop outside it keeps its option, and the region is solved again by a small programme (below)
with random noise on the costs of its options and the condition that the region must change.  The new selection
is priced and accepted by the Metropolis rule at the temperature of the chain.  Neighbouring chains swap
their selections now and then.  With one chain at a low temperature this is a large neighbourhood search.

The region programme (a cover of the loops by closed walks).  Variables: y[x, v] for every row of a free loop,
d[L] for "loop L has no row", and roots r[x, j] for the 5 strands j of a walk at state x.  Every loop takes one
option, every state has as many rows in as out, so the rows form closed walks.  The strands of a walk are
permuted by the port maps of its rows; each cycle of strands is one closed trail and must contain a root.  The
cost is (6 - v) per row (+1 for v = 5, whose row adds a closed trail of two slices), 1 per loop without a row and
1 per root: Q + T.  For words of whole slices Q + T - 1 is a lower bound on Q + J (T trails need T - 1 joins
of cost 1 or more), and the search skips a candidate whose Q + T - 1 is too high.
Cycles of strands without a root are cut away in a loop, as in price.py.
"""
import math
import os
import random
import time

from . import milp
from . import model as M
from . import openings as OP
from . import price as PR

SID = {x: i for i, x in enumerate(M.STATES)}
NBR = {L: set() for L in M.LOOPS}
for _x in M.STATES:
    for _v in M.VALUES:
        _L2 = M.canon(M.gstep(_x, _v))
        if _L2 != M.canon(_x):
            NBR[M.canon(_x)].add(_L2)
            NBR[_L2].add(M.canon(_x))


def region(r, rng, center=None):
    L0 = center if center is not None else rng.choice(M.LOOPS)
    out, seen, fr = [L0], {L0}, [L0]
    while len(out) < r and fr:
        u = fr.pop(0)
        nb = sorted(NBR[u] - seen)
        rng.shuffle(nb)
        for w in nb:
            if len(out) < r:
                out.append(w)
                seen.add(w)
                fr.append(w)
    return seen


def base_cost(v):
    return M.K - v + (1 if v == 5 else 0)


def floor_value(sel):
    """Q + T - 1, a lower bound on Q + J (every join costs at least 1)."""
    T = M.rowless(sel)
    for w in M.walks(sel):
        T += M.port_trails([v for x, v in w])
    return M.q_of(sel) + T - 1


def solve_region(cur, free, rng, sigma, solver="highs", time_limit=10, nogood=True):
    """re-solve the free loops of the selection cur with noise sigma on their costs; returns a selection or None."""
    P = milp.Problem()
    y = {}
    for L in free:
        for x in M.LOOP_STATES[L]:
            for v in M.VALUES:
                if M.canon(M.gstep(x, v)) != L:
                    y[x, v] = P.var(base_cost(v) + rng.gauss(0, sigma))
    d = {L: P.var(1 + rng.gauss(0, sigma)) for L in free}
    # fixed rows outside the region
    fixed = {x: v for L, (x, v) in cur.items() if L not in free and v}
    act = {}
    inn = {}
    for (x, v), var in y.items():
        act.setdefault(x, []).append(var)
        inn.setdefault(M.gstep(x, v), []).append(var)
    for L in free:
        P.row([y[x, v] for x in M.LOOP_STATES[L] for v in M.VALUES if (x, v) in y] + [d[L]], 1, 1, 1)
    fixed_in = {}
    for x, v in fixed.items():
        fixed_in[M.gstep(x, v)] = fixed_in.get(M.gstep(x, v), 0) + 1
    for x in M.STATES:
        a = act.get(x, [])
        i = inn.get(x, [])
        rhs = (1 if x in fixed else 0) - fixed_in.get(x, 0)
        if not a and not i:
            if rhs != 0:
                return None
            continue
        P.row(i + a, [1] * len(i) + [-1] * len(a), rhs, rhs)  # in - out = out_fixed - in_fixed
    # roots on the strands of states that can be active
    states = set(x for x, v in y) | set(fixed)
    r = {}
    for x in states:
        for j in range(M.K - 1):
            r[x, j] = P.var(1)
            if x not in fixed:      # a root only where a row starts
                P.row([r[x, j]] + act[x], [1] + [-1] * len(act[x]), hi=0)
    if nogood:
        keep = []
        for L in free:
            x, v = cur[L]
            keep.append(d[L] if not v else y.get((x, v)))
        keep = [k for k in keep if k is not None]
        P.row(keep, 1, hi=len(keep) - 1)
    t0 = time.time()
    while True:
        left = max(0.5, time_limit - (time.time() - t0))
        res = milp.solve(P, solver, left)
        if res.x is None:
            return None
        sel = {L: o for L, o in cur.items() if L not in free}
        for L in free:
            if res.x[d[L]] > 0.5:
                sel[L] = (L, 0)
        for (x, v), var in y.items():
            if res.x[var] > 0.5:
                sel[M.canon(x)] = (x, v)
        rows = {x: v for x, v in sel.values() if v}
        roots = {k for k, var in r.items() if res.x[var] > 0.5}
        nxt = {}
        for x, v in rows.items():
            g = M.gstep(x, v)
            for j in range(M.K - 1):
                nxt[x, j] = (g, M.PORT[v][j])
        seen = set()
        cuts = 0
        for p0 in sorted(nxt):
            if p0 in seen:
                continue
            cyc = []
            u = p0
            while u not in seen:
                seen.add(u)
                cyc.append(u)
                u = nxt[u]
            if any(p in roots for p in cyc):
                continue
            # this cycle of strands has no root: a root on it, or a row that leaves it, whenever it is there
            S = set(cyc)
            out = []
            for (x, j) in S:
                for v in M.VALUES:
                    if (x, v) in y and (M.gstep(x, v), M.PORT[v][j]) not in S:
                        out.append(y[x, v])
            x0 = cyc[0][0]
            lhs = [r[p] for p in S] + out
            if x0 in fixed:
                P.row(lhs, 1, lo=1)
            else:
                P.row(lhs + act[x0], [1] * len(lhs) + [-1] * len(act[x0]), lo=0)
            cuts += 1
        if cuts == 0 or time.time() - t0 > time_limit:
            return sel if M.balanced(sel) else None


class Priced:
    def __init__(self, **kw):
        self.__dict__.update(kw)


class Pricer:
    """Q + J of the best word of a selection, with a cache.  model "trails": openings.py (every trail in one run,
    opened at steps of weight >= min_weight); model "slices": price.py.  Words shorter than save_below letters are
    checked and written to outdir."""

    def __init__(self, solver, time_limit, outdir, save_below, log, model="trails", min_weight=3):
        self.cache = {}
        self.solver = solver
        self.time_limit = time_limit
        self.outdir = outdir
        self.save_below = save_below
        self.log = log
        self.model = model
        self.min_weight = min_weight
        self.calls = 0
        self.seconds = 0.0
        self.best = None

    def price(self, sel, cut=None):
        Q = M.q_of(sel)
        if self.model == "slices":
            p = PR.price(sel, solver=self.solver, time_limit=self.time_limit, cutoff=None if cut is None else cut - Q)
            if p.status == "cutoff":
                return Priced(word=None, J=None, bound=p.bound, status="cutoff", Q=Q)
            return Priced(word=p.word, J=p.J, bound=p.bound, status=p.status, Q=Q)
        o = OP.price_openings(sel, min_weight=self.min_weight, solver=self.solver, time_limit=self.time_limit,
                              cutoff=None if cut is None else cut - Q)
        if o is None:
            return Priced(word=None, J=None, bound=None, status="error", Q=Q)
        if o["status"] == "cutoff":
            return Priced(word=None, J=None, bound=o["bound"], status="cutoff", Q=Q)
        return Priced(word=o["word"], J=o["J"], bound=o["bound"], status=o["status"], Q=Q)

    def __call__(self, sel, cut=None):
        """Q + J, or None if it is >= cut."""
        key = tuple(sorted(sel.values()))
        if key in self.cache:
            e = self.cache[key]
            return e if (cut is None or e < cut) else None
        t0 = time.time()
        p = self.price(sel, cut)
        self.seconds += time.time() - t0
        self.calls += 1
        if p.word is None:          # no word, or none below the cut: remember the bound
            if p.bound is not None:
                self.cache[key] = max(p.Q + p.bound, cut if (cut is not None and p.status == "cutoff") else 0)
            return None
        e = p.Q + p.J
        self.cache[key] = e
        if len(p.word) < self.save_below:
            self.save(sel, p)
        if self.best is None or e < self.best[0]:
            self.best = (e, sel, p)
        return e if (cut is None or e < cut) else None

    def save(self, sel, p):
        import hashlib
        h = hashlib.sha256(p.word.encode()).hexdigest()
        os.makedirs(self.outdir, exist_ok=True)
        base = os.path.join(self.outdir, "%d-%s" % (len(p.word), h[:12]))
        if os.path.exists(base + ".txt"):
            return
        chk = M.check_word(p.word)
        with open(base + ".txt", "w", newline="\n") as f:
            f.write(p.word + "\n")
        M.write_selection(base + ".selection.txt", sel, [
            "found by n8.py search: length %d = 46,085 + Q %d + J %d, %s" % (len(p.word), p.Q, p.J, p.status),
            "SHA-256 of the word without line feed %s" % h])
        self.log("WORD %d letters (Q %d, J %d), missing permutations %d, deletable letters %s -> %s.txt" % (
            len(p.word), p.Q, p.J, chk["missing"], chk.get("deletable"), base))


def tempering(starts, pricer, temps, total, rng, rmin=12, rmax=50, sigma=None, swap_every=10, solver="highs",
              log=print, region_time=5.0):
    sig = sigma if sigma is not None else [0.5 * t for t in temps]
    n = len(temps)
    cur = [dict(starts[i % len(starts)]) for i in range(n)]
    E = []
    for s in cur:
        E.append(pricer(s))
    log("start: energies %s (word length 46,085 + energy)" % E)
    t0 = time.time()
    moves = 0
    acc = [0] * n
    tried = [0] * n
    while time.time() - t0 < total:
        for k in range(n):
            free = region(rng.randint(rmin, rmax), rng)
            sel = solve_region(cur[k], free, rng, sig[k], solver, region_time)
            tried[k] += 1
            if sel is None:
                continue
            u = rng.random()
            cut = int(math.floor(E[k] - temps[k] * math.log(max(u, 1e-300)))) + 1    # accept iff energy < cut
            if floor_value(sel) >= cut:
                continue
            e = pricer(sel, cut)
            if e is None:
                continue
            cur[k], E[k] = sel, e
            acc[k] += 1
            if time.time() - t0 >= total:
                break
        moves += 1
        if moves % swap_every == 0 and n > 1:
            i = rng.randrange(n - 1)
            dl = (1 / temps[i] - 1 / temps[i + 1]) * (E[i] - E[i + 1])
            if dl >= 0 or rng.random() < math.exp(dl):
                cur[i], cur[i + 1] = cur[i + 1], cur[i]
                E[i], E[i + 1] = E[i + 1], E[i]
        log("move %d, %.0f s: energies %s, accepted %s, best %s, pricings %d (%.0f s)" % (
            moves, time.time() - t0, E, ["%d/%d" % (a, b) for a, b in zip(acc, tried)],
            pricer.best[0] if pricer.best else None, pricer.calls, pricer.seconds))
    return cur, E
