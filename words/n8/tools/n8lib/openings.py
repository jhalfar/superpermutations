"""The best word of a selection when every closed trail is written as one piece, opened anywhere.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

price.py writes whole slices in any order; a closed trail may then be opened only between two of its slices.
Here a closed trail is written in one piece, but the piece may start at any permutation window of the trail.

A closed trail read around is a cyclic word C (its slices, each without the 5 letters it shares with the next).
The piece opened at the permutation window s starts at s and runs once around C up to and including the last
permutation window before s.  If the window before s lies g letters before it (the weight g of the step into s),
the piece has |C| - g + 8 letters.  An opening between two slices has g = 3; inside a slice the steps have
weight 2 or 1.  The word is the pieces of all trails in some order, each joined to the previous one with the
largest overlap (up to 7 letters).

The programme: y[t, s] = 1 when trail t is opened at s (one opening per trail).  Leaving trail t, the word goes
to a hub (k, w) when its piece ends with the k letters w, and from the hub into a trail whose piece starts with
w; this saves k letters (k = 0 .. 7; k = 0 is one hub for any join).  A hub may be used by a trail only if the
chosen opening of the trail ends (or starts) with its letters.  A depot starts and ends the word.  The length is
the sum of the piece lengths minus the overlaps.  As in price.py, parts of a solution that are not connected to
the depot are cut away in a loop, and every programme of the loop gives a lower bound.

min_weight = 3 (the default) allows only the openings between slices, min_weight = 2 also the steps of weight 2
inside a slice, min_weight = 1 every window.  The windows that count are those inside one slice: a window
across two slices repeats a permutation of a slice, so a piece may leave it out.  With min_weight = 3 the words are
exactly the words of whole slices in which every closed trail is written in one run.
"""
import time

from . import milp
from . import model as M


class Trail:
    def __init__(self, cyc, strs):
        self.slices = cyc
        self.C = "".join(strs[i][:-5] for i in cyc)
        n = len(self.C)
        # the permutation windows that lie inside one slice; a window across two slices repeats a permutation
        # that a slice has as well, so a piece need not hold it
        win = []
        o = 0
        for i in cyc:
            s = strs[i]
            win += [(o + p) % n for p in range(len(s) - 7) if len(set(s[p:p + 8])) == 8]
            o += len(s) - 5
        win = sorted(set(win))
        self.starts = {}        # offset in C of the first letter of each slice -> its place in the trail
        o = 0
        for t, i in enumerate(cyc):
            self.starts[o] = t
            o += len(strs[i]) - 5
        self.openings = []      # (s, g, piece length)
        for a, s in enumerate(win):
            g = (s - win[a - 1]) % n if a else (s - win[-1]) % n
            self.openings.append((s, g, n - g + 8))

    def piece(self, s, g):
        R = self.C[s:] + self.C[:s]
        return (R + R[:8])[:len(self.C) - g + 8]


def price_openings(sel, min_weight=3, min_overlap=0, solver="highs", time_limit=None, threads=1, verbose=False,
                   log=None, cutoff=None):
    """min_overlap = m > 0: only joins of overlap m or more.  cutoff: stop as soon as the lower bound on J reaches
    this value (the result then has status "cutoff")."""
    t0 = time.time()
    say = log or (lambda *a: None)
    keys, strs = M.slices(sel)
    Q = M.q_of(sel)
    cycles, _ = M.trail_cycles(strs)
    trails = [Trail(c, strs) for c in cycles]
    T = len(trails)
    P = milp.Problem()
    y = []                        # y[t] = list of (var, s, g, start7, end7)
    base_piece = [len(tr.C) + 5 for tr in trails]   # costs are counted from |C| + 5, the piece of whole slices
    for t, tr in enumerate(trails):
        row = []
        for s, g, ln in tr.openings:
            if g < min_weight:
                continue
            pc = tr.piece(s, g)
            row.append((P.var(ln - base_piece[t]), s, g, pc[:7], pc[-7:]))
        y.append(row)
        P.row([r[0] for r in row], 1, 1, 1)
    # exits and entries through the hubs (k, w), k = 1..7
    exits, entries = {}, {}       # (t, k, w) -> list of y vars compatible
    for t, row in enumerate(y):
        for var, s, g, st, en in row:
            for k in range(max(1, min_overlap), 8):
                exits.setdefault((t, k, en[-k:]), []).append(var)
                entries.setdefault((t, k, st[:k]), []).append(var)
    hub_out = {}
    hub_in = {}
    for (t, k, w) in exits:
        hub_out.setdefault((k, w), []).append(t)
    for (t, k, w) in entries:
        hub_in.setdefault((k, w), []).append(t)
    hubs = [h for h in hub_out if h in hub_in and (len(set(hub_out[h]) | set(hub_in[h])) > 1)]
    hid = {h: T + i for i, h in enumerate(hubs)}
    H0 = T + len(hubs)
    D = H0 + 1
    nnodes = D + 1
    arcs = []                     # (tail, head, var)
    out_of = [[] for _ in range(T)]
    in_of = [[] for _ in range(T)]
    for h in hubs:
        k, w = h
        for t in sorted(set(hub_out[h])):
            v = P.var(-k)
            arcs.append((t, hid[h], v))
            out_of[t].append(v)
            P.row([v] + exits[(t, k, w)], [1] + [-1] * len(exits[(t, k, w)]), hi=0)
        for t in sorted(set(hub_in[h])):
            v = P.var(0)
            arcs.append((hid[h], t, v))
            in_of[t].append(v)
            P.row([v] + entries[(t, k, w)], [1] + [-1] * len(entries[(t, k, w)]), hi=0)
    for t in range(T):
        for tail, head, c in ((t, H0, 0), (H0, t, 0), (t, D, 0), (D, t, 0))[0 if min_overlap == 0 else 2:]:
            v = P.var(c)
            arcs.append((tail, head, v))
            (out_of[t] if tail == t else in_of[t]).append(v)
    for t in range(T):
        P.row(out_of[t], 1, 1, 1)
        P.row(in_of[t], 1, 1, 1)
    node_out = [[] for _ in range(nnodes)]
    node_in = [[] for _ in range(nnodes)]
    for tail, head, v in arcs:
        node_out[tail].append(v)
        node_in[head].append(v)
    for h in list(hid.values()) + [H0]:
        P.row(node_out[h] + node_in[h], [1] * len(node_out[h]) + [-1] * len(node_in[h]), 0, 0)
    P.row(node_out[D], 1, 1, 1)
    P.row(node_in[D], 1, 1, 1)

    def cut(U):
        P.row([v for tail, head, v in arcs if tail in U and head not in U], 1, 1)
        P.row([v for tail, head, v in arcs if head in U and tail not in U], 1, 1)

    nopen = sum(len(r) for r in y)
    say("model: %d closed trails, %d openings (steps of weight >= %d), %d hubs, %d variables" % (
        T, nopen, min_weight, len(hubs), P.nvars))
    base = M.BASE_LENGTH + Q - sum(base_piece)   # length = sum(base_piece) + objective
    bound = None
    best = None
    rounds = 0
    status = "error"
    closed = False
    while True:
        rounds += 1
        left = None if time_limit is None else max(1.0, time_limit - (time.time() - t0))
        res = milp.solve(P, solver, left, threads, verbose)
        if res.bound is not None:
            b = res.bound - base
            bound = b if bound is None else max(bound, b)
        if res.x is None:
            status = res.status
            say("round %d: %s after %.1f s, no solution" % (rounds, res.status, res.seconds))
            break
        used = [(tail, head) for tail, head, v in arcs if res.x[v] > 0.5]
        choice = {}
        for t, row in enumerate(y):
            for var, s, g, st, en in row:
                if res.x[var] > 0.5:
                    choice[t] = (s, g)
        comps = _components(nnodes, used)
        loose = [U for U in comps if D not in U]
        order = _trail_order(used, comps, D, T)
        pieces = [trails[t].piece(*choice[t]) for t in order]
        word, ovs = M.assemble(pieces, list(range(len(pieces))))
        J = len(word) - M.BASE_LENGTH - Q
        allowed = not ovs or min(ovs) >= min_overlap
        if allowed and (best is None or J < best[0]):
            best = (J, word, order, [choice[t] for t in order], ovs)
        say("round %d: %s after %.1f s, value %g, bound %s, %d parts not joined to the depot, word J = %s" % (
            rounds, res.status, res.seconds, res.obj - base, "-" if res.bound is None else "%g" % (
                res.bound - base), len(loose), J if allowed else "- (a join below the minimum overlap)"))
        if not loose:
            status = res.status
            closed = status == "optimal"
            break
        if bound is not None and best is not None and best[0] <= bound + 1e-6:
            status, closed = "optimal", True
            break
        if cutoff is not None and bound is not None and bound > cutoff - 1e-6:
            status = "cutoff"
            break
        if time_limit is not None and time.time() - t0 >= time_limit:
            status = "time_limit"
            break
        for U in loose:
            cut(U)
    lb = None
    if bound is not None:
        lb = int(round(bound)) if abs(bound - round(bound)) < 1e-6 else int(-(-bound // 1))
    if best is None:
        return None
    J, word, order, opened, ovs = best
    if closed:
        lb = J
    weights = [g for s, g in opened]
    # as a slice order, when every trail is opened between two slices
    slice_order, slice_ovs = [], []
    for n_, (t, (s, g)) in enumerate(zip(order, opened)):
        tr = trails[t]
        if s not in tr.starts:
            slice_order = None
            break
        a = tr.starts[s]
        if n_:
            slice_ovs.append(ovs[n_ - 1])
        slice_order += tr.slices[a:] + tr.slices[:a]
        slice_ovs += [5] * (len(tr.slices) - 1)
    if slice_order is not None:
        assert M.assemble(strs, slice_order, slice_ovs)[0] == word
    return {"word": word, "J": J, "bound": lb, "status": "optimal" if lb == J else status, "rounds": rounds,
            "seconds": time.time() - t0, "Q": Q, "trails": T, "order": order, "opened": opened, "overlaps": ovs,
            "weights": weights, "solver": solver, "min_weight": min_weight, "min_overlap": min_overlap,
            "pieces": [trails[t].piece(*o) for t, o in zip(order, opened)], "keys": keys, "strs": strs,
            "slice_order": slice_order, "slice_overlaps": slice_ovs if slice_order is not None else None}


def _components(nnodes, used):
    parent = list(range(nnodes))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for t, h in used:
        ra, rb = find(t), find(h)
        if ra != rb:
            parent[ra] = rb
    comp = {}
    for t, h in used:
        comp.setdefault(find(t), set()).update((t, h))
    return list(comp.values())


def _euler(start, out):
    adj = {u: list(reversed(v)) for u, v in out.items()}
    stack, circ = [start], []
    while stack:
        u = stack[-1]
        if adj.get(u):
            stack.append(adj[u].pop())
        else:
            circ.append(stack.pop())
    return circ[::-1]


def _trail_order(used, comps, D, T):
    """trails in the order of an Euler circuit from the depot through its part, then the other parts appended."""
    out = {}
    for t, h in sorted(used):
        out.setdefault(t, []).append(h)
    order = []
    for U in sorted(comps, key=lambda U: (D not in U, min(U))):
        start = D if D in U else min(u for u in U if u < T)
        circ = _euler(start, {u: out[u] for u in U if u in out})
        for u in circ:
            if u < T and u not in order:
                order.append(u)
    return order
