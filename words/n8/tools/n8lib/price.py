"""The best word of a selection: the shortest word that writes every slice of the selection once.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

The word writes the 720 + Q slices in some order, each joined to the previous one with the largest overlap ov of
the two (0 .. 5 letters), and has 46,085 + Q + J letters, J = sum of (5 - ov).  The best order is the solution of
an asymmetric travelling salesman problem on the slices, which this module solves exactly as an integer programme.

The programme.  There is one 0/1 variable for every ordered pair of slices with an overlap of at least 1 letter,
at cost 5 - ov, and two for every slice: "a segment starts here" (cost 0) and "a segment ends here" (cost 5).
A segment is a run of slices joined with overlap 1 or more; two segments are joined with overlap 0, which costs 5.
Every slice has one way in and one way out.  J = (cost of the solution) - 5.  The pair variables alone allow sets
of slices that close into cycles; a cut for each such set U (at least one pair leaves U or one segment ends in U)
removes them (and the same with "enters U" and "starts in U").  First the linear relaxation is solved a few times,
with cuts found by minimum cuts.  Then the cuts are added in a loop: solve, find the cycles of the solution, add a
cut for each cycle and for the closed trails it touches, solve again.  Every programme of the loop is a relaxation
of the problem, so its optimum (or the solver's lower bound) is a lower bound on J.  The loop stops when the
solution has no cycle, which is then optimal, or when the cycles can be put into the word at no extra cost, so
that the word reaches the lower bound.

With min_overlap = m > 0 only pairs with overlap m or more get a variable and the word is one segment.
"""
import time

from . import milp
from . import model as M


class Pricing:
    """result of price(): word, J, bound, status, solver, order (slice indices), overlaps, keys, strs, ..."""

    def __init__(self, **kw):
        self.__dict__.update(kw)


def overlap_pairs(strs, kmin):
    """{(i, j): ov} for all ordered pairs of different slices with largest overlap ov >= kmin (kmin >= 1)."""
    pre = {}
    for j, s in enumerate(strs):
        for k in range(kmin, 8):
            pre.setdefault((k, s[:k]), []).append(j)
    ov = {}
    for i, s in enumerate(strs):
        for k in range(7, kmin - 1, -1):
            for j in pre.get((k, s[-k:]), ()):
                if j != i and (i, j) not in ov:
                    ov[i, j] = k
    return ov


def _cycles(succ):
    """succ: dict slice -> next slice (None at a segment end).  Returns (segments, cycles) as lists of slices."""
    pred = {j: i for i, j in succ.items() if j is not None}
    segs, cycs, seen = [], [], set()
    for s in sorted(succ):
        if s in pred or s in seen:
            continue
        seg = []
        u = s
        while u is not None:
            seen.add(u)
            seg.append(u)
            u = succ[u]
        segs.append(seg)
    for s in sorted(succ):
        if s in seen:
            continue
        c = []
        u = s
        while u not in seen:
            seen.add(u)
            c.append(u)
            u = succ[u]
        cycs.append(c)
    return segs, cycs


def _min_cuts(N, pair, seg_end, x, scale=10 ** 6):
    """sets U of slices whose way out in the fractional solution x is less than 1: for each slice t, the minimum
    cut between t and the depot (node N) in the graph with capacities x; t is skipped when it already lies in a
    set found in this round."""
    import numpy as np
    from scipy.sparse import csr_matrix
    from scipy.sparse.csgraph import breadth_first_order, maximum_flow
    rows, cols, cap = [], [], []
    for (i, j), v in pair.items():
        c = int(x[v] * scale)
        if c > 0:
            rows.append(i)
            cols.append(j)
            cap.append(c)
    for i in range(N):
        c = int(x[seg_end[i]] * scale)
        if c > 0:
            rows.append(i)
            cols.append(N)
            cap.append(c)
    G = csr_matrix((np.array(cap, dtype=np.int32), (rows, cols)), shape=(N + 1, N + 1))
    G.sum_duplicates()
    found = []
    covered = np.zeros(N + 1, dtype=bool)
    for t in range(N):
        if covered[t]:
            continue
        f = maximum_flow(G, t, N)
        if f.flow_value >= scale - 1000:
            continue
        # residual graph (the flow matrix is skew-symmetric): arcs with capacity left
        Rg = (G - f.flow).tocsr()
        Rg.data = (Rg.data > 0).astype(np.int8)
        Rg.eliminate_zeros()
        reach = breadth_first_order(Rg, t, directed=True, return_predecessors=False)
        U = [u for u in reach if u < N]
        if N in set(reach.tolist()) or not U:
            continue
        covered[U] = True
        found.append(U)
    return found


def price(sel, min_overlap=0, solver="highs", time_limit=None, threads=1, verbose=False, log=None, cutoff=None,
          lp_rounds=30):
    """cutoff: stop as soon as the lower bound on J reaches this value (the caller only wants shorter words).
    lp_rounds: rounds of cuts on the linear relaxation before the integer rounds."""
    t0 = time.time()
    say = log or (lambda *a: None)
    keys, strs = M.slices(sel)
    N = len(strs)
    Q = M.q_of(sel)
    trails, _ = M.trail_cycles(strs)
    trail_of = [0] * N
    for t, c in enumerate(trails):
        for i in c:
            trail_of[i] = t
    ov = overlap_pairs(strs, max(1, min_overlap))
    P = milp.Problem()
    pair = {}
    out_v = [[] for _ in range(N)]
    in_v = [[] for _ in range(N)]
    for (i, j), k in sorted(ov.items()):
        v = P.var(5 - k)
        pair[i, j] = v
        out_v[i].append(v)
        in_v[j].append(v)
    seg_start = [P.var(0) for _ in range(N)]
    seg_end = [P.var(5) for _ in range(N)]
    for i in range(N):
        P.row(out_v[i] + [seg_end[i]], 1, 1, 1)
        P.row(in_v[i] + [seg_start[i]], 1, 1, 1)
    if min_overlap == 0:
        P.row(seg_end, 1, 1)                  # at least one segment
    else:
        P.row(seg_end, 1, 1, 1)               # exactly one
    P.row(seg_end + seg_start, [1] * N + [-1] * N, 0, 0)

    out_pairs = [[] for _ in range(N)]
    in_pairs = [[] for _ in range(N)]
    for (i, j), v in pair.items():
        out_pairs[i].append((j, v))
        in_pairs[j].append((i, v))

    def cut(U):
        """a set U of slices needs a way out (a pair that leaves U, or a segment end in U) and a way in."""
        U = set(U)
        P.row([v for i in U for j, v in out_pairs[i] if j not in U] + [seg_end[i] for i in U], 1, 1)
        P.row([v for j in U for i, v in in_pairs[j] if i not in U] + [seg_start[j] for j in U], 1, 1)

    for c in trails:                          # every closed trail needs a way out and a way in
        cut(c)
    say("model: %d slices, %d closed trails, Q %d, %d pairs with overlap >= %d, %d variables" % (
        N, len(trails), Q, len(pair), max(1, min_overlap), P.nvars))
    # cuts on the linear relaxation: sets of slices that the fractional solution connects only among themselves
    for it in range(lp_rounds):
        res = milp.solve(P, solver, None if time_limit is None else max(1.0, time_limit - (time.time() - t0)),
                         threads, verbose, relax=True)
        if res.x is None:
            break
        new = 0
        for U in _min_cuts(N, pair, seg_end, res.x):
            cut(U)
            new += 1
        say("relaxation %d: value %.2f, %d new cuts" % (it + 1, res.obj - 5, new))
        if not new:
            break
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
            b = res.bound - 5
            bound = b if bound is None else max(bound, b)
        if res.x is None:
            status = res.status
            say("round %d: %s after %.1f s, no solution" % (rounds, res.status, res.seconds))
            break
        succ = {i: None for i in range(N)}
        for (i, j), v in pair.items():
            if res.x[v] > 0.5:
                succ[i] = j
        segs, cycs = _cycles(succ)
        order = _order(segs, cycs, ov, min_overlap > 0)
        word, ovs = M.assemble(strs, order)
        J = len(word) - M.BASE_LENGTH - Q
        allowed = min(ovs) >= min_overlap
        if allowed and (best is None or J < best[0]):
            best = (J, order, word, ovs)
        say("round %d: %s after %.1f s, value %g, bound %s, cycles %s, word J = %s" % (
            rounds, res.status, res.seconds, res.obj - 5, "-" if res.bound is None else "%g" % (res.bound - 5),
            sorted(len(c) for c in cycs) or "none", J if allowed else "- (a join below the minimum overlap)"))
        if not cycs:
            status = res.status
            closed = status == "optimal"
            break
        if bound is not None and best is not None and best[0] <= bound + 1e-6:
            # the word made by opening the cycles is as short as the lower bound: it is optimal
            status = "optimal"
            closed = True
            break
        if cutoff is not None and bound is not None and bound > cutoff - 1e-6:
            status = "cutoff"
            break
        if time_limit is not None and time.time() - t0 >= time_limit:
            status = "time_limit"
            break
        done = set()
        for c in cycs:
            # the cycle itself, and the set of all slices of the closed trails it touches
            for U in (frozenset(c), frozenset(i for t in {trail_of[i] for i in c} for i in trails[t])):
                if U not in done and len(U) < N:
                    done.add(U)
                    cut(U)
    lb = None
    if bound is not None:   # J is an integer, so the bound can be rounded up (with a tolerance for the solver)
        lb = int(round(bound)) if abs(bound - round(bound)) < 1e-6 else int(-(-bound // 1))
    if best is None:
        return Pricing(word=None, J=None, bound=lb, status=status, solver=solver, rounds=rounds, Q=Q,
                       seconds=time.time() - t0, keys=keys, strs=strs, trails=len(trails), min_overlap=min_overlap)
    J, order, word, ovs = best
    if closed:          # the last programme was solved to optimality and its solution has no cycle
        lb = J
    return Pricing(word=word, J=J, bound=lb, status="optimal" if lb == J else status, solver=solver,
                   rounds=rounds, seconds=time.time() - t0, Q=Q, keys=keys, strs=strs, order=order,
                   overlaps=ovs, trails=len(trails), min_overlap=min_overlap)


def _order(segs, cycs, ov, strict):
    """a word from a solution with cycles: the segments in the order found, then each cycle (largest first) opened
    at one join and put between two neighbours of the order so far, at the place that costs least.  strict: joins
    that are not in ov are not allowed (they cost 100)."""
    def cost(a, b):
        k = ov.get((a, b))
        return 5 - k if k is not None else (100 if strict else 5)

    order = [u for s in segs for u in s]
    for c in sorted(cycs, key=len, reverse=True):
        m = len(c)
        best = None
        for t in range(m):
            first, last = c[t], c[t - 1]
            inner = -cost(last, first)          # the join that is opened
            for p in range(len(order) + 1):
                a = order[p - 1] if p > 0 else None
                b = order[p] if p < len(order) else None
                d = inner + (cost(a, first) if a is not None else 0) + (cost(last, b) if b is not None else 0)
                if a is not None and b is not None:
                    d -= cost(a, b)
                if best is None or d < best[0]:
                    best = (d, t, p)
        d, t, p = best
        order = order[:p] + c[t:] + c[:t] + order[p:]
    return order


def write_order(path, keys, order, overlaps, comments=()):
    """order file: one slice per line, "loop name overlap" (the overlap with the previous slice; 0 on line one)."""
    with open(path, "w", newline="\n") as f:
        for c in list(comments) + [
                "one slice per line: its loop, its name (i0..i5, r0..r5 as in n8lib/model.py) and the overlap with",
                "the slice before it; n8.py rebuild SELECTION --order THIS -o WORD writes the word"]:
            f.write("# %s\n" % c)
        for t, i in enumerate(order):
            L, name = keys[i]
            f.write("%s %s %d\n" % (M.fmt(L), name, overlaps[t - 1] if t else 0))


def read_order(path, sel):
    """returns (order as slice indices, overlaps or None, keys, strs)."""
    keys, strs = M.slices(sel)
    index = {(M.fmt(L), name): i for i, (L, name) in enumerate(keys)}
    order, ovs = [], []
    with open(path) as f:
        for no, line in enumerate(f, 1):
            line = line.split("#")[0].split()
            if not line:
                continue
            i = index.get((line[0], line[1]))
            if i is None:
                raise ValueError("%s:%d: %s %s is not a slice of the selection" % (path, no, line[0], line[1]))
            order.append(i)
            ovs.append(int(line[2]) if len(line) > 2 else None)
    if sorted(order) != list(range(len(strs))):
        raise ValueError("%s: the order must list every slice of the selection once (%d lines, %d slices)" % (
            path, len(order), len(strs)))
    ovs = ovs[1:]
    if any(o is None for o in ovs):
        ovs = None
    return order, ovs, keys, strs
