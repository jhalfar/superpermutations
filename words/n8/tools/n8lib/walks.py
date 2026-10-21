"""Closed walks of rows, up to relabelling of the letters 0..5, and their placements.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

A closed walk is a cyclic sequence of rows (x_1, v_1), ..., (x_L, v_L) with x_{t+1} = gstep(x_t, v_t), that visits
L different loops and returns to x_1.  Relabelling 0..5 maps walks to walks and can move any state to 012345, so a
walk type is the cyclic sequence of its row lengths v, read from a walk through 012345.  The search goes depth
first from 012345 and keeps the walks with Q <= max_q and L <= max_loops; a type is printed once, as its smallest
rotation.  It prunes with two tables computed in advance: the fewest rows and the least Q needed to get back to
012345 from each state (ignoring the condition that the loops differ).

The cost of a walk type in a selection is Q + T: its rows cost Q letters and its T closed trails need at least T
joins.  A rowless loop costs at least 1 (it is a trail of its own).  So the types with a small ratio (Q + T) / L
are the ones that can make a short word.
"""
import heapq
import time

from . import model as M

IDENT = tuple(range(M.K))
SID = {x: i for i, x in enumerate(M.STATES)}
LOOP_ID = [M.LOOPS.index(M.canon(x)) for x in M.STATES]


def _tables(vs):
    step = [[SID[M.gstep(x, v)] for v in vs] for x in M.STATES]
    back = [[] for _ in M.STATES]         # reverse arcs
    for s, row in enumerate(step):
        for k, t in enumerate(row):
            back[t].append((s, M.K - vs[k]))
    n = len(M.STATES)
    hops = [None] * n
    qmin = [None] * n
    z = SID[IDENT]
    # fewest rows back to the identity (BFS on reverse arcs)
    hops[z] = 0
    fr = [z]
    while fr:
        nf = []
        for t in fr:
            for s, c in back[t]:
                if hops[s] is None:
                    hops[s] = hops[t] + 1
                    nf.append(s)
        fr = nf
    # least Q back to the identity (Dijkstra on reverse arcs)
    qmin[z] = 0
    hq = [(0, z)]
    while hq:
        d, t = heapq.heappop(hq)
        if d > qmin[t]:
            continue
        for s, c in back[t]:
            if qmin[s] is None or d + c < qmin[s]:
                qmin[s] = d + c
                heapq.heappush(hq, (d + c, s))
    return step, hops, qmin


def least_rotation(seq):
    return min(tuple(seq[i:] + seq[:i]) for i in range(len(seq)))


def enumerate_types(max_loops, max_q, vs=M.VALUES, max_ratio=None, time_limit=None, log=None):
    """returns (list of (L, Q, T, "v1v2...vL") sorted by (Q + T) / L, complete flag)."""
    vs = tuple(sorted(vs, reverse=True))
    step, hops, qmin = _tables(vs)
    z = SID[IDENT]
    used = [False] * len(M.LOOPS)
    used[LOOP_ID[z]] = True
    seq = []
    found = {}
    t0 = time.time()
    complete = [True]
    count = [0]

    def dfs(u, q):
        count[0] += 1
        if time_limit is not None and count[0] % 4096 == 0 and time.time() - t0 > time_limit:
            complete[0] = False
            raise TimeoutError
        depth = len(seq)
        for k, v in enumerate(vs):
            q2 = q + M.K - v
            w = step[u][k]
            if w == z:
                if q2 <= max_q:
                    seq.append(v)
                    L = len(seq)
                    if L >= 2 and (max_ratio is None or q2 <= max_ratio * L + 1e-9):
                        key = least_rotation(seq)
                        if key not in found:
                            found[key] = (L, q2, M.port_trails(list(key)), "".join(map(str, key)))
                    seq.pop()
                continue
            if used[LOOP_ID[w]] or depth + 1 + hops[w] > max_loops or q2 + qmin[w] > max_q:
                continue
            used[LOOP_ID[w]] = True
            seq.append(v)
            dfs(w, q2)
            seq.pop()
            used[LOOP_ID[w]] = False

    try:
        dfs(z, 0)
    except TimeoutError:
        pass
    out = sorted(found.values(), key=lambda t: ((t[1] + t[2]) / t[0], t[0], t[3]))
    if log:
        log("walk types with at most %d loops and Q <= %d: %d (%s, %.0f s)" % (
            max_loops, max_q, len(out), "complete" if complete[0] else "stopped by the time limit", time.time() - t0))
    return out, complete[0]


def read_types(path):
    out = []
    with open(path) as f:
        for line in f:
            line = line.split("#")[0].split()
            if len(line) >= 4:
                out.append((int(line[0]), int(line[1]), int(line[2]), line[3]))
    return out


def write_types(path, types, comments=()):
    with open(path, "w", newline="\n") as f:
        for c in comments:
            f.write("# %s\n" % c)
        f.write("# L Q T row-lengths   (L loops, Q letters for the rows, T closed trails)\n")
        for L, Q, T, s in types:
            f.write("%d %d %d %s\n" % (L, Q, T, s))


def placements(vs):
    """all placed walks of a type: frozensets of rows (x, v), one per start state (duplicates removed)."""
    vs = [int(c) for c in vs] if isinstance(vs, str) else list(vs)
    out = set()
    for g in M.STATES:
        rows = []
        x = g
        for v in vs:
            rows.append((x, v))
            x = M.gstep(x, v)
        if x != g or len(set(M.canon(r[0]) for r in rows)) != len(rows):
            continue
        out.add(frozenset(rows))
    return sorted(out, key=lambda r: sorted(r))
