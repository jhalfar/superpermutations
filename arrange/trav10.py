#!/usr/bin/env python
"""trav10.py - the cheapest traversals of the groups at n = 10 and the chains they form.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: trav10.py BASE.txt GT.npz        writes c10m_states.pkl (read by parts10.py, chain10.py and plans10.py)

  BASE.txt  the base word of the n = 10 pieces (48 groups of 7 small trails, 14 big trails)
  GT.npz    its traversal tables (gt.py)

A traversal of a group goes through its 7 small trails in one run: it enters at a cut y of one trail and leaves at a
cut x of another, every trail written once.  The cheapest traversals have W-sum 12.  The script
  1. lists all traversals with W-sum 12, each as (group, entry, exit);
  2. computes W from the exit of each to the entry of each traversal of another group;
  3. keeps the joins with W = 8 and finds every directed cycle of six traversals of six different groups joined at
     W = 8.  I call such a cycle a chain: cut at one of its six joins it is a path through six groups.
The search for the cycles is exhaustive (depth first, every cycle found once, from its smallest traversal).

Prints the traversals (in all and per group) with the D of their entries and exits, the joins between traversals by
W, how many successors at W = 8 a traversal has, the number of cycles, how many traversals lie on cycles and how many
cycles pass through each group; if no traversal has more than one successor, also the lengths of the paths and
cycles of that graph.
On the n = 10 pieces: 1,008 traversals with W-sum 12, 21 per group; 336 of them enter and leave at vertices,
and exactly these have a successor at W = 8, one each.  The joins at W = 8 form 56 cycles of six and nothing
else; every group lies on 7 of them.  Joins between traversals at W = 9: 1,344; at W = 10: 3,696.

c10m_states.pkl: "nodes" the traversals as (group, entry, exit) with cuts numbered inside the group; "W" the matrix
of step 2 (99 inside one group); "cyc" the cycles as tuples of traversal numbers.

Needs: Python 3, numpy; tl10.py and what it imports.  Time and memory, measured: 8 s, 0.45 GB.
"""
import sys, time, pickle, numpy as np, collections
import tl10

log = lambda *x: print(*x, flush=True)
M = tl10.TL(sys.argv[1], sys.argv[2], log)
T = M.T
NG = M.NG
H = lambda a: {int(k): int(v) for k, v in zip(*np.unique(a, return_counts=True))}
nodes = []
for g in range(NG):
    yy, xx = np.nonzero(M.Tt[g] == 12)
    for y, x in zip(yy.tolist(), xx.tolist()):
        nodes.append((g, y, x))
log("traversals with W-sum 12: %d (per group %d); D of entry/exit: %s" % (len(nodes), len(nodes) // NG,
    collections.Counter((int(M.D[M.cuts[g][y]]), int(M.D[M.cuts[g][x]])) for g, y, x in nodes)))
idx = {nd: i for i, nd in enumerate(nodes)}
ex = np.array([M.cuts[g][x] for g, y, x in nodes])
en = np.array([M.cuts[g][y] for g, y, x in nodes])
gg = np.array([g for g, y, x in nodes])
W = np.array([[T.W(int(a), int(b)) for b in en] for a in ex]) if len(nodes) <= 1200 else None
W[gg[:, None] == gg[None, :]] = 99
log("joins between a traversal and a traversal of another group, W: %s" % H(W[W < 99]))
adj = [np.nonzero(W[i] == 8)[0].tolist() for i in range(len(nodes))]
log("successors at W = 8 per traversal: %s; D type of those with successors: %s" % (H([len(a) for a in adj]),
    collections.Counter(int(M.D[ex[i]]) for i in range(len(nodes)) if adj[i])))
# cycles of 6
cyc = set()


def dfs(path, gs):
    """extend a path of traversals joined at W = 8 through groups not yet met (gs); a path of six whose last
    traversal joins the first at W = 8 is a cycle and is stored from its smallest traversal"""
    if len(path) == 6:
        if path[0] in adj[path[-1]]:
            i = path.index(min(path))
            cyc.add(tuple(path[i:] + path[:i]))
        return
    for b in adj[path[-1]]:
        if gg[b] not in gs and b > path[0]:
            dfs(path + [b], gs | {int(gg[b])})


for a in range(len(nodes)):
    dfs([a], {int(gg[a])})
log("directed 6-cycles of traversals at W = 8: %d; traversals on cycles %d; cycles per group %s" % (len(cyc),
    len({i for c in cyc for i in c}), H(np.bincount([int(gg[i]) for c in cyc for i in c], minlength=NG))))
# longer cycles? length of the cycle of each node if out-degree 1
if all(len(a) <= 1 for a in adj):
    seen = set()
    lens = []
    for a in range(len(nodes)):
        if a in seen or not adj[a]:
            continue
        p = [a]
        seen.add(a)
        c = adj[a][0]
        while c not in seen and adj[c]:
            p.append(c)
            seen.add(c)
            c = adj[c][0]
        lens.append((len(p), c == a))
    log("functional graph: path/cycle lengths %s" % collections.Counter(lens))
pickle.dump(dict(nodes=nodes, W=W, cyc=sorted(cyc)), open("c10m_states.pkl", "wb"))
