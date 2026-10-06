#!/usr/bin/env python
"""parts10.py - all ways to split the 48 groups of n = 10 into 8 chains.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: parts10.py        reads c10m_states.pkl (trav10.py), writes c10m_parts.pkl

A chain is a cycle of six traversals of six different groups (trav10.py).  A partition is a set of 8 chains that
together meet every group once.  All partitions are found by exhaustive search: the smallest group not yet covered
is taken, and every chain through it that avoids the groups already covered is tried.
Prints the number of partitions and, for every number k, how many chains occur in exactly k partitions.
On the n = 10 pieces: 56 partitions; every chain occurs in 8 of them.

c10m_parts.pkl: the partitions, each a tuple of 8 chain numbers.

Needs: Python 3, numpy.  Time: below a second.
"""
import pickle, numpy as np

d = pickle.load(open("c10m_states.pkl", "rb"))
nodes = d["nodes"]
cyc = d["cyc"]
gs = [frozenset(nodes[i][0] for i in c) for c in cyc]
assert all(len(s) == 6 for s in gs)
NG = 48
by = [[] for _ in range(NG)]
for i, s in enumerate(gs):
    for g in s:
        by[g].append(i)
sols = []


def rec(used, chosen):
    """complete a set of disjoint chains (chosen, covering the groups in used) to partitions in all ways"""
    if len(used) == NG:
        sols.append(tuple(chosen))
        return
    g = min(x for x in range(NG) if x not in used)
    for i in by[g]:
        if not (gs[i] & used):
            rec(used | gs[i], chosen + [i])


rec(frozenset(), [])
print("partitions of the 48 groups into 8 of the 56 chains:", len(sols))
from collections import Counter

print("chains used by how many partitions:", Counter(Counter(i for s in sols for i in s).values()))
pickle.dump(sols, open("c10m_parts.pkl", "wb"))
