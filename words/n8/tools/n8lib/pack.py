"""Packings: selections made of loop-disjoint closed walks of given types; every other loop has no row.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

partition(): a set partition programme.  There is a column for every placement of every walk type (all 720
relabellings), at cost Q + T of the walk, and a column per loop for "no row", at cost rowless_cost.  Every loop is
covered once.  With a large rowless_cost the programme first covers as many loops as it can.

enumerate_copies(): every packing of k pairwise disjoint copies of one type, by depth first search, reduced up to
the 720 relabellings of 0..5.  For the 27-walk and k = 4 it finds all packings that cover 108 loops.
"""
import time

from . import milp
from . import model as M
from . import walks as W


def selection_of(placed):
    sel = {L: (L, 0) for L in M.LOOPS}
    for rows in placed:
        for x, v in rows:
            sel[M.canon(x)] = (x, v)
    return sel


def partition(types, rowless_cost=100.0, solver="highs", time_limit=None, threads=1, log=None, forbid=()):
    """types: [(L, Q, T, row lengths)].  Returns (selection, objective, bound, status, list of type strings used).
    forbid: selections (as sets of placed walks) that must not be returned again."""
    say = log or (lambda *a: None)
    cols = []
    for L, Q, T, s in types:
        for rows in W.placements(s):
            cols.append((rows, Q + T, s))
    P = milp.Problem()
    cover = {L: [] for L in M.LOOPS}
    zs = []
    for rows, c, s in cols:
        z = P.var(c)
        zs.append(z)
        for x, v in rows:
            cover[M.canon(x)].append(z)
    d = {L: P.var(rowless_cost) for L in M.LOOPS}
    for L in M.LOOPS:
        P.row(cover[L] + [d[L]], 1, 1, 1)
    for f in forbid:
        idx = [zs[i] for i, (rows, c, s) in enumerate(cols) if rows in f]
        if idx:
            P.row(idx, 1, hi=len(idx) - 1)
    say("packing programme: %d walk types, %d placed walks, %d variables" % (len(types), len(cols), P.nvars))
    res = milp.solve(P, solver, time_limit, threads)
    if res.x is None:
        return None, None, res.bound, res.status, []
    placed = [cols[i][0] for i, z in enumerate(zs) if res.x[z] > 0.5]
    used = sorted(cols[i][2] for i, z in enumerate(zs) if res.x[z] > 0.5)
    sel = selection_of(placed)
    assert M.balanced(sel)
    say("packing: %s after %.0f s, %d walks %s, %d loops without a row, objective %g, bound %s" % (
        res.status, res.seconds, len(placed), used, M.rowless(sel), res.obj,
        "-" if res.bound is None else "%g" % res.bound))
    return sel, res.obj, res.bound, res.status, placed


def relabel(sel, g):
    """the selection with the letters 0..5 renamed by g (a tuple: c -> g[c])."""
    out = {}
    for L, (x, v) in sel.items():
        y = tuple(g[c] for c in x)
        out[M.canon(y)] = (y, v) if v else (M.canon(y), 0)
    return out


def canonical_key(sel):
    return min(tuple(sorted(relabel(sel, g).values())) for g in M.STATES)


def enumerate_copies(vs, k, log=None):
    """all packings of k disjoint placed copies of the type vs; returns (number of packings, list of selections,
    one per class up to relabelling)."""
    say = log or (lambda *a: None)
    t0 = time.time()
    pl = W.placements(vs)
    LID = {L: i for i, L in enumerate(M.LOOPS)}
    masks = []
    for rows in pl:
        m = 0
        for x, v in rows:
            m |= 1 << LID[M.canon(x)]
        masks.append(m)
    n = len(pl)
    packs = []

    def rec(chosen, start, mask):
        if len(chosen) == k:
            packs.append(list(chosen))
            return
        for j in range(start, n):
            if not masks[j] & mask:
                chosen.append(j)
                rec(chosen, j + 1, mask | masks[j])
                chosen.pop()

    rec([], 0, 0)
    classes = {}
    for p in packs:
        sel = selection_of([pl[i] for i in p])
        classes.setdefault(canonical_key(sel), sel)
    say("%d placed walks of type %s, %d packings of %d copies, %d classes up to relabelling (%.0f s)" % (
        n, vs, len(packs), k, len(classes), time.time() - t0))
    return len(packs), list(classes.values())
