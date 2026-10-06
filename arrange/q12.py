#!/usr/bin/env python
"""q12.py - the run programme of the small trails as a linear programme on the quotient by the symmetry (n = 12).

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: q12.py E [E ...]      (default 6 8 10)   needs cuts12c.bin and sym12.pkl

The piece set.  These scripts were written for one piece set at n = 12, the first one that beat Pantone's pieces:
the 11-symbol selection with full and short rows only (Q = 178,080).  Its numbers are fixed in the code: 7,200
closed trails, of which the first 6,048 of the table are small trails with 110 cuts each (100 at steps of weight 2,
10 at vertices); then 144 trails of the three short walks of every block (63, 133 and 182 loops, one trail each;
kinds 1 to 3 of the table, "short-walk trails" below); then 1,008 big trails.  Letters: 0 .. 6 are the old letters,
7, 8, 9 the added letters, A the distinguished letter, B the completion letter.

Half letters.  For a cut x written before a cut y, W(x, y) = 2 (h - k) + D_x + D_y, where k is the largest number of
letters (at most h = 9) in which the end of the piece cut at x agrees with the start of the piece cut at y, and D is
the cost of a cut (0 at a vertex, 1 at a step of weight 2).  A join of cost c between two vertices has W = 2 c.
For a word, 2 (cuts + joins) = D(first cut) + sum of W over its joins + D(last cut).

Level E.  A run is a maximal sequence of consecutive small trails joined by joins with W < E.  As in runs12.py,
    sum over runs [2 E + 2 (W-sum inside)] = 2 E N - 2 sum (E - W) z   >=   2 E N - 2 LPmax(E),
    LPmax(E) = max sum (E - W) z   over 0 <= z, y with:   sum of y over the cuts of a trail <= 1,
               joins out of a cut <= y of the cut,   joins into a cut <= y of the cut.
This is the linear relaxation of the systems of paths, and cycles are not excluded.  So LPmax is an upper bound of
the true maximum, and 2 E N - 2 LPmax a valid lower bound of the sum over runs.
The 168 relabellings of sym12.py act on the cuts with orbits of 168 cuts each (asserted).  Averaging a solution
over the group keeps its value, so the optimum is attained by solutions that are constant on orbits: one variable
per orbit of cuts (3,960) and one per orbit of joins.

Status of the numbers.  The programme is solved by Gurobi's barrier method without crossover, in floating point.
The values printed are not certified; on this piece set they came out integral at every level tried:
    E             4       6       7       8       9      10      11      12
    sum over runs 34,272  44,352  46,032  47,040  48,048  49,056  49,392  49,728
At E = 6 the value equals the integer optimum of runs12.py; at E = 4 the integer optimum is 34,368.

Prints, per level: LPmax, the weight the optimum puts on the joins of every W, and the bound of the sum over runs
(also divided by 4: in letters).

Also a module: the class Small (the cuts of the small trails and their orbits) is used by q12b.py.

Needs: Python 3, numpy, scipy, c12.py, Gurobi (gurobipy, with a licence beyond the size-limited one).
All files are read from and written to the working directory.
Time and memory, measured: 28 s for the eight levels 4, 6, 7, .., 12 together (22 s of it for the orbits), 0.55 GB.
"""
import sys, time, pickle
import numpy as np
import gurobipy as gp
from gurobipy import GRB
import c12


def relabel(w, D, perm):
    """the cut words w (9 letters, or 10 where D = 1) with every letter a replaced by perm[a]"""
    out = np.zeros(len(w), np.int64)
    P = np.array(perm, np.int64)
    for i in range(10):
        a = (w >> (4 * i)) & 15
        valid = (i < 9) | (D == 1)
        out |= np.where(valid, P[a], 0) << (4 * i)
    return out


class Small:
    """the cuts of the small trails (cut c belongs to trail c // 110) with their end and start codes ex, en, and
    their orbits under the group G of sym12.pkl: orb[c] = orbit of cut c, rep[o] = the first cut of orbit o,
    torb[t] = orbit of trail t (two trails are in one orbit when their cuts lie in the same orbits)"""

    def __init__(self, log=print):
        C = c12.Cuts("cuts12c.bin", log=log)
        self.h = C.h
        self.NS = 6048
        ns = self.NS * 110
        self.ns = ns
        self.w = C.col("w", 0, ns).astype(np.int64)
        self.D = C.D[:ns].astype(np.int64)
        self.t = C.t[:ns].astype(np.int64)
        self.ex = self.w & ((1 << 36) - 1)
        self.en = self.w >> (4 * self.D)
        G = pickle.load(open("sym12.pkl", "rb"))["small"]
        self.G = G
        t0 = time.time()
        can = None
        for g in G:
            k = relabel(self.w, self.D, g) * 2 + self.D
            can = k if can is None else np.minimum(can, k)
        uo, self.orb = np.unique(can, return_inverse=True)
        self.no = len(uo)
        self.rep = np.zeros(self.no, np.int64)
        self.rep[self.orb[::-1]] = np.arange(ns)[::-1]
        assert (np.bincount(self.orb) == len(G)).all(), "an orbit of cuts is not regular"
        # orbits of trails: the multiset of cut orbits of a trail
        key = np.sort(self.orb.reshape(self.NS, 110), 1)
        ut, self.torb = np.unique(key, axis=0, return_inverse=True)
        self.torb = self.torb.ravel()
        self.nto = len(ut)
        log("small cuts %d in %d orbits; trails %d in %d orbits (sizes %s)  (%.0fs)" % (ns, self.no, self.NS, self.nto,
            sorted(set(np.bincount(self.torb).tolist())), time.time() - t0))

    def arcs_from(self, X, wmax):
        """all joins (i, y, W) from the cuts X[i] to cuts y of other small trails with W <= wmax, each pair once
        with its largest overlap"""
        h = self.h
        ex, Dx = self.ex[X], self.D[X]
        I, J, Wc = [], [], []
        for k in range(h, -1, -1):
            c = h - k
            if 2 * c > wmax:
                break
            a = c12.suffix(ex, k)
            b = c12.prefix(self.en, k, h)
            o = np.argsort(b, kind="stable")
            bs = b[o]
            lo = np.searchsorted(bs, a, "left")
            hi = np.searchsorted(bs, a, "right")
            cn = hi - lo
            tot = int(cn.sum())
            if tot == 0:
                continue
            ii = np.repeat(np.arange(len(X)), cn)
            jj = o[np.repeat(lo, cn) + (np.arange(tot) - np.repeat(np.cumsum(cn) - cn, cn))]
            I.append(ii)
            J.append(jj)
            Wc.append(2 * c + Dx[ii] + self.D[jj])
        I = np.concatenate(I)
        J = np.concatenate(J)
        Wc = np.concatenate(Wc)
        key = I * self.ns + J
        o = np.lexsort((Wc, key))
        key, I, J, Wc = key[o], I[o], J[o], Wc[o]
        f = np.concatenate([[True], key[1:] != key[:-1]])
        I, J, Wc = I[f], J[f], Wc[f]
        m = (Wc <= wmax) & (self.t[X[I]] != self.t[J])
        return I[m], J[m], Wc[m]


def run_lp(S, E, arcs, env, log=print, extra=None):
    """LPmax(E) in orbit variables.  arcs = (orbit of the cut the join leaves, cut it enters, W) for the joins out
    of the representative cuts.  Returns (LPmax / 168, {W: weight of the joins with that W in the optimum})."""
    I, J, W = arcs
    m_ = W < E
    I, J, W = I[m_], J[m_], W[m_]
    no = S.no
    m = gp.Model("q", env=env)
    m.Params.Threads = 2
    m.Params.Method = 2
    m.Params.Crossover = 0
    y = m.addMVar(no, lb=0.0, ub=1.0)
    z = m.addMVar(len(I), lb=0.0, obj=(E - W).astype(float))
    m.ModelSense = GRB.MAXIMIZE
    import scipy.sparse as sp
    na = len(I)
    # out: sum of z out of rep i <= y_i ; in: sum of z into orbit o <= y_o
    A_out = sp.csr_matrix((np.ones(na), (I, np.arange(na))), shape=(no, na))
    A_in = sp.csr_matrix((np.ones(na), (S.orb[J], np.arange(na))), shape=(no, na))
    m.addConstr(A_out @ z - y <= 0)
    m.addConstr(A_in @ z - y <= 0)
    # one cut per trail: a representative trail of every orbit of trails
    rows, cols = [], []
    for to in range(S.nto):
        tr = int(np.nonzero(S.torb == to)[0][0])
        oc = S.orb[tr * 110:(tr + 1) * 110]
        rows += [to] * 110
        cols += oc.tolist()
    A_t = sp.csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(S.nto, no))
    m.addConstr(A_t @ y <= 1)
    m.optimize()
    assert m.Status == GRB.OPTIMAL, m.Status
    val = m.ObjVal
    zz = z.X
    hist = {}
    for wv in np.unique(W).tolist():
        hist[int(wv)] = round(float(zz[W == wv].sum()) * len(S.G), 1)
    return val, hist


if __name__ == "__main__":
    log = lambda *x: print(*x, flush=True)
    S = Small(log)
    Es = [int(x) for x in sys.argv[1:]] or [6, 8, 10]
    t0 = time.time()
    arcs = S.arcs_from(S.rep, max(Es) - 1)
    log("joins out of the %d representative cuts with W <= %d: %d  (%.0fs)" % (S.no, max(Es) - 1, len(arcs[0]),
        time.time() - t0))
    arcs = (S.orb[S.rep[arcs[0]]], arcs[1], arcs[2])
    env = gp.Env(params={"OutputFlag": 0})
    N = S.NS
    for E in Es:
        t0 = time.time()
        val, hist = run_lp(S, E, arcs, env, log)
        tot = val * len(S.G)
        run = 2 * E * N - 2 * tot
        log("E = %2d: LPmax = %.3f x %d = %.1f; joins by W (weight in the optimum) %s; sum over runs >= %.1f  (in letters: %.1f)  (%.0fs)" % (
            E, val, len(S.G), tot, hist, run, run / 4, time.time() - t0))
