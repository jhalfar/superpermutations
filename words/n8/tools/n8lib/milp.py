"""A small adapter to mixed integer linear programming solvers.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

A program builds a Problem (variables with cost, bounds and integrality; rows lo <= sum coef * x <= hi), then calls
solve(problem, solver).  The solver is a name from BACKENDS:

  highs   scipy.optimize.milp (HiGHS, comes with scipy).  The default.
  gurobi  gurobipy, if it is installed and licensed.
  scip    OR-Tools (pywraplp) with SCIP, if ortools is installed.
  cbc     OR-Tools (pywraplp) with CBC, if ortools is installed.

To add a solver, write one function backend(problem, time_limit, threads, verbose) -> Result and put it in BACKENDS.
It must return the status ("optimal", "time_limit", "infeasible" or "error"), the values of the variables of the
best solution (or None), its objective and the best proven lower bound of the minimum.  It should solve to a
gap of zero: the programs here read "optimal" as proved.

All problems here are minimisations.  The programs that use this module re-solve a problem after adding rows (cut
loops), so a backend does not need to support callbacks.
"""
import time


class Problem:
    def __init__(self):
        self.cost = []
        self.lb = []
        self.ub = []
        self.integer = []
        self.rows = []          # (indices, coefficients, lo, hi)
        self.start = None       # optional list of values of a feasible solution (used by solvers that take one)

    def var(self, cost=0.0, lb=0.0, ub=1.0, integer=True):
        self.cost.append(float(cost))
        self.lb.append(float(lb))
        self.ub.append(float(ub))
        self.integer.append(bool(integer))
        return len(self.cost) - 1

    def row(self, idx, coef, lo=-float("inf"), hi=float("inf")):
        if not isinstance(coef, (list, tuple)):
            coef = [float(coef)] * len(idx)
        self.rows.append((list(idx), [float(c) for c in coef], float(lo), float(hi)))

    @property
    def nvars(self):
        return len(self.cost)


class Result:
    def __init__(self, solver, status, x=None, obj=None, bound=None, seconds=0.0):
        self.solver = solver
        self.status = status
        self.x = x
        self.obj = obj
        self.bound = bound
        self.seconds = seconds

    def __repr__(self):
        return "Result(%s, %s, obj=%s, bound=%s, %.1f s)" % (self.solver, self.status, self.obj, self.bound,
                                                              self.seconds)


def _highs(p, time_limit, threads, verbose):
    import numpy as np
    from scipy.optimize import Bounds, LinearConstraint, milp
    from scipy.sparse import csr_matrix
    data, ri, ci, lo, hi = [], [], [], [], []
    for r, (idx, coef, a, b) in enumerate(p.rows):
        ri += [r] * len(idx)
        ci += idx
        data += coef
        lo.append(a)
        hi.append(b)
    cons = []
    if p.rows:
        A = csr_matrix((data, (ri, ci)), shape=(len(p.rows), p.nvars))
        cons = [LinearConstraint(A, np.array(lo), np.array(hi))]
    opts = {"disp": bool(verbose), "presolve": True, "mip_rel_gap": 0.0}
    if time_limit is not None:
        opts["time_limit"] = float(time_limit)
    res = milp(np.array(p.cost), integrality=np.array(p.integer, dtype=int), bounds=Bounds(p.lb, p.ub),
               constraints=cons, options=opts)
    bound = getattr(res, "mip_dual_bound", None)
    if res.status == 0:
        st = "optimal"
    elif res.status == 1:
        st = "time_limit"
    elif res.status == 2:
        st = "infeasible"
    else:
        st = "error"
    x = None if res.x is None else [float(v) for v in res.x]
    obj = None if x is None else float(res.fun)
    if st == "optimal" and (bound is None or bound != bound):
        bound = obj
    return Result("highs", st, x, obj, None if bound is None or bound != bound else float(bound))


def _gurobi(p, time_limit, threads, verbose):
    import gurobipy as gp
    from gurobipy import GRB
    global _GRB_ENV
    if _GRB_ENV is None:
        _GRB_ENV = gp.Env(empty=True)
        _GRB_ENV.setParam("OutputFlag", 0)
        _GRB_ENV.start()
    m = gp.Model(env=_GRB_ENV)
    m.Params.OutputFlag = 1 if verbose else 0
    m.Params.Threads = threads
    m.Params.MIPGap = 0.0
    m.Params.MIPGapAbs = 1e-6
    if time_limit is not None:
        m.Params.TimeLimit = time_limit
    xs = m.addVars(p.nvars, lb=p.lb, ub=p.ub, obj=p.cost,
                   vtype=[GRB.BINARY if (i and lo == 0 and hi == 1) else (GRB.INTEGER if i else GRB.CONTINUOUS)
                          for i, lo, hi in zip(p.integer, p.lb, p.ub)])
    for idx, coef, lo, hi in p.rows:
        e = gp.LinExpr(coef, [xs[i] for i in idx])
        if lo == hi:
            m.addLConstr(e, GRB.EQUAL, lo)
        else:
            if lo > -float("inf"):
                m.addLConstr(e, GRB.GREATER_EQUAL, lo)
            if hi < float("inf"):
                m.addLConstr(e, GRB.LESS_EQUAL, hi)
    if p.start is not None:
        for i, v in enumerate(p.start):
            xs[i].Start = v
    m.optimize()
    st = {GRB.OPTIMAL: "optimal", GRB.TIME_LIMIT: "time_limit", GRB.INFEASIBLE: "infeasible"}.get(m.Status, "error")
    x = [xs[i].X for i in range(p.nvars)] if m.SolCount else None
    res = Result("gurobi", st, x, m.ObjVal if m.SolCount else None, m.ObjBound if st != "infeasible" else None)
    m.dispose()
    return res


_GRB_ENV = None


def _ortools(name):
    def run(p, time_limit, threads, verbose):
        from ortools.linear_solver import pywraplp
        s = pywraplp.Solver.CreateSolver(name)
        if s is None:
            raise RuntimeError("OR-Tools has no %s solver here" % name)
        if verbose:
            s.EnableOutput()
        if time_limit is not None:
            s.SetTimeLimit(int(time_limit * 1000))
        s.SetNumThreads(threads)
        inf = s.infinity()
        xs = [s.IntVar(lo, hi, "") if i else s.NumVar(lo, hi, "") for i, lo, hi in zip(p.integer, p.lb, p.ub)]
        for idx, coef, lo, hi in p.rows:
            c = s.Constraint(lo if lo > -float("inf") else -inf, hi if hi < float("inf") else inf)
            for i, a in zip(idx, coef):
                c.SetCoefficient(xs[i], c.GetCoefficient(xs[i]) + a)
        obj = s.Objective()
        for v, c in zip(xs, p.cost):
            obj.SetCoefficient(v, c)
        obj.SetMinimization()
        prm = pywraplp.MPSolverParameters()
        prm.SetDoubleParam(pywraplp.MPSolverParameters.RELATIVE_MIP_GAP, 0.0)
        r = s.Solve(prm)
        st = {pywraplp.Solver.OPTIMAL: "optimal", pywraplp.Solver.INFEASIBLE: "infeasible"}.get(r, None)
        has = r in (pywraplp.Solver.OPTIMAL, pywraplp.Solver.FEASIBLE)
        if st is None:
            st = "time_limit" if r in (pywraplp.Solver.FEASIBLE, pywraplp.Solver.NOT_SOLVED) else "error"
        x = [v.solution_value() for v in xs] if has else None
        return Result(name.lower(), st, x, obj.Value() if has else None, obj.BestBound() if has else None)
    return run


BACKENDS = {"highs": _highs, "gurobi": _gurobi, "scip": _ortools("SCIP"), "cbc": _ortools("CBC")}


def solve(p, solver="highs", time_limit=None, threads=1, verbose=False, relax=False):
    """relax=True solves the linear relaxation (every variable continuous)."""
    if solver not in BACKENDS:
        raise ValueError("unknown solver %r; known: %s" % (solver, ", ".join(BACKENDS)))
    if relax:
        q = Problem()
        q.cost, q.lb, q.ub, q.rows = p.cost, p.lb, p.ub, p.rows
        q.integer = [False] * p.nvars
        p = q
    t0 = time.time()
    res = BACKENDS[solver](p, time_limit, threads, verbose)
    res.seconds = time.time() - t0
    return res


def available(solver):
    """True if the backend can be imported here."""
    mod = {"highs": "scipy.optimize", "gurobi": "gurobipy", "scip": "ortools.linear_solver.pywraplp",
           "cbc": "ortools.linear_solver.pywraplp"}.get(solver)
    if mod is None:
        return False
    try:
        __import__(mod)
        return True
    except Exception:
        return False
