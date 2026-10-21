#!/usr/bin/env python3
"""n8.py - superpermutations on 8 symbols in Pantone's completion: check, price, rebuild, extract, search.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

usage: python3 n8.py COMMAND ...      (python3 n8.py COMMAND --help for the options of one command)

  check WORD                         every permutation of 01234567 occurs; no single letter can be deleted
  price SELECTION [-o WORD]          the best word of a selection and the proven lower bound on its J
  rebuild SELECTION -o WORD          the same, then checks the word; with --order ORDER no solver is used
  extract WORD -o SELECTION          the selection (and with --order-out the slice order) of a word
  walks [-o TYPES]                   closed walk types with few letters per loop
  pack [-o SELECTION]                a packing of the loops by disjoint closed walks
  search [--time T] [--seed S]       walk types, packing, then parallel tempering with exact pricing

The solver of every integer programme is chosen with --solver: highs (scipy, the default), gurobi, scip or cbc
(OR-Tools).  Needs Python 3 with numpy and scipy.
"""
import argparse
import hashlib
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from n8lib import milp  # noqa: E402
from n8lib import model as M  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))


def say(*a):
    print(*a, flush=True)


def sha(w):
    return hashlib.sha256(w.encode()).hexdigest()


def write_word(path, w):
    with open(path, "w", newline="\n") as f:
        f.write(w + "\n")


def report_check(w, deletions=True):
    r = M.check_word(w, deletions)
    say("length %d, permutation windows %d, distinct permutations %d, missing %d%s" % (
        r["length"], r["windows"], r["distinct"], r["missing"],
        ", letters that can be deleted %d" % r["deletable"] if "deletable" in r else ""))
    ok = r["missing"] == 0 and r.get("deletable", 0) == 0
    say("VALID: every permutation occurs%s" % (" and no letter can be deleted" if deletions else "") if ok else
        "NOT VALID")
    return ok


def solver_args(p):
    p.add_argument("--solver", default="highs", choices=sorted(milp.BACKENDS),
                   help="integer programming solver (default highs, from scipy)")
    p.add_argument("--threads", type=int, default=1, help="solver threads (default 1; HiGHS through scipy uses 1)")


def need_solver(name):
    if not milp.available(name):
        sys.exit("the solver %s cannot be imported here" % name)


# ---------------------------------------------------------------- commands

def cmd_check(a):
    w = M.read_word(a.word)
    ok = report_check(w, not a.no_deletions)
    say("SHA-256 of the word without line feed %s" % sha(w))
    return 0 if ok else 1


class Priced:
    def __init__(self, **kw):
        self.__dict__.update(kw)


def do_price(a, sel):
    from n8lib import openings as OP
    from n8lib import price as PR
    need_solver(a.solver)
    log = None if a.quiet else (lambda s: say("  " + s))
    rule = "joins of every overlap" if a.min_overlap == 0 else "only joins of overlap >= %d" % a.min_overlap
    if a.model == "slices":
        p = PR.price(sel, min_overlap=a.min_overlap, solver=a.solver, time_limit=a.time, threads=a.threads, log=log)
        what = "model slices: whole slices in any order"
        r = Priced(word=p.word, J=p.J, bound=p.bound, status=p.status, seconds=p.seconds, rounds=p.rounds, Q=p.Q,
                   trails=p.trails, nslices=len(p.strs), keys=p.keys, order=getattr(p, "order", None),
                   overlaps=getattr(p, "overlaps", None))
    else:
        o = OP.price_openings(sel, min_weight=a.min_weight, min_overlap=a.min_overlap, solver=a.solver,
                              time_limit=a.time, threads=a.threads, log=log)
        what = "model trails: every closed trail in one run, opened %s" % {
            3: "between two slices", 2: "at a step of weight 2 or 3", 1: "at any permutation window"}[a.min_weight]
        if o is None:
            sys.exit("no word found")
        r = Priced(word=o["word"], J=o["J"], bound=o["bound"], status=o["status"], seconds=o["seconds"],
                   rounds=o["rounds"], Q=o["Q"], trails=o["trails"], nslices=len(o["strs"]), keys=o["keys"],
                   order=o["slice_order"], overlaps=o["slice_overlaps"], weights=o["weights"])
    say("solver %s; %s; %s" % (a.solver, what, rule))
    say("%d slices, %d closed trails, Q %d" % (r.nslices, r.trails, r.Q))
    if r.word is None:
        say("no word found (%s after %.0f s); lower bound on J: %s" % (r.status, r.seconds, r.bound))
        return r
    say("J %d, lower bound on J %s: %s" % (r.J, r.bound, "optimal in this model" if r.status == "optimal" else
                                              "not proved optimal (%s)" % r.status))
    say("length %d = 46,085 + Q %d + J %d (%d rounds, %.1f s)" % (len(r.word), r.Q, r.J, r.rounds, r.seconds))
    if r.overlaps is not None:
        hist = {}
        for k in r.overlaps:
            if k < 5:
                hist[k] = hist.get(k, 0) + 1
        say("joins between trails by overlap: %s" % ", ".join(
            "%d x %d" % (hist[k], k) for k in sorted(hist, reverse=True)))
    if getattr(r, "weights", None) and min(r.weights) < 3:
        say("trails opened inside a slice: %d" % sum(1 for g in r.weights if g < 3))
    say("SHA-256 of the word without line feed %s" % sha(r.word))
    if a.out:
        write_word(a.out, r.word)
        say("word written to %s" % a.out)
    if a.order_out:
        if r.order is None:
            say("no order written: a trail is opened inside a slice, which an order file cannot say")
        else:
            PR.write_order(a.order_out, r.keys, r.order, r.overlaps,
                           ["slice order of a word of %d letters (%s; %s; solver %s)" % (
                               len(r.word), what, rule, a.solver)])
            say("order written to %s" % a.order_out)
    return r


def cmd_price(a):
    sel = M.read_selection(a.selection)
    p = do_price(a, sel)
    return 0 if p.word is not None else 1


def cmd_rebuild(a):
    from n8lib import price as PR
    sel = M.read_selection(a.selection)
    if a.order:
        order, ovs, keys, strs = PR.read_order(a.order, sel)
        w, used = M.assemble(strs, order, ovs)
        say("word of the order %s: %d letters = 46,085 + Q %d + J %d" % (
            a.order, len(w), M.q_of(sel), len(w) - M.BASE_LENGTH - M.q_of(sel)))
        say("SHA-256 of the word without line feed %s" % sha(w))
        write_word(a.out, w)
        say("word written to %s" % a.out)
    else:
        p = do_price(a, sel)
        if p.word is None:
            return 1
        w = p.word
    return 0 if report_check(w) else 1


def cmd_extract(a):
    from n8lib import extract as X
    from n8lib import pack as PK
    from n8lib import price as PR
    w = M.read_word(a.word)
    t0 = time.time()
    found = X.extract(w)
    if not found:
        say("%s is not a word of Pantone's completion on 8 symbols that this program can read" % a.word)
        return 1
    r = found[0]
    sel = r["sel"]
    Tn = len(M.trail_cycles(M.slices(sel)[1])[0])
    table = "".join(r["table"][c] for c in sorted(r["table"]))
    say("read %s, the letters %s renamed to %s (s = %s, z = %s)" % (
        r["direction"], "".join(sorted(r["table"])), table, r["s"], r["z"]))
    say("selection: Q %d, %d loops without a row, %d closed walks, %d closed trails" % (
        M.q_of(sel), M.rowless(sel), len(M.walks(sel)), Tn))
    if r["order"] is not None:
        J = len(w) - M.BASE_LENGTH - M.q_of(sel)
        say("a word of whole slices: length %d = 46,085 + Q %d + J %d" % (len(w), M.q_of(sel), J))
    elif r["partial"]:
        say("not a word of whole slices: %d loops have a slice that is cut; their option is the one with most "
            "slices present" % r["partial"])
    else:
        say("the selection is complete, but the word is not its slices in order (no order written)")
    M.write_selection(a.out, sel, ["selection of a word of %d letters, SHA-256 %s" % (len(w), sha(w)),
                                   "read %s with the letters %s renamed to %s" % (
                                       r["direction"], "".join(sorted(r["table"])), table)])
    say("selection written to %s (%.1f s)" % (a.out, time.time() - t0))
    if a.order_out and r["order"] is not None:
        PR.write_order(a.order_out, r["keys"], r["order"], r["overlaps"],
                       ["slice order of the word of %d letters, SHA-256 %s" % (len(w), sha(w))])
        say("order written to %s" % a.order_out)
    if a.compare:
        ref = M.read_selection(a.compare)
        if ref == sel:
            say("the selection equals %s" % a.compare)
        elif PK.canonical_key(ref) == PK.canonical_key(sel):
            say("the selection equals %s up to renaming the letters 0..5" % a.compare)
        else:
            # other readings of the word: backwards, or with other letters as 6 and 7
            key = PK.canonical_key(ref)
            hit = None
            for r2 in X.extract(w, find_all=True)[1:]:
                if PK.canonical_key(r2["sel"]) == key:
                    hit = r2
                    break
            if hit:
                say("the word read %s with s = %s, z = %s has the selection %s, up to renaming 0..5" % (
                    hit["direction"], hit["s"], hit["z"], a.compare))
            else:
                say("no reading of the word has the selection %s, also up to renaming 0..5" % a.compare)
    return 0


def cmd_walks(a):
    from n8lib import walks as W
    max_q = a.max_q if a.max_q is not None else int(a.max_ratio * a.max_loops)
    types, complete = W.enumerate_types(a.max_loops, max_q, max_ratio=a.max_ratio, time_limit=a.time, log=say)
    for L, Q, T, s in types:
        say("%3d loops  Q %2d  trails %d  (Q + T) / L = %.3f  %s" % (L, Q, T, (Q + T) / L, s))
    if a.out:
        W.write_types(a.out, types, ["walk types with at most %d loops, Q <= %d, Q / L <= %g (%s)" % (
            a.max_loops, max_q, a.max_ratio, "complete" if complete else "incomplete: time limit")])
        say("written to %s" % a.out)
    return 0


def default_types():
    from n8lib import walks as W
    return W.read_types(os.path.join(HERE, "walk-types.txt"))


def cmd_pack(a):
    from n8lib import pack as PK
    from n8lib import walks as W
    need_solver(a.solver)
    if a.copies:
        vs, k = a.copies[0], int(a.copies[1])
        n, classes = PK.enumerate_copies(vs, k, log=say)
        sels = classes
    else:
        types = W.read_types(a.types) if a.types else default_types()
        types = [t for t in types if (t[1] + t[2]) / t[0] <= a.max_ratio]
        sel, obj, bound, status, placed = PK.partition(types, a.rowless_cost, a.solver, a.time, a.threads, log=say)
        if sel is None:
            return 1
        sels = [sel]
    for i, sel in enumerate(sels):
        say("packing %d: Q %d, %d loops without a row, walks %s" % (
            i, M.q_of(sel), M.rowless(sel), sorted(len(w) for w in M.walks(sel))))
        if a.out:
            path = a.out if len(sels) == 1 else "%s.%d" % (a.out, i)
            M.write_selection(path, sel, ["packing by closed walks: Q %d, %d loops without a row" % (
                M.q_of(sel), M.rowless(sel))])
            say("written to %s" % path)
    return 0


def cmd_search(a):
    from n8lib import pack as PK
    from n8lib import search as S
    from n8lib import walks as W
    need_solver(a.solver)
    rng = random.Random(a.seed)
    t0 = time.time()
    os.makedirs(a.out, exist_ok=True)
    say("search: solver %s, seed %d, %g s, results in %s" % (a.solver, a.seed, a.time, a.out))
    if a.start:
        starts = [M.read_selection(p) for p in a.start]
        say("start from %d given selections" % len(starts))
    else:
        say("step 1: closed walk types with at most %d loops and Q / L <= %g" % (a.walk_loops, a.max_ratio))
        types, complete = W.enumerate_types(a.walk_loops, int(a.max_ratio * a.walk_loops), max_ratio=a.max_ratio,
                                            time_limit=max(10.0, 0.2 * a.time), log=say)
        for L, Q, T, s in types:
            say("  %3d loops  Q %2d  trails %d  (Q + T) / L = %.3f  %s" % (L, Q, T, (Q + T) / L, s))
        W.write_types(os.path.join(a.out, "walk-types.txt"), types)
        good = [t for t in types if (t[1] + t[2]) / t[0] <= a.pack_ratio]
        say("step 2: packing by the %d types with (Q + T) / L <= %g" % (len(good), a.pack_ratio))
        sel, obj, bound, status, placed = PK.partition(good, 100.0, a.solver, max(10.0, 0.2 * a.time), a.threads,
                                                       log=say)
        if sel is None:
            say("no packing found")
            return 1
        M.write_selection(os.path.join(a.out, "packing.txt"), sel, ["packing found by n8.py search"])
        starts = [sel]
    pricer = S.Pricer(a.solver, a.price_time, a.out, a.save_below, say, a.model, a.min_weight)
    temps = [float(t) for t in a.temps.split(",")]
    say("step 3: parallel tempering, temperatures %s, regions of %d to %d loops" % (temps, a.rmin, a.rmax))
    left = a.time - (time.time() - t0)
    S.tempering(starts, pricer, temps, left, rng, a.rmin, a.rmax, solver=a.solver, log=say)
    if pricer.best:
        e, sel, p = pricer.best
        say("best: %d letters = 46,085 + Q %d + J %d (%s)" % (len(p.word), p.Q, p.J, p.status))
        M.write_selection(os.path.join(a.out, "best-selection.txt"), sel, ["best selection of the search: %d letters" %
                                                                         len(p.word)])
        write_word(os.path.join(a.out, "best-word.txt"), p.word)
        report_check(p.word)
    say("search done after %.0f s; %d pricings" % (time.time() - t0, pricer.calls))
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(prog="n8.py", description=__doc__.split("\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter,
                                 epilog="\n".join(__doc__.split("\n")[4:]))
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("check", help="check a word")
    p.add_argument("word")
    p.add_argument("--no-deletions", action="store_true", help="only test that every permutation occurs")
    p.set_defaults(fn=cmd_check)

    for name, fn, hlp in (("price", cmd_price, "the best word of a selection and its lower bound"),
                          ("rebuild", cmd_rebuild, "write and check the best word of a selection")):
        p = sub.add_parser(name, help=hlp)
        p.add_argument("selection")
        p.add_argument("-o", "--out", required=(name == "rebuild"), help="write the word here")
        p.add_argument("--model", default="trails", choices=("trails", "slices"),
                       help="trails (default): every closed trail written in one run; slices: whole slices in any "
                            "order")
        p.add_argument("--min-weight", type=int, default=3, choices=(1, 2, 3),
                       help="model trails: open a trail at steps of at least this weight (3, the default: between "
                            "slices; 2 or 1: also inside a slice)")
        p.add_argument("--min-overlap", type=int, default=0, choices=range(0, 6),
                       help="allow only joins of at least this overlap (default 0: every join)")
        p.add_argument("--time", type=float, default=None, help="time limit in seconds (default none)")
        p.add_argument("--order-out", help="write the slice order of the word here")
        p.add_argument("--quiet", action="store_true", help="do not print the rounds of the solver loop")
        if name == "rebuild":
            p.add_argument("--order", help="write the word of this slice order instead (no solver)")
        solver_args(p)
        p.set_defaults(fn=fn)

    p = sub.add_parser("extract", help="selection and slice order of a word")
    p.add_argument("word")
    p.add_argument("-o", "--out", required=True, help="selection file to write")
    p.add_argument("--order-out", help="write the slice order here")
    p.add_argument("--compare", help="say whether the selection equals this one (up to renaming 0..5)")
    p.set_defaults(fn=cmd_extract)

    p = sub.add_parser("walks", help="enumerate closed walk types")
    p.add_argument("--max-loops", type=int, default=32)
    p.add_argument("--max-ratio", type=float, default=0.625, help="keep walks with Q / L at most this")
    p.add_argument("--max-q", type=int, default=None, help="default max-ratio * max-loops")
    p.add_argument("--time", type=float, default=None, help="stop after this many seconds")
    p.add_argument("-o", "--out")
    p.set_defaults(fn=cmd_walks)

    p = sub.add_parser("pack", help="pack the loops with closed walks")
    p.add_argument("--types", help="walk types (output of walks); default walk-types.txt next to n8.py")
    p.add_argument("--max-ratio", type=float, default=0.66, help="use types with (Q + T) / L at most this")
    p.add_argument("--rowless-cost", type=float, default=100.0, help="cost of a loop without a row")
    p.add_argument("--copies", nargs=2, metavar=("TYPE", "K"),
                   help="instead: every packing of K copies of one type, up to renaming 0..5")
    p.add_argument("--time", type=float, default=None)
    p.add_argument("-o", "--out")
    solver_args(p)
    p.set_defaults(fn=cmd_pack)

    p = sub.add_parser("search", help="the whole search: walks, packing, parallel tempering")
    p.add_argument("--time", type=float, default=1800, help="seconds in all (default 1800)")
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--out", default="n8-search", help="directory for the results (default n8-search)")
    p.add_argument("--start", nargs="+", help="start from these selections instead of steps 1 and 2")
    p.add_argument("--walk-loops", type=int, default=30, help="walks of at most this many loops (step 1)")
    p.add_argument("--max-ratio", type=float, default=0.625, help="walks with Q / L at most this (step 1)")
    p.add_argument("--pack-ratio", type=float, default=0.66, help="pack with types of (Q + T) / L at most this")
    p.add_argument("--temps", default="0.7,1.5,3", help="temperatures of the chains")
    p.add_argument("--rmin", type=int, default=12)
    p.add_argument("--rmax", type=int, default=50)
    p.add_argument("--price-time", type=float, default=60, help="time limit of one pricing (default 60 s)")
    p.add_argument("--save-below", type=int, default=46178, help="write every word shorter than this")
    p.add_argument("--model", default="trails", choices=("trails", "slices"), help="pricing model (as in price)")
    p.add_argument("--min-weight", type=int, default=3, choices=(1, 2, 3), help="as in price")
    solver_args(p)
    p.set_defaults(fn=cmd_search)

    a = ap.parse_args(argv)
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
