"""cutlns2.py WORD N STEPS.bin OUTDIR [options]: the reorder with the persistent solver of net.py (one Gurobi LP kept
across rounds: a round switches off the pieces it splits, switches on their parts, re-solves from the previous basis
and keeps every subtour cut).  Iterated exact reordering with cuts opened locally: Jay Pantone's move of W-0107 /
W-0108 (Almanac, 12 Nov 2026), rebuilt.

The word is cut at every step of weight >= --gbase (the backbone, always open).  A round chooses K joins of the
current order (heaviest untried first, then random), opens the cuts of weight in [--gopen, --gbase) inside the --nb
pieces on each side of each join (only the --R nearest to the join if R > 0; --far 1 also the R at the far end), solves
the order of all pieces exactly (maximum-weight path cover, net.py), keeps a gain (else undoes the cuts; --neutral 1
also keeps a different order of equal length) and closes every opened cut whose two sides stay neighbours with their
natural overlap.  STEPS.bin from steps.exe (steps of weight >= the smallest gopen used).

Output: OUTDIR/run.log (a line a round), OUTDIR/state.npz (open non-backbone cuts, order, length) whenever the length
drops, with --write 1 the word OUTDIR/w.txt at the end, and an END line.  --resume STATE.npz continues a state."""
import argparse, json, os, random, sys, time
import numpy as np
import gurobipy as gp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from net import Net, ovl as ovl_

ap = argparse.ArgumentParser()
ap.add_argument("word"); ap.add_argument("n", type=int); ap.add_argument("steps"); ap.add_argument("out")
ap.add_argument("--gbase", type=int, default=5)
ap.add_argument("--gopen", type=int, default=4)
ap.add_argument("--K", type=int, default=4)
ap.add_argument("--R", type=int, default=0)
ap.add_argument("--far", type=int, default=0)
ap.add_argument("--gfine", type=int, default=0, help="also open the --Rfine cuts of weight gfine .. gopen-1 nearest to the join")
ap.add_argument("--Rfine", type=int, default=100)
ap.add_argument("--nb", type=int, default=1)
ap.add_argument("--rounds", type=int, default=1000000)
ap.add_argument("--time", type=float, default=3600)
ap.add_argument("--heavy", type=int, default=1)
ap.add_argument("--wmin", type=int, default=0)
ap.add_argument("--neutral", type=int, default=0)
ap.add_argument("--threads", type=int, default=2)
ap.add_argument("--miptime", type=float, default=60)
ap.add_argument("--lpit", type=int, default=40)
ap.add_argument("--seed", type=int, default=1)
ap.add_argument("--resume", default="")
ap.add_argument("--write", type=int, default=1)
ap.add_argument("--noise", type=float, default=0.0, help="noise rounds: arc weights + uniform [0, noise); keep if true length <= current")
ap.add_argument("--noiseevery", type=int, default=5, help="with --noise: every noiseevery-th round is a normal round")
ap.add_argument("--solve0", type=int, default=1, help="0: keep the start order (no round-0 solve); with --rounds 0 a pure writer")
ap.add_argument("--rebuild", type=float, default=2.0, help="rebuild the model when slots > rebuild x pieces")
ap.add_argument("--stop", default="", help="stop when this file exists")
ap.add_argument("--fthr", default="0.3,0.5,0.7", help="thresholds of the fractional component cuts ('' = none)")
ap.add_argument("--chain", type=int, default=0, help="1: contract runs of pieces away from the chosen joins")
ap.add_argument("--wbreak", type=int, default=8, help="chain mode: chains also break at joins of weight >= wbreak")
ap.add_argument("--D", type=int, default=2, help="chain mode: pieces within D places of a chosen join are free")
ap.add_argument("--maxchain", type=int, default=0, help="chain mode: longest chain (0 = no limit)")
ap.add_argument("--k0", type=int, default=4, help="overlaps >= k0 are direct arcs, smaller ones go through nodes")
ap.add_argument("--stallmax", type=int, default=2, help="LP rounds without bound change before the MIP")
ap.add_argument("--mipparams", default="", help="Gurobi parameters of the MIP fallback, e.g. Cuts=0,Presolve=0")
A = ap.parse_args()
n = A.n; m = n - 1
os.makedirs(A.out, exist_ok=True)
LOG = open(os.path.join(A.out, "run.log"), "a", buffering=1)
T0 = time.time()


def say(*a):
    s = time.strftime("%m-%d %H:%M:%S") + f" [{time.time() - T0:8.1f}s] " + " ".join(str(x) for x in a)
    LOG.write(s + "\n"); print(s, flush=True)


W = np.memmap(A.word, dtype=np.uint8, mode="r")
LW = len(W)
while W[LW - 1] in (10, 13): LW -= 1
lut = np.zeros(256, np.int64)
for i, c in enumerate("0123456789ABCDEF"): lut[ord(c)] = i
st = np.fromfile(A.steps, dtype=np.int64)
SV = st >> 4; SW = (st & 15).astype(np.int8); SU = SV - SW
del st
FIRST = 0
while len(set(W[FIRST:FIRST + n].tolist())) != n: FIRST += 1
LAST = LW - n
while len(set(W[LAST:LAST + n].tolist())) != n: LAST -= 1
BACK = SW >= A.gbase
say(f"start word {A.word} n={n} length {LW} steps>={int(SW.min())} {len(SV)} backbone>={A.gbase} {int(BACK.sum())}"
    f" gopen {A.gopen} gfine {A.gfine} Rfine {A.Rfine} K {A.K} R {A.R} far {A.far} nb {A.nb} neutral {A.neutral} heavy {A.heavy} threads {A.threads}"
    f" seed {A.seed} chain {A.chain} wbreak {A.wbreak} D {A.D} k0 {A.k0}")
if min(A.gopen, A.gfine or 99) < int(SW.min()): sys.exit("steps table does not hold the weight gopen / gfine")
OPEN = BACK.copy()
SH = [4 * (m - k) for k in range(n)]
MK = [(1 << (4 * k)) - 1 for k in range(n)]
AR = np.arange(m, dtype=np.int64)
WT = (16 ** np.arange(m - 1, -1, -1)).astype(np.int64)


def ovl(E, S): return ovl_(E, S, n, MK, SH)


def bounds(pids, oc):
    pids = np.asarray(pids, dtype=np.int64)
    ps = np.where(pids >= 0, SV[np.maximum(pids, 0)], FIRST)
    nx = np.searchsorted(oc, pids, side="right")
    pe = np.where(nx < len(oc), SU[oc[np.minimum(nx, len(oc) - 1)]], LAST)
    return ps, pe


def keys(ps, pe):
    S = (lut[W[ps[:, None] + AR]] * WT).sum(1)
    E = (lut[W[pe[:, None] + 1 + AR]] * WT).sum(1)
    return S, E


def length(pids, oc):
    ps, pe = bounds(pids, oc)
    S, E = keys(ps, pe)
    o = ovl(E[:-1], S[1:])
    return int((pe - ps + n).sum() - o.sum()), o


def save(order, L):
    tmp = os.path.join(A.out, "state_tmp.npz")
    np.savez(tmp, open=np.flatnonzero(OPEN & ~BACK), order=np.asarray(order), length=L, gbase=A.gbase)
    os.replace(tmp, os.path.join(A.out, "state.npz"))


def write(order, path):
    oc = np.flatnonzero(OPEN)
    ps, pe = bounds(order, oc)
    S, E = keys(ps, pe); o = np.concatenate([[0], ovl(E[:-1], S[1:])])
    tot = 0
    with open(path, "wb") as f:
        for a, b, k in zip(ps, pe, o):
            s, e = int(a + k), int(b + n)
            while s < e:
                t = min(e, s + (1 << 26)); f.write(W[s:t].tobytes()); tot += t - s; s = t
    return tot


ENV = gp.Env(empty=True); ENV.setParam("OutputFlag", 0); ENV.start()
NRNG = np.random.default_rng(A.seed)
NET = None


def newnet():
    global NET
    if NET is not None: NET.md.dispose()
    NET = Net(n, ENV, threads=A.threads, miptime=A.miptime, lpit=A.lpit,
              fthr=tuple(float(v) for v in A.fthr.split(",") if v), stallmax=A.stallmax,
              mipparams=A.mipparams.split(","), k0=A.k0)


def solve(pids, oc, free=None, noise=0.0):
    """best order of the pieces pids (cut ids, in the current = warm order) given the open cuts oc.  Without --chain
    every piece is a vertex (exact over all pieces).  With --chain 1 runs of consecutive pieces are contracted into
    one vertex, broken before and after every piece of the set free and at every join of weight >= --wbreak (exact
    over the contracted model only)."""
    ps, pe = bounds(pids, oc); S, E = keys(ps, pe)
    t0 = time.time()
    P = len(pids)
    if A.chain:
        jw = n - ovl(E[:-1], S[1:])
        fr = np.zeros(P, bool)
        if free:
            fs = set(free); fr = np.array([p in fs for p in pids])
        brk = np.zeros(P, bool); brk[0] = True
        brk[1:] = fr[1:] | fr[:-1] | (jw >= A.wbreak)
        if A.maxchain > 0:
            cl = 0
            for q in range(P):
                cl = 0 if brk[q] else cl + 1
                if cl >= A.maxchain: brk[q] = True; cl = 0
        st_ = np.flatnonzero(brk); en_ = np.append(st_[1:] - 1, P - 1)
    else:
        st_ = np.arange(P); en_ = st_
    U = len(st_)
    if len(NET.skey) > A.rebuild * U + 1000: newnet()
    want = {}
    for u in range(U):
        a, b = int(st_[u]), int(en_[u])
        k = (int(ps[a]), int(pe[b])) if a == b else (int(ps[a]), int(pe[b]), b - a + 1, int(pids[a]), int(pids[b]))
        want[k] = u
    for s_, k in enumerate(NET.skey):
        if NET.act[s_] and k not in want: NET.off(s_)
    sid = np.empty(U, np.int64)
    for k, u in want.items(): sid[u] = NET.add(k, int(S[st_[u]]), int(E[en_[u]]))
    tsync = time.time() - t0
    od, objv, info = NET.solve([int(v) for v in sid], noise=noise, rng=NRNG)
    inv = {int(s_): u for u, s_ in enumerate(sid)}
    order = []
    for s_ in od:
        u = inv[s_]; order.extend(pids[int(st_[u]):int(en_[u]) + 1])
    info["tsync"] = round(tsync, 2); info["units"] = U
    return order, info


# ---- initial state
if A.resume:
    z = np.load(A.resume)
    OPEN[z["open"]] = True
    order = [int(v) for v in z["order"]]
else:
    order = [-1] + [int(v) for v in np.flatnonzero(BACK)]
oc = np.flatnonzero(OPEN)
L0, _ = length(order, oc)
say(f"initial pieces {len(order)} length {L0}")
newnet()
if A.solve0: order, info = solve(order, oc)
else: info = "skipped (--solve0 0)"
L, _ = length(order, oc)
say(f"round 0 ({'chains' if A.chain else 'all pieces, exact'}): length {L} ({L - L0:+d}) {info}")
save(order, L)
rng = random.Random(A.seed)
tried = set(); ngain = 0
r = 0
RJ = open(os.path.join(A.out, "rounds.jsonl"), "a", buffering=1)
last_gain_round = 0; last_gain_wpos = []
RUNNAME = os.path.basename(os.path.normpath(A.out))


def emit(rec):
    RJ.write(json.dumps(rec, separators=(",", ":")) + chr(10))


def joinrec(q, wts, rank, oc):
    a, b = order[q], order[q + 1]
    ps2, pe2 = bounds([a, b], oc)
    wl, wr = int(pe2[0]) + n, int(ps2[1])   # letter positions (original word) of the join's two sides
    d = min((abs(wl - x) for x in last_gain_wpos), default=None)
    return dict(pos=int(q), pos_frac=round(q / max(1, len(order) - 1), 6), weight=int(wts[q]), rank=int(rank),
                wpos_left_end=wl, wpos_right_start=wr, len_left=int(pe2[0] - ps2[0] + n),
                len_right=int(pe2[1] - ps2[1] + n), left_is_backbone=bool(a < 0 or BACK[a]),
                right_is_backbone=bool(b < 0 or BACK[b]), letters_to_last_gain=d,
                trail_left=None, trail_right=None)

while r < A.rounds and time.time() - T0 < A.time:
    if A.stop and os.path.exists(A.stop): say("stop file"); break
    r += 1; rsg = r - last_gain_round
    t0 = time.time()
    oc = np.flatnonzero(OPEN)
    P = len(order)
    L, jo = length(order, oc)
    wts = n - jo
    pid = np.asarray(order)
    jk = [(order[q], order[q + 1]) for q in range(P - 1)]
    mode = "heavy"
    cand = []
    if A.heavy:
        cand = [int(q) for q in np.argsort(-wts, kind="stable") if wts[q] >= max(A.wmin, 1) and jk[q] not in tried]
    if cand: sel = cand[:A.K]
    else: mode = "random"; sel = rng.sample(range(P - 1), min(A.K, P - 1))
    rank_of = {}
    if mode == "heavy":
        for i_, q in enumerate(sel): rank_of[q] = i_
    jrecs = [joinrec(q, wts, rank_of.get(q, -1), oc) for q in sel]
    for q in sel: tried.add(jk[q])
    want = {}
    for q in sel:
        for d in range(A.nb):
            if q - d >= 0: want.setdefault(q - d, set()).add(1)
            if q + 1 + d < P: want.setdefault(q + 1 + d, set()).add(0)
    newc = []
    nxt = np.searchsorted(oc, pid, side="right")
    for pos, sides in want.items():
        a = order[pos]
        lo = a + 1 if a >= 0 else 0
        hi = oc[nxt[pos]] if nxt[pos] < len(oc) else len(SV)
        if hi <= lo: continue
        c = lo + np.flatnonzero(SW[lo:hi] >= A.gopen)
        if A.R > 0 and len(c) > A.R:
            pick = []
            if 1 in sides or A.far: pick.append(c[-A.R:])
            if 0 in sides or A.far: pick.append(c[:A.R])
            c = np.unique(np.concatenate(pick))
        if len(c): newc.append(c)
        if A.gfine:
            seg = SW[lo:hi]
            c = lo + np.flatnonzero((seg >= A.gfine) & (seg < A.gopen))
            if len(c) > A.Rfine:
                pick = []
                if 1 in sides or A.far: pick.append(c[-A.Rfine:])
                if 0 in sides or A.far: pick.append(c[:A.Rfine])
                c = np.unique(np.concatenate(pick))
            if len(c): newc.append(c)
    if not newc:
        say(f"round {r} {mode} joins {[int(wts[q]) for q in sel]}: nothing to open")
        emit(dict(n=n, run=RUNNAME, word=os.path.basename(A.word), round=r, mode=mode, K=A.K, joins=jrecs, cuts_opened={}, status="nothing",
                  accepted=False, gain=0, length_before=L, length_after=L)); continue
    newc = np.unique(np.concatenate(newc))
    OPEN[newc] = True
    oc2 = np.flatnonzero(OPEN)
    ins = {}
    for c in newc:
        k = np.searchsorted(oc, c, side="right") - 1
        ins.setdefault(int(oc[k]) if k >= 0 else -1, []).append(int(c))
    exp = []
    for a in order:
        exp.append(a)
        if a in ins: exp.extend(sorted(ins[a]))
    freeset = set()
    for q in sel:
        for d in range(A.D + 1):
            if q - d >= 0: freeset.add(order[q - d])
            if q + 1 + d < P: freeset.add(order[q + 1 + d])
    freeset.update(int(c) for c in newc)
    nz = A.noise if (A.noise > 0 and r % max(1, A.noiseevery) != 0) else 0.0
    neword, info = solve(exp, oc2, freeset, noise=nz)
    cw = {str(int(w_)): int(c_) for w_, c_ in zip(*np.unique(SW[newc], return_counts=True))}
    L2, on_ = length(neword, oc2)
    if L2 < L or ((A.neutral or nz > 0) and L2 == L and neword != exp):
        res = [neword[0]]; tail = neword[0]; closed = 0
        for q in range(1, len(neword)):
            b = neword[q]
            k = np.searchsorted(oc2, tail, side="right")
            nb_ = int(oc2[k]) if k < len(oc2) else None
            if b >= 0 and not BACK[b] and nb_ == b and on_[q - 1] == n - SW[b]:
                OPEN[b] = False; tail = b; closed += 1
            else:
                res.append(b); tail = b
        order = res
        L3, _ = length(order, np.flatnonzero(OPEN))
        if L3 != L2: raise RuntimeError(f"closing cuts changed the length {L2} -> {L3}")
        if L2 < L:
            ngain += 1; last_gain_round = r
            last_gain_wpos = [jr["wpos_left_end"] for jr in jrecs]
        save(order, L2)
        emit(dict(n=n, run=RUNNAME, word=os.path.basename(A.word), round=r, mode=mode, K=A.K, R=A.R, Rfine=A.Rfine, gopen=A.gopen, gfine=A.gfine,
                  chain=A.chain, joins=jrecs, cuts_opened=cw, cuts_kept=int(len(newc) - closed),
                  pieces=P, units=info.get("units", info["P"]), slots=info["slots"], subtour_cuts=info["ncuts"],
                  lp_its=info["it"], status=info["st"], t_lp=info["tlp"], t_solve=info["tsolve"],
                  t_round=round(time.time() - t0, 3), length_before=L, length_after=L2, gain=L - L2,
                  accepted=True, rounds_since_gain=rsg, noise=nz))
        say(f"round {r} {mode} joins {[int(wts[q]) for q in sel]} opened {len(newc)} kept {len(newc) - closed}: "
            f"{L} -> {L2} ({L2 - L:+d}) open {int((OPEN & ~BACK).sum())} pieces {len(order)} {info} "
            f"{time.time() - t0:.2f}s")
    else:
        OPEN[newc] = False
        if L2 > L and nz == 0: raise RuntimeError(f"exact solve gave {L2} > current {L}")
        emit(dict(n=n, run=RUNNAME, word=os.path.basename(A.word), round=r, mode=mode, K=A.K, R=A.R, Rfine=A.Rfine, gopen=A.gopen, gfine=A.gfine,
                  chain=A.chain, joins=jrecs, cuts_opened=cw, cuts_kept=0,
                  pieces=P, units=info.get("units", info["P"]), slots=info["slots"], subtour_cuts=info["ncuts"],
                  lp_its=info["it"], status=info["st"], t_lp=info["tlp"], t_solve=info["tsolve"],
                  t_round=round(time.time() - t0, 3), length_before=L, length_after=L, gain=0,
                  accepted=False, rounds_since_gain=rsg, noise=nz, length_found=L2))
        say(f"round {r} {mode} joins {[int(wts[q]) for q in sel]} opened {len(newc)}: no gain ({L2}) {info} "
            f"{time.time() - t0:.2f}s")
oc = np.flatnonzero(OPEN)
L, _ = length(order, oc)
say(f"done rounds {r} gains {ngain} length {L} open non-backbone cuts {int((OPEN & ~BACK).sum())}")
if A.write:
    wl = write(order, os.path.join(A.out, "w.txt"))
    say(f"wrote {A.out}/w.txt: {wl} letters (expected {L})")
say("END")
