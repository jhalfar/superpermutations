"""brute-force test of the checks (b), (e2), (e3) of check9m.py on a sample: the dense matrix W for 3000 random big cuts
(and all cuts of the smallest big trail) against all big cuts, compared with the trie computations.
usage: test_b.py BASE"""
import sys

src = open(__file__.replace("test_b.py", "check9m.py")).read().split("# ------------------------------------------------------------------ (e4)")[0]
exec(src)
rng = np.random.default_rng(5)
samp = np.unique(np.concatenate([rng.choice(len(BC), 3000, replace=False), np.nonzero(ct[BC] == big_t[0])[0]]))
viol = 0; tight = 0; tight0 = 0; neg = 0
tp = set((int(a), int(b)) for a, b, _ in P.tolist())
found = set()
for c0 in range(0, len(samp), 200):
    rows_ = samp[c0:c0 + 200]
    Wd = Wm(BC[rows_], BC)
    neg += int((Wd < 0).sum())
    viol += int((Wd < fo[rows_][:, None] - fo[None, :]).sum()) + int((Wd < fi[None, :] - fi[rows_][:, None]).sum())
    t_ = (Wd == fo[rows_][:, None] - fo[None, :]) & (psi[rows_][:, None] == psi[None, :])
    t_[np.arange(len(rows_)), rows_] = False
    i, j = np.nonzero(t_)
    for a, b in zip(rows_[i].tolist(), j.tolist()):
        found.add((a, b))
exp = set(p for p in tp if p[0] in set(samp.tolist()))
say("sample of %d big cuts against all %d: W < 0: %d; violations of (b): %d; tight joins by brute force %d, by the trie "
    "enumeration %d, equal sets: %s" % (len(samp), len(BC), neg, viol, len(found), len(exp), found == exp))
# in1 / out1 by brute force for the sample
Wi = np.concatenate([Wm(sc[c0:c0 + 300], BC[samp]) for c0 in range(0, len(sc), 300)]).min(0)
Wo = np.concatenate([Wm(BC[samp], sc[c0:c0 + 300]) for c0 in range(0, len(sc), 300)], 1).min(1)
say("min over small cuts before / after the sampled big cuts: equal to the trie values: %s, %s" % (
    bool((Wi == in1[samp]).all()), bool((Wo == out1[samp]).all())))
