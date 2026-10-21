"""The selection and the slice order of an n = 8 word of Pantone's completion.

Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

A word of this framework writes every slice of one selection once.  Which two letters play the parts of 6 and 7,
and whether the word is read forwards or backwards, is not known in advance, so every choice is tried: the word
(or its reverse) is relabelled so that the two letters become 6 and 7 and the other six become 0 .. 5 in their
order, and then every option of every loop is tested.  An option belongs to the selection when all of its slices
occur in the word.  If every loop has exactly one such option, the options form the selection.  The word is a
word of whole slices when it is exactly the slices in the order of their positions, each overlapping the next;
then the order is returned as well, and J = length - 46,085 - Q.

If a few slices are cut (a word that opens a trail inside a slice), a loop may have no option with all slices
present.  Such a loop gets the option with the most slices present, and the result says so.
"""
import hashlib
import itertools

from . import model as M

PRE = 15        # every slice starts with b d b, 15 letters


def _relabelled(w, s, z):
    others = [c for c in sorted(set(w)) if c not in (s, z)]
    table = {c: str(i) for i, c in enumerate(others)}
    table[s] = "6"
    table[z] = "7"
    return "".join(table[c] for c in w), table


def _options(L):
    yield (L, 0)
    for x in M.LOOP_STATES[L]:
        for v in M.VALUES:
            yield (x, v)


def decompose(w):
    """w on the letters 0..7 with 6 = s and 7 = z.  Returns None or a dict with the selection, the number of loops
    without a complete option, and (for a word of whole slices) the order and the overlaps."""
    index = {}
    for p in range(len(w) - PRE + 1):
        index.setdefault(w[p:p + PRE], []).append(p)

    def where(s):
        return [p for p in index.get(s[:PRE], ()) if w.startswith(s, p)]

    sel = {}
    partial = 0
    for L in M.LOOPS:
        full, best = [], (0, None)
        for o in _options(L):
            sl = M.option_slices(*o)
            found = sum(1 for name, s in sl if where(s))
            if found == len(sl):
                full.append(o)
            elif found / len(sl) > best[0]:
                best = (found / len(sl), o)
        if len(full) == 1:
            sel[L] = full[0]
        elif not full and best[1] is not None and best[0] >= 0.5:
            sel[L] = best[1]
            partial += 1
        else:
            return None
    if not M.balanced(sel):
        return None
    out = {"sel": sel, "partial": partial, "order": None, "overlaps": None}
    if partial:
        return out
    keys, strs = M.slices(sel)
    pos = []
    for i, s in enumerate(strs):
        ps = where(s)
        if len(ps) != 1:
            return out
        pos.append(ps[0])
    order = sorted(range(len(strs)), key=lambda i: pos[i])
    ovs = []
    for a, b in zip(order, order[1:]):
        ovs.append(pos[a] + len(strs[a]) - pos[b])
    if pos[order[0]] != 0 or any(k < 0 for k in ovs):
        return out
    word, _ = M.assemble(strs, order, ovs)
    if word == w:
        out["order"] = order
        out["overlaps"] = ovs
        out["keys"] = keys
        out["strs"] = strs
    return out


def extract(w, find_all=False):
    """try both directions and all 56 choices of the letters s and z.  Returns a list of results (dicts with the
    keys of decompose() and direction, s, z, table)."""
    letters = sorted(set(w))
    if len(letters) != 8:
        raise ValueError("the word has %d different letters, not 8" % len(letters))
    found = []
    tries = [(d, s, z) for d in ("forward", "backward") for s, z in itertools.permutations(letters, 2)]
    # the usual labelling first
    tries.sort(key=lambda t: (t[0] != "forward", (t[1], t[2]) != (letters[6], letters[7])))
    for d, s, z in tries:
        src = w if d == "forward" else w[::-1]
        r, table = _relabelled(src, s, z)
        res = decompose(r)
        if res is None:
            continue
        res.update(direction=d, s=s, z=z, table=table)
        found.append(res)
        if not find_all:
            break
    return found


def sha256(w):
    return hashlib.sha256(w.encode()).hexdigest()
