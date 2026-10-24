# mkcore.py (agent n7-gpuj): jr_core.h = lines 38..363 of programs/jr/jr.c (geometry, tables, the search above the
# gate) with two hooks: a node at the gate becomes a task of the card (rows), a completed piece above the gate becomes
# a task (jump).  Every anchor must occur exactly once.
import io, os, sys
here = os.path.dirname(os.path.abspath(__file__))
src = io.open(os.path.join(here, '..', 'jrev', 'jr.c'), encoding='utf-8').read().split('\n')
core = '\n'.join(src[37:363]) + '\n'
def rep(s, old, new):
    if s.count(old) != 1:
        sys.exit('anchor not unique: ' + old[:60])
    return s.replace(old, new)
old = ("            stk_e[sp] = st; stk_l[sp] = l; stk_p[sp] = i; stk_k[sp] = kind; sp++;\n"
       "            if (ptype[i]) ring_node(i, a, b, kr, st0, ent[l - 1], r + 1, dd, pm, pM);\n"
       "            else seq_node(i, a, b, ent[l - 1], r + 1, dd, t, recmax, pm, pM);\n"
       "            sp--;\n")
new = ("            if (GATE && i == 0 && r + 1 == DEPTH) { if (NPARTS == 1 || (fcount++ % NPARTS) == PARTI) emit_gate(st, st0, l, isd, r, d, t, recmax, kind, pm, pM); } else {\n"
       + old + "            }\n")
core = rep(core, old, new)
old = "    if (RMODE == 2) { pm = pM = 0; basef[i] = 0; }\n    uint8_t save[MAXC];"
new = "    if (GATE) { emit_jump(i, a, b); return; }\n" + old
core = rep(core, old, new)
core = rep(core, "static void rows(int i, int a, int b, const uint8_t *kr, int st0, int st, int r, int d, int t, int recmax, int kind, int pm, int pM) {",
           "static int GATE = 0;\nstatic void emit_gate(int st, int st0, int l, const int *isd, int r, int d, int t, int recmax, int kind, int pm, int pM);\nstatic void emit_jump(int i, int a, int b);\n"
           "static void rows(int i, int a, int b, const uint8_t *kr, int st0, int st, int r, int d, int t, int recmax, int kind, int pm, int pM) {")
io.open(os.path.join(here, 'jr_core.h'), 'w', encoding='utf-8', newline='\n').write(core)
print('jr_core.h written,', core.count('\n'), 'lines')
