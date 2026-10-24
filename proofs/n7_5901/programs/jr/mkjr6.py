"""mkjr6.py: jr6.c = ../jrev/jr.c (the source of jr3.exe) + env RVMIN (agent n7-ring16).
RVMIN=a restricts the statement to ring pieces of value rows - holes >= a, exactly as RLO / RHI restrict it to
rings with RLO..RHI holes: (1) a completed ring piece is taken only if its value is >= a; (2) a target (T, H) of
the ring rule (PROOF_5900 5.4 step 5) must have T - H >= a. Nothing else changes. Default: no restriction."""
src = open("../jrev/jr.c").read()
def rep(old, new, cnt=1):
    global src
    assert src.count(old) == cnt, (src.count(old), old[:70])
    src = src.replace(old, new)
rep("static int RLO = 0, RHI = WM;",
    "static int RVMIN = -(1 << 20);   /* env RVMIN: only rings with rows - holes >= RVMIN */\nstatic int RLO = 0, RHI = WM;")
rep("        int Tlo = NOCUT ? 2 : H + a - Best[i + 1][b - H]; if (Tlo < 2) Tlo = 2;",
    "        int Tlo = NOCUT ? 2 : H + a - Best[i + 1][b - H]; if (Tlo < 2) Tlo = 2;\n        if (Tlo < H + RVMIN) Tlo = H + RVMIN;")
rep("    if (r >= 2 && link3(q, st0) && d >= RLO && d <= RHI && JMP(i, r)) {",
    "    if (r >= 2 && link3(q, st0) && d >= RLO && d <= RHI && r - d >= RVMIN && JMP(i, r)) {")
rep('    if (getenv("RLO")) RLO = atoi(getenv("RLO"));',
    '    if (getenv("RLO")) RLO = atoi(getenv("RLO"));\n    if (getenv("RVMIN")) RVMIN = atoi(getenv("RVMIN"));')
open("jr6.c", "w").write(src)
# the same test in the estimator (mode est)
src = open("jr6.c").read()
rep("                if (r >= 2 && link3(q, s->st0) && d >= RLO && d <= RHI) {",
    "                if (r >= 2 && link3(q, s->st0) && d >= RLO && d <= RHI && r - d >= RVMIN) {")
open("jr6.c", "w").write(src)
# env RVMAX: only rings with rows - holes <= RVMAX (the same restriction as a ring row lowered to H + RVMAX,
# but exact: also tested when a ring is completed). Used by the tests; production can use a lowered ring row.
src = open("jr6.c").read()
rep("static int RLO = 0, RHI = WM;", "static int RVMAX = (1 << 20);\nstatic int RLO = 0, RHI = WM;")
rep("        int Thi = NOCUT ? RM - 1 : PRt[H]; if (Thi > RM - 1) Thi = RM - 1;",
    "        int Thi = NOCUT ? RM - 1 : PRt[H]; if (Thi > RM - 1) Thi = RM - 1;\n        if (Thi > H + RVMAX) Thi = H + RVMAX;")
rep("d >= RLO && d <= RHI && r - d >= RVMIN", "d >= RLO && d <= RHI && r - d >= RVMIN && r - d <= RVMAX", 2)
rep("                if (ptype[i] == 1) v = (w < RLO || w > RHI) ? -INF : ((NOCUT || PRt[w] >= INF) ? INF : PRt[w] - w);",
    "                if (ptype[i] == 1) { v = (w < RLO || w > RHI) ? -INF : ((NOCUT || PRt[w] >= INF) ? INF : PRt[w] - w); if (v > RVMAX) v = RVMAX; }")
rep('    if (getenv("RLO")) RLO = atoi(getenv("RLO"));', '    if (getenv("RLO")) RLO = atoi(getenv("RLO"));\n    if (getenv("RVMAX")) RVMAX = atoi(getenv("RVMAX"));')
open("jr6.c", "w").write(src)
