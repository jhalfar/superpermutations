"""mkgj3.py (agent n7-tune16): gj3 = the card program gpu2/gj2 (host gj2.c, core jr_core.h, kernel gj2.cu) + env RVMIN.
RVMIN=a restricts the statement to ring pieces with rows - holes >= a, exactly as ringcap/mkjr6.py does it in jr.c:
(1) a target (T, H) of the ring rule must have T - H >= a (host keep table and getkeep of the core);
(2) a completed ring is taken only if rows - holes >= a (core above the gate, kernel below it, and the look-ahead table).
The kernel gets RVMIN packed into the argument RHI (RHI + 256 * (RVMIN + 128), RVMIN clamped to -128..127), so the
argument list is unchanged.  Default: no restriction, and then every count is that of gj2.  Nothing in gpu2 is changed."""
G = "../../gpu2/"
def patch(name, out, reps):
    src = open(G + name).read()
    for old, new, cnt in reps:
        assert src.count(old) == cnt, (name, src.count(old), old[:60])
        src = src.replace(old, new)
    open(out, "w", newline="\n").write(src)
patch("jr_core.h", "jr_core.h", [
    ("static int RLO = 0, RHI = WM;", "static int RVMIN = -(1 << 20);   /* env RVMIN: only rings with rows - holes >= RVMIN */\nstatic int RLO = 0, RHI = WM;", 1),
    ("        int Tlo = NOCUT ? 2 : H + a - Best[i + 1][b - H]; if (Tlo < 2) Tlo = 2;",
     "        int Tlo = NOCUT ? 2 : H + a - Best[i + 1][b - H]; if (Tlo < 2) Tlo = 2;\n        if (Tlo < H + RVMIN) Tlo = H + RVMIN;", 1),
    ("    if (r >= 2 && link3(q, st0) && d >= RLO && d <= RHI && JMP(i, r)) {",
     "    if (r >= 2 && link3(q, st0) && d >= RLO && d <= RHI && r - d >= RVMIN && JMP(i, r)) {", 1),
])
patch("gj2.c", "gj3.c", [
    ('RLO = envi("RLO", 0); RHI = envi("RHI", WM);', 'RLO = envi("RLO", 0); RHI = envi("RHI", WM); RVMIN = envi("RVMIN", -(1 << 20));', 1),
    ('RLO=%d RHI=%d REV=%d', 'RLO=%d RHI=%d RVMIN=%d REV=%d', 1),
    ('NOCUT, PARTI, NPARTS, DEPTH, P2, NP2, RLO, RHI, REV,', 'NOCUT, PARTI, NPARTS, DEPTH, P2, NP2, RLO, RHI, RVMIN, REV,', 1),
    ("                if ((r + 1 > 2 ? r + 1 : 2) > hi) continue;",
     "                if ((r + 1 > 2 ? r + 1 : 2) > hi) continue;\n                if (hi < H + RVMIN) continue;      /* RVMIN: no target of value >= RVMIN is left */", 1),
    ("if (r2 >= 2 && d2 >= RLO && d2 <= RHI && Best[i + 1][b - d2] > -INF) {", "if (r2 >= 2 && d2 >= RLO && d2 <= RHI && r2 - d2 >= RVMIN && Best[i + 1][b - d2] > -INF) {", 1),
    ('sprintf(pdef, "gj2_%d.ptx", K);', 'sprintf(pdef, "gj3_%d.ptx", K);', 1),
    ("int qni = (int)qn, round = 0,", "int RHIX = RHI + 256 * ((RVMIN < -128 ? -128 : (RVMIN > 127 ? 127 : RVMIN)) + 128);\n    int qni = (int)qn, round = 0,", 1),
    ("&PA, &PB, &PH, &RLO, &RHI, &P2,", "&PA, &PB, &PH, &RLO, &RHIX, &P2,", 1),
])
patch("gj2.cu", "gj3.cu", [
    ("int RLO, int RHI, int p2, int np2, int lw, int krw)\n{", "int RLO, int RHIX, int p2, int np2, int lw, int krw)\n{\n    const int RHI = RHIX & 255, RVM = (RHIX >> 8) - 128;      /* RVMIN packed by the host gj3.c */", 1),
    ("            if (r2 >= 2 && d2 >= RLO && d2 <= RHI) {", "            if (r2 >= 2 && d2 >= RLO && d2 <= RHI && val >= RVM) {", 1),
    ("vi = k3 | (u32)(r2 >= 2 && d2 >= RLO && d2 <= RHI && (!ordsk || val <= pv));", "vi = k3 | (u32)(r2 >= 2 && d2 >= RLO && d2 <= RHI && val >= RVM && (!ordsk || val <= pv));", 1),
])
print("written: jr_core.h gj3.c gj3.cu")
