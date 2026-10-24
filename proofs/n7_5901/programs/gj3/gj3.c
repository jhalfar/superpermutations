/* gj.c (agent n7-gpuj, 2026-10-11): host of gj.cu, the joint search of programs/jr/jr.c on the card.
 * jr_core.h = lines 38..363 of jr.c (geometry, caps, tables Best / G / reversal tables / ring keep, the search) with
 * two hooks (mkcore.py): the host walks piece 1 down to the gate with the code of jr.c and hands over
 *   - every node at the gate (DEPTH rows of piece 1, index modulo NPARTS = PART, as jr.c) as a task "parent frame with
 *     this one row and this one length", and
 *   - every piece completed above the gate (part 0 only, as jr.c) as a task "start frame of piece 2".
 * Without DEPTH the one task is the start frame of piece 1.  The card does the rest (gj.cu) and counts kept prefixes,
 * rows tried and objects per piece; nodes above the gate are counted by the code of jr.c.
 * usage: gj K caps run V W B piece...     env as jr.c: PART NPARTS DEPTH PART2 NPARTS2 RLO RHI NOCUT ORD JCAP,
 *        REV=1 RMODE=2 RP PA PB PH (the cut on one piece; RMODE=1 is not on the card)
 *        card: GN threads (262144), GK steps per round (5000), GTRIES (8), MAXSEC (1500), VERB, PTX (gj<K>.ptx), GBT (128, as built), CHECK=1
 * build: gcc -O2 -o gj.exe gj.c ; build_ptx.bat gj.cu gj7.ptx 6   (5, 6 symbols: gj5.ptx 4, gj6.ptx 5)
 * limits: at most 7 symbols, 4 pieces, B <= 3, V <= 118; the first 10 objects are written out and checked on the host
 */
#include <windows.h>
#include "jr_core.h"
typedef unsigned long long u64;
typedef unsigned int u32;
#define STK 192
#define UW 45
#define SMX 10
#define NOFF2 168
#define NN2 428
#define MAXSV 4
#define NFND 16

static void finish(void) { }
static void est_piece(int i, int a, int b, const uint64_t *U0, int dups0, double w0, int base, int pm0, int pM0, int pv) { (void)i; (void)a; (void)b; (void)U0; (void)dups0; (void)w0; (void)base; (void)pm0; (void)pM0; (void)pv; }

static u32 *TASKU; static u64 *TASKF; static int *TASKH; static long long qn, qcap;
static int N3, N4, NS, NVd, dv[MAXP], idv[MAXP * 2];
static int replay = 0; static long long want = -1; static int rp_e[1024], rp_l[1024], rp_k[1024], rp_n;
static int ctxpack(int a, int b, int pv) { return (a & 0xffff) | (b << 16) | ((pv & 0xff) << 24); }
static int task_new(void) {
    if (replay) { if (qn == want) { rp_n = sp; for (int i = 0; i < sp; i++) { rp_e[i] = stk_e[i]; rp_l[i] = stk_l[i]; rp_k[i] = stk_k[i]; } } qn++; return 0; }
    if (qn == qcap) {
        qcap = qcap ? 2 * qcap : 1 << 14;
        TASKU = (u32 *)realloc(TASKU, (size_t)qcap * UW * 4); TASKF = (u64 *)realloc(TASKF, (size_t)qcap * 16); TASKH = (int *)realloc(TASKH, (size_t)qcap * 8);
        if (!TASKU || !TASKF || !TASKH) { fprintf(stderr, "out of memory for the gate tasks\n"); exit(1); }
    }
    memset(TASKU + qn * UW, 0, UW * 4);
    return 1;
}
static void emit_gate(int st, int st0, int l, const int *isd, int r, int d, int t, int recmax, int kind, int pm, int pM) {
    if (!task_new()) return;
    u32 *u = TASKU + qn * UW;
    int rowc[8], x = st, nd = 0; unsigned dmk = 0;
    for (int q = 0; q < l; q++) { rowc[q] = CLS[x]; x = T2[x]; if (isd[q]) { nd++; dmk |= 1u << q; } }
    for (int c = 0; c < NC; c++) {
        int uu = U[c], cc = C[c];
        for (int q = 0; q < l; q++) if (rowc[q] == c) { cc = 0; if (!isd[q]) uu = 0; }
        u[c >> 4] |= (u32)((uu ? 1 : 0) | (cc ? 2 : 0)) << (2 * (c & 15));
    }
    int tpar = t - (kind == 4), rc8 = recmax < -128 ? -128 : recmax;
    TASKF[2 * qn] = ((u64)dv[st] << 32) | ((u64)l << 45) | ((u64)(l - 1) << 48) | ((u64)(kind == 4 ? N3 : 0) << 51) | ((u64)dmk << 56) | (1ull << 63);
    TASKF[2 * qn + 1] = (ptype[0] ? (u64)(dv[st0] & 0x3fff) : ((u64)(pm & 0x3fff) | ((u64)(pM & 0x3fff) << 14))) | ((u64)7 << 28) | ((u64)7 << 61)
        | ((u64)r << 32) | ((u64)d << 40) | ((u64)tpar << 47) | ((u64)(rc8 & 0xff) << 51) | ((u64)((dups - nd) & 3) << 59) | ((u64)((dups - nd) >> 2) << 31);
    TASKH[2 * qn] = 0; TASKH[2 * qn + 1] = ctxpack(V, W, 0);
    qn++;
}
static void emit_jump(int i, int a, int b) {
    if (i != 1) { fprintf(stderr, "jump above the gate into piece %d\n", i + 1); exit(9); }
    int cnt = (NP - P2 + NP2 - 1) / NP2;
    if (!task_new()) return;
    tries[1] += cnt;
    u32 *u = TASKU + qn * UW;
    for (int c = 0; c < NC; c++) if (U[c]) u[c >> 4] |= 1u << (2 * (c & 15));
    TASKF[2 * qn] = ((u64)cnt << 13) | (1ull << 63);
    TASKF[2 * qn + 1] = ((u64)0x80 << 51) | ((u64)(dups & 3) << 59) | ((u64)(dups >> 2) << 31) | ((u64)7 << 28) | ((u64)7 << 61);
    TASKH[2 * qn] = 1; TASKH[2 * qn + 1] = ctxpack(a, b, pval[0]);
    qn++;
}
static int cl16(long long v) { return v >= 30000 ? 30000 : (v <= -30000 ? -30000 : (int)v); }
static u64 pk4(long long a, long long b, long long c, long long d) { return (u64)(uint16_t)cl16(a) | ((u64)(uint16_t)cl16(b) << 16) | ((u64)(uint16_t)cl16(c) << 32) | ((u64)(uint16_t)cl16(d) << 48); }

/* an object written by the card: print it as jr.c does and check it from the definitions */
static void show_object(const u64 *fo, const long long *tq) {
    int n = (int)fo[0]; long long q = (long long)fo[1];
    int e[1024], ln[1024], pc[1024], kd[1024], m = 0;
    int p = tq ? TASKH[2 * q] : 0;
    if (GATE) {                                   /* rows above the gate: walk again to task q */
        long long sk_[MAXPC], st_[MAXPC], sc_[MAXPC], sf_ = fcount, sq_ = qn;
        memcpy(sk_, kept, sizeof sk_); memcpy(st_, tries, sizeof st_); memcpy(sc_, comp, sizeof sc_);
        replay = 1; want = q; qn = 0; fcount = 0; sp = 0; dups = 0; memset(U, 0, sizeof U); memset(C, 0, sizeof C);
        const uint8_t *kr = ptype[0] ? getkeep(0, V, W) : NULL;
        rows(0, V, W, kr, 0, 0, 0, 0, 0, -INF, 0, 0, 0);
        replay = 0; fcount = sf_; qn = sq_;
        memcpy(kept, sk_, sizeof sk_); memcpy(tries, st_, sizeof st_); memcpy(comp, sc_, sizeof sc_);
        for (int i = 0; i < rp_n; i++) { e[m] = rp_e[i]; ln[m] = rp_l[i]; pc[m] = 0; kd[m] = rp_k[i]; m++; }
    }
    for (int g = 0; g < n; g++) {
        u64 a = fo[2 + 2 * g];
        int st = (int)(a >> 63), x = idv[(int)(a >> 32) & 0x1fff], l2 = (int)(a >> 48) & 7, j = (int)(a >> 51) & 31;
        if (st && g > 0) p++;
        if (!l2) continue;
        e[m] = st ? x : (j < N3 ? succ3[x][j] : succ4[x][j - N3]); ln[m] = l2; pc[m] = p; kd[m] = j >= N3 ? 4 : 3; m++;
    }
    printf("FOUND:");
    for (int i = 0; i < m; i++) {
        if (i == 0 || pc[i] != pc[i - 1]) printf(" | %c", ptype[pc[i]] ? 'R' : 'S'); else if (kd[i] == 4) printf(" /");
        printf(" "); for (int k = 0; k < K; k++) printf("%d", PERM[e[i]][k]); printf(":%d", ln[i]);
    }
    /* check */
    static int cntc[MAXC]; memset(cntc, 0, sizeof cntc);
    int ok = 1, tv = 0, tw = 0, i0 = 0;
    while (i0 < m) {
        int i1 = i0; while (i1 < m && pc[i1] == pc[i0]) i1++;
        int pi = pc[i0], rows_ = i1 - i0, holes = 0, heavy = 0; static int inp[MAXC]; memset(inp, 0, sizeof inp);
        for (int i = i0; i < i1; i++) {
            int x = e[i], endv = x;
            for (int k = 0; k < ln[i]; k++) { if (inp[CLS[x]]++) ok = 0; endv = x; x = T2[x]; }
            holes += L - ln[i];
            int nx = i + 1 < i1 ? e[i + 1] : (ptype[pi] ? e[i0] : -1);
            if (nx >= 0) {
                int k4 = (i + 1 < i1) && kd[i + 1] == 4, f = 0;
                if (k4) { heavy++; for (int k = 0; k < nsucc4[endv]; k++) if (succ4[endv][k] == nx) f = 1; } else f = link3(endv, nx);
                if (!f) ok = 0;
            }
        }
        if (ptype[pi]) { tv += rows_ - holes; tw += holes; if (rows_ < 2 || holes < RLO || holes > RHI) ok = 0; }
        else { tv += rows_ - holes - c5 * heavy; tw += holes + c6 * heavy; if (heavy > pS[pi]) ok = 0; }
        for (int c = 0; c < NC; c++) if (inp[c]) cntc[c]++;
        i0 = i1;
    }
    int sh = 0; for (int c = 0; c < NC; c++) if (cntc[c] > 1) sh += cntc[c] - 1;
    if (tv < V || tw > W || sh > B || (m ? pc[m - 1] : -1) != npc - 1) ok = 0;
    printf("   [value %d weight %d shared %d: %s]\n", tv, tw, sh, ok ? "checked" : "BAD OBJECT");
}

/* ---------------------------------------------------- CUDA driver ---------------------------------------------------- */
typedef u64 DP;
static int (__stdcall *cuInit)(unsigned), (__stdcall *cuDeviceGet)(int *, int), (__stdcall *cuCtxCreate)(void **, unsigned, int), (__stdcall *cuCtxDestroy)(void *);
static int (__stdcall *cuModuleLoadData)(void **, const void *), (__stdcall *cuModuleGetFunction)(void **, void *, const char *);
static int (__stdcall *cuMemAlloc)(DP *, size_t), (__stdcall *cuMemsetD8)(DP, unsigned char, size_t);
static int (__stdcall *cuHtoD)(DP, const void *, size_t), (__stdcall *cuDtoH)(void *, DP, size_t), (__stdcall *cuCtxSync)(void);
static int (__stdcall *cuLaunch)(void *, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned, void *, void **, void **);
#define CK(x) do { int e_ = (x); if (e_) { fprintf(stderr, "CUDA driver error %d at line %d\n", e_, __LINE__); exit(3); } } while (0)
static double wall(void) { LARGE_INTEGER f, c; QueryPerformanceFrequency(&f); QueryPerformanceCounter(&c); return (double)c.QuadPart / (double)f.QuadPart; }
static double devbytes = 0;
static DP dalloc(size_t n, const void *src) { DP p; devbytes += (double)n; CK(cuMemAlloc(&p, n ? n : 8)); if (src) CK(cuHtoD(p, src, n)); else CK(cuMemsetD8(p, 0, n ? n : 8)); return p; }
static int envi(const char *n, int dflt) { return getenv(n) ? atoi(getenv(n)) : dflt; }

int main(int argc, char **argv) {
    if (argc < 8 || strcmp(argv[3], "run")) { fprintf(stderr, "usage: gj K caps run V W B piece...\n"); return 2; }
    K = atoi(argv[1]); build();
    NOCUT = envi("NOCUT", 0); PARTI = envi("PART", 0); NPARTS = envi("NPARTS", 1); DEPTH = envi("DEPTH", 0); P2 = envi("PART2", 0); NP2 = envi("NPARTS2", 1);
    RLO = envi("RLO", 0); RHI = envi("RHI", WM); RVMIN = envi("RVMIN", -(1 << 20)); REV = envi("REV", 0); RMODE = envi("RMODE", 1); PA = envi("PA", 10); PB = envi("PB", 15); PH = envi("PH", 30);
    ORD = envi("ORD", 0); RP = envi("RP", 0); int ORDS = envi("ORDS", 0);
    int GN = envi("GN", 262144), GK = envi("GK", 5000), GTRIES = envi("GTRIES", 8), MAXSEC = envi("MAXSEC", 1500), VERB = envi("VERB", 0);
    readcaps(argv[2]);
    V = atoi(argv[4]); W = atoi(argv[5]); B = atoi(argv[6]);
    if (W > WM - 2) { fprintf(stderr, "W too large\n"); return 2; }
    int ai = 7; npc = 0;
    while (ai < argc && (argv[ai][0] == 'R' || argv[ai][0] == 'S') && npc < MAXPC) {
        if (argv[ai][0] == 'R') { ptype[npc] = 1; pS[npc] = 0; } else { ptype[npc] = 0; pS[npc] = atoi(argv[ai] + 1); }
        npc++; ai++;
    }
    mktables();
    for (int i = 1; i < npc; i++) samekind[i] = ptype[i] == ptype[i - 1] && pS[i] == pS[i - 1];
    if (ORD && npc == 2 && samekind[1]) HALFV = V > 0 ? (V + 1) / 2 : -INF;
    if (getenv("JCAP")) readjcap(getenv("JCAP"));
    mkrev();
    if (RP < 0 || RP >= npc) { fprintf(stderr, "RP out of range\n"); return 2; }
    if (REV && RMODE != 2) { fprintf(stderr, "the card has the cut on one piece only: REV=1 needs RMODE=2\n"); return 2; }
    if (PA * 200 + PB * 127 + PH * 21 > 8000 || V + 9 > 127 || (NOCUT && V + 7 * W + 16 > 127)) { fprintf(stderr, "potential or V out of the range of the frame\n"); return 2; }
    if (B > 4 || npc > 5 || NP2 > 2048 || P2 >= NP2 || (NPARTS > 1 && DEPTH < 1) || K > 7) { fprintf(stderr, "parameters out of range\n"); return 2; }
    for (int i = 0; i < npc; i++) if (pS[i] >= SMX) return 2;
    int n3 = nsucc3[0], n4 = nsucc4[0], ns = n3 + n4;
    for (int q = 0; q < NP; q++) if (nsucc3[q] != n3 || nsucc4[q] != n4) { fprintf(stderr, "successor counts differ\n"); return 9; }
    if (ns > 32 || n3 < 1) { fprintf(stderr, "successors do not fit a 32-bit mask\n"); return 9; }
    N3 = n3; N4 = n4; NS = ns;
    if (ns > 24 && envi("SC", 3) == 2) { fprintf(stderr, "more than 24 successors: build the kernel with -DSC=3 and set SC=3\n"); return 9; }
    printf("gj K=%d caps=%s V=%d W=%d B=%d pieces", K, argv[2], V, W, B);
    for (int i = 0; i < npc; i++) { if (ptype[i]) printf(" R"); else printf(" S%d", pS[i]); }
    printf("  NOCUT=%d PART=%d/%d DEPTH=%d PART2=%d/%d RLO=%d RHI=%d RVMIN=%d REV=%d RP=%d potential %d,%d,%d ORD=%d ORDS=%d JCAP=%s  table bound of the total: %d\n",
           NOCUT, PARTI, NPARTS, DEPTH, P2, NP2, RLO, RHI, RVMIN, REV, RP, PA, PB, PH, ORD, ORDS, getenv("JCAP") ? getenv("JCAP") : "-", Best[0][W]);
    fflush(stdout);
    /* ---- device tables ---- */
    for (int q = 0; q < NP; q++) dv[q] = -1;
    { int orb = 0; for (int q = 0; q < NP; q++) if (dv[q] < 0) { int x = q, pos = 0; do { dv[x] = orb * 8 + pos; idv[orb * 8 + pos] = x; pos++; x = T2[x]; } while (x != q); if (pos != L) return 9; orb++; } NVd = orb * 8; }
    size_t nrow = (size_t)NVd * 33;
    u64 *hROWC2 = (u64 *)calloc(nrow * 2, 8), *hSUCCC = (u64 *)calloc((size_t)NVd * 6, 8); int SCW = envi("SC", 3);
    if (SCW != 2 && SCW != 3) return 2; unsigned short *hX2 = (unsigned short *)calloc(NP, 2);
    for (int q = 0; q < NP; q++) hX2[q] = (unsigned short)dv[q];
    for (int q = 0; q < NP; q++) {
        for (int i = 0; i <= ns; i++) {
            int v = i < n3 ? succ3[q][i] : i < ns ? succ4[q][i - n3] : q;
            size_t rid = i < ns ? (size_t)dv[q] * 32 + i : (size_t)NVd * 32 + dv[q];
            int x = v; u64 w = 0;
            for (int l = 1; l <= L; l++) { w |= (u64)CLS[x] << (10 * (l - 1)); x = T2[x]; }
            hROWC2[2 * rid] = w; hROWC2[2 * rid + 1] = (u64)dv[v];
            if (i < ns) hSUCCC[dv[q] * 2 * SCW + i / 6] |= (u64)CLS[v] << (10 * (i % 6));
        }
    }
    size_t ntb = (size_t)npc * SMX * 128; u64 *hTB = (u64 *)calloc(ntb, 8);
    for (int i = 0; i < npc; i++) for (int tl = 0; tl < SMX; tl++) for (int bl = 0; bl < 128; bl++) {
        long long g3 = -INF, g4 = -INF, b1 = Best[i + 1][bl], b2 = INF;
        if (!ptype[i] && tl <= pS[i]) { g3 = G[i][tl][bl]; if (tl >= 1 && bl >= c6) g4 = G[i][tl - 1][bl - c6]; }
        if (ORD && i < npc - 1 && samekind[i + 1]) b2 = Best[i + 2][bl];
        if (i == 0 && HALFV > -INF && !ptype[0]) {
            long long h3 = (long long)V - HALFV + G1[tl][bl]; if (h3 < g3) g3 = h3;
            if (tl >= 1 && bl >= c6) { long long h4 = (long long)V - HALFV + G1[tl - 1][bl - c6]; if (h4 < g4) g4 = h4; }
            if (V - HALFV < b1) b1 = V - HALFV;
        }
        hTB[((size_t)(i * SMX + tl) << 7) + bl] = pk4(g3, g4, b1, b2);
    }
    int isrp = REV && !ptype[RP];
    size_t nrv = isrp ? (size_t)SMX * NN2 * 128 : 1; u64 *hRV = (u64 *)calloc(nrv, 8);
    if (isrp) for (int tl = 0; tl < SMX; tl++) for (int n = 0; n < NN2; n++) for (int bl = 0; bl < 128; bl++) {
        int need = n - NOFF2; long long c1h = 0, a2h = 0;
        if (tl >= 1 && bl >= c6) { c1h = (long long)CN1(need + c5, bl - c6) - 2 * PH; a2h = A2P(tl - 1, need + c5, bl - c6); }
        hRV[((size_t)(tl * NN2 + n) << 7) + bl] = pk4(CN1(need, bl), A2P(tl, need, bl), c1h, a2h);
    }
    int nring = 0, rordv[MAXPC];
    for (int i = 0; i < npc; i++) rordv[i] = ptype[i] ? nring++ : 0;
    int krw = (W + 1) * RM * 128; unsigned char *hKR = (unsigned char *)calloc((size_t)(nring ? nring : 1) * krw, 1);
    for (int i = 0; i < npc; i++) if (ptype[i]) {
        unsigned char *kt = hKR + (size_t)rordv[i] * krw;
        for (int b = 0; b <= W; b++) for (int H = 0; H <= b && H < WM; H++) {
            int bb = Best[i + 1][b - H];
            if (bb <= -INF || H < RLO || H > RHI) continue;
            int Thi = NOCUT ? RM - 1 : PRt[H]; if (Thi > RM - 1) Thi = RM - 1;
            for (int d = 0; d <= H; d++) for (int r = 1; r < Thi; r++) {
                int hi = Thi;
                if (!NOCUT) { if (P[0][H - d] < INF && r + P[0][H - d] < hi) hi = r + P[0][H - d]; if (d > 0 && (r * H) / d < hi) hi = (r * H) / d; }
                if ((r + 1 > 2 ? r + 1 : 2) > hi) continue;
                if (hi < H + RVMIN) continue;      /* RVMIN: no target of value >= RVMIN is left */
                long long am = (NOCUT || bb >= INF) ? WM : (long long)hi - H + bb;
                if (am > WM) am = WM;
                if (am < 0) continue;
                unsigned char *e = kt + ((size_t)b * RM + r) * 128 + d;
                if (am + 1 > *e) *e = (unsigned char)(am + 1);
            }
        }
        if (envi("CHECK", 0)) {
            long long bad = 0, cmp = 0;
            for (int s = 0; s < 60; s++) {
                int a = (int)(rng() % (unsigned)(V + 12)) - 6, b = (int)(rng() % (unsigned)(W + 1));
                const uint8_t *k = getkeep(i, a, b);
                for (int r = 0; r < RM; r++) for (int d = 0; d < WM; d++) { cmp++; if ((k[r * WM + d] != 0) != ((int)kt[((size_t)b * RM + r) * 128 + d] > (a > 0 ? a : 0))) bad++; }
            }
            fprintf(stderr, "CHECK ring keep table of piece %d against getkeep: %lld entries compared, %lld differ\n", i + 1, cmp, bad);
            if (bad) return 9;
        }
    }
    /* prefilter: MT = for a sequence node (piece, links left, weight left), per number of holes k of the next row, the
       largest "value still needed" with which the child can be kept or complete (light, heavy); RK6 the same for rings */
    u64 *hMT = (u64 *)calloc(ntb * 2, 8);
    for (int i = 0; i < npc; i++) for (int tl = 0; tl < SMX; tl++) for (int bl = 0; bl < 128; bl++) {
        u64 lt = 0, hv = 0;
        for (int k = 0; k < L; k++) for (int hh = 0; hh < 2; hh++) {
            int tl2 = tl - hh, bl2 = bl - k - (hh ? c6 : 0); long long thr = 0;
            if (!ptype[i] && tl <= pS[i] && tl2 >= 0 && bl2 >= 0) {
                u64 E = hTB[((size_t)(i * SMX + tl2) << 7) + bl2];
                int mx = (short)(E & 0xffff), g4 = (short)((E >> 16) & 0xffff), b1 = (short)((E >> 32) & 0xffff);
                if (g4 > mx) mx = g4; if (b1 > mx) mx = b1;
                thr = (long long)mx + 1 - k - (hh ? c5 : 0) + 40;
                if (thr > 127) thr = 127; if (thr < 1) thr = 1;
            }
            if (hh) hv |= (u64)thr << (8 * k); else lt |= (u64)thr << (8 * k);
        }
        for (int k = L - 2; k >= 0; k--) {                     /* masks are prefixes: make the thresholds monotone */
            u64 n3_ = (lt >> (8 * (k + 1))) & 255, n4_ = (hv >> (8 * (k + 1))) & 255;
            if (n3_ > ((lt >> (8 * k)) & 255)) lt = (lt & ~((u64)255 << (8 * k))) | (n3_ << (8 * k));
            if (n4_ > ((hv >> (8 * k)) & 255)) hv = (hv & ~((u64)255 << (8 * k))) | (n4_ << (8 * k));
        }
        {   u64 E = hTB[((size_t)(i * SMX + tl) << 7) + bl]; int vv[4];
            for (int z = 0; z < 4; z++) { int v = (short)((E >> (16 * z)) & 0xffff);
                if (v <= -30000) vv[z] = 0; else if (v + 60 >= 255) vv[z] = 255; else if (v + 60 < 1) { fprintf(stderr, "table value %d below the range of the rule bytes\n", v); return 9; } else vv[z] = v + 60; }
            lt |= ((u64)vv[0] << 48) | ((u64)vv[1] << 56); hv |= ((u64)vv[2] << 48) | ((u64)vv[3] << 56); }
        hMT[2 * (((size_t)(i * SMX + tl) << 7) + bl)] = lt; hMT[2 * (((size_t)(i * SMX + tl) << 7) + bl) + 1] = hv;
    }
    size_t nrk = (size_t)(nring ? nring : 1) * krw + 512; u64 *hRK6 = (u64 *)calloc(nrk, 8);
    for (int i = 0; i < npc; i++) if (ptype[i]) {
        const unsigned char *kt = hKR + (size_t)rordv[i] * krw;
        for (int b = 0; b <= W; b++) for (int r = 0; r < RM; r++) for (int d = 0; d < 128; d++) {
            u64 e = 0;
            for (int k = 0; k < L; k++) {
                int r2 = r + 1, d2 = d + k, by = 0;
                if (d2 <= b && d2 < 128) {
                    if (r2 < RM && kt[((size_t)b * RM + r2) * 128 + d2]) { by = kt[((size_t)b * RM + r2) * 128 + d2]; if (by > 127) by = 127; }
                    if (r2 >= 2 && d2 >= RLO && d2 <= RHI && r2 - d2 >= RVMIN && Best[i + 1][b - d2] > -INF) {
                        long long v = (long long)r2 - d2 + Best[i + 1][b - d2] + 1; if (v > 127) v = 127; if (v < 1) v = 1;
                        if (v > by) by = (int)v;
                    }
                }
                e |= (u64)by << (8 * k);
            }
            for (int k = L - 2; k >= 0; k--) { u64 n_ = (e >> (8 * (k + 1))) & 255; if (n_ > ((e >> (8 * k)) & 255)) e = (e & ~((u64)255 << (8 * k))) | (n_ << (8 * k)); }
            { int own = kt[((size_t)b * RM + r) * 128 + d]; if (own > 127) own = 127; e |= (u64)own << 56; }
            hRK6[(size_t)rordv[i] * krw + ((size_t)b * RM + r) * 128 + d] = e;
        }
    }
    int lw = (NVd + 31) / 32; u32 *hL3 = (u32 *)calloc((size_t)NVd * lw, 4);
    for (int q = 0; q < NP; q++) for (int i = 0; i < n3; i++) { int v = dv[succ3[q][i]]; hL3[(size_t)dv[q] * lw + (v >> 5)] |= 1u << (v & 31); }
    u64 pcw = 0;
    for (int i = 0; i < npc; i++) {
        int ords = ORDS && i >= 2 && ptype[i] && ptype[i - 1];      /* rule ORDS: runs of rings behind piece 1 are listed by start vertex */
        u64 pi = (u64)ptype[i] | ((u64)pS[i] << 1) | ((u64)((ORD && i >= 1 && samekind[i] && !(ORDS && ptype[i])) ? 1 : 0) << 5) | ((u64)ords << 10) | ((u64)((isrp && i == RP) ? 1 : 0) << 6)
            | ((u64)(i == npc - 1) << 7) | ((u64)rordv[i] << 8);
        pcw |= pi << (12 * i);
    }
    /* ---- the gate ---- */
    double t0 = wall();
    if (DEPTH >= 1) {
        GATE = 1;
        const uint8_t *kr = ptype[0] ? getkeep(0, V, W) : NULL;
        rows(0, V, W, kr, 0, 0, 0, 0, 0, -INF, 0, 0, 0);
    } else {
        task_new();
        TASKF[0] = ((u64)1 << 13) | (1ull << 63); TASKF[1] = ((u64)0x80 << 51) | ((u64)7 << 28) | ((u64)7 << 61); TASKH[0] = 0; TASKH[1] = ctxpack(V, W, 0); qn = 1;
        if (P2 == 0) tries[0]++;
    }
    double tgate = wall() - t0;
    if (qn >= 2147483647LL / (UW)) { fprintf(stderr, "too many gate tasks in this part (%lld): use more parts\n", qn); return 2; }
    /* ---- the card ---- */
    void *lib = LoadLibraryA("nvcuda.dll"); if (!lib) { fprintf(stderr, "nvcuda.dll not found\n"); return 3; }
#define SYM(v, name) do { *(void **)&v = (void *)GetProcAddress(lib, name); if (!v) { fprintf(stderr, "%s missing\n", name); return 3; } } while (0)
    SYM(cuInit, "cuInit"); SYM(cuDeviceGet, "cuDeviceGet"); SYM(cuCtxCreate, "cuCtxCreate_v2"); SYM(cuCtxDestroy, "cuCtxDestroy_v2");
    SYM(cuModuleLoadData, "cuModuleLoadData"); SYM(cuModuleGetFunction, "cuModuleGetFunction"); SYM(cuMemAlloc, "cuMemAlloc_v2");
    SYM(cuMemsetD8, "cuMemsetD8_v2"); SYM(cuHtoD, "cuMemcpyHtoD_v2"); SYM(cuDtoH, "cuMemcpyDtoH_v2"); SYM(cuCtxSync, "cuCtxSynchronize"); SYM(cuLaunch, "cuLaunchKernel");
    char pdef[32]; sprintf(pdef, "gj3_%d.ptx", K);
    const char *pn = getenv("PTX") ? getenv("PTX") : pdef;
    FILE *pf = fopen(pn, "rb"); if (!pf) { fprintf(stderr, "no kernel file %s\n", pn); return 3; }
    fseek(pf, 0, SEEK_END); long psz = ftell(pf); fseek(pf, 0, SEEK_SET); char *ptx = (char *)calloc((size_t)psz + 1, 1);
    if (fread(ptx, 1, (size_t)psz, pf) != (size_t)psz) return 3;
    fclose(pf);
    int dev; void *ctx, *mod, *frun, *fsteal;
    CK(cuInit(0)); CK(cuDeviceGet(&dev, 0)); CK(cuCtxCreate(&ctx, 4, dev));
    CK(cuModuleLoadData(&mod, ptx)); CK(cuModuleGetFunction(&frun, mod, "gj_run")); CK(cuModuleGetFunction(&fsteal, mod, "gj_steal"));
    DP dROWC2 = dalloc(nrow * 16, hROWC2), dSUCCC = dalloc((size_t)NVd * 16 * SCW, hSUCCC), dX2 = dalloc((size_t)NP * 2, hX2), dTB = dalloc(ntb * 8, hTB), dRV = dalloc(nrv * 8, hRV);
    DP dKR = dalloc((size_t)(nring ? nring : 1) * krw, hKR), dL3 = dalloc((size_t)NVd * lw * 4, hL3), dMT = dalloc(ntb * 16, hMT), dRK6 = dalloc(nrk * 8, hRK6);
    DP dUSED = dalloc((size_t)GN * UW * 4, NULL), dCSV = dalloc((size_t)GN * MAXSV * UW * 4, NULL), dHDR = dalloc((size_t)GN * 32, NULL), dCTX = dalloc((size_t)GN * 32, NULL);
    DP dCNT = dalloc((size_t)GN * 128, NULL), dSTK = dalloc((size_t)GN * 16 * STK, NULL), dLOCK = dalloc((size_t)GN * 4, NULL), dCTL = dalloc(128, NULL);
    DP dFND = dalloc((size_t)NFND * (STK + 1) * 16, NULL);
    DP dTU = dalloc((size_t)qn * UW * 4, TASKU), dTF = dalloc((size_t)qn * 16, TASKF), dTH = dalloc((size_t)qn * 8, TASKH);
    int RHIX = RHI + 256 * ((RVMIN < -128 ? -128 : (RVMIN > 127 ? 127 : RVMIN)) + 128);
    int qni = (int)qn, round = 0, flags = (NOCUT ? 1 : 0) | (REV ? 2 : 0), BT = envi("GBT", 128);
    unsigned grid = (unsigned)((GN + BT - 1) / BT);
    int sround = 0, GKMAX = GK, GKMIN = envi("GKMIN", 64), GSTEAL = envi("GSTEAL", 4); long long lastact = 0; double slots = 0;
    void *prun[] = { &dROWC2, &dSUCCC, &dX2, &dTB, &dRV, &dKR, &dL3, &dMT, &dRK6, &dUSED, &dCSV, &dHDR, &dCTX, &dCNT, &dSTK, &dCTL, &dFND,
                     &GN, &GK, &n3, &ns, &NP, &B, &pcw, &flags, &PA, &PB, &PH, &RLO, &RHIX, &P2, &NP2, &lw, &krw };
    void *pst[] = { &dROWC2, &dUSED, &dCSV, &dHDR, &dCTX, &dSTK, &dLOCK, &dCTL, &dTU, &dTF, &dTH, &GN, &qni, &sround, &GTRIES, &NP };
    u64 ctl[16], prevact = 0; long long sumact = 0; double t1 = wall(), tst = 0, trn = 0, tlast = t1; int aborted = 0;
    for (;;) {
        double a0 = wall(), frac = (double)lastact / GN;
        int nsteal = frac > 0.9 ? 1 : GSTEAL;
        GK = frac > 0.9 ? GKMAX : frac > 0.5 ? (GKMAX / 8 > GKMIN ? GKMAX / 8 : GKMIN) : GKMIN;
        for (int q = 0; q < nsteal; q++) { CK(cuLaunch(fsteal, grid, 1, 1, BT, 1, 1, 0, NULL, pst, NULL)); CK(cuCtxSync()); sround++; }
        slots += (double)GN * GK;
        double a1 = wall();
        CK(cuLaunch(frun, grid, 1, 1, BT, 1, 1, 0, NULL, prun, NULL));
        CK(cuDtoH(ctl, dCTL, 128));
        double a2 = wall(); tst += a1 - a0; trn += a2 - a1;
        long long act = (long long)(ctl[1] - prevact); prevact = ctl[1]; sumact += act; lastact = act; round++;
        if (ctl[3]) { fprintf(stderr, ctl[3] == 3 ? "GBT differs from the block size the kernel file was built with\n" : "stack of %d rows exceeded\n", STK); return 4; }
        if (act == 0 && ctl[0] >= (u64)qn) break;
        if (VERB && a2 - tlast > 10) { tlast = a2; fprintf(stderr, "  %.0fs round %d active %lld of %d, list %llu of %lld, splits %llu, objects %llu\n", a2 - t1, round, act, GN, ctl[0] < (u64)qn ? ctl[0] : (u64)qn, qn, ctl[4], ctl[5]); }
        if (a2 - t1 > MAXSEC) { aborted = 1; break; }
    }
    double sec = wall() - t1;
    u64 *cnt = (u64 *)malloc((size_t)GN * 128); CK(cuDtoH(cnt, dCNT, (size_t)GN * 128));
    u64 gkept[8] = {0}, gtry[8] = {0}, gf = 0, gnod = 0, git = 0, gk = 0, gt = 0;
    for (int i = 0; i < GN; i++) { for (int p = 0; p < 5; p++) { gkept[p] += cnt[16 * i + 2 * p]; gtry[p] += cnt[16 * i + 2 * p + 1]; } gf += cnt[16 * i + 10]; gnod += cnt[16 * i + 11]; git += cnt[16 * i + 12]; }
    for (int p = 0; p < 5; p++) { gk += gkept[p]; gt += gtry[p]; }
    static u64 fnd[NFND * (STK + 1) * 2]; CK(cuDtoH(fnd, dFND, sizeof fnd));
    cuCtxDestroy(ctx);
    if (aborted) { printf("ABORTED after %d s (MAXSEC): no result; so far on the card kept %llu rows tried %llu objects %llu\n", MAXSEC, gk, gt, gf); return 5; }
    for (int s = 0; s < NFND && s < (int)ctl[5] && s < 10; s++) show_object(fnd + (size_t)s * (STK + 1) * 2, &qn);
    long long tk = 0, tt = 0;
    for (int i = 0; i < npc; i++) {
        long long k = kept[i] + ((i > 0 || P2 == 0) ? (long long)gkept[i] : 0), t = tries[i] + ((i > 0 || P2 == 0) ? (long long)gtry[i] : 0);
        printf("piece %d: kept %lld  rows tried %lld   (above the gate: kept %lld  rows tried %lld)\n", i + 1, k, t, kept[i], tries[i]); tk += k; tt += t;
    }
    printf("gate visits %lld   tasks of this part %lld\n", fcount, qn);
    printf("RESULT: found %llu   kept %lld   rows tried %lld   time %.2fs (%.6f us per row tried)\n", gf, tk, tt, sec + tgate, tt ? 1e6 * (sec + tgate) / tt : 0.0);
    printf("card: rows tried %llu in %.2fs = %.3e tried/s, kept %llu = %.3e kept/s; nodes judged %llu; steps %llu, %.2f per row tried, %.3e steps/s; threads %d, steps per round %d, rounds %d, splits %llu; step slots used %.1f%%; threads busy at the end of a round %.1f%%; time: host gate %.2fs, split kernel %.2fs, run kernel %.2fs; device memory %.0f MB\n",
           gt, sec, gt / sec, gk, gk / sec, gnod, git, gt ? (double)git / gt : 0, git / sec, GN, GKMAX, round, ctl[4],
           100.0 * git / slots, 100.0 * sumact / ((double)GN * round), tgate, tst, trn, devbytes / 1048576.0);
    fflush(stdout);
    return 0;
}
