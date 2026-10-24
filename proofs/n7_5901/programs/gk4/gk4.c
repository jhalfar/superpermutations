/* gk4.c (agent n7-gpu, 2026-10-11): host of gk4.cu (generated from gk.c by mk2.py, mk3.py and mk4.py), the kernel-alone search of kfast.c of defect 15 (a file of mine, not in this repository) on the card.
 * gk_tables.h = lines 23..156 of kfast.c verbatim (geometry, caps file, tables keepN/keepS/revA1/revA2).
 * The host walks the tree down to the gate (prefixes of DEPTH rows, index modulo NPARTS, as kfast.c) and hands the
 * gate prefixes of this part to the card; the card does the rest (gk.cu).
 * usage: gk run S GTOP caps      env: CUT (0, 4, 12) LO POTA POTB POTH PART NPARTS DEPTH   (as kfast.c)
 *        card: GN threads (262144), GK steps per round (5000), GTRIES (8), MAXSEC (1500), VERB, PTX (gk.ptx)
 * build: gcc -O2 -o gk.exe gk.c ; build_ptx.bat (nvcc -arch=sm_120 -ptx -o gk.ptx gk.cu)
 */
#include <windows.h>
#include "gk_tables.h"
#include <windows.h>
typedef unsigned long long u64;
typedef unsigned int u32;
#define STK 160
#define UW 24
static int16_t ROWC[NP][6], ROWE[NP][6];
static uint8_t IM[SM + 1][GM][RM + 1];
static uint8_t used[NC];
static long long hnodes, hkept, hviol, fcount, hcut, hgate;
static int PARTI = 0, NPARTS = 1, DEPTH = 0;
static u32 *TASKU; static u64 *TASKF; static long long qn, qcap;

static int N3G, X0, J0;
/* a task = the frame of the parent (end vertex px) with the one successor row pj and the one length l2 + 1 .. len2 */
static void emit(int px, int pj, int len2, int l2, int d, int tpar, int m, int M, unsigned mk) {
    if (qn == qcap) {
        qcap = qcap ? 2 * qcap : 1 << 16;
        TASKU = (u32 *)realloc(TASKU, (size_t)qcap * UW * 4); TASKF = (u64 *)realloc(TASKF, (size_t)qcap * 16);
        if (!TASKU || !TASKF) { fprintf(stderr, "out of memory for the gate prefixes\n"); exit(1); }
    }
    u32 *u = TASKU + qn * UW; memset(u, 0, UW * 4);
    for (int c = 0; c < NC; c++) if (used[c]) u[c >> 5] |= 1u << (c & 31);
    TASKF[2 * qn] = ((u64)px << 32) | ((u64)len2 << 45) | ((u64)l2 << 48) | ((u64)pj << 51) | ((u64)mk << 56);
    TASKF[2 * qn + 1] = (u64)(m & 0xffff) | ((u64)(M & 0xffff) << 16) | ((u64)d << 32) | ((u64)tpar << 39) | ((u64)mk << 43);
    qn++;
}
/* the tree above the gate: rows() of kfast.c; a prefix of DEPTH rows of this part becomes a task */
static void hrows(int st, int r1, int d, int t, int m, int M, unsigned mk, int px, int pj) {
    const int16_t *rc = ROWC[st];
    int len = 0;
    while (len < 6 && !used[rc[len]]) len++;
    if (!(mk >> (6 - len))) return;
    const int f0 = POTA * r1 - 2 * POTH * t;
    for (int l = 1; l <= len; l++) {
        used[rc[l - 1]] = 1;
        int k = 6 - l, dd = d + k;
        if (!((mk >> k) & 1)) continue;
        hnodes++;
        if (t == TS && dd > LO && r1 > P[TS][dd]) { hviol++; continue; }
        if (r1 == DEPTH) {
            hgate++;
            if (NPARTS > 1 && (fcount++ % NPARTS) != PARTI) continue;
            used[rc[l - 1]] = 0; emit(px, pj, l, l - 1, d, t - (pj >= N3G), m, M, mk); used[rc[l - 1]] = 1;
            continue;
        }
        int a = keepN[t][dd][r1], b = keepS[t][dd][r1];
        if (!(a | b)) continue;
        int mN = m, MN = M, mS = m, MS = M;
        if (CUT & 4) {
            int f = f0 - POTB * dd, g = f - POTH, A1 = revA1[t][dd][r1], A2 = revA2[t][dd][r1];
            if (f < mN) mN = f;
            if (f > MN) MN = f;
            if (g < mS) mS = g;
            if (g > MS) MS = g;
            if (a && mN < 0 && !(MN + mN >= A1 || mN >= A2)) { a = 0; hcut++; }
            if (b && mS < 0 && !(MS + mS >= A1 || mS >= A2)) { b = 0; hcut++; }
            if (!(a | b)) continue;
        }
        hkept++;
        int x = ROWE[st][l - 1];
        unsigned mkN = IM[t][dd][r1 + 1], mkS = IM[t + 1][dd][r1 + 1];
        if (a && mkN) for (int i = 0; i < nsucc3[x]; i++) hrows(succ3[x][i], r1 + 1, dd, t, mN, MN, mkN, x, i);
        if (b && mkS) for (int i = 0; i < nsucc4[x]; i++) hrows(succ4[x][i], r1 + 1, dd, t + 1, mS, MS, mkS, x, N3G + i);
    }
    while (len > 0) used[rc[--len]] = 0;
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
static DP dalloc(size_t n, const void *src) { DP p; CK(cuMemAlloc(&p, n ? n : 8)); if (src) CK(cuHtoD(p, src, n)); else CK(cuMemsetD8(p, 0, n ? n : 8)); return p; }
static int envi(const char *n, int dflt) { return getenv(n) ? atoi(getenv(n)) : dflt; }

int main(int argc, char **argv) {
    if (argc < 5 || strcmp(argv[1], "run")) { fprintf(stderr, "usage: gk run S GTOP caps\n"); return 2; }
    CUT = envi("CUT", 0); LO = envi("LO", -1); POTA = envi("POTA", 2); POTB = envi("POTB", 3); POTH = envi("POTH", 5);
    PARTI = envi("PART", 0); NPARTS = envi("NPARTS", 1); DEPTH = envi("DEPTH", 0);
    int GN = envi("GN", 262144), GK = envi("GK", 5000), GTRIES = envi("GTRIES", 8), MAXSEC = envi("MAXSEC", 1500), VERB = envi("VERB", 0);
    if (CUT != 0 && CUT != 4 && CUT != 12) { fprintf(stderr, "CUT must be 0, 4 or 12\n"); return 2; }
    TS = atoi(argv[2]); GTOP = atoi(argv[3]); readcaps(argv[4]);
    build(); tables();
    if (TS > 11 || TS + 1 > 15) return 2;
    for (int p = 0; p < NP; p++) { int x = p; for (int i = 0; i < 6; i++) { ROWE[p][i] = (int16_t)x; ROWC[p][i] = CLS[x]; x = T2[x]; } }
    memset(IM, 0, sizeof IM);
    for (int t = 0; t <= TS; t++) for (int d = 0; d < GM; d++) for (int r = 0; r < RM; r++) {
        unsigned mk = 0;
        for (int k = 0; k < 6; k++) {
            int dd = d + k; if (dd > G) continue;
            if ((t == TS && dd > LO && r > P[TS][dd]) || keepN[t][dd][r] || keepS[t][dd][r]) mk |= 1u << k;
        }
        IM[t][d][r] = (uint8_t)mk;
    }
    for (int t = 0; t <= TS; t++) for (int d = 0; d < GM; d++) IM[t][d][RM] = IM[t][d][RM - 1];
    /* device tables */
    int n3 = nsucc3[0], n4 = nsucc4[0], ns = n3 + n4;
    for (int q = 0; q < NP; q++) if (nsucc3[q] != n3 || nsucc4[q] != n4) { fprintf(stderr, "successor counts differ\n"); return 9; }
    if (ns > 32 || n3 < 1 || n4 < 1) { fprintf(stderr, "successors do not fit a 32-bit mask\n"); return 9; }
    u32 *hSUCC = (u32 *)calloc(NP * 32, 4); u64 *hROWC = (u64 *)calloc(NP, 8); unsigned short *hROWE = (unsigned short *)calloc(NP * 6, 2);
    size_t nrule = (size_t)(TS + 1) * GM * RM; u64 *hRULE = (u64 *)calloc(nrule, 8);
    for (int q = 0; q < NP; q++) {
        for (int i = 0; i < n3; i++) hSUCC[q * 32 + i] = (u32)succ3[q][i] | ((u32)CLS[succ3[q][i]] << 16);
        for (int i = 0; i < n4; i++) hSUCC[q * 32 + n3 + i] = (u32)succ4[q][i] | ((u32)CLS[succ4[q][i]] << 16);
        for (int i = 0; i < 6; i++) { hROWC[q] |= (u64)ROWC[q][i] << (10 * i); hROWE[q * 6 + i] = (unsigned short)ROWE[q][i]; }
    }
    for (int t = 0; t <= TS; t++) for (int d = 0; d < GM; d++) for (int r = 0; r < RM; r++) {
        u64 fl = (keepN[t][d][r] ? 1 : 0) | (keepS[t][d][r] ? 2 : 0) | ((t == TS && d > LO && d <= G && r > P[TS][d]) ? 4 : 0);
        hRULE[((size_t)t * GM + d) * RM + r] = (u64)(uint16_t)revA1[t][d][r] | ((u64)(uint16_t)revA2[t][d][r] << 16) | (fl << 32)
            | ((u64)IM[t][d][r + 1] << 40) | ((u64)IM[t + 1][d][r + 1] << 48);
    }
    N3G = n3; X0 = -1;
    for (int q = 0; q < NP && X0 < 0; q++) for (int i = 0; i < n3; i++) if (succ3[q][i] == 0) { X0 = q; J0 = i; break; }
    if (X0 < 0) return 9;
    u64 *hSUCCC = (u64 *)calloc(NP * 6, 8), *hROWC2 = (u64 *)calloc(NP * 32, 8); unsigned short *hX2 = (unsigned short *)calloc(NP * 256, 2);
    for (int q = 0; q < NP; q++) for (int i = 0; i < ns; i++) {
        int v = (int)(hSUCC[q * 32 + i] & 0xffff);
        hSUCCC[q * 6 + i / 6] |= (u64)(hSUCC[q * 32 + i] >> 16) << (10 * (i % 6));
        hROWC2[q * 32 + i] = hROWC[v];
        for (int l = 1; l <= 6; l++) hX2[(q * 32 + i) * 8 + l - 1] = (unsigned short)ROWE[v][l - 1];
    }
    /* the gate */
    double t0 = wall();
    int depth0;
    memset(used, 0, sizeof used);
    if (DEPTH <= 0) { if (NPARTS != 1) { fprintf(stderr, "parts need DEPTH\n"); return 2; } emit(X0, J0, 6, 0, 0, 0, 0, 0, 63); depth0 = 0; }
    else { hrows(0, 1, 0, 0, 0, 0, 63, X0, J0); depth0 = DEPTH - 1; hnodes -= qn; }
    double tgate = wall() - t0;
    if (qn >= 2147483647LL / UW) { fprintf(stderr, "too many gate prefixes in this part (%lld): use more parts\n", qn); return 2; }
    /* the card */
    void *lib = LoadLibraryA("nvcuda.dll"); if (!lib) { fprintf(stderr, "nvcuda.dll not found\n"); return 3; }
#define SYM(v, name) do { *(void **)&v = (void *)GetProcAddress(lib, name); if (!v) { fprintf(stderr, "%s missing\n", name); return 3; } } while (0)
    SYM(cuInit, "cuInit"); SYM(cuDeviceGet, "cuDeviceGet"); SYM(cuCtxCreate, "cuCtxCreate_v2"); SYM(cuCtxDestroy, "cuCtxDestroy_v2");
    SYM(cuModuleLoadData, "cuModuleLoadData"); SYM(cuModuleGetFunction, "cuModuleGetFunction"); SYM(cuMemAlloc, "cuMemAlloc_v2");
    SYM(cuMemsetD8, "cuMemsetD8_v2"); SYM(cuHtoD, "cuMemcpyHtoD_v2"); SYM(cuDtoH, "cuMemcpyDtoH_v2"); SYM(cuCtxSync, "cuCtxSynchronize"); SYM(cuLaunch, "cuLaunchKernel");
    const char *pn = getenv("PTX") ? getenv("PTX") : "gk4.ptx";
    FILE *pf = fopen(pn, "rb"); if (!pf) { fprintf(stderr, "no kernel file %s\n", pn); return 3; }
    fseek(pf, 0, SEEK_END); long psz = ftell(pf); fseek(pf, 0, SEEK_SET); char *ptx = (char *)calloc((size_t)psz + 1, 1);
    if (fread(ptx, 1, (size_t)psz, pf) != (size_t)psz) return 3;
    fclose(pf);
    int dev; void *ctx, *mod, *frun, *fsteal;
    CK(cuInit(0)); CK(cuDeviceGet(&dev, 0)); CK(cuCtxCreate(&ctx, 4, dev));
    CK(cuModuleLoadData(&mod, ptx)); CK(cuModuleGetFunction(&frun, mod, "gk_run")); CK(cuModuleGetFunction(&fsteal, mod, "gk_steal"));
    DP dSUCCC = dalloc((size_t)NP * 48, hSUCCC), dROWC2 = dalloc((size_t)NP * 256, hROWC2), dX2 = dalloc((size_t)NP * 512, hX2); DP dSUCC = dalloc((size_t)NP * 32 * 4, hSUCC), dROWC = dalloc((size_t)NP * 8, hROWC), dROWE = dalloc((size_t)NP * 12, hROWE), dRULE = dalloc(nrule * 8, hRULE);
    DP dUSED = dalloc((size_t)GN * UW * 4, NULL), dHDR = dalloc((size_t)GN * 16, NULL), dCNT = dalloc((size_t)GN * 64, NULL);
    DP dSTK = dalloc((size_t)GN * 2 * STK * 8, NULL), dLOCK = dalloc((size_t)GN * 4, NULL), dCTL = dalloc(128, NULL);
    DP dTU = dalloc((size_t)qn * UW * 4, TASKU), dTF = dalloc((size_t)qn * 16, TASKF);
    double devmb = ((double)NP * 988 + nrule * 8.0 + (double)GN * (UW * 4 + 16 + 64 + 2 * STK * 8 + 4) + (double)qn * (UW * 4 + 16)) / 1048576.0;
    int qni = (int)qn, round = 0, cutf = (CUT & 4) ? 1 : 0, BT = 256;
    unsigned grid = (unsigned)((GN + BT - 1) / BT);
    int sround = 0, GKMAX = GK, GKMIN = envi("GKMIN", 64), GSTEAL = envi("GSTEAL", 4); long long lastact = 0; double slots = 0;
    void *prun[] = { &dROWC2, &dSUCCC, &dX2, &dRULE, &dUSED, &dHDR, &dCNT, &dSTK, &dCTL, &GN, &GK, &n3, &ns, &cutf, &POTA, &POTB, &POTH };
    void *pst[] = { &dROWC2, &dUSED, &dHDR, &dSTK, &dLOCK, &dCTL, &dTU, &dTF, &GN, &qni, &depth0, &sround, &GTRIES, &n3 };
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
        if (ctl[3]) { fprintf(stderr, "stack of %d rows exceeded\n", STK); return 4; }
        if (act == 0 && ctl[0] >= (u64)qn) break;
        if (VERB && a2 - tlast > 10) { tlast = a2; fprintf(stderr, "  %.0fs round %d active %lld of %d, list %llu of %lld, splits %llu\n", a2 - t1, round, act, GN, ctl[0] < (u64)qn ? ctl[0] : (u64)qn, qn, ctl[4]); }
        if (a2 - t1 > MAXSEC) { aborted = 1; break; }
    }
    double sec = wall() - t1;
    u64 *cnt = (u64 *)malloc((size_t)GN * 64); CK(cuDtoH(cnt, dCNT, (size_t)GN * 64));
    u64 gk = 0, gnod = 0, gv = 0, gc = 0, git = 0;
    for (int i = 0; i < GN; i++) { gk += cnt[8 * i]; gnod += cnt[8 * i + 1]; gv += cnt[8 * i + 2]; gc += cnt[8 * i + 3]; git += cnt[8 * i + 4]; }
    cuCtxDestroy(ctx);
    if (aborted) { printf("ABORTED after %d s (MAXSEC): no result; so far kept %llu on the card\n", MAXSEC, gk); return 5; }
    printf("gpu run S=%d GTOP=%d (holes <= %d) LO=%d CUT=%d POT=%d,%d,%d part %d of %d at depth %d: violations %lld   rows placed %lld   kept %lld   above the gate: rows placed %lld kept %lld   prefixes at the gate %lld (this part %lld)\n",
           TS, GTOP, G, LO, CUT, POTA, POTB, POTH, PARTI, NPARTS, DEPTH, hviol + (long long)gv, hnodes + (long long)gnod, hkept + (long long)gk, hnodes, hkept, hgate, qn);
    printf("card: kept %llu in %.2fs = %.3e kept/s (%.5f us per kept); steps %llu, %.1f per kept, %.3e steps/s; threads %d, steps per round %d, rounds %d, splits %llu; step slots used %.1f%%; threads busy at the end of a round %.1f%%; time: host gate %.2fs, split kernel %.2fs, run kernel %.2fs; device memory %.0f MB\n",
           gk, sec, gk / sec, gk ? 1e6 * sec / gk : 0, git, gk ? (double)git / gk : 0, git / sec, GN, GKMAX, round, ctl[4],
           100.0 * git / slots, 100.0 * sumact / ((double)GN * round), tgate, tst, trn, devmb);
    fflush(stdout);
    return 0;
}
