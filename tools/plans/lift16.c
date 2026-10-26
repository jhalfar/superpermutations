/* lift16.c - unit plans for gen16 at n = 13 + L' from a unit plan one level down (construction Jay Pantone's).

   One unit at level n = one closed trail at n - 1.  The order of the units is the order in which the plan at n - 1
   writes its closed trails; then every unit gets its opening (small unit: j = 0 .. h-1; walk unit: any full row,
   two ways) by an exact dynamic programme over that fixed order: the cost of a join is h - overlap of the last h
   letters of one unit and the first h letters of the next (the n = 14 lift, made general in L).

   usage:
     lift16 lift L SEL PLAN(n-1) OUT.uplan     L = lifts of the output (2 or 3); PLAN is an N(n-1)-UNITPLAN
     lift16 dp   L SEL IN.uplan OUT.uplan      re-open the units of a unit plan at n
   Prints the exact length of the word gen16 writes for OUT:
     length = sum R + h + (h-1) per small unit + h per walk unit + sum over joins (h - overlap). */
#ifndef _WIN32                                         /* Linux: the Windows names used below */
#define _FILE_OFFSET_BITS 64
#include <stdlib.h>
#include <string.h>
#define fseeko64 fseeko
static int portable_putenv(const char *s) {            /* _putenv: "NAME=" removes NAME */
    const char *eq = strchr(s, '='); if (!eq) return -1;
    if (!eq[1]) { char name[64]; size_t n = (size_t)(eq - s); if (n >= sizeof name) return -1; memcpy(name, s, n); name[n] = 0; return unsetenv(name); }
    return putenv(strdup(s));
}
#define _putenv portable_putenv
#endif
#define GEN15_NO_MAIN
#include "../../recipes/n15/gen16.c"

typedef struct { char k; int d; int g[3]; int w; int src; } Unit;   /* 'D' d g[0..L-2]  /  'W' w */
static Unit *U; static int NU;
static u64 packh(const u8 *w) { u64 v = 0; for (int i = 0; i < HH; i++) v = v << 4 | w[i]; return v; }

static u64 *cS, *cE; static u32 *cM; static size_t ccap;
static int cands(const Unit *u) {
    int n = 0;
    if (u->k == 'D') {
        u8 y[16], r[16]; small_y(u->d, u->g, y);
        if (ccap < (size_t)HH) DIE("ccap");
        for (int j = 0; j < HH; j++) { rot(r, y, HH, j); cS[n] = packh(r); rot(r, y, HH, j - 1); cE[n] = packh(r); cM[n] = j; n++; }
    } else {
        load_walk(u->w); u64 a = wstart[u->w], m = wstart[u->w + 1] - a; u8 b[16], t[16];
        if (ccap < 2 * (size_t)m) { ccap = 2 * m + 16; cS = realloc(cS, 8 * ccap); cE = realloc(cE, 8 * ccap); cM = realloc(cM, 4 * ccap); }
        for (u64 i = 0; i < m; i++) {
            if (rty(wrow[a + i])) continue;
            unpackK(wrow[a + i], b);
            cS[n] = packh(b); t[0] = b[K - 1]; memcpy(t + 1, b, HH - 1); cE[n] = packh(t); cM[n] = (u32)(i * 2); n++;
            cS[n] = packh(b + 1); cE[n] = packh(b); cM[n] = (u32)(i * 2 + 1); n++;
        }
    }
    return n;
}

#define HB 24
static u64 *hk; static u32 *hf, *hi, *hs; static u32 stamp = 0;
static inline u64 hh_(u64 k) { k ^= k >> 31; k *= 0x9E3779B97F4A7C15ULL; return k >> (64 - HB); }
static void hput(u64 k, u32 f, u32 i) {
    u64 p = hh_(k);
    for (;;) { if (hs[p] != stamp) { hs[p] = stamp; hk[p] = k; hf[p] = f; hi[p] = i; return; }
               if (hk[p] == k) { if (f < hf[p]) { hf[p] = f; hi[p] = i; } return; } p = (p + 1) & ((1u << HB) - 1); }
}
static int hget(u64 k, u32 *f, u32 *i) {
    u64 p = hh_(k);
    for (;;) { if (hs[p] != stamp) return 0; if (hk[p] == k) { *f = hf[p]; *i = hi[p]; return 1; } p = (p + 1) & ((1u << HB) - 1); }
}

static void dp_and_write(const char *outp, const char *note) {
    hk = malloc(8ULL << HB); hf = malloc(4ULL << HB); hi = malloc(4ULL << HB); hs = calloc(1ULL << HB, 4);
    ccap = 1 << 16; cS = malloc(8 * ccap); cE = malloc(8 * ccap); cM = malloc(4 * ccap);
    /* back pointers go to a file (n = 16: about 2 * 3e9 candidates, 4 bytes each); boff[ui] = byte offset of unit ui */
    const char *bp = getenv("LIFT16_BACK"); if (!bp) bp = "lift16.back";
    FILE *bf = fopen(bp, "w+b"); if (!bf) DIE("cannot open back file %s", bp);
    u64 *boff = malloc(8 * ((size_t)NU + 1)); u64 bpos = 0;
    u32 *bcur = NULL; size_t bcap = 0;
    u32 *fprev = NULL, *fcur = NULL; u64 *Eprev = NULL; size_t pcap = 0;
    int np = 0;
    for (int ui = 0; ui < NU; ui++) {
        int n = cands(&U[ui]);
        if ((size_t)n > bcap) { bcap = 2 * (size_t)n + 16; bcur = realloc(bcur, 4 * bcap); }
        if (np * (size_t)HH * 2 > ((size_t)1 << HB)) DIE("hash table too small for %d candidates", np);
        if ((size_t)n > pcap) { pcap = n * 2; fprev = realloc(fprev, 4 * pcap); fcur = realloc(fcur, 4 * pcap); Eprev = realloc(Eprev, 8 * pcap); }
        if (ui == 0) { for (int c = 0; c < n; c++) { fcur[c] = 0; bcur[c] = 0; } }
        else {
            stamp++; u32 gmin = ~0u, gi = 0;
            for (int c = 0; c < np; c++) {
                if (fprev[c] < gmin) { gmin = fprev[c]; gi = c; }
                for (int q = 1; q <= HH; q++) hput((u64)q << 56 | (Eprev[c] & ((1ULL << (4 * q)) - 1)), fprev[c], c);
            }
            for (int c = 0; c < n; c++) {
                u32 best = gmin + HH, bi = gi, f, i;
                for (int q = 1; q <= HH; q++) if (hget((u64)q << 56 | (cS[c] >> (4 * (HH - q))), &f, &i) && f + HH - q < best) { best = f + HH - q; bi = i; }
                fcur[c] = best; bcur[c] = bi;
            }
        }
        boff[ui] = bpos; if (fwrite(bcur, 4, n, bf) != (size_t)n) DIE("back file write failed"); bpos += 4 * (u64)n;
        memcpy(fprev, fcur, 4 * (size_t)n); memcpy(Eprev, cE, 8 * (size_t)n); np = n;
        if (ui % 100000 == 0) fprintf(stderr, "  dp unit %d (%.0fs)\n", ui, wall() - t0g);
    }
    u32 best = ~0u, bc = 0; for (int c = 0; c < np; c++) if (fprev[c] < best) { best = fprev[c]; bc = c; }
    u32 *choice = malloc(4 * (size_t)NU); u32 c = bc;
    for (int ui = NU - 1; ui >= 0; ui--) { choice[ui] = c; u32 bv; if (fseeko64(bf, (long long)(boff[ui] + 4 * (u64)c), SEEK_SET) || fread(&bv, 4, 1, bf) != 1) DIE("back file read failed"); c = bv; }
    fclose(bf); remove(bp);
    long nS = 0, nW = 0; long hist[17] = {0}; long ccount[8] = {0}, ccost[8] = {0}, cbig[8] = {0};
    FILE *o = fopen(outp, "w"); if (!o) DIE("cannot write %s", outp);
    fprintf(o, "N%d-UNITPLAN 1\n# %s\n", NN, note);
    u64 prevE = 0;
    for (int ui = 0; ui < NU; ui++) {
        cands(&U[ui]); u32 ch = choice[ui];
        if (ui) { int ov = 0; for (int q = HH; q >= 1; q--) if ((prevE & ((1ULL << (4 * q)) - 1)) == (cS[ch] >> (4 * (HH - q)))) { ov = q; break; } hist[HH - ov]++;
            const Unit *ua = &U[ui - 1], *ub = &U[ui]; int cl = (ua->src >= 0 && ua->src == ub->src ? 0 : 4) + (ua->k == 'W') * 2 + (ub->k == 'W');
            ccount[cl]++; ccost[cl] += HH - ov; if (HH - ov >= 8) cbig[cl]++; }
        prevE = cE[ch];
        if (U[ui].k == 'D') { fprintf(o, "D %d", U[ui].d); for (int l = 0; l < L - 1; l++) fprintf(o, " %d", U[ui].g[l]); fprintf(o, " %u\n", cM[ch]); nS++; }
        else { fprintf(o, "W %d %u %u\n", U[ui].w, cM[ch] >> 1, cM[ch] & 1); nW++; }
    }
    fclose(o);
    u64 fact[20]; fact[0] = 1; for (int i = 1; i < 20; i++) fact[i] = fact[i - 1] * i;
    u64 nshort = 0; for (int i = 0; i < nsel; i++) nshort += sel[i].ty == 1;
    u64 mult = 1; for (int l = 0; l < L; l++) mult *= (u64)(10 + l);
    u64 sumR = fact[NN] + fact[NN - 1] + fact[NN - 2] + 2 * nshort * mult;
    u64 len = sumR + HH + (u64)(HH - 1) * nS + (u64)HH * nW + best;
    fprintf(stderr, "units %d (small %ld, walk %ld); joins %u (sum of h - overlap); join costs:", NU, nS, nW, best);
    for (int q = 0; q <= HH; q++) if (hist[q]) fprintf(stderr, " %d:%ld", q, hist[q]);
    fprintf(stderr, "\nLENGTH %llu\n", (unsigned long long)len);
}

/* the trails of a plan at n - 1, in order, as units at n */
static int L1;                                         /* lifts of the input plan = L - 1 */
static void read_lower(const char *path) {
    /* rows of the input level are needed for its walk units: build the (L-1)-lift separately */
    int Lsave = L, NNs = NN, Ks = K, Hs = HH, Ss = SL, Zs = ZL, LAZYs = LAZY, LBs = LB, KPs = KP;
    char *envs = getenv("GEN16_LAZY"); char envsave[64] = ""; if (envs) snprintf(envsave, sizeof envsave, "GEN16_LAZY=%s", envs);
    _putenv("GEN16_LAZY=");                                /* the lower level is always built in full */
    L = L1; NN = 12 + L; K = 10 + L; HH = NN - 3; SL = K; ZL = K + 1;
    u64 *wrow_s = wrow, *wstart_s = wstart; int nwl_s = nwl; u64 nrows_s = nrows; int *wbase_s = wbase; int wcap_s = wcap;
    wrow = NULL; wstart = NULL; wbase = NULL; nwl = 0; nrows = 0; wcap = 0;
    build_walks();
    u64 *lrow = wrow, *lstart = wstart; int lnw = nwl;
    int h1 = HH, K1 = K;
    FILE *f = fopen(path, "r"); if (!f) DIE("cannot open %s", path);
    char line[512], hdr[32]; int nl = 0; sprintf(hdr, "N%d-UNITPLAN", NN);
    int src = 0;
    while (fgets(line, sizeof line, f)) {
        nl++;
        if (nl == 1) { if (strncmp(line, hdr, strlen(hdr))) DIE("not an n = %d unit plan", NN); continue; }
        if (line[0] == '#' || line[0] == '\n' || line[0] == '\r') continue;
        char *tok[16]; int nt = 0; char *sv = NULL;
        for (char *t = strtok_r(line, " \t\r\n", &sv); t && nt < 16; t = strtok_r(NULL, " \t\r\n", &sv)) tok[nt++] = t;
        if (nt && tok[nt - 1][0] == 'o') nt--;
        if (tok[0][0] == 'D') {
            if (nt != 2 + L) DIE("D line %d", nl);
            int d = atoi(tok[1]), j = atoi(tok[nt - 1]), g[3] = {0, 0, 0};
            for (int l = 0; l < L - 1; l++) g[l] = atoi(tok[2 + l]);
            for (int i = 0; i < h1; i++) {                 /* its trails: letter K1-1 inserted at a = j + i */
                Unit u; memset(&u, 0, sizeof u); u.k = 'D'; u.d = d;
                for (int l = 0; l < L - 1; l++) u.g[l] = g[l];
                u.g[L - 1] = (j + i) % h1; u.src = src; U[NU++] = u;
            }
        } else if (tok[0][0] == 'W' && nt == 4) {
            int w = atoi(tok[1]), way = atoi(tok[3]); u64 i0 = strtoull(tok[2], NULL, 10);
            u64 a = lstart[w], m = lstart[w + 1] - a;
            if (i0 >= m || rty(lrow[a + i0])) DIE("W line %d: not a full row", nl);
            for (int i = 0; i < h1; i++) {
                int q = way == 0 ? i : i + 1, port = q == K1 - 1 ? 0 : q;
                int p = port; for (u64 r = i0; r < m; r++) p = nextport(rty(lrow[a + r]), p);   /* port at row 0 */
                Unit u; memset(&u, 0, sizeof u); u.k = 'W'; u.w = w * (K1 - 1) + p; u.src = src; U[NU++] = u;
            }
        src++;
        } else DIE("bad line %d", nl);
    }
    fclose(f);
    free(lrow); free(lstart); free(wbase); (void)lnw;
    if (envs) _putenv(envsave);
    LAZY = LAZYs; LB = LBs; KP = KPs;
    L = Lsave; NN = NNs; K = Ks; HH = Hs; SL = Ss; ZL = Zs;
    wrow = wrow_s; wstart = wstart_s; nwl = nwl_s; nrows = nrows_s; wbase = wbase_s; wcap = wcap_s;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: lift15 lift|dp L SEL IN OUT\n"); return 2; }
    t0g = wall();
    L = atoi(argv[2]); if (L < 1 || L > 4) DIE("L must be 1..4");
    NN = 12 + L; K = 10 + L; HH = NN - 3; SL = K; ZL = K + 1;
    read_sel(argv[3]); build_walks();
    /* check: the W walks of level L come in groups of K-2 per walk one level down (one pass each) */
    { u64 ucap = (u64)ndet; for (int l = 0; l < L - 1; l++) ucap *= (u64)(10 + l); ucap += (u64)nwl + 16; U = malloc(sizeof(Unit) * ucap); } NU = 0;
    char note[1024];
    if (!strcmp(argv[1], "lift")) {
        if (L < 2) DIE("lift needs L >= 2");
        L1 = L - 1;
        read_lower(argv[4]);
        snprintf(note, sizeof note, "units in the order of the trails of %s, openings by lift15 dp", argv[4]);
    } else if (!strcmp(argv[1], "dp")) {
        FILE *f = fopen(argv[4], "r"); if (!f) DIE("cannot open %s", argv[4]);
        char line[512];
        while (fgets(line, sizeof line, f)) {
            if (line[0] == '#' || line[0] == 'N' || line[0] == '\n') continue;
            char *tok[16]; int nt = 0; char *sv = NULL;
            for (char *t = strtok_r(line, " \t\r\n", &sv); t && nt < 16; t = strtok_r(NULL, " \t\r\n", &sv)) tok[nt++] = t;
            if (nt && tok[nt - 1][0] == 'o') nt--;
            Unit u; memset(&u, 0, sizeof u); u.k = tok[0][0]; u.src = -1;
            if (u.k == 'D') { u.d = atoi(tok[1]); for (int l = 0; l < L - 1; l++) u.g[l] = atoi(tok[2 + l]); }
            else u.w = atoi(tok[1]);
            U[NU++] = u;
        }
        fclose(f);
        snprintf(note, sizeof note, "units of %s re-opened by lift15 dp", argv[4]);
    } else DIE("unknown mode");
    /* every unit exactly once */
    u64 nsu = (u64)ndet; for (int l = 0; l < L - 1; l++) nsu *= (u64)(10 + l);
    if ((u64)NU != nsu + (u64)nwl) DIE("plan has %d units, expected %llu", NU, (unsigned long long)(nsu + nwl));
    char *seen = calloc(nsu + nwl, 1);
    for (int i = 0; i < NU; i++) {
        u64 id;
        if (U[i].k == 'D') { id = U[i].d; for (int l = 0; l < L - 1; l++) id = id * (10 + l) + U[i].g[l]; }
        else id = nsu + U[i].w;
        if (seen[id]++) DIE("unit %d repeated", i);
    }
    fprintf(stderr, "units %d, each once (%.0fs)\n", NU, wall() - t0g);
    dp_and_write(argv[5], note);
    fprintf(stderr, "(%.0fs)\n", wall() - t0g);
    return 0;
}
