/* lift17.c - lift16.c on top of genBt.c (no block): unit plan at n = 12 + L (L = 2..5) from the unit plan one level down.
   Same construction as lift16/lift15: the units are the closed trails of the plan at n - 1 in its order; the opening of
   every unit is chosen by an exact DP over that order (join cost h - overlap of the last h letters of one unit and the
   first h letters of the next).  Differences against lift16:
   - the lower level's walks are not built in full: they are the stored walks (GEN17_LAZY = 1) or the level-1 walks made
     per walk from a stored one (GEN17_LAZY = 2, n = 17), and the upper walk number of a lower trail is
     first walk of the lower walk's transport + (port mod g), g = number of orbits (g = h whenever D = 0);
   - back pointers are not stored: one byte per candidate, f - min f of its unit (0..h), goes to a file, plus min f
     and the candidate count per unit; the backward pass recomputes the predecessor with the lift16 tie-breaking
     (smallest q, then first candidate), so the plan is the one lift16 would write;
   - puts into the hash only where they can win (q > f - gmin of the previous unit; exact, see dp_forward);
   - Unit is 12 bytes.
   usage: lift17 lift L SEL PLAN(n-1) OUT.uplan        (env LIFT17_BACK = back file; LIFT17_STATS=1 prints counts)
   Prints "LENGTH x": the exact length of the word gen17 writes for OUT. */
#ifndef _WIN32                                         /* Linux: the Windows name used below */
#define _FILE_OFFSET_BITS 64
#define fseeko64 fseeko
#endif
#define GEN15_NO_MAIN
#include "../../recipes/n17/genBt.c"

typedef struct { u32 a, src; uint16_t g; u8 k; } Unit;      /* k 'D': a = d, g = 4 bits a letter g[0..3]; k 'W': a = w */
static Unit *U; static u32 NU;
static inline int ug(const Unit *u, int l) { return (u->g >> (4 * l)) & 15; }
static u64 packh(const u8 *w) { u64 v = 0; for (int i = 0; i < HH; i++) v = v << 4 | w[i]; return v; }

static u64 *cS, *cE; static u32 *cM; static size_t ccap;
static void cgrow(size_t need) { if (need > ccap) { ccap = 2 * need + 16; cS = realloc(cS, 8 * ccap); cE = realloc(cE, 8 * ccap); cM = realloc(cM, 4 * ccap); if (!cS || !cE || !cM) DIE("oom (cands)"); } }
/* candidates of unit u into (S, E, M) (arrays of at least ccap entries) */
static int cands_into(const Unit *u, u64 **pS, u64 **pE, u32 **pM) {
    int n = 0;
    if (u->k == 'D') {
        int g[5] = {0}; for (int l = 0; l < L - 1; l++) g[l] = ug(u, l);
        u8 y[24], r[24]; small_y((int)u->a, g, y);
        cgrow(HH); *pS = cS; *pE = cE; *pM = cM;
        for (int j = 0; j < HH; j++) { rot(r, y, HH, j); cS[n] = packh(r); rot(r, y, HH, j - 1); cE[n] = packh(r); cM[n] = j; n++; }
    } else {
        load_walk((int)u->a); u64 a = wbeg((int)u->a), m = wlen((int)u->a); u8 b[24], t[24];
        cgrow(2 * (size_t)m);
        for (u64 i = 0; i < m; i++) {
            if (rty(wrow[a + i])) continue;
            unpackK(wrow[a + i], b);
            cS[n] = packh(b); t[0] = b[K - 1]; memcpy(t + 1, b, HH - 1); cE[n] = packh(t); cM[n] = (u32)(i * 2); n++;
            cS[n] = packh(b + 1); cE[n] = packh(b); cM[n] = (u32)(i * 2 + 1); n++;
        }
        *pS = cS; *pE = cE; *pM = cM;
    }
    return n;
}

/* hash of the previous unit's ends: entries {key, f, idx}, sized per unit (small units stay in cache) */
typedef struct { u64 k; u32 f, i; } HE;
static HE *ht; static int hb_ = 0; static size_t htcap = 0;
static inline u64 hh_(u64 k) { k ^= k >> 31; k *= 0x9E3779B97F4A7C15ULL; return k >> (64 - hb_); }
static void hinit(size_t puts) {
    int b = 6; while (((size_t)1 << b) < 2 * puts) b++;
    if (b > 28) DIE("hash too large");
    size_t sz = (size_t)1 << b; if (sz > htcap) { free(ht); ht = malloc(sizeof(HE) * sz); if (!ht) DIE("oom (hash)"); htcap = sz; }
    hb_ = b; for (size_t p = 0; p < sz; p++) ht[p].k = ~0ULL;
}
static inline void hput(u64 k, u32 f, u32 i) {
    u64 p = hh_(k), mk = ((u64)1 << hb_) - 1;
    for (;;) { if (ht[p].k == ~0ULL) { ht[p].k = k; ht[p].f = f; ht[p].i = i; return; }
               if (ht[p].k == k) { if (f < ht[p].f) { ht[p].f = f; ht[p].i = i; } return; } p = (p + 1) & mk; }
}
static inline int hget(u64 k, u32 *f, u32 *i) {
    u64 p = hh_(k), mk = ((u64)1 << hb_) - 1;
    for (;;) { if (ht[p].k == ~0ULL) return 0; if (ht[p].k == k) { *f = ht[p].f; *i = ht[p].i; return 1; } p = (p + 1) & mk; }
}
static double t_cand = 0, t_put = 0, t_get = 0, t_rest = 0;

/* ------------------------------------------------------------------ back file: bytes f - fmin per candidate */
static FILE *bf; static u64 bsize;
static u8 *wbuf; static size_t wfill; static const size_t WBUF = 8u << 20;
static void bflush(void) { if (wfill && fwrite(wbuf, 1, wfill, bf) != wfill) DIE("back file write failed"); wfill = 0; }
static void bput(const u8 *p, size_t n) { if (wfill + n > WBUF) bflush(); memcpy(wbuf + wfill, p, n); wfill += n; bsize += n; }
static u8 *rwin; static u64 rlo = 0, rhi = 0; static const u64 RWIN = 256ull << 20;
static void bget(u64 off, size_t n, u8 *dst) {
    if (!(off >= rlo && off + n <= rhi)) {
        u64 hi_ = off + n, lo = hi_ > RWIN ? hi_ - RWIN : 0; if (hi_ > bsize) DIE("bget beyond file");
        if (fseeko64(bf, (long long)lo, SEEK_SET) || fread(rwin, 1, hi_ - lo, bf) != hi_ - lo) DIE("back file read failed");
        rlo = lo; rhi = hi_;
    }
    memcpy(dst, rwin + (off - rlo), n);
}

static u32 *fmin_, *ncand_, *choice_;
static u8 *fb; static u32 *fprev, *fcur; static u64 *Eprev; static size_t pcap;

static void dp_forward(void) {
    ccap = 0; cgrow(1 << 16);
    wbuf = malloc(WBUF); rwin = malloc(RWIN);
    fmin_ = malloc(4 * (size_t)NU); ncand_ = malloc(4 * (size_t)NU);
    int np = 0; u32 pgmin = 0, pgi = 0;
    u64 *S, *E; u32 *M;
    for (u32 ui = 0; ui < NU; ui++) {
        double tA = wall();
        int n = cands_into(&U[ui], &S, &E, &M);
        double tB = wall(); t_cand += tB - tA;
        if ((size_t)n > pcap) { pcap = 2 * (size_t)n + 16; fprev = realloc(fprev, 4 * pcap); fcur = realloc(fcur, 4 * pcap); Eprev = realloc(Eprev, 8 * pcap); fb = realloc(fb, pcap); if (!fprev || !fcur || !Eprev || !fb) DIE("oom"); }
        if (ui == 0) { for (int c = 0; c < n; c++) fcur[c] = 0; }
        else {
            hinit((size_t)np * HH);
            int have[16] = {0}; u32 qmin[16]; for (int q = 0; q <= HH; q++) qmin[q] = ~0u;
            for (int c = 0; c < np; c++) {
                u32 d = fprev[c] - pgmin;                      /* an entry at q can win only if q > d (default cost is pgmin + HH) */
                for (int q = d + 1; q <= HH; q++) {
                    hput((u64)q << 56 | (Eprev[c] & ((1ULL << (4 * q)) - 1)), fprev[c], c); have[q] = 1;
                    if (fprev[c] < qmin[q]) qmin[q] = fprev[c];
                }
            }
            double tC = wall(); t_put += tC - tB; tB = tC;
            for (int c = 0; c < n; c++) {
                u32 best = pgmin + HH, bi = pgi, f, i;
                for (int q = 1; q <= HH; q++) {
                    if (!have[q] || qmin[q] + HH - q >= best) continue;
                    if (hget((u64)q << 56 | (S[c] >> (4 * (HH - q))), &f, &i) && f + HH - q < best) { best = f + HH - q; bi = i; }
                }
                fcur[c] = best; (void)bi;
            }
            tC = wall(); t_get += tC - tB; tB = tC;
        }
        u32 gmin = ~0u, gi = 0; for (int c = 0; c < n; c++) if (fcur[c] < gmin) { gmin = fcur[c]; gi = c; }
        for (int c = 0; c < n; c++) { u32 d = fcur[c] - gmin; if (d > 255) DIE("f spread %u", d); fb[c] = (u8)d; }
        bput(fb, n); fmin_[ui] = gmin; ncand_[ui] = n;
        { u32 *t = fprev; fprev = fcur; fcur = t; }                 /* fprev = this unit's f */
        memcpy(Eprev, E, 8 * (size_t)n); np = n; pgmin = gmin; pgi = gi;
        t_rest += wall() - tB;
        if (getenv("LIFT17_STOP") && ui + 1 == (u32)atoi(getenv("LIFT17_STOP"))) { fprintf(stderr, "stopped at %u (%.0fs): cands %.0fs put %.0fs get %.0fs rest %.0fs\n", ui, wall() - t0g, t_cand, t_put, t_get, t_rest); exit(0); }
        if (ui % 1000000 == 0) fprintf(stderr, "  dp unit %u (%.0fs) back %.1f GB\n", ui, wall() - t0g, bsize / 1e9);
    }
    bflush(); fflush(bf);
    /* the best end candidate: first with min f */
    choice_ = malloc(4 * (size_t)NU);
    { u8 *tmp = malloc(np); u64 off = bsize - np; bget(off, np, tmp); int bc = 0; for (int c = 0; c < np; c++) if (tmp[c] < tmp[bc]) bc = c; choice_[NU - 1] = bc; free(tmp); }
    fprintf(stderr, "forward done: join total %u (%.0fs)\n", fmin_[NU - 1], wall() - t0g);
    fprintf(stderr, "time: cands %.0fs put %.0fs get %.0fs rest %.0fs\n", t_cand, t_put, t_get, t_rest);
}

/* backward: from the choice in unit ui find the predecessor choice in ui - 1 with lift16's tie-breaking */
static void dp_backward(void) {
    u64 off = bsize;
    u64 *S, *E; u32 *M;
    u64 *cS0 = NULL; size_t cs0cap = 0;                                   /* start keys of unit ui */
    u8 *fbp = NULL; size_t fbcap = 0;
    u64 *Ep = NULL; size_t epcap = 0;
    int n = cands_into(&U[NU - 1], &S, &E, &M);
    if ((size_t)n > cs0cap) { cs0cap = 2 * (size_t)n + 16; cS0 = realloc(cS0, 8 * cs0cap); }
    memcpy(cS0, S, 8 * (size_t)n);
    for (u32 ui = NU - 1; ui >= 1; ui--) {
        off -= ncand_[ui];
        int c = choice_[ui];
        u8 byte; bget(off + c, 1, &byte); u32 fc = fmin_[ui] + byte;
        int np = cands_into(&U[ui - 1], &S, &E, &M);
        if ((size_t)np > fbcap) { fbcap = 2 * (size_t)np + 16; fbp = realloc(fbp, fbcap); }
        if ((size_t)np > epcap) { epcap = 2 * (size_t)np + 16; Ep = realloc(Ep, 8 * epcap); }
        memcpy(Ep, E, 8 * (size_t)np);
        bget(off - np, np, fbp);
        u32 pgmin = fmin_[ui - 1]; int pgi = 0; while (fbp[pgi]) pgi++;
        u32 best = pgmin + HH, bi = pgi;
        for (int q = 1; q <= HH; q++) {
            u64 key = cS0[c] >> (4 * (HH - q)), mask = (1ULL << (4 * q)) - 1; u32 mf = ~0u; int mi = -1;
            for (int j = 0; j < np; j++) if ((Ep[j] & mask) == key) { u32 f = pgmin + fbp[j]; if (f < mf) { mf = f; mi = j; } }
            if (mi >= 0 && mf + HH - q < best) { best = mf + HH - q; bi = mi; }
        }
        if (best != fc) DIE("backward: unit %u candidate %d has f %u, recomputed %u", ui, c, fc, best);
        choice_[ui - 1] = bi;
        if ((size_t)np > cs0cap) { cs0cap = 2 * (size_t)np + 16; cS0 = realloc(cS0, 8 * cs0cap); }
        memcpy(cS0, S, 8 * (size_t)np);
        if (ui % 1000000 == 0) fprintf(stderr, "  back unit %u (%.0fs)\n", ui, wall() - t0g);
    }
}

/* ------------------------------------------------------------------ lower level */
static u64 *lrbuf; static size_t lrcap, lrst[24]; static int lr_v = -1;           /* level-1 transport cache */
static const u64 *low_rows(int w, u64 *m, int *Kl, int *first, int *g) {          /* rows of lower walk w; its first upper walk number, number of orbits */
    if (LAZY == 1) {
        const u64 *r = wrow_sh + wstart_sh[w]; *m = wstart_sh[w + 1] - wstart_sh[w]; *Kl = KP; *first = pre1[w];
        *g = pre1[w + 1] - pre1[w]; return r;
    }
    if (LAZY == 2) {
        int v = pre_find(pre1, nst, w), a1 = w - pre1[v];
        if (v != lr_v) { int no = ptransport(wrow_sh + wstart_sh[v], wstart_sh[v + 1] - wstart_sh[v], KP, &lrbuf, &lrcap, lrst);
                         if (no != pre1[v + 1] - pre1[v]) DIE("stored walk %d: %d orbits", v, no); lr_v = v; }
        const u64 *r = lrbuf + lrst[a1]; *m = lrst[a1 + 1] - lrst[a1]; *Kl = KP + 1; *first = pre2[w];
        *g = pre2[w + 1] - pre2[w]; return r;
    }
    DIE("lift17 needs GEN17_LAZY >= 1"); return NULL;
}
static void read_lower(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) DIE("cannot open %s", path);
    char line[512], hdr[32]; int nl = 0; sprintf(hdr, "N%d-UNITPLAN", NN - 1);
    u32 src = 0; int h1 = HH - 1;                       /* lower h = n - 1 - 3 = K - 1 - 1... */
    h1 = (NN - 1) - 3;
    int L1 = L - 1;
    while (fgets(line, sizeof line, f)) {
        nl++;
        if (nl == 1) { if (strncmp(line, hdr, strlen(hdr))) DIE("not an n = %d unit plan", NN - 1); continue; }
        if (line[0] == '#' || line[0] == '\n' || line[0] == '\r') continue;
        char *tok[16]; int nt = 0; char *sv = NULL;
        for (char *t = strtok_r(line, " \t\r\n", &sv); t && nt < 16; t = strtok_r(NULL, " \t\r\n", &sv)) tok[nt++] = t;
        if (nt && tok[nt - 1][0] == 'o') nt--;
        if (tok[0][0] == 'D') {
            if (nt != 2 + L1) DIE("D line %d", nl);
            int d = atoi(tok[1]), j = atoi(tok[nt - 1]), g[5] = {0};
            for (int l = 0; l < L1 - 1; l++) g[l] = atoi(tok[2 + l]);
            for (int i = 0; i < h1; i++) {              /* its trails: the new letter inserted at a = j + i */
                Unit u; memset(&u, 0, sizeof u); u.k = 'D'; u.a = d; g[L1 - 1] = (j + i) % h1;
                for (int l = 0; l < L1; l++) u.g |= (uint16_t)(g[l] << (4 * l));
                u.src = src; U[NU++] = u;
            }
            src++;
        } else if (tok[0][0] == 'W' && nt == 4) {
            int w = atoi(tok[1]), way = atoi(tok[3]); u64 i0 = strtoull(tok[2], NULL, 10);
            u64 m; int Kl, first, g; const u64 *lr = low_rows(w, &m, &Kl, &first, &g);
            int H = Kl - 1;
            if (i0 >= m || rty(lr[i0])) DIE("W line %d: not a full row", nl);
            if (H != h1) DIE("lower H %d, h %d", H, h1);
            for (int i = 0; i < h1; i++) {
                int q = way == 0 ? i : i + 1, port = q == Kl - 1 ? 0 : q;
                int p = port; for (u64 r = i0; r < m; r++) p = (p + (rty(lr[r]) == 0 ? -1 : 1) + H) % H;   /* port at row 0 */
                Unit u; memset(&u, 0, sizeof u); u.k = 'W'; u.a = first + p % g; u.src = src; U[NU++] = u;
            }
            src++;
        } else DIE("bad line %d", nl);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 6 || strcmp(argv[1], "lift")) { fprintf(stderr, "usage: lift17 lift L SEL PLAN(n-1) OUT.uplan\n"); return 2; }
    t0g = wall(); gs_new();
    L = atoi(argv[2]); if (L < 2 || L > 5) DIE("L must be 2..5");
    NN = 12 + L; K = 10 + L; HH = NN - 3; SL = K; ZL = K + 1;
    read_sel(argv[3]); build_walks();
    if (!LAZY) DIE("lift17 needs GEN17_LAZY >= 1 (L >= 4, or the variable)");
    u64 nsu = (u64)ndet; for (int l = 0; l < L - 1; l++) nsu *= (u64)(10 + l);
    u64 ucap = nsu + (u64)nwl + 16;
    U = malloc(sizeof(Unit) * ucap); if (!U) DIE("oom (units)"); NU = 0;
    read_lower(argv[4]);
    fprintf(stderr, "lower plan read: %u units (%.0fs)\n", NU, wall() - t0g);
    if ((u64)NU != nsu + (u64)nwl) DIE("plan has %u units, expected %llu", NU, (unsigned long long)(nsu + nwl));
    char *seen = calloc(nsu + nwl, 1);
    for (u32 i = 0; i < NU; i++) {
        u64 id;
        if (U[i].k == 'D') { id = U[i].a; for (int l = 0; l < L - 1; l++) id = id * (10 + l) + ug(&U[i], l); }
        else id = nsu + U[i].a;
        if (id >= nsu + nwl || seen[id]++) DIE("unit %u repeated or out of range", i);
    }
    free(seen);
    fprintf(stderr, "units %u, each once (%.0fs)\n", NU, wall() - t0g);
    const char *bp = getenv("LIFT17_BACK"); if (!bp) bp = "lift17.back";
    bf = fopen(bp, "w+b"); if (!bf) DIE("cannot open back file %s", bp);
    dp_forward();
    dp_backward();
    fclose(bf); remove(bp);
    /* write the plan */
    long nS = 0, nW = 0; long hist[17] = {0}; long ccount[8] = {0}, ccost[8] = {0};
    FILE *o = fopen(argv[5], "w"); if (!o) DIE("cannot write %s", argv[5]);
    setvbuf(o, NULL, _IOFBF, 1 << 20);
    fprintf(o, "N%d-UNITPLAN 1\n# units in the order of the trails of %s, openings by lift17 dp\n", NN, argv[4]);
    u64 prevE = 0; u64 *S, *E; u32 *M; u32 joins = 0;
    for (u32 ui = 0; ui < NU; ui++) {
        cands_into(&U[ui], &S, &E, &M); u32 ch = choice_[ui];
        if (ui) { int ov = 0; for (int q = HH; q >= 1; q--) if ((prevE & ((1ULL << (4 * q)) - 1)) == (S[ch] >> (4 * (HH - q)))) { ov = q; break; } hist[HH - ov]++; joins += HH - ov;
            const Unit *ua = &U[ui - 1], *ub = &U[ui]; int cl = (ua->src == ub->src ? 0 : 4) + (ua->k == 'W') * 2 + (ub->k == 'W');
            ccount[cl]++; ccost[cl] += HH - ov; }
        prevE = E[ch];
        if (U[ui].k == 'D') { fprintf(o, "D %u", U[ui].a); for (int l = 0; l < L - 1; l++) fprintf(o, " %d", ug(&U[ui], l)); fprintf(o, " %u\n", M[ch]); nS++; }
        else { fprintf(o, "W %u %u %u\n", U[ui].a, M[ch] >> 1, M[ch] & 1); nW++; }
    }
    fclose(o);
    u64 fact[20]; fact[0] = 1; for (int i = 1; i < 20; i++) fact[i] = fact[i - 1] * i;
    u64 nshort = 0; for (int i = 0; i < nsel; i++) nshort += sel[i].ty == 1;
    u64 mult = 1; for (int l = 0; l < L; l++) mult *= (u64)(10 + l);
    u64 sumR = fact[NN] + fact[NN - 1] + fact[NN - 2] + 2 * nshort * mult;
    u32 best = fmin_[NU - 1];
    if (joins != best) DIE("join total %u from the written choices, %u from the DP", joins, best);
    u64 len = sumR + HH + (u64)(HH - 1) * nS + (u64)HH * nW + best;
    fprintf(stderr, "units %u (small %ld, walk %ld); joins %u (sum of h - overlap); join costs:", NU, nS, nW, best);
    for (int q = 0; q <= HH; q++) if (hist[q]) fprintf(stderr, " %d:%ld", q, hist[q]);
    fprintf(stderr, "\nclasses (same lower unit/other; D/W -> D/W): count cost:");
    for (int c = 0; c < 8; c++) fprintf(stderr, " %d:%ld/%ld", c, ccount[c], ccost[c]);
    fprintf(stderr, "\nLENGTH %llu\n", (unsigned long long)len);
    fprintf(stderr, "(%.0fs)\n", wall() - t0g);
    return 0;
}
