/* uopt15.c - local search on a unit plan of gen15 (any L >= 1), without the word: uopt.c made general in L.
   Cost of a plan = sum over joins of (h - overlap(E, S)); the rest of the length is fixed.
   Move: take a segment of up to SEG consecutive units out and put it between two other units; the openings of the
   units next to both places and of the moved units are chosen again by an exact DP over a window (WIN units on
   each side free, the units beyond fixed).  Places come from an index of the current last and first words.
   Walk-unit candidates are not stored: candidate 2 f + way of walk w is its f-th full row (index table) and way.

   usage: uopt15 L SEL IN.uplan OUT.uplan [--time SEC] [--seed S] [--eq P] [--seg L] [--win W] [--qmin Q] [--places M]
   Writes OUT at every improvement of 1000 and at the end; prints the exact length. */
#define GEN15_NO_MAIN
#include "../../recipes/n15/gen16.c"

typedef struct { char k; int d; int g[3]; int w; } Unit;
static Unit *U; static int NU;
static u64 MASKH;                                     /* low 4h bits */
static u64 packh(const u8 *w) { u64 v = 0; for (int i = 0; i < HH; i++) v = v << 4 | w[i]; return v; }
/* candidates: small units 12 stored (S, E); walk units computed */
static u64 *coff;                                     /* first candidate of each unit */
static u64 *sS, *sE; static u64 *soff;                /* small candidates (by unit: soff[u] index into sS) */
static u32 *fidx; static u64 *foff;                   /* full rows of each lifted walk */
static int ncand(int u) { return (int)(coff[u + 1] - coff[u]); }
static inline u64 nibrev(u64 x) {                     /* nibble t -> nibble 15 - t */
    x = ((x & 0x0F0F0F0F0F0F0F0FULL) << 4) | ((x >> 4) & 0x0F0F0F0F0F0F0F0FULL);
    return __builtin_bswap64(x);
}
/* S and E of global candidate c of unit u */
static inline void candSE(int u, u64 c, u64 *S, u64 *E) {
    u64 i = c - coff[u];
    if (U[u].k == 'D') { *S = sS[soff[u] + i]; *E = sE[soff[u] + i]; return; }
    int w = U[u].w; u64 row = wrow[wstart[w] + fidx[foff[w] + (i >> 1)]] & ((1ULL << (4 * K)) - 1);
    u64 r = nibrev(row);                              /* b[t] at nibble 15 - t */
    int sh = 4 * (16 - K);                            /* b[0] .. b[K-1] at nibbles K-1 .. 0 after >> sh */
    u64 rr = r >> sh;
    u64 S0 = rr >> 4, S1 = rr & MASKH;                /* way 0: b[0..h-1]; way 1: b[1..K-1] */
    if (i & 1) { *S = S1; *E = S0; }
    else { *S = S0; *E = ((rr & 15) << (4 * (HH - 1))) | ((rr >> 8) & ((1ULL << (4 * (HH - 1))) - 1)); }
}
static inline u64 cS_(int u, u64 c) { u64 s, e; candSE(u, c, &s, &e); return s; }
static inline u64 cE_(int u, u64 c) { u64 s, e; candSE(u, c, &s, &e); return e; }
static u32 candM(int u, u64 c) { u64 i = c - coff[u]; if (U[u].k == 'D') return (u32)i; return fidx[foff[U[u].w] + (i >> 1)] * 2 + (u32)(i & 1); }

static void build_cands(void) {
    foff = malloc(8 * (size_t)(nwl + 1)); u64 nf = 0;
    for (int w = 0; w < nwl; w++) { foff[w] = nf; for (u64 r = wstart[w]; r < wstart[w + 1]; r++) nf += !rty(wrow[r]); }
    foff[nwl] = nf; fidx = malloc(4 * nf);
    for (int w = 0; w < nwl; w++) { u64 q = foff[w]; for (u64 r = wstart[w]; r < wstart[w + 1]; r++) if (!rty(wrow[r])) fidx[q++] = (u32)(r - wstart[w]); }
    coff = malloc(8 * (size_t)(NU + 1)); soff = malloc(8 * (size_t)NU); u64 tot = 0, ns = 0;
    for (int u = 0; u < NU; u++) { coff[u] = tot; if (U[u].k == 'D') { soff[u] = ns; ns += HH; tot += HH; } else tot += 2 * (foff[U[u].w + 1] - foff[U[u].w]); }
    coff[NU] = tot;
    sS = malloc(8 * ns); sE = malloc(8 * ns);
    for (int u = 0; u < NU; u++) if (U[u].k == 'D') {
        u8 y[16], r[16]; small_y(U[u].d, U[u].g, y);
        for (int j = 0; j < HH; j++) { rot(r, y, HH, j); sS[soff[u] + j] = packh(r); rot(r, y, HH, j - 1); sE[soff[u] + j] = packh(r); }
    }
    fprintf(stderr, "candidates %llu (walk full rows %llu)\n", (unsigned long long)tot, (unsigned long long)nf);
}
static inline int jc(u64 E, u64 S) {
    for (int q = HH; q >= 1; q--) if ((E & ((1ULL << (4 * q)) - 1)) == (S >> (4 * (HH - q)))) return HH - q;
    return HH;
}
static int *nx, *pv; static u64 *cho; static int head, tailu;
static inline u64 CE(int u) { return cE_(u, cho[u]); }
static inline u64 CSu(int u) { return cS_(u, cho[u]); }
static i64 total_cost(void) { i64 c = 0; for (int u = head; nx[u] >= 0; u = nx[u]) c += jc(CE(u), CSu(nx[u])); return c; }

#define LB 20
static u64 *lk; static u32 *lf, *li, *ls; static u32 lstamp = 0;
static inline u64 lh(u64 k) { k ^= k >> 29; k *= 0x9E3779B97F4A7C15ULL; return k >> (64 - LB); }
static void lput(u64 k, u32 f, u32 i) { u64 p = lh(k); for (;;) { if (ls[p] != lstamp) { ls[p] = lstamp; lk[p] = k; lf[p] = f; li[p] = i; return; } if (lk[p] == k) { if (f < lf[p]) { lf[p] = f; li[p] = i; } return; } p = (p + 1) & ((1u << LB) - 1); } }
static int lget(u64 k, u32 *f, u32 *i) { u64 p = lh(k); for (;;) { if (ls[p] != lstamp) return 0; if (lk[p] == k) { *f = lf[p]; *i = li[p]; return 1; } p = (p + 1) & ((1u << LB) - 1); } }

#define MAXW 26
static u32 *dpf[MAXW], *dpb[MAXW]; static size_t dpcap[MAXW];
static u64 *tS[MAXW], *tE[MAXW];
static u32 dp_chain(const int *w, int m, u64 c0, u64 cm, u64 *out) {
#define CAND(s, c) ((s == 0 && c0 != ~0ULL) ? c0 : (s == m - 1 && cm != ~0ULL) ? cm : coff[w[s]] + (c))
#define NC(s) (((s == 0 && c0 != ~0ULL) || (s == m - 1 && cm != ~0ULL)) ? 1 : ncand(w[s]))
    for (int s = 0; s < m; s++) {
        int n = NC(s);
        if ((size_t)n > dpcap[s]) { dpcap[s] = n * 2; dpf[s] = realloc(dpf[s], 4 * dpcap[s]); dpb[s] = realloc(dpb[s], 4 * dpcap[s]); tS[s] = realloc(tS[s], 8 * dpcap[s]); tE[s] = realloc(tE[s], 8 * dpcap[s]); }
        for (int c = 0; c < n; c++) candSE(w[s], CAND(s, c), &tS[s][c], &tE[s][c]);
    }
    for (int c = 0; c < NC(0); c++) dpf[0][c] = 0;
    for (int s = 1; s < m; s++) {
        int np = NC(s - 1), n = NC(s);
        if ((i64)np * n <= 4096) {
            for (int c = 0; c < n; c++) { u64 S = tS[s][c]; u32 best = ~0u, bi = 0;
                for (int p = 0; p < np; p++) { u32 v = dpf[s - 1][p] + jc(tE[s - 1][p], S); if (v < best) { best = v; bi = p; } }
                dpf[s][c] = best; dpb[s][c] = bi; }
        } else {
            lstamp++; u32 gmin = ~0u, gi = 0;
            for (int p = 0; p < np; p++) { u64 E = tE[s - 1][p]; u32 f = dpf[s - 1][p]; if (f < gmin) { gmin = f; gi = p; }
                for (int q = 1; q <= HH; q++) lput((u64)q << 56 | (E & ((1ULL << (4 * q)) - 1)), f, p); }
            for (int c = 0; c < n; c++) { u64 S = tS[s][c]; u32 best = gmin + HH, bi = gi, f, i;
                for (int q = 1; q <= HH; q++) if (lget((u64)q << 56 | (S >> (4 * (HH - q))), &f, &i) && f + HH - q < best) { best = f + HH - q; bi = i; }
                dpf[s][c] = best; dpb[s][c] = bi; }
        }
    }
    int n = NC(m - 1); u32 best = ~0u; int bc = 0;
    for (int c = 0; c < n; c++) if (dpf[m - 1][c] < best) { best = dpf[m - 1][c]; bc = c; }
    if (out) { int c = bc; for (int s = m - 1; s >= 0; s--) { out[s] = CAND(s, c); c = dpb[s][c]; } }
    return best;
#undef CAND
#undef NC
}

#define IB 26
static u64 *ik; static u32 *ihead; static u32 *inext, *iunit; static u32 inn, icap;
static int QMIN = 8;
static void ix_clear(void) { memset(ihead, 0xff, 4ULL << IB); for (u64 p = 0; p < (1ULL << IB); p++) ik[p] = ~0ULL; inn = 0; }
static inline u64 ixh(u64 k) { k ^= k >> 31; k *= 0xD6E8FEB86659FD93ULL; return k >> (64 - IB); }
static void ix_add(u64 key, int u) {
    u64 p = ixh(key);
    while (ik[p] != ~0ULL && ik[p] != key) p = (p + 1) & ((1ULL << IB) - 1);
    if (ik[p] == ~0ULL) ik[p] = key;
    if (inn == icap) { icap = icap * 2 + 1024; inext = realloc(inext, 4ULL * icap); iunit = realloc(iunit, 4ULL * icap); }
    inext[inn] = ihead[p]; iunit[inn] = u; ihead[p] = inn++;
}
static u32 ix_first(u64 key) { u64 p = ixh(key); while (ik[p] != ~0ULL) { if (ik[p] == key) return ihead[p]; p = (p + 1) & ((1ULL << IB) - 1); } return ~0u; }
static void ix_unit(int u) {
    u64 E = CE(u), S = CSu(u);
    for (int q = QMIN; q <= HH; q++) {
        ix_add((u64)q << 56 | (E & ((1ULL << (4 * q)) - 1)), u);
        ix_add(1ULL << 63 | (u64)q << 56 | (S >> (4 * (HH - q))), u);
    }
}
static void ix_build(void) { ix_clear(); for (int u = head; u >= 0; u = nx[u]) ix_unit(u); }
static u64 rng = 88172645463325252ULL;
static inline u64 xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static void write_plan(const char *path, const char *note) {
    char tmp[1024]; snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *o = fopen(tmp, "w"); if (!o) DIE("cannot write %s", tmp);
    fprintf(o, "N%d-UNITPLAN 1\n# %s\n", NN, note);
    for (int u = head; u >= 0; u = nx[u]) {
        u32 m = candM(u, cho[u]);
        if (U[u].k == 'D') { fprintf(o, "D %d", U[u].d); for (int l = 0; l < L - 1; l++) fprintf(o, " %d", U[u].g[l]); fprintf(o, " %u\n", m); }
        else fprintf(o, "W %d %u %u\n", U[u].w, m >> 1, m & 1);
    }
    fclose(o); remove(path); rename(tmp, path);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: uopt15 L SEL IN.uplan OUT.uplan [--time SEC] [--seed S] [--eq P] [--seg L] [--win W] [--qmin Q] [--places M]\n"); return 2; }
    double tlim = 600, peq = 0; int SEG = 1, WIN = 1, PLACES = 24; u64 seed = 1;
    for (int i = 5; i < argc; i++) {
        if (!strcmp(argv[i], "--time")) tlim = atof(argv[++i]);
        else if (!strcmp(argv[i], "--seed")) seed = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--eq")) peq = atof(argv[++i]);
        else if (!strcmp(argv[i], "--seg")) SEG = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--win")) WIN = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--qmin")) QMIN = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--places")) { PLACES = atoi(argv[++i]); if (PLACES > 32) PLACES = 32; }
        else DIE("unknown option %s", argv[i]);
    }
    if (SEG < 1 || SEG > 4 || WIN < 1 || WIN > 3) DIE("seg 1..4, win 1..3");
    rng ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) xr();
    t0g = wall();
    L = atoi(argv[1]); if (L < 1 || L > 3) DIE("L 1..3");
    NN = 12 + L; K = 10 + L; HH = NN - 3; SL = K; ZL = K + 1; MASKH = (1ULL << (4 * HH)) - 1;
    read_sel(argv[2]); build_walks();
    U = malloc(sizeof(Unit) * 1000000); NU = 0;
    u32 *m0 = malloc(4 * 1000000);
    FILE *f = fopen(argv[3], "r"); if (!f) DIE("cannot open %s", argv[3]);
    char line[512];
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#' || line[0] == 'N' || line[0] == '\n') continue;
        char *tok[16]; int nt = 0; char *sv = NULL;
        for (char *t = strtok_r(line, " \t\r\n", &sv); t && nt < 16; t = strtok_r(NULL, " \t\r\n", &sv)) tok[nt++] = t;
        if (nt && tok[nt - 1][0] == 'o') nt--;
        Unit u; memset(&u, 0, sizeof u); u.k = tok[0][0];
        if (u.k == 'D') { u.d = atoi(tok[1]); for (int l = 0; l < L - 1; l++) u.g[l] = atoi(tok[2 + l]); m0[NU] = (u32)atoi(tok[nt - 1]); }
        else { u.w = atoi(tok[1]); m0[NU] = (u32)(atoi(tok[2]) * 2 + atoi(tok[3])); }
        U[NU++] = u;
    }
    fclose(f);
    build_cands();
    nx = malloc(4 * NU); pv = malloc(4 * NU); cho = malloc(8 * NU);
    long nS = 0, nW = 0;
    for (int u = 0; u < NU; u++) {
        nx[u] = u + 1 < NU ? u + 1 : -1; pv[u] = u - 1;
        u64 c;
        if (U[u].k == 'D') c = coff[u] + m0[u];
        else { u32 row = m0[u] >> 1; u64 lo = foff[U[u].w], hi = foff[U[u].w + 1], a = lo, b = hi;
               while (a < b) { u64 mid = (a + b) / 2; if (fidx[mid] < row) a = mid + 1; else b = mid; }
               if (a == hi || fidx[a] != row) DIE("unit %d: opening not a full row", u);
               c = coff[u] + 2 * (a - lo) + (m0[u] & 1); }
        if (candM(u, c) != m0[u]) DIE("unit %d: opening bookkeeping", u);
        cho[u] = c; if (U[u].k == 'D') nS++; else nW++;
    }
    head = 0; tailu = NU - 1;
    u64 fact[20]; fact[0] = 1; for (int i = 1; i < 20; i++) fact[i] = fact[i - 1] * i;
    u64 nshort = 0; for (int i = 0; i < nsel; i++) nshort += sel[i].ty == 1;
    u64 mult = 1; for (int l = 0; l < L; l++) mult *= (u64)(10 + l);
    u64 sumR = fact[NN] + fact[NN - 1] + fact[NN - 2] + 2 * nshort * mult, base = sumR + HH + (u64)(HH - 1) * nS + (u64)HH * nW;
    i64 cost = total_cost();
    fprintf(stderr, "units %d, cost %lld, length %llu (%.0fs)\n", NU, cost, (unsigned long long)(base + cost), wall() - t0g);
    lk = malloc(8ULL << LB); lf = malloc(4ULL << LB); li = malloc(4ULL << LB); ls = calloc(1ULL << LB, 4);
    ik = malloc(8ULL << IB); ihead = malloc(4ULL << IB);
    ix_build();
    i64 start_cost = cost, last_write = cost; long tried = 0, acc = 0, eqacc = 0; double lastrep = wall();
    int *perm = malloc(4 * NU); for (int i = 0; i < NU; i++) perm[i] = i;
    int pass = 0; char note[512];
    while (wall() - t0g < tlim) {
        for (int i = NU - 1; i > 0; i--) { int j = (int)(xr() % (i + 1)); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        long acc_pass = 0;
        for (int pi = 0; pi < NU && wall() - t0g < tlim; pi++) {
            int u0 = perm[pi]; int Lg = 1 + (int)(xr() % SEG);
            int seg[16]; seg[0] = u0; int ok = 1;
            for (int s = 1; s < Lg; s++) { int v = nx[seg[s - 1]]; if (v < 0) { ok = 0; break; } seg[s] = v; }
            if (!ok) continue;
            int u1 = seg[Lg - 1];
            int left[4], right[4], nl = 0, nr = 0, x = pv[u0];
            while (x >= 0 && nl < WIN + 1) { left[nl++] = x; x = pv[x]; }
            x = nx[u1]; while (x >= 0 && nr < WIN + 1) { right[nr++] = x; x = nx[x]; }
            int win[MAXW]; int m = 0;
            for (int s = nl - 1; s >= 0; s--) win[m++] = left[s];
            for (int s = 0; s < Lg; s++) win[m++] = seg[s];
            for (int s = 0; s < nr; s++) win[m++] = right[s];
            i64 curA = 0; for (int s = 0; s + 1 < m; s++) curA += jc(CE(win[s]), CSu(win[s + 1]));
            int wr[MAXW]; int mr = 0; for (int s = nl - 1; s >= 0; s--) wr[mr++] = left[s]; for (int s = 0; s < nr; s++) wr[mr++] = right[s];
            u64 outR[MAXW]; i64 newA;
            if (mr == 0) newA = 0;
            else {
                u64 c0 = (nl == WIN + 1) ? cho[wr[0]] : ~0ULL, cm = (nr == WIN + 1) ? cho[wr[mr - 1]] : ~0ULL;
                if (mr == 1) { c0 = cho[wr[0]]; cm = ~0ULL; }
                newA = dp_chain(wr, mr, c0, cm, outR);
            }
            i64 gainA = curA - newA;
            int places[64]; int np = 0;
            u64 c0a = coff[u0], c1a = coff[u0 + 1];
            u64 step = (c1a - c0a) > 64 ? (c1a - c0a) / 64 : 1;
            for (int q = HH; q >= QMIN && np < PLACES; q--) {
                for (u64 c = c0a + (xr() % step); c < c1a && np < PLACES; c += step) {
                    u64 Sc = cS_(u0, c), key = (u64)q << 56 | (Sc >> (4 * (HH - q)));
                    for (u32 e = ix_first(key); e != ~0u && np < PLACES; e = inext[e]) {
                        int a = iunit[e];
                        if ((CE(a) & ((1ULL << (4 * q)) - 1)) != (Sc >> (4 * (HH - q)))) continue;
                        int bad = 0; for (int s = 0; s < m; s++) if (win[s] == a) bad = 1;
                        if (nx[a] >= 0) for (int s = 0; s < m; s++) if (win[s] == nx[a]) bad = 1;
                        for (int t = 0; t < np; t++) if (places[t] == a) bad = 1;
                        if (!bad) places[np++] = a;
                    }
                }
            }
            u64 c0b = coff[u1], c1b = coff[u1 + 1]; step = (c1b - c0b) > 64 ? (c1b - c0b) / 64 : 1;
            for (int q = HH; q >= QMIN && np < 2 * PLACES; q--) {
                for (u64 c = c0b + (xr() % step); c < c1b && np < 2 * PLACES; c += step) {
                    u64 Ec = cE_(u1, c), key = 1ULL << 63 | (u64)q << 56 | (Ec & ((1ULL << (4 * q)) - 1));
                    for (u32 e = ix_first(key); e != ~0u && np < 2 * PLACES; e = inext[e]) {
                        int b = iunit[e]; if (pv[b] < 0) continue;
                        if ((CSu(b) >> (4 * (HH - q))) != (Ec & ((1ULL << (4 * q)) - 1))) continue;
                        int a = pv[b];
                        int bad = 0; for (int s = 0; s < m; s++) if (win[s] == a || win[s] == b) bad = 1;
                        for (int t = 0; t < np; t++) if (places[t] == a) bad = 1;
                        if (!bad) places[np++] = a;
                    }
                }
            }
            i64 bestd = 1; int besta = -1; u64 bestout[MAXW]; int bestw[MAXW], bestm = 0;
            for (int t = 0; t < np; t++) {
                int a = places[t];
                int L2[4], R2[4], nl2 = 0, nr2 = 0; x = a;
                while (x >= 0 && nl2 < WIN + 1) { L2[nl2++] = x; x = pv[x]; }
                x = nx[a]; while (x >= 0 && nr2 < WIN + 1) { R2[nr2++] = x; x = nx[x]; }
                int w2[MAXW], m2 = 0, bad = 0;
                for (int s = nl2 - 1; s >= 0; s--) w2[m2++] = L2[s];
                for (int s = 0; s < nr2; s++) w2[m2++] = R2[s];
                for (int s = 0; s < m2; s++) for (int r = 0; r < m; r++) if (w2[s] == win[r]) bad = 1;
                if (bad) continue;
                i64 curB = 0; for (int s = 0; s + 1 < m2; s++) curB += jc(CE(w2[s]), CSu(w2[s + 1]));
                int w3[MAXW], m3 = 0; for (int s = nl2 - 1; s >= 0; s--) w3[m3++] = L2[s]; for (int s = 0; s < Lg; s++) w3[m3++] = seg[s]; for (int s = 0; s < nr2; s++) w3[m3++] = R2[s];
                u64 c0 = (nl2 == WIN + 1) ? cho[w3[0]] : ~0ULL, cm = (nr2 == WIN + 1) ? cho[w3[m3 - 1]] : ~0ULL;
                u64 out3[MAXW]; i64 newB = dp_chain(w3, m3, c0, cm, out3);
                i64 d = (newB - curB) - gainA;
                if (d < bestd) { bestd = d; besta = a; memcpy(bestout, out3, sizeof out3); memcpy(bestw, w3, sizeof w3); bestm = m3; }
            }
            tried++;
            if (besta < 0) continue;
            if (bestd > 0 || (bestd == 0 && (peq <= 0 || (double)(xr() % 1000000) / 1e6 >= peq))) continue;
            int p = pv[u0], n = nx[u1];
            if (p >= 0) nx[p] = n; else head = n;
            if (n >= 0) pv[n] = p; else tailu = p;
            for (int s = 0; s < mr; s++) cho[wr[s]] = outR[s];
            int b = nx[besta];
            nx[besta] = u0; pv[u0] = besta; nx[u1] = b; if (b >= 0) pv[b] = u1; else tailu = u1;
            for (int s = 0; s < bestm; s++) cho[bestw[s]] = bestout[s];
            for (int s = 0; s < mr; s++) ix_unit(wr[s]);
            for (int s = 0; s < bestm; s++) ix_unit(bestw[s]);
            cost += bestd; acc++; acc_pass++; if (bestd == 0) eqacc++;
            if (wall() - lastrep > 60) {
                fprintf(stderr, "  pass %d: tried %ld, accepted %ld (equal %ld), cost %lld, length %llu (%.0fs)\n", pass, tried, acc, eqacc, cost, (unsigned long long)(base + cost), wall() - t0g);
                lastrep = wall();
            }
            if (last_write - cost >= 1000) { snprintf(note, sizeof note, "uopt15 from %s, length %llu", argv[3], (unsigned long long)(base + cost)); write_plan(argv[4], note); last_write = cost; }
            if (inn > 400000000u) ix_build();
        }
        pass++;
        i64 chk = total_cost();
        if (chk != cost) DIE("cost bookkeeping %lld != %lld", cost, chk);
        fprintf(stderr, "pass %d done: accepted %ld in this pass, cost %lld, length %llu (%.0fs)\n", pass, acc_pass, cost, (unsigned long long)(base + cost), wall() - t0g);
        ix_build();
        if (acc_pass == 0 && peq <= 0) break;
    }
    snprintf(note, sizeof note, "uopt15 from %s (seg %d, win %d, qmin %d, seed %llu), length %llu", argv[3], SEG, WIN, QMIN, (unsigned long long)seed, (unsigned long long)(base + cost));
    write_plan(argv[4], note);
    fprintf(stderr, "start cost %lld, end cost %lld; LENGTH %llu (%.0fs)\n", start_cost, cost, (unsigned long long)(base + cost), wall() - t0g);
    return 0;
}
