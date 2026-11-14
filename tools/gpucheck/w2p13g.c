/* w2p13g.c - tools/pipeline/w2p13.c (built as w2p13o) with its bitmap passes, the index and the full lookups
   on the card (kernels w2pg.cu -> w2pg.ptx next to the program).  Same usage, same plan, same log lines.
   Changes, all in main and full_lookup:
   - the duplicated windows (trail windows seen twice, base windows seen twice, intersected) are computed on the card;
   - the index entries are made on the card in the order of w2p13.c's serial loop (trail, offset) and sorted with the
     same qsort call, so the sorted index is the same array;
   - full_lookup scans the trails on the card; when a key occurs in several trails the matches are taken in the order
     (trail, offset) (w2p13.c takes them in the order its OpenMP threads find them, which is not fixed).
   The rest (base and word loading, pieces, the walk) is w2p13.c's code unchanged.
   build: gcc -O2 -fopenmp -o w2p13g w2p13g.c; PTX: nvcc -arch=sm_120 -O3 -ptx -o w2pg.ptx w2pg.cu

   Original header of w2p13.c: */
/* w2p13.c - word2plan for n = 13: express a word made of the closed trails of BASE as a trailsearch plan of O events
   (one closed trail written once from one of its cuts), without the n!-entry table of word2plan.c.

   usage: w2p13 BASE.txt WORD.txt OUT.plan

   BASE is parsed as trailsearch.c parses it (pieces split at window gaps >= 4; every piece must be closed: trail t =
   piece t, cyclic word of R = len - h letters from the piece's first letter).  The cuts of a trail are trailsearch's
   options: a cut at window p_i+1 whose predecessor p_i lies g = 2 or 3 letters before (O t start g 0), and, when the
   window p_i is duplicated (in the trails and in BASE), the cut at p_i+2 that drops it (O t start g2 g1).  The event
   of a cut writes R + n - g letters of the trail from `start`.

   Method: an index of about one window in 64 of the trails (key = the 13 letters, 4 bits each).  The word is read event
   by event: from the letter after the previous event, the first indexed window gives (trail, offset) candidates; the
   one that matches the word longest is followed; the event starts at the earliest offset at or after the end of the
   previous event minus h whose cut fits inside the match.  Anything else (a gap, a stretch that is no cut) is
   reported and the program exits 3.  The plan is meant to be checked by
       trailsearch BASE.txt OUT.txt --plan-in PLAN --time 0      (OUT must equal WORD letter for letter)
   Memory: BASE and WORD at 4 bits a letter, three bitmaps of n! bits, the index (16 bytes a sampled window). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include "gp_cuda.h"
#ifdef _OPENMP
#include <omp.h>
#endif

typedef long long i64;
typedef unsigned long long u64;
#define DIE(...) do { fprintf(stderr, "w2p13: " __VA_ARGS__); fprintf(stderr, "\n"); exit(2); } while (0)
static const int n = 13, h = 10;
static u64 fact[17];

typedef struct { unsigned char *a; i64 len; } Packed;
static inline int G(const Packed *p, i64 i) { return (p->a[i >> 1] >> ((i & 1) << 2)) & 15; }

static Packed load(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) DIE("cannot open %s", path);
    _fseeki64(f, 0, SEEK_END); i64 sz = _ftelli64(f); _fseeki64(f, 0, SEEK_SET);
    Packed p; p.a = calloc((size_t)(sz / 2 + 16), 1); p.len = 0;
    if (!p.a) DIE("out of memory");
    static unsigned char buf[1 << 24];
    size_t r;
    while ((r = fread(buf, 1, sizeof buf, f)) > 0)
        for (size_t i = 0; i < r; i++) {
            int c = buf[i];
            if (c == '\r' || c == '\n') continue;
            int v = c >= '0' && c <= '9' ? c - '0' : c >= 'A' && c <= 'F' ? c - 'A' + 10 : -1;
            if (v < 0 || v >= n) DIE("bad symbol in %s", path);
            p.a[p.len >> 1] |= (unsigned char)(v << ((p.len & 1) << 2));
            p.len++;
        }
    fclose(f);
    return p;
}

/* base */
static Packed B;
static i64 NP, *PS, *PR; /* piece start, trail length R (open piece: its length) */
static char *OPEN;        /* open piece of BASE: an open path, written only whole (P k) */
static inline int T(i64 t, i64 o) {
    i64 R = PR[t];
    if (OPEN[t]) return o < 0 || o >= R ? 15 : G(&B, PS[t] + o);
    o %= R; if (o < 0) o += R; return G(&B, PS[t] + o);
}
static inline i64 NWIN(i64 t) { return OPEN[t] ? PR[t] - n + 1 : PR[t]; }
static inline int perm_t(i64 t, i64 o, u64 *key, u64 *rank) {
    unsigned used = 0; u64 k = 0, r = 0;
    for (int j = 0; j < n; j++) {
        int c = T(t, o + j);
        if (c >= n || used >> c & 1) return 0;
        r += (u64)(c - __builtin_popcount(used & ((1u << c) - 1))) * fact[n - 1 - j];
        used |= 1u << c; k = k << 4 | (u64)c;
    }
    if (key) *key = k;
    if (rank) *rank = r;
    return 1;
}
static inline int perm_w(const Packed *w, i64 q, u64 *key, u64 *rank) {
    unsigned used = 0; u64 k = 0, r = 0;
    for (int j = 0; j < n; j++) {
        int c = G(w, q + j);
        if (used >> c & 1) return 0;
        r += (u64)(c - __builtin_popcount(used & ((1u << c) - 1))) * fact[n - 1 - j];
        used |= 1u << c; k = k << 4 | (u64)c;
    }
    if (key) *key = k;
    if (rank) *rank = r;
    return 1;
}
static inline int sampled(u64 key) { return ((key * 0x9E3779B97F4A7C15ULL) >> 58) == 0; }

typedef struct { u64 key; uint32_t t, o; } Ent;
static int cmpent(const void *x, const void *y) {
    u64 a = ((const Ent *)x)->key, b = ((const Ent *)y)->key;
    return a < b ? -1 : a > b;
}
static u64 *dup; /* duplicated in the trails and in BASE */
static inline int isdup(u64 r) { return dup[r >> 6] >> (r & 63) & 1; }

/* previous permutation window of trail t before offset o (cyclic), as a distance 1..4 (5: none within 4) */
static int prevgap(i64 t, i64 o) {
    for (int d = 1; d <= 4; d++) if (perm_t(t, o - d, 0, 0)) return d;
    return 5;
}

/* every (trail, offset) of the window with this key, by a scan of all trails on the card (for stretches too short
   for the index); matches in the order (trail, offset) */
static DP gB, gPS, gPR, gOPEN, gWP, gct, gco, gcnt; static u64 gWtot; static void *kflook;
typedef struct { uint32_t t, o; } TO;
static int cmpto(const void *x, const void *y) {
    const TO *a = x, *b = y; return a->t != b->t ? (a->t < b->t ? -1 : 1) : (a->o < b->o ? -1 : a->o > b->o);
}
#define FLCAP 4096
static i64 full_lookup(u64 key, uint32_t *ct, uint32_t *co, i64 max) {
    static uint32_t ht[FLCAP], ho[FLCAP]; static TO pr[FLCAP];
    CK(cMemsetD8(gcnt, 0, 4));
    int S = 64, bt = 256; u64 NPu = (u64)NP; u32 cap = FLCAP;
    unsigned blocks = (unsigned)((gWtot + (u64)bt * S - 1) / ((u64)bt * S));
    void *a[] = { &gB, &gPS, &gPR, &gOPEN, &gWP, &NPu, &gWtot, &S, &key, &gct, &gco, &gcnt, &cap };
    gp_launch(kflook, blocks, bt, 0, a);
    u32 m; CK(cDtoH(&m, gcnt, 4));
    if (m > FLCAP) DIE("full lookup: %u matches of one window (more than %d)", m, FLCAP);
    if (m) { CK(cDtoH(ht, gct, (size_t)m * 4)); CK(cDtoH(ho, gco, (size_t)m * 4)); }
    for (u32 i = 0; i < m; i++) { pr[i].t = ht[i]; pr[i].o = ho[i]; }
    qsort(pr, m, sizeof(TO), cmpto);
    i64 k = (i64)m < max ? (i64)m : max;
    for (i64 i = 0; i < k; i++) { ct[i] = pr[i].t; co[i] = pr[i].o; }
    return k;
}

static double t00;
static double wall(void) { return (double)clock() / CLOCKS_PER_SEC - t00; }

int main(int argc, char **argv) {
    if (argc != 4) DIE("usage: w2p13 BASE.txt WORD.txt OUT.plan");
    fact[0] = 1; for (int i = 1; i < 17; i++) fact[i] = fact[i - 1] * i;
    u64 NF = fact[n];
    B = load(argv[1]);
    printf("base %lld letters (%.0fs)\n", B.len, wall()); fflush(stdout);
    /* pieces as trailsearch.c */
    i64 cap = 1 << 16; PS = malloc(cap * 8); PR = malloc(cap * 8); NP = 0;
    {
        int cnt[16] = {0}, distinct = 0; i64 prev = -1, pstart = -1;
        for (i64 i = 0; i < B.len; i++) {
            if (cnt[G(&B, i)]++ == 0) distinct++;
            if (i >= n && --cnt[G(&B, i - n)] == 0) distinct--;
            if (i < n - 1 || distinct != n) continue;
            i64 p = i - n + 1;
            if (prev < 0) pstart = p;
            else if (p - prev >= 4) {
                if (NP == cap) { cap *= 2; PS = realloc(PS, cap * 8); PR = realloc(PR, cap * 8); }
                PS[NP] = pstart; PR[NP] = prev + n - pstart; NP++; pstart = p;
            }
            prev = p;
        }
        if (NP == cap) { cap *= 2; PS = realloc(PS, cap * 8); PR = realloc(PR, cap * 8); }
        PS[NP] = pstart; PR[NP] = prev + n - pstart; NP++;
    }
    i64 sumR = 0, nopen = 0;
    OPEN = calloc((size_t)NP, 1);
    for (i64 k = 0; k < NP; k++) { /* closed: the last h letters repeat the first h; otherwise an open path */
        i64 R = PR[k] - h;
        int cl = 1;
        for (int j = 0; j < h && cl; j++) cl = G(&B, PS[k] + j) == G(&B, PS[k] + R + j);
        if (cl) { PR[k] = R; sumR += R; } else { OPEN[k] = 1; nopen++; }
    }
    printf("base: %lld pieces, %lld open paths, sum R of the closed %lld (%.0fs)\n", NP, nopen, sumR, wall()); fflush(stdout);
    /* duplicated windows: in the trails (cyclic) and in BASE (linear), intersected, as trailsearch.c */
    u64 words = (NF >> 6) + 1;
    /* on the card: duplicated windows and the index (w2p13.c: two parallel bitmap passes, a serial index loop) */
    gp_init_ptx(argv[0], "w2pg.ptx");
    void *ktwin = gp_fn("twin"), *kbwin = gp_fn("bwin"), *kand = gp_fn("andbits");
    kflook = gp_fn("flook");
    u64 NPu = (u64)NP, *WPh = malloc((size_t)(NP + 1) * 8);
    WPh[0] = 0; for (i64 t = 0; t < NP; t++) WPh[t + 1] = WPh[t] + (u64)NWIN(t);
    gWtot = WPh[NP];
    gB = gp_alloc((size_t)(B.len / 2 + 16), 0); CK(cHtoD(gB, B.a, (size_t)(B.len / 2 + 16)));
    gPS = gp_alloc((size_t)NP * 8 + 8, 0); CK(cHtoD(gPS, PS, (size_t)NP * 8));
    gPR = gp_alloc((size_t)NP * 8 + 8, 0); CK(cHtoD(gPR, PR, (size_t)NP * 8));
    gOPEN = gp_alloc((size_t)NP + 8, 0); CK(cHtoD(gOPEN, OPEN, (size_t)NP));
    gWP = gp_alloc((size_t)(NP + 1) * 8, 0); CK(cHtoD(gWP, WPh, (size_t)(NP + 1) * 8));
    gct = gp_alloc(FLCAP * 4, 0); gco = gp_alloc(FLCAP * 4, 0); gcnt = gp_alloc(8, 1);
    int S = 32, bt = 256; u64 per = (u64)bt * S;
    unsigned nblk = (unsigned)((gWtot + per - 1) / per);
    DP gseen = gp_alloc(words * 8, 1), gdup = gp_alloc(words * 8, 1), gbc = gp_alloc((size_t)nblk * 4 + 8, 1), z = 0;
    int mode = 0; u64 elo = 0, ehi = 0;
    {
        void *a[] = { &gB, &gPS, &gPR, &gOPEN, &gWP, &NPu, &gWtot, &S, &gseen, &gdup, &gbc, &mode, &z, &z, &elo, &ehi };
        gp_launch(ktwin, nblk, bt, 0, a); CK(cCtxSync());
    }
    CK(cMemsetD8(gseen, 0, words * 8));
    DP gwd = gp_alloc(words * 8, 1);
    {
        u64 Blen = (u64)B.len; unsigned nb2 = (unsigned)((Blen + per - 1) / per);
        void *a[] = { &gB, &Blen, &S, &gseen, &gwd };
        gp_launch(kbwin, nb2, bt, 0, a); CK(cCtxSync());
    }
    { u64 nw32 = words * 2; void *a[] = { &gdup, &gwd, &nw32 }; gp_launch(kand, 4096, 256, 0, a); CK(cCtxSync()); }
    u64 nd = gp_popcount(gdup, words * 2);
    dup = malloc(words * 8); if (!dup) DIE("out of memory");
    CK(cDtoH(dup, gdup, words * 8));
    CK(cMemFree(gseen)); CK(cMemFree(gwd)); CK(cMemFree(gdup));
    uint32_t *bc = malloc((size_t)nblk * 4); u64 *bb = malloc((size_t)nblk * 8);
    CK(cDtoH(bc, gbc, (size_t)nblk * 4));
    i64 nidx = 0;
    for (unsigned i = 0; i < nblk; i++) { bb[i] = (u64)nidx; nidx += bc[i]; }
    printf("duplicated windows %llu; index entries %lld (%.0fs)\n", nd, nidx, wall()); fflush(stdout);
    Ent *E = malloc((size_t)nidx * sizeof(Ent) + 16);
    if (!E) DIE("out of memory");
    i64 ne = nidx;
    {
        DP gbb = gp_alloc((size_t)nblk * 8, 0); CK(cHtoD(gbb, bb, (size_t)nblk * 8));
        u64 part = 16u << 20;   /* entries per part: 256 MB on the card */
        DP gE = gp_alloc((size_t)part * 16, 0);
        mode = 1;
        for (elo = 0; elo < (u64)nidx; elo += part) {
            ehi = elo + part < (u64)nidx ? elo + part : (u64)nidx;
            void *a[] = { &gB, &gPS, &gPR, &gOPEN, &gWP, &NPu, &gWtot, &S, &z, &z, &gbc, &mode, &gE, &gbb, &elo, &ehi };
            gp_launch(ktwin, nblk, bt, 0, a);
            CK(cDtoH(E + elo, gE, (size_t)(ehi - elo) * 16));
        }
        CK(cMemFree(gE)); CK(cMemFree(gbb));
    }
    CK(cMemFree(gbc)); free(bc); free(bb); free(WPh);
    qsort(E, (size_t)ne, sizeof(Ent), cmpent);
    printf("index sorted (%.0fs)\n", wall()); fflush(stdout);
    Packed Wd = load(argv[2]);
    i64 L = Wd.len;
    printf("word %lld letters (%.0fs)\n", L, wall()); fflush(stdout);
    FILE *out = fopen(argv[3], "w");
    if (!out) DIE("cannot write %s", argv[3]);
    fprintf(out, "TRAILSEARCH-PLAN %d %lld %12lld\n", n, B.len, NP);
    i64 pe = 0, nev = 0, nskip = 0, bad = 0, nseg = 0, nfull = 0;
    int verbose = getenv("W2P_VERBOSE") != NULL;
    char *used = calloc((size_t)NP, 1);
    i64 *segw = calloc((size_t)NP, 8);
    while (pe < L) {
        i64 lo = pe - h < 0 ? 0 : pe - h;
        /* first indexed window at or after pe */
        i64 q = pe; u64 key = 0; i64 elo = 0, ehi = 0;
        for (;; q++) {
            if (q + n > L) DIE("no indexed window after letter %lld", pe);
            if (perm_w(&Wd, q, &key, 0) && sampled(key)) {
                i64 a = 0, b = ne;
                while (a < b) { i64 m = (a + b) / 2; if (E[m].key < key) a = m + 1; else b = m; }
                elo = a; while (a < ne && E[a].key == key) a++; ehi = a;
                if (ehi > elo) break;
            }
        }
        i64 bt = -1, bo = 0, bb = 0, be = 0;
        for (i64 z = elo; z < ehi; z++) {
            i64 t = E[z].t, o = E[z].o, R = PR[t], b = q, e = q;
            while (b > lo && G(&Wd, b - 1) == T(t, o - (q - b) - 1)) b--;
            while (e < L && e - b < R + n && G(&Wd, e) == T(t, o + (e - q))) e++;
            if (bt < 0 || e - b > be - bb) { bt = t; bo = o; bb = b; be = e; }
        }
        if (bb > pe) { /* the next event has no indexed window before q: look the first window after pe up in full */
            i64 q2 = pe; u64 k2 = 0;
            while (q2 + n <= L && !perm_w(&Wd, q2, &k2, 0)) q2++;
            static uint32_t ct[64], co[64];
            i64 nc = full_lookup(k2, ct, co, 64);
            nfull++;
            for (i64 z = 0; z < nc; z++) {
                i64 t = ct[z], o = co[z], R = PR[t], b = q2, e = q2;
                while (b > lo && G(&Wd, b - 1) == T(t, o - (q2 - b) - 1)) b--;
                while (e < L && e - b < R + n && G(&Wd, e) == T(t, o + (e - q2))) e++;
                if (z == 0 || e - b > be - bb) { bt = t; bo = o; bb = b; be = e; }
            }
            q = q2;
            if (bb > pe) { printf("ANOMALY: letters %lld..%lld belong to no event\n", pe, bb); bad++; }
        }
        i64 t = bt, R = PR[t], s, found = 0;
        if (OPEN[t]) { /* an open path of BASE: only the whole piece, letter for letter */
            i64 s0 = q - bo;
            if (bb != s0 || be - s0 != R) { printf("ANOMALY: open path %lld only partly written at letter %lld\n", t, bb); bad++; }
            fprintf(out, "P %lld\n", t);
            if (used[t]) { printf("ANOMALY: trail %lld written twice (second at letter %lld)\n", t, s0); bad++; }
            used[t] = 1; nev++; pe = s0 + R; found = 1;
        }
        for (s = bb; s <= q && !found; s++) {
            i64 o = ((bo - (q - s)) % R + R) % R;
            u64 rr;
            if (!perm_t(t, o, 0, 0)) continue;
            int g = prevgap(t, o);
            int g1 = 0, gg = 0;
            if (g >= 2 && g <= 3 && s + R + n - g <= be) gg = g;
            else if (g <= 4) { /* skip: the window g before o is duplicated, its own predecessor g1 before it */
                int d1 = prevgap(t, o - g);
                if (d1 <= 4 && perm_t(t, o - g, 0, &rr) && isdup(rr) && g + d1 >= 2 && g + d1 <= 4 + 3 &&
                    s + R + n - (g + d1) <= be) { gg = g + d1; g1 = d1; }
            }
            if (!gg) continue;
            fprintf(out, "O %lld %lld %d %d\n", t, o, gg, g1);
            if (used[t]) { printf("ANOMALY: trail %lld written twice (second at letter %lld)\n", t, s); bad++; }
            used[t] = 1; nev++; if (g1) nskip++;
            pe = s + R + n - gg; found = 1;
        }
        if (!found) { /* a stretch of the trail that is no whole cut: a segment */
            i64 o = ((bo - (q - bb)) % R + R) % R;
            fprintf(out, "S %lld %lld %lld\n", t, o, be - bb);
            if (verbose) printf("segment: letter %lld trail %lld (R %lld) offset %lld, %lld letters\n", bb, t, R, o, be - bb);
            segw[t] += be - bb; nseg++; nev++; pe = be;
        }
        if (bad > 50) break;
    }
    fseek(out, 0, SEEK_SET);
    fprintf(out, "TRAILSEARCH-PLAN %d %lld %12lld\n", n, B.len, nev);
    fclose(out);
    i64 unused = 0, segtr = 0;
    for (i64 t = 0; t < NP; t++) { unused += !used[t] && !segw[t]; segtr += segw[t] > 0; }
    printf("events %lld (skip cuts %lld, segments %lld of %lld trails, full lookups %lld), trails not written %lld, "
           "anomalies %lld (%.0fs)\n", nev, nskip, nseg, segtr, nfull, unused, bad, wall());
    return bad || unused ? 3 : 0;
}
