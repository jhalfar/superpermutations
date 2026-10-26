/* gcore.h - the group check engine of gchk.c and gen15c.c (included; everything static).

   Groups.  Fix a satellite letter S and the smallest other letter m.  A permutation p is written uniquely as a
   rotation of  S q, where q is the cyclic sequence of the other n-1 letters read after S.  Its group G(p) is the
   cyclic order of q (q rotated to start with m; G = Lehmer rank of the remaining n-2 letters, 0 <= G < (n-2)!), its
   class t = position of m in q (0..n-2; it fixes the cyclic class of p inside the group) and its rotation j = the
   position of S in p (0..n-1).  (G, t, j) <-> p is a bijection, so the groups partition the n! permutations into
   (n-2)! groups of n(n-1) members (member bit t*n + j).  A group is a 2-loop of Pantone's construction with
   satellite S.

   Claim checked: every group has all its n(n-1) members among the windows of the word.  This holds iff every
   permutation occurs (the groups partition the permutations; a member is a permutation and conversely), so the
   check is exact whatever the word is.  Memory: one bit per group, (n-2)! bits (10.9 GB at n = 16, 0.78 GB at
   n = 15), plus small tables.  The construction only decides how much bookkeeping the partial groups need.

   Work.  The letters (values 0..n-1) arrive as blocks of 64 MiB, each starting with the last n-1 letters of the
   block before, so every window lies in exactly one block.  Workers take blocks in any order.  A worker scans its
   block window by window: a window is tested for being a permutation and (G, t, j) is computed; then the run of
   the following windows that are its left rotations (letter i+n = letter i) is taken in one step (same G and t,
   j - 1, j - 2, ...).  After a run ending at window e, window e+1 is never a permutation; if letters e+n, e+n+1 are
   e+1, e (a weight-2 step) window e+2 is one, and if S is one of those two letters it stays in the group (class
   t-1 or t+1, S at position n-1 or n-2), otherwise it is classified from scratch.  The members seen are OR-ed into
   an open-addressing table of the worker, one entry per open group.  A group whose members are all seen sets its
   bit at once and leaves the table.  A group not touched for W runs is flushed as partial at the next sweep (when
   the table is half full; if it stays crowded, W is halved).  At the end of the block every open group is flushed
   as partial into the block's list.
   A coordinator merges the lists in block order: a group seen in two consecutive blocks is OR-ed (its bit is set
   when complete); a partial group not touched in the next block goes to the residue list.  At the end the residue
   list is sorted and OR-ed per group.  Missing permutations are counted exactly: (n(n-1) minus the merged members)
   for every group without bit. */
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <immintrin.h>
typedef uint64_t u64; typedef uint32_t u32; typedef uint8_t u8;

static int GN, GNT = 2, GSAT = -1, GMINS, GCS = 1 << 17, GNOMARK;
static u64 gfact[21], GNG;           /* GNG = (n-2)! groups */
static int GMW;                      /* members per group n(n-1) <= 240 */
static u64 GFM[4];                   /* full member mask */
static u64 *GB2;                     /* GNG bits */
static u32 GFULLL;                   /* mask of all n letters */
static u64 GW0 = 1ULL << 22;         /* runs: a group not touched for W runs is flushed at the next sweep */

typedef struct { u64 g; u64 m[4]; } Res;
#define EMPTY (~0ULL)
typedef struct { u64 g, last; u64 m[4]; } Ent;
typedef struct {
    Ent *t, *t2; u64 cap, cnt, W, maxlive, sweeps, wcut;
    Res *res; size_t nres, capres;   /* partial groups of the current block */
    u64 pw, runs, fulls, partial, w2;
} Local;

static inline int g_isfull(const u64 *m) { return m[0] == GFM[0] && m[1] == GFM[1] && m[2] == GFM[2] && m[3] == GFM[3]; }
static inline void g_setbit(u64 g) { __atomic_fetch_or(&GB2[g >> 6], 1ULL << (g & 63), __ATOMIC_RELAXED); }
static void res_push(Res **a, size_t *n, size_t *cap, u64 g, const u64 *m) {
    if (*n == *cap) { *cap = *cap ? 2 * *cap : 1 << 12; *a = realloc(*a, *cap * sizeof(Res)); if (!*a) { fprintf(stderr, "gcore: out of memory (partial groups)\n"); exit(2); } }
    Res *r = &(*a)[(*n)++]; r->g = g; memcpy(r->m, m, 32);
}
static void g_flush(Local *L, u64 g, const u64 *m) {
    if (g_isfull(m)) { g_setbit(g); L->fulls++; return; }
    L->partial++; res_push(&L->res, &L->nres, &L->capres, g, m);
}
static inline u64 g_hsh(u64 g) { return (g * 0x9E3779B97F4A7C15ULL) >> 20; }
static void local_init(Local *L) {
    memset(L, 0, sizeof *L);
    L->cap = (u64)GCS; L->W = GW0;
    L->t = malloc(L->cap * sizeof(Ent)); L->t2 = malloc(L->cap * sizeof(Ent));
    if (!L->t || !L->t2) { fprintf(stderr, "gcore: out of memory (table)\n"); exit(2); }
    for (u64 i = 0; i < L->cap; i++) L->t[i].g = EMPTY;
}
/* flush the groups not touched in the last W runs (all if W == 0); keep the others */
static void g_sweep(Local *L, u64 W) {
    Ent *o = L->t, *nt = L->t2; u64 mask = L->cap - 1, kept = 0;
    for (u64 i = 0; i < L->cap; i++) nt[i].g = EMPTY;
    for (u64 i = 0; i < L->cap; i++) {
        if (o[i].g == EMPTY) continue;
        if (W == 0 || L->runs - o[i].last > W) { g_flush(L, o[i].g, o[i].m); continue; }
        u64 h = g_hsh(o[i].g) & mask; while (nt[h].g != EMPTY) h = (h + 1) & mask;
        nt[h] = o[i]; kept++;
    }
    L->t = nt; L->t2 = o; L->cnt = kept; L->sweeps++;
}
static inline void g_mark(Local *L, u64 g, int t, int j, u64 cnt) {
    /* windows: class t, satellite at j, j-1, ..., j-cnt+1 (mod n) */
    const int N = GN; u32 rm;
    if (cnt >= (u64)N) rm = (1u << N) - 1;
    else {
        int c = (int)cnt, lo = j - c + 1;
        if (lo >= 0) rm = ((1u << c) - 1) << lo;
        else rm = ((1u << (j + 1)) - 1) | (((1u << (-lo)) - 1) << (N + lo));
    }
    u64 mask = L->cap - 1, h = g_hsh(g) & mask;
    Ent *e;
    for (;;) {
        e = &L->t[h];
        if (e->g == g) break;
        if (e->g == EMPTY) {
            if (2 * (L->cnt + 1) > L->cap) {           /* half full: flush the old groups, then insert */
                g_sweep(L, L->W);
                if (4 * L->cnt > L->cap) { L->W /= 2; L->wcut++; }
                h = g_hsh(g) & mask; continue;
            }
            e->g = g; memset(e->m, 0, 32); L->cnt++; if (L->cnt > L->maxlive) L->maxlive = L->cnt;
            break;
        }
        h = (h + 1) & mask;
    }
    e->last = L->runs;
    int off = t * N, w = off >> 6, sh = off & 63;
    e->m[w] |= (u64)rm << sh;
    if (sh + N > 64) e->m[w + 1] |= (u64)rm >> (64 - sh);
    if (g_isfull(e->m)) {                              /* complete: set the bit, free the slot (backward shift) */
        g_setbit(g); L->fulls++;
        u64 i = h;
        for (;;) {
            u64 jn = (i + 1) & mask;
            for (;;) {
                if (L->t[jn].g == EMPTY) { L->t[i].g = EMPTY; L->cnt--; return; }
                u64 k = g_hsh(L->t[jn].g) & mask;
                if ((i <= jn) ? (k <= i || k > jn) : (k <= i && k > jn)) break;   /* home not in (i, jn] */
                jn = (jn + 1) & mask;
            }
            L->t[i] = L->t[jn]; i = jn;
        }
    }
}
/* group, class, rotation of the permutation x[0..n-1] */
static inline u64 g_classify(const u8 *x, int *tt, int *jj) {
    const int N = GN, S = GSAT, M = GMINS;
    int js = 0; while (x[js] != S) js++;
    u8 q[32];
    for (int k = 0; k < N - 1; k++) { int p = js + 1 + k; if (p >= N) p -= N; q[k] = x[p]; q[k + N - 1] = x[p]; }
    int t = 0; while (q[t] != M) t++;
    u32 avail = GFULLL & ~(1u << S) & ~(1u << M);
    u64 r = 0;
    for (int k = 1; k <= N - 3; k++) { int s = q[t + k]; r += (u64)__builtin_popcount(avail & ((1u << s) - 1)) * gfact[N - 2 - k]; avail &= ~(1u << s); }
    *tt = t; *jj = js; return r;
}
static void g_unrank(u64 g, int t, int j, u8 *p) {     /* inverse of g_classify */
    const int N = GN; u8 qq[32]; qq[0] = (u8)GMINS; u32 avail = GFULLL & ~(1u << GSAT) & ~(1u << GMINS);
    for (int k = 1; k <= N - 2; k++) {
        u64 f = gfact[N - 2 - k], c = g / f; g %= f;
        for (int s = 0; s < N; s++) if (avail >> s & 1) { if (c == 0) { qq[k] = (u8)s; avail &= ~(1u << s); break; } c--; }
    }
    u8 sq[32]; sq[0] = (u8)GSAT;
    for (int k = 0; k < N - 1; k++) sq[1 + k] = qq[((k - t) % (N - 1) + (N - 1)) % (N - 1)];
    for (int k = 0; k < N; k++) p[(j + k) % N] = sq[k];
}
/* scan the windows starting at 0 .. len-n of d (d[len .. len+127] is padding that equals no letter) */
static void g_scan(Local *L, const u8 *d, size_t len) {
    const int N = GN, S = GSAT; const u32 FULL = GFULLL;
    if (len < (size_t)N) return;
    size_t last = len - N + 1, i = 0;
    int have = 0, t = 0, j = 0; u64 g = 0;
    while (i < last) {
        const u8 *x = d + i;
        if (!have) {
            u32 seen = 0; for (int k = 0; k < N; k++) seen |= 1u << x[k];
            if (seen != FULL) { i++; continue; }
            g = g_classify(x, &t, &j);
        }
        size_t k = 0;                                  /* run: windows i+1, i+2, .. are left rotations */
        for (;;) {
            __m256i a = _mm256_loadu_si256((const __m256i *)(x + k)), b = _mm256_loadu_si256((const __m256i *)(x + k + N));
            u32 ne = ~(u32)_mm256_movemask_epi8(_mm256_cmpeq_epi8(a, b));
            if (ne) { k += __builtin_ctz(ne); break; }
            k += 32;
        }
        /* windows i .. i+k are permutations of class t; letter i+k+n differs from letter i+k and has index <= len
           (the padding stops the run), so i+k <= last-1 */
        u64 cnt = k + 1;
        if (!GNOMARK) g_mark(L, g, t, j, cnt); else L->fulls += g + t + j;
        L->pw += cnt; L->runs++;
        size_t e = i + k;
        u8 a1 = d[e], a2 = d[e + 1];
        if (e + 2 < last && d[e + N] == a2 && d[e + N + 1] == a1) {
            if (a1 == S) { t = t == 0 ? N - 2 : t - 1; j = N - 1; }
            else if (a2 == S) { t = t == N - 2 ? 0 : t + 1; j = N - 2; }
            else g = g_classify(d + e + 2, &t, &j);
            have = 1; L->w2++;
        } else have = 0;
        i = e + 2;
    }
}

/* ------------------------------------------------------------------ blocks, workers, coordinator */
#define GBLOCK (64u << 20)
#define GNBUF 16
typedef struct { u8 *data; size_t len; int state; u64 seq; } GBuf;   /* state 0 free, 1 full, 2 taken, 3 filling */
static GBuf gbufs[GNBUF];
static int g_done_feeding; static u64 g_nseq;
static pthread_mutex_t gmu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t g_cv_full = PTHREAD_COND_INITIALIZER, g_cv_free = PTHREAD_COND_INITIALIZER, g_cv_list = PTHREAD_COND_INITIALIZER;
static Local *glocs;
static pthread_t gth[64], gcoord;
/* finished blocks' partial lists, by sequence number (ring) */
#define GPEND 64
typedef struct { Res *r; size_t n; u64 seq; int ready; } GList;
static GList gpend[GPEND];
static u64 g_merged;                 /* blocks merged so far */
static Res *gM; static size_t gnM, gcapM;          /* open partial groups from the last block, sorted */
static Res *gR; static size_t gnR, gcapR;          /* residues */
static u64 g_stitched, g_maxM;
/* the filling side */
static int g_fill = -1; static size_t g_flen; static u8 g_carry[16]; static size_t g_ncarry;
static u64 g_total;

static void *g_worker(void *arg) {
    Local *L = (Local *)arg;
    for (;;) {
        pthread_mutex_lock(&gmu);
        int b;
        for (;;) { b = -1; for (int i = 0; i < GNBUF; i++) if (gbufs[i].state == 1 && (b < 0 || gbufs[i].seq < gbufs[b].seq)) b = i; if (b >= 0 || g_done_feeding) break; pthread_cond_wait(&g_cv_full, &gmu); }
        if (b < 0) { pthread_mutex_unlock(&gmu); break; }
        gbufs[b].state = 2; u64 seq = gbufs[b].seq;
        /* do not run more than GPEND blocks ahead of the coordinator */
        while (seq >= g_merged + GPEND) pthread_cond_wait(&g_cv_list, &gmu);
        pthread_mutex_unlock(&gmu);
        g_scan(L, gbufs[b].data, gbufs[b].len);
        g_sweep(L, 0);                                 /* every open group into the block's list */
        pthread_mutex_lock(&gmu);
        GList *pl = &gpend[seq % GPEND]; pl->r = L->res; pl->n = L->nres; pl->seq = seq; pl->ready = 1;
        L->res = NULL; L->nres = L->capres = 0;
        gbufs[b].state = 0;
        pthread_cond_broadcast(&g_cv_free); pthread_cond_broadcast(&g_cv_list);
        pthread_mutex_unlock(&gmu);
    }
    return NULL;
}
static int g_cmpres(const void *a, const void *b) { u64 x = ((const Res *)a)->g, y = ((const Res *)b)->g; return x < y ? -1 : x > y; }
/* merge the list of the next block into the open partial groups */
static void g_merge(Res *P, size_t np) {
    qsort(P, np, sizeof(Res), g_cmpres);
    size_t w = 0;                                       /* combine repeats inside P */
    for (size_t a = 0; a < np;) { size_t b = a + 1; while (b < np && P[b].g == P[a].g) { for (int q = 0; q < 4; q++) P[a].m[q] |= P[b].m[q]; b++; } P[w++] = P[a]; a = b; }
    np = w;
    Res *O = malloc((gnM + np + 1) * sizeof(Res)); size_t no = 0, i = 0, j = 0;
    while (i < gnM || j < np) {
        if (j >= np || (i < gnM && gM[i].g < P[j].g)) { res_push(&gR, &gnR, &gcapR, gM[i].g, gM[i].m); i++; }   /* not continued */
        else if (i >= gnM || P[j].g < gM[i].g) { if (g_isfull(P[j].m)) { g_setbit(P[j].g); g_stitched++; } else O[no++] = P[j]; j++; }
        else {
            Res r = P[j]; for (int q = 0; q < 4; q++) r.m[q] |= gM[i].m[q];
            if (g_isfull(r.m)) { g_setbit(r.g); g_stitched++; } else O[no++] = r;
            i++; j++;
        }
    }
    free(gM); gM = O; gnM = no; if (no > g_maxM) g_maxM = no;
}
static void *g_coordinator(void *arg) {
    (void)arg;
    for (;;) {
        pthread_mutex_lock(&gmu);
        GList *pl = &gpend[g_merged % GPEND];
        while (!(pl->ready && pl->seq == g_merged) && !(g_done_feeding && g_merged >= g_nseq)) pthread_cond_wait(&g_cv_list, &gmu);
        if (!(pl->ready && pl->seq == g_merged)) { pthread_mutex_unlock(&gmu); break; }
        Res *r = pl->r; size_t n = pl->n; pl->ready = 0;
        pthread_mutex_unlock(&gmu);
        g_merge(r, n); free(r);
        pthread_mutex_lock(&gmu); g_merged++; pthread_cond_broadcast(&g_cv_list); pthread_mutex_unlock(&gmu);
    }
    return NULL;
}

static void gc_init(int n, int sat, int threads, int table) {
    GN = n; GNT = threads; GCS = table; GSAT = sat < 0 ? n - 2 : sat; GMINS = GSAT == 0 ? 1 : 0;
    if (n < 4 || n > 16 || GSAT >= n || threads < 1 || threads > 64 || table < 16 || (table & (table - 1))) { fprintf(stderr, "gcore: bad arguments\n"); exit(2); }
    gfact[0] = 1; for (int i = 1; i < 21; i++) gfact[i] = gfact[i - 1] * i;
    GNG = gfact[n - 2]; GMW = n * (n - 1); GFULLL = (1u << n) - 1;
    memset(GFM, 0, sizeof GFM); for (int b = 0; b < GMW; b++) GFM[b >> 6] |= 1ULL << (b & 63);
    GB2 = calloc(GNG / 64 + 1, 8);
    if (!GB2) { fprintf(stderr, "gcore: cannot allocate %llu bytes for the group bits\n", (unsigned long long)(GNG / 8)); exit(2); }
    glocs = calloc(GNT, sizeof(Local));
    for (int i = 0; i < GNT; i++) local_init(&glocs[i]);
    for (int i = 0; i < GNBUF; i++) { gbufs[i].data = malloc(GBLOCK + 256); if (!gbufs[i].data) { fprintf(stderr, "gcore: out of memory\n"); exit(2); } }
    for (int i = 0; i < GNT; i++) pthread_create(&gth[i], NULL, g_worker, &glocs[i]);
    pthread_create(&gcoord, NULL, g_coordinator, NULL);
}
static void g_publish(void) {
    int b = g_fill; GBuf *B = &gbufs[b];
    B->len = g_flen;
    g_ncarry = g_flen < (size_t)(GN - 1) ? g_flen : (size_t)(GN - 1);
    memcpy(g_carry, B->data + g_flen - g_ncarry, g_ncarry);
    memset(B->data + g_flen, 0xEE, 128);
    pthread_mutex_lock(&gmu); B->state = 1; B->seq = g_nseq++; pthread_cond_broadcast(&g_cv_full); pthread_mutex_unlock(&gmu);
    g_fill = -1;
}
static u8 *g_fillbuf(size_t *room) {                   /* the block being filled (a new one if needed) */
    if (g_fill < 0) {
        pthread_mutex_lock(&gmu);
        for (;;) { g_fill = -1; for (int i = 0; i < GNBUF; i++) if (gbufs[i].state == 0) { g_fill = i; break; } if (g_fill >= 0) break; pthread_cond_wait(&g_cv_free, &gmu); }
        gbufs[g_fill].state = 3;
        pthread_mutex_unlock(&gmu);
        memcpy(gbufs[g_fill].data, g_carry, g_ncarry); g_flen = g_ncarry;
    }
    *room = GBLOCK - g_flen;
    return gbufs[g_fill].data + g_flen;
}
/* append letters (values 0..n-1) to the word; callers that produce letters in place use g_fillbuf / g_filled */
static void g_filled(size_t k) { g_flen += k; g_total += k; if (g_flen == GBLOCK) g_publish(); }
static void gc_submit(const u8 *p, size_t n) {
    while (n) { size_t room; u8 *d = g_fillbuf(&room); size_t c = n < room ? n : room; memcpy(d, p, c); g_filled(c); p += c; n -= c; }
}
typedef struct {
    u64 total, pw, runs, fulls, partial, stitched, maxlive, maxM, sweeps, wcut, wfin, nres, ngr, nmfull, bitsset, missing_groups, missing, npart;
    Res *part; size_t nparts;            /* partial groups without bit, sorted (for listing) */
} GRes;
static void gc_finish(GRes *o) {
    if (g_fill >= 0 && g_flen > g_ncarry) g_publish(); else if (g_fill >= 0) { pthread_mutex_lock(&gmu); gbufs[g_fill].state = 0; pthread_mutex_unlock(&gmu); g_fill = -1; }
    pthread_mutex_lock(&gmu); g_done_feeding = 1; pthread_cond_broadcast(&g_cv_full); pthread_cond_broadcast(&g_cv_list); pthread_mutex_unlock(&gmu);
    for (int i = 0; i < GNT; i++) pthread_join(gth[i], NULL);
    pthread_mutex_lock(&gmu); pthread_cond_broadcast(&g_cv_list); pthread_mutex_unlock(&gmu);
    pthread_join(gcoord, NULL);
    memset(o, 0, sizeof *o); o->total = g_total; o->wfin = ~0ULL;
    for (int i = 0; i < GNT; i++) {
        Local *L = &glocs[i];
        o->pw += L->pw; o->runs += L->runs; o->fulls += L->fulls; o->partial += L->partial; o->sweeps += L->sweeps; o->wcut += L->wcut;
        if (L->maxlive > o->maxlive) o->maxlive = L->maxlive; if (L->W < o->wfin) o->wfin = L->W;
    }
    for (size_t i = 0; i < gnM; i++) res_push(&gR, &gnR, &gcapR, gM[i].g, gM[i].m);
    o->stitched = g_stitched; o->maxM = g_maxM; o->nres = gnR;
    qsort(gR, gnR, sizeof(Res), g_cmpres);
    size_t w = 0;
    for (size_t a = 0; a < gnR;) {
        size_t b = a; u64 m[4] = {0, 0, 0, 0};
        while (b < gnR && gR[b].g == gR[a].g) { for (int q = 0; q < 4; q++) m[q] |= gR[b].m[q]; b++; }
        o->ngr++;
        if (g_isfull(m)) { GB2[gR[a].g >> 6] |= 1ULL << (gR[a].g & 63); o->nmfull++; }
        else { gR[w].g = gR[a].g; memcpy(gR[w].m, m, 32); w++; }
        a = b;
    }
    for (u64 i = 0; i < GNG / 64 + 1; i++) o->bitsset += (u64)__builtin_popcountll(GB2[i]);
    o->missing_groups = GNG - o->bitsset; o->missing = o->missing_groups * (u64)GMW;
    size_t w2 = 0;
    for (size_t a = 0; a < w; a++) if (!(GB2[gR[a].g >> 6] >> (gR[a].g & 63) & 1)) { o->npart++; for (int q = 0; q < 4; q++) o->missing -= (u64)__builtin_popcountll(gR[a].m[q]); gR[w2++] = gR[a]; }
    o->part = gR; o->nparts = w2;
}
static void gc_json(FILE *f, const GRes *o) {
    fprintf(f, "\"satellite\":%d,\"permutation_windows\":%llu,\"rotation_runs\":%llu,\"groups\":%llu,\"groups_complete_in_a_block\":%llu,"
            "\"partial_flushes\":%llu,\"groups_stitched\":%llu,\"residues\":%llu,\"residue_groups\":%llu,\"residue_groups_complete\":%llu,"
            "\"groups_missing\":%llu,\"groups_partial\":%llu,\"distinct_permutations\":%llu,\"missing_permutations\":%llu,"
            "\"workers\":%d,\"table\":%d,\"table_max_live\":%llu,\"open_between_blocks_max\":%llu,\"memory_cuts\":%llu,\"memory_runs\":%llu",
            GSAT, (unsigned long long)o->pw, (unsigned long long)o->runs, (unsigned long long)GNG, (unsigned long long)o->fulls,
            (unsigned long long)o->partial, (unsigned long long)o->stitched, (unsigned long long)o->nres, (unsigned long long)o->ngr, (unsigned long long)o->nmfull,
            (unsigned long long)o->missing_groups, (unsigned long long)o->npart, (unsigned long long)(gfact[GN] - o->missing), (unsigned long long)o->missing,
            GNT, GCS, (unsigned long long)o->maxlive, (unsigned long long)o->maxM, (unsigned long long)o->wcut, (unsigned long long)o->wfin);
}
/* up to K missing permutations on stderr, letters spelled with alp */
static void gc_list(const GRes *o, int K, const char *alp) {
    int listed = 0; size_t pa = 0;
    for (u64 g = 0; g < GNG && listed < K; g++) {
        if (GB2[g >> 6] >> (g & 63) & 1) continue;
        while (pa < o->nparts && o->part[pa].g < g) pa++;
        const u64 *m = (pa < o->nparts && o->part[pa].g == g) ? o->part[pa].m : NULL;
        for (int b = 0; b < GMW && listed < K; b++) {
            if (m && (m[b >> 6] >> (b & 63) & 1)) continue;
            u8 p[16]; g_unrank(g, b / GN, b % GN, p);
            char s[17]; for (int q = 0; q < GN; q++) s[q] = alp[p[q]]; s[GN] = 0;
            fprintf(stderr, "missing %s\n", s); listed++;
        }
    }
}
