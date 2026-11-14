/* gdelcheck.c - delcheck (tools/delcheck.c, used by tools/prepub/prepub.sh) on the card:
   coverage and the single-deletion test, the same predicate and the same JSON fields.

   usage: gdelcheck WORD [threads] [--n N] [--skip P] [--shards K] [--chunk MB] [--nbuf B] [--readers R] [--io direct|buffered]
                         [--xz EXE]
     WORD     letters 0-9A-F (delcheck's alphabet), final CR/LF ignored; WORD.xz is streamed through "xz -dc" (twice).
     threads  accepted for delcheck's command line and printed; the card does the work, R reader threads read.
     --n      the number of symbols (default as delcheck: the largest symbol in the first 65,536 letters + 1).
     --skip P the word without its letter P (0-based; e.g. after a deletion, without writing a copy)
     --shards K  pass 1 in K passes over the word, each with 1/K of the "seen" table on the card (memory n!/8 for
              "seen twice" + n!/8/K): n = 14 with K = 8 and --nbuf 4 took 13.5 GB of a 16 GB job (79-135 s).
   Output: delcheck's fields in delcheck's order (n, length, permutation_occurrences, distinct_permutations,
   required_permutations, missing_permutations, extra_occurrences, permutations_occurring_once, tested_deletions,
   coverage_preserving_deletions_count, coverage_preserving_deletions = the first 4096 positions), then
   pass1_seconds, pass2_seconds, seconds, threads, shards.  Exit code as delcheck: 0 if no permutation is missing,
   3 if one is, 2 on an error (a byte outside 0-9A-F, or a symbol >= N: delcheck would read such a word wrongly).

   Pass 1: every permutation window sets its bit in "seen" (atomicOr); if the bit was set, also in "twice".
   Pass 2: a window occurring once (bit clear in "twice") forbids [s + (w[s-1] == w[s]), s + n - (w[s+n-1] == w[s+n]));
   each card block decides a run of positions from the intervals of the windows that can reach them (delcheck.c's
   argument: one deletion destroys at most one occurrence of a permutation and can recreate a destroyed unique window
   only through an equal neighbour).  The positions no interval covers are counted; the first 4096 are listed.

   build: gcc -O2 -o gdelcheck gdelcheck.c -lpthread; PTX: nvcc -arch=sm_120 -O3 -ptx -o gpuprep.ptx gpuprep.cu */
#include "gp_cuda.h"
#include "gp_reader.h"

static int cmp64(const void *a, const void *b) { u64 x = *(const u64 *)a, y = *(const u64 *)b; return x < y ? -1 : x > y; }
#define KEEP 4096
#define CAP (1u << 20)
#define BADCHECK() do { u64 nb_; CK(cDtoH(&nb_, dbad, 8)); if (nb_) { fprintf(stderr, "gdelcheck: read failed or bad symbol\n"); return 2; } } while (0)

typedef struct { const char *word, *io, *xz; size_t chunk; int nbuf, nrd; } Src;
static u8 lut[256];
static DP dlut;
static void *fmap, *frank, *fdel;

/* strip CR/LF at the end of a chunk; a chunk after a stripped line end must be empty (delcheck: bad symbol) */
static size_t strip_tail(const u8 *d, size_t len, int *pend) {
    if (len && *pend) { fprintf(stderr, "gdelcheck: read failed or bad symbol (a line end inside the word)\n"); exit(2); }
    size_t t = 0; while (t < len && (d[len - 1 - t] == '\n' || d[len - 1 - t] == '\r')) t++;
    if (t) *pend = 1;
    return len - t;
}
/* letters -> symbols on the card; bad bytes are counted in dbad (not reset here).  wait = 1: check now (one wait) */
static void map_chunk(DP draw, DP dsym, const u8 *h, u64 len, DP dbad, int wait) {
    if (!len) return;
    CK(cHtoD(draw, h, len));
    void *a[] = { &draw, &len, &dsym, &dlut, &dbad }; gp_launch(fmap, 2048, 256, 0, a);
    if (!wait) return;
    u64 nb; CK(cDtoH(&nb, dbad, 8));
    if (nb) { fprintf(stderr, "gdelcheck: read failed or bad symbol\n"); exit(2); }
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: gdelcheck WORD [threads] [--n N] [--shards K] [--chunk MB] [--readers R] [--io direct|buffered] [--xz EXE]\n"); return 2; }
    Src src = { argv[1], "direct", NULL, 256ULL << 20, 6, 2 };
    int T = 0, n = 0, K = 1, S = 32, bt = 256, DS = 16, ai = 2;
    u64 skip = ~0ULL;   /* --skip P: the word without its letter P (0-based) */
    if (argc > 2 && argv[2][0] != '-') { T = atoi(argv[2]); ai = 3; }
    for (int i = ai; i < argc; i++) {
        if (!strcmp(argv[i], "--n") && i + 1 < argc) n = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--shards") && i + 1 < argc) K = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--chunk") && i + 1 < argc) src.chunk = (size_t)atoll(argv[++i]) << 20;
        else if (!strcmp(argv[i], "--nbuf") && i + 1 < argc) src.nbuf = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--readers") && i + 1 < argc) src.nrd = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--io") && i + 1 < argc) src.io = argv[++i];
        else if (!strcmp(argv[i], "--xz") && i + 1 < argc) src.xz = argv[++i];
        else if (!strcmp(argv[i], "--skip") && i + 1 < argc) skip = (u64)atoll(argv[++i]);
        else { fprintf(stderr, "gdelcheck: unknown option %s\n", argv[i]); return 2; }
    }
    if (K < 1 || src.chunk < (1 << 20) || src.nbuf < 2) { fprintf(stderr, "gdelcheck: bad arguments\n"); return 2; }
    double t0 = gp_wall();
    gp_init(argv[0]);
    fmap = gp_fn("mapsym"); frank = gp_fn("rankmark"); fdel = gp_fn("delmark");
    memset(lut, 0xFF, sizeof lut);
    for (int c = 0; c < 16; c++) lut[(u8)"0123456789ABCDEF"[c]] = (u8)c;
    dlut = gp_alloc(256, 0);
    DP draw = gp_alloc(src.chunk + 128, 0), dsym = gp_alloc(src.chunk + 128, 0), dst = gp_alloc(64, 1);
    DP dbad = dst + 32, dcnt = dst + 16;

    /* pass 1 (K times with shards) */
    u64 nf = 0, nw = 0, total = 0, nperm = 0, distinct = 0;
    DP dseen = 0, ddup = 0; u64 span = 0, sw = 0;
    for (int k = 0; k < K; k++) {
        Reader R; rd_open(&R, src.word, src.chunk, src.nbuf, src.nrd, src.io, src.xz);
        u8 car[16]; int nc = 0, pend = 0, first = 1; u64 tot = 0; int skdone = 0;
        for (;;) {
            RBuf *b = rd_next(&R); if (!b) { fprintf(stderr, "gdelcheck: read failed\n"); return 2; }
            u8 *d = b->data; size_t m = strip_tail(d, b->len, &pend);
            if (skip != ~0ULL && !skdone && skip >= tot && skip < tot + m) { skdone = 1; size_t q = (size_t)(skip - tot); memmove(d + q, d + q + 1, m - q - 1); m--; }
            if (first && k == 0) {   /* n as delcheck: largest symbol of the first 65,536 letters + 1 */
                if (!n) { int mx = -1; for (size_t i = 0; i < m && i < 65536; i++) { int v = lut[d[i]] == 0xFF ? -1 : lut[d[i]]; if (v > mx) mx = v; } n = mx + 1; }
                if (n < 2 || n > 14) { fprintf(stderr, "bad word\n"); return 2; }
                u8 l2[256]; memcpy(l2, lut, 256); for (int c = 0; c < 256; c++) if (l2[c] != 0xFF && l2[c] >= n) l2[c] = 0xFF;
                memcpy(lut, l2, 256); CK(cHtoD(dlut, lut, 256));
                nf = 1; for (int i = 2; i <= n; i++) nf *= i;
                nw = nf / 32 + 1; span = (nf + K - 1) / K; sw = span / 32 + 1;
                size_t fr, tt; CK(cMemGetInfo(&fr, &tt));
                if ((nw + sw) * 4 + 2 * src.chunk + (256ULL << 20) > fr) { fprintf(stderr, "gdelcheck: tables of %.1f GB do not fit (%.1f GB free); use --shards\n", (nw + sw) * 4 / 1e9, fr / 1e9); return 2; }
                ddup = gp_alloc(nw * 4, 1); dseen = gp_alloc(sw * 4, 0);
            }
            if (first) { first = 0; CK(cMemsetD8(dseen, 0, sw * 4)); CK(cMemsetD8(dst, 0, 16)); }
            memcpy(d - nc, car, nc);
            u64 have = nc + m;
            map_chunk(draw, dsym, d - nc, have, dbad, 0);
            int nc2 = have < (u64)(n - 1) ? (int)have : n - 1;
            memcpy(car, d - nc + have - nc2, nc2);
            int eof = b->eof; rd_release(&R, b);
            tot += m;
            if (have >= (u64)n) {
                u64 nwin = have - n + 1, lo = (u64)k * span, sp = (k + 1) * span <= nf ? span : nf - lo;
                unsigned blocks = (unsigned)((nwin + (u64)bt * S - 1) / ((u64)bt * S));
                void *ra[] = { &dsym, &nwin, &n, &lo, &sp, &dseen, &ddup, &dst, &S, &dbad };
                gp_launch(frank, blocks, bt, bt * S + n + 16, ra);
            }
            nc = nc2;
            if (eof) break;
        }
        if (rd_close(&R)) { fprintf(stderr, "gdelcheck: xz reported an error\n"); return 2; }
        BADCHECK();
        if (tot == 0) { fprintf(stderr, "bad word\n"); return 2; }
        u64 st[2]; CK(cDtoH(st, dst, 16));
        if (k == 0) { total = tot; nperm = st[0]; } else if (tot != total || st[0] != nperm) { fprintf(stderr, "gdelcheck: the word changed between passes\n"); return 2; }
        distinct += gp_popcount(dseen, sw);
    }
    u64 L = total;
    if (L < (u64)n) { fprintf(stderr, "bad word\n"); return 2; }
    u64 twice = gp_popcount(ddup, nw);
    CK(cMemFree(dseen));
    double t1 = gp_wall();

    /* pass 2: deletable positions */
    DP dout = gp_alloc((size_t)CAP * 8, 0);
    u64 *hout = malloc((size_t)CAP * 8), keep[KEEP]; int nkeep = 0; u64 ndel = 0;
    {
        Reader R; rd_open(&R, src.word, src.chunk, src.nbuf, src.nrd, src.io, src.xz);
        u8 car[40]; int nc = 0, pend = 0; u64 consumed = 0, d0 = 0; int skdone = 0;
        const int TB = bt * DS; const unsigned shm = TB + 2 * n + 2 + 2 * (TB + n);
        for (;;) {
            RBuf *b = rd_next(&R); if (!b) { fprintf(stderr, "gdelcheck: read failed\n"); return 2; }
            u8 *d = b->data; size_t m = strip_tail(d, b->len, &pend);
            if (skip != ~0ULL && !skdone && skip >= consumed && skip < consumed + m) { skdone = 1; size_t q = (size_t)(skip - consumed); memmove(d + q, d + q + 1, m - q - 1); m--; }
            memcpy(d - nc, car, nc);
            u64 have = nc + m, wbase = consumed - nc;
            map_chunk(draw, dsym, d - nc, have, dbad, 0);
            int nc2 = have < (u64)(2 * n) ? (int)have : 2 * n;
            memcpy(car, d - nc + have - nc2, nc2);
            int eof = b->eof; rd_release(&R, b);
            consumed += m;
            u64 d1 = eof ? L : (wbase + have >= (u64)n && wbase + have - n > d0 ? wbase + have - n : d0);
            if (eof && consumed != L) { fprintf(stderr, "gdelcheck: the word changed between passes\n"); return 2; }
            if (d1 > d0) {
                /* count all, list the first ones; if the list overflows while positions are still wanted, list again
                   over halves of the range (only for words with very many deletable letters) */
                u64 c[2];
                #define DELRUN(A0, A1, CAPV) do { u64 a0_ = (A0), a1_ = (A1), cap_ = (CAPV); CK(cMemsetD8(dcnt, 0, 16)); \
                    unsigned blocks_ = (unsigned)((a1_ - a0_ + TB - 1) / TB); \
                    void *da_[] = { &dsym, &wbase, &have, &L, &n, &a0_, &a1_, &ddup, &dcnt, &dout, &cap_, &DS }; \
                    gp_launch(fdel, blocks_, bt, shm, da_); CK(cCtxSync()); CK(cDtoH(c, dcnt, 16)); } while (0)
                DELRUN(d0, d1, nkeep < KEEP ? CAP : 0);
                ndel += c[0];
                if (nkeep < KEEP && c[0]) {
                    if (c[0] <= CAP) {
                        CK(cDtoH(hout, dout, c[0] * 8)); qsort(hout, c[0], 8, cmp64);
                        for (u64 i = 0; i < c[0] && nkeep < KEEP; i++) keep[nkeep++] = hout[i];
                    } else {      /* more than CAP deletable positions in this chunk: list them over parts of the range, in order */
                        u64 a0 = d0, w = (d1 - d0) / 2 ? (d1 - d0) / 2 : 1;
                        while (a0 < d1 && nkeep < KEEP) {
                            u64 a1 = a0 + w < d1 ? a0 + w : d1;
                            DELRUN(a0, a1, CAP);
                            if (c[0] > CAP) { w = w / 2 ? w / 2 : 1; continue; }
                            if (c[0]) { CK(cDtoH(hout, dout, c[0] * 8)); qsort(hout, c[0], 8, cmp64); }
                            for (u64 i = 0; i < c[0] && nkeep < KEEP; i++) keep[nkeep++] = hout[i];
                            a0 = a1;
                        }
                    }
                }
                d0 = d1;
            }
            nc = nc2;
            if (eof) break;
        }
        if (rd_close(&R)) { fprintf(stderr, "gdelcheck: xz reported an error\n"); return 2; }
        BADCHECK();
    }
    double t2 = gp_wall();
    printf("{\"n\":%d,\"length\":%llu,\"permutation_occurrences\":%llu,\"distinct_permutations\":%llu,\"required_permutations\":%llu,"
           "\"missing_permutations\":%llu,\"extra_occurrences\":%llu,\"permutations_occurring_once\":%llu,\"tested_deletions\":%llu,"
           "\"coverage_preserving_deletions_count\":%llu,\"coverage_preserving_deletions\":[",
           n, (unsigned long long)L, (unsigned long long)nperm, (unsigned long long)distinct, (unsigned long long)nf,
           (unsigned long long)(nf - distinct), (unsigned long long)(nperm - distinct), (unsigned long long)(distinct - twice),
           (unsigned long long)L, (unsigned long long)ndel);
    for (int i = 0; i < nkeep; i++) printf("%s%llu", i ? "," : "", (unsigned long long)keep[i]);
    printf("],\"pass1_seconds\":%.2f,\"pass2_seconds\":%.2f,\"seconds\":%.2f,\"threads\":%d,\"shards\":%d", t1 - t0, t2 - t1, t2 - t0, T, K);
    if (skip != ~0ULL) printf(",\"left_out_letter\":%llu", (unsigned long long)skip);
    printf("}\n");
    return distinct == nf ? 0 : 3;
}
