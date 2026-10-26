/* gen16c.c - generator and check in one process: the n = 12 + L word (L <= 4) of a unit plan (gen15, Jay Pantone's
   construction; gen16.c = opt/n15/gen15.c with one hook in its output and L = 4) is handed block by block, as letter values,
   to the group check of gcore.h, without a pipe and without storing the word.  The generator thread spells the
   word; a second thread computes its SHA-256 (in the generator thread when --to is given); T worker threads and a
   coordinator check it.

   usage: gen16c plan L SEL PLAN [--check T] [--sat S] [--table C] [--nosha] [--limit LETTERS] [--to CMD] [--list K] [--flip POS] [--gpu I/K]
          gen16c base L SEL [same options]
   Output: one JSON line on stdout (length, SHA-256 of the word, and the check); the generator's lines on stderr.
   Exit code 0 only if the word contains every permutation (and the plan's expect line matches, if it has one).
   build: gcc -O3 -march=native -pthread -o gen16c gen16c.c */
#define GEN15_NO_MAIN
#include "gen16.c"
#include "gcore.h"
#include "gpusink.h"

/* --flip POS (a test): both checks (and --gpu) get letter POS changed to the next letter value (mod n); the SHA is of the true word */
static u64 flip_at = ~0ULL, fed = 0;
static u8 *flipped(const u8 *p, size_t k) {     /* a changed copy if POS is in this block, else NULL */
    u8 *c = NULL;
    if (flip_at >= fed && flip_at < fed + k) { c = malloc(k); memcpy(c, p, k); c[flip_at - fed] = (u8)((c[flip_at - fed] + 1) % NN); fprintf(stderr, "flip: letter %llu changed\n", (unsigned long long)flip_at); }
    fed += k; return c;
}

/* SHA-256 of the word in its own thread: the generator hands every output block (letter values) to a ring; the
   thread spells it with the alphabet and hashes it, in order.  (gen15 does this in the generator thread, where it
   costs about 40% of the generator's time.) */
#define SRB (64u << 20)
#define NSR 4
typedef struct { u8 *d; size_t n; int full; u64 seq; } SR;
static SR sring[NSR]; static u64 s_in, s_out; static int s_done; static Sha tsha;
static pthread_mutex_t smu = PTHREAD_MUTEX_INITIALIZER; static pthread_cond_t s_cv = PTHREAD_COND_INITIALIZER;
static void sha_push(const u8 *p, size_t k) {
    while (k) {
        size_t c = k < SRB ? k : SRB;
        pthread_mutex_lock(&smu);
        while (s_in - s_out >= NSR) pthread_cond_wait(&s_cv, &smu);
        SR *r = &sring[s_in % NSR];
        pthread_mutex_unlock(&smu);
        memcpy(r->d, p, c); r->n = c;
        pthread_mutex_lock(&smu); r->full = 1; r->seq = s_in++; pthread_cond_broadcast(&s_cv); pthread_mutex_unlock(&smu);
        p += c; k -= c;
    }
}
static void *sha_thread(void *arg) {
    (void)arg; static u8 m[1 << 20];
    for (;;) {
        pthread_mutex_lock(&smu);
        while (s_out == s_in && !s_done) pthread_cond_wait(&s_cv, &smu);
        if (s_out == s_in) { pthread_mutex_unlock(&smu); break; }
        SR *r = &sring[s_out % NSR];
        pthread_mutex_unlock(&smu);
        for (size_t o = 0; o < r->n; o += sizeof m) {
            size_t c = r->n - o < sizeof m ? r->n - o : sizeof m;
            for (size_t i = 0; i < c; i++) m[i] = alpha[r->d[o + i]];
            sha_update(&tsha, m, c);
        }
        pthread_mutex_lock(&smu); r->full = 0; s_out++; pthread_cond_broadcast(&s_cv); pthread_mutex_unlock(&smu);
    }
    return NULL;
}
static int sha_in_thread = 0; static u64 gI = 0, gK = 0;   /* --gpu I/K: shard I of K checked on the card too (gpusink.h) */
static void hook_all(const u8 *p, size_t k) {
    if (sha_in_thread) sha_push(p, k);
    u8 *c = flip_at == ~0ULL ? NULL : flipped(p, k); const u8 *q = c ? c : p;
    if (gs.on) gs_push(q, k);
    gc_submit(q, k); free(c);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: gen16c plan|base L SEL [PLAN] [--check T] [--sat S] [--table C] [--nosha] [--limit N] [--to CMD] [--list K]\n"); return 2; }
    double t0 = wall(); t0g = t0;
    const char *mode = argv[1], *selp = argv[3], *planp = NULL;
    const char *tos[MAXSINK]; int nto = 0, threads = 2, sat = -1, table = 1 << 17, listk = 0;
    L = atoi(argv[2]); if (L < 0 || L > 4) DIE("L must be 0..4");
    NN = 12 + L; K = 10 + L; HH = NN - 3; SL = K; ZL = K + 1;
    int ai = 4;
    if (!strcmp(mode, "plan")) { if (argc < 5) DIE("plan needs a file"); planp = argv[4]; ai = 5; }
    else if (strcmp(mode, "base")) DIE("mode must be plan or base");
    for (; ai < argc; ai++) {
        if (!strcmp(argv[ai], "--limit") && ai + 1 < argc) limit = strtoull(argv[++ai], NULL, 10);
        else if (!strcmp(argv[ai], "--to") && ai + 1 < argc) { if (nto == MAXSINK) DIE("too many --to"); tos[nto++] = argv[++ai]; }
        else if (!strcmp(argv[ai], "--check") && ai + 1 < argc) threads = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "--sat") && ai + 1 < argc) sat = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "--table") && ai + 1 < argc) table = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "--list") && ai + 1 < argc) listk = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "--flip") && ai + 1 < argc) flip_at = strtoull(argv[++ai], NULL, 10);
        else if (!strcmp(argv[ai], "--nosha")) dosha = 0;
        else if (!strcmp(argv[ai], "--gpu") && ai + 1 < argc) { if (sscanf(argv[++ai], "%llu/%llu", (unsigned long long *)&gI, (unsigned long long *)&gK) != 2 || gK < 1 || gI >= gK) DIE("bad --gpu I/K"); }
        else DIE("unknown option %s", argv[ai]);
    }
    const char *alp = "0123456789ABCDEFG";
    for (int i = 0; i < NN; i++) alpha[i] = (u8)alp[i];
    sha_selftest();
    read_sel(selp);
    if (!strcmp(mode, "plan") && L == 0) DIE("unit plans need L >= 1");
    build_walks();
    fprintf(stderr, "n = %d (L = %d): %d lifted walks with %llu rows (%.1fs)\n", NN, L, nwl, (unsigned long long)nrows, wall() - t0);
    dowrite = nto > 0;
    for (int i = 0; i < nto; i++) sinks[nsink++] = open_sink(tos[i], i);
    gc_init(NN, sat, threads, table);
    int want_sha = dosha;
    if (dosha && !dowrite) {                       /* SHA in its own thread */
        sha_in_thread = 1; dosha = 0; sha_init(&tsha);
        for (int i = 0; i < NSR; i++) { sring[i].d = malloc(SRB); if (!sring[i].d) DIE("oom"); }
    }
    pthread_t sht; if (sha_in_thread) pthread_create(&sht, NULL, sha_thread, NULL);
    if (gK) { gs_init(argv[0], NN, gI, gK); gs_start(); }
    check_hook = hook_all;
    obuf = malloc(OBUF); sha_init(&sha);
    double tg = wall();
    if (!strcmp(mode, "base")) all_trails(1); else plan(planp);
    flush_out();
    double tg1 = wall();
    if (sha_in_thread) { pthread_mutex_lock(&smu); s_done = 1; pthread_cond_broadcast(&s_cv); pthread_mutex_unlock(&smu); pthread_join(sht, NULL); }
    char hex[65] = "none"; if (dosha) sha_final(&sha, hex); else if (sha_in_thread) sha_final(&tsha, hex);
    int rc = 0;
    for (int i = 0; i < nto; i++) { int r = close_sink(sinks[i], i); fprintf(stderr, "sink %d (%s) exit %d\n", i, tos[i], r); if (r) rc = 4; }
    GRes o; gc_finish(&o);
    u64 gseen = 0, gpw = 0, gmarked = 0; if (gs.on) gs_finish(&gseen, &gpw, &gmarked);
    double t1 = wall();
    int ok = o.missing == 0 && o.total == written && !(gs.on && !gs.stopped && gseen != gs.span);   /* the card's shard must be complete too */
    int exp_ok = 1;
    if (expect_len) exp_ok = written == expect_len && (!expect_sha[0] || !want_sha || !strcmp(expect_sha, hex));
    printf("{\"mode\":\"%s\",\"n\":%d,\"length\":%llu,\"sha256\":\"%s\",\"expect\":\"%s\",\"small_trails\":%llu,\"walk_trails\":%llu,\"checked_letters\":%llu,",
           mode, NN, (unsigned long long)written, hex, expect_len ? (exp_ok ? "MATCH" : "MISMATCH") : "none",
           (unsigned long long)cnt_small, (unsigned long long)cnt_walk, (unsigned long long)o.total);
    gc_json(stdout, &o);
    if (gs.on) printf(",\"gpu_shard\":\"%llu/%llu\",\"gpu_span\":%llu,\"gpu_letters\":%llu,\"gpu_permutation_windows\":%llu,\"gpu_marked\":%llu,\"gpu_seen\":%llu,\"gpu_missing\":%llu,\"gpu_kernel_seconds\":%.1f,\"gpu_complete\":%s",
        (unsigned long long)gI, (unsigned long long)gK, (unsigned long long)gs.span, (unsigned long long)gs.fed, (unsigned long long)gpw, (unsigned long long)gmarked, (unsigned long long)gseen, (unsigned long long)(gs.span - gseen), gs.tk, gs.stopped ? "\"stopped\"" : (gseen == gs.span ? "true" : "false"));
    printf(",\"generate_seconds\":%.1f,\"seconds\":%.1f,\"setup_seconds\":%.1f,\"valid\":%s}\n", tg1 - tg, t1 - t0, tg - t0, ok ? "true" : "false");
    fflush(stdout);
    if (listk > 0 && o.missing) gc_list(&o, listk, alp);
    if (!ok) return 1;
    if (!exp_ok) return 3;
    return rc;
}
