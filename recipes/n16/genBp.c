/* genBp.c - opt/n17/gen17p.c on top of genBt.c (construction (B), agent constB): the same host threads, card check and
   --predict; the plan's units are checked against the construction (check_units; GENB_NOUNITCHECK=1 skips it, for
   negative tests), --predict uses Q of the stored rows.  Block: env GENB_BLOCK=FILE.  Kernels: gcheck17.ptx next to
   the exe (a copy of opt/n17/gcheck17.ptx). */
/* gen17p.c - opt/fastcheck/gen16p.c for n = 13..17 (L = 1..5) with group shards (agent n17).
   T host threads turn jobs (consecutive units of the plan) into spans (gen17t.c: descriptor mode, per-thread state),
   one thread feeds the card in job order (gcard17.h): the card spells the letters, checks the groups of the shard and
   hashes the leaves of the tree hash.
   A job needs only the last h letters written before it (the overlap of its first unit): they are the last h letters
   of the last trail of the unit before it, so the thread builds that one trail first (unit_tail) without output.
   The first unit of the plan has no overlap (as in gen15).  So the word is the one gen15 writes, whatever T is, and
   the tree hash (SHA-256 of the SHA-256 of every 64 KiB leaf) is the same for every T, job size and group shard.

   --gshard I/K: record only the groups g with g mod K = I ((n-2)!/K bits on the card).  A word is a superpermutation
   iff every pass I = 0..K-1 is valid (all groups of its shard complete, no overflow) and all K passes report the same
   length and tree hash (see opt/n17/STATE.md, section 2).
   --predict: no card; the length of the plan's word from the construction's sum of trail lengths (F3 + Q) and the
   overlaps between units (first h letters of each unit against the last h letters of the one before).  A forecast
   only: it trusts the construction; the check is the card run.

   usage: gen17p L SEL PLAN [--threads T] [--seg LOG2] [--table LOG2] [--sat S] [--gshard I/K] [--rank I/K] [--plain]
                 [--job LOG2] [--flip POS] [--cut LEN] [--predict]
   build: gcc -O3 -march=native -pthread -o gen17p gen17p.c */
#define GEN15_NO_MAIN
#include <pthread.h>
#include "genBt.c"
#include "gcard17.h"

/* a unit of the plan in 16 bytes: D: dw = d, wj = j, x = g[0..3] (one byte each); W: dw = w, wj = way, x = i0 */
typedef struct { u64 x; u32 dw; u8 ty, wj, cap, pad; } Unit;
static Unit *U; static u64 NU;
static void load_plan(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) DIE("cannot open %s", path);
    char line[512], hdr[32]; u64 nl = 0; u64 cap = 1 << 20; U = malloc(cap * sizeof(Unit)); NU = 0;
    sprintf(hdr, "N%d-UNITPLAN", NN);
    while (fgets(line, sizeof line, f)) {
        nl++;
        if (nl == 1) { if (strncmp(line, hdr, strlen(hdr))) DIE("not an n = %d unit plan", NN); continue; }
        if (!strncmp(line, "# expect length ", 16)) { if (sscanf(line + 16, "%llu sha256 %64s", &expect_len, expect_sha) < 1) DIE("bad expect line"); continue; }
        if (line[0] == '#' || line[0] == '\n' || line[0] == '\r') continue;
        char *tok[16]; int nt = 0; char *sv = NULL;
        for (char *t = strtok_r(line, " \t\r\n", &sv); t && nt < 16; t = strtok_r(NULL, " \t\r\n", &sv)) tok[nt++] = t;
        int cp = HH; if (nt && tok[nt - 1][0] == 'o') { cp = atoi(tok[nt - 1] + 1); nt--; }
        if (cp < 0 || cp > HH) DIE("bad cap line %llu", (unsigned long long)nl);
        if (NU == cap) { cap *= 2; U = realloc(U, cap * sizeof(Unit)); if (!U) DIE("oom"); }
        Unit *u = &U[NU]; memset(u, 0, sizeof *u); u->cap = (u8)cp;
        if (nt >= 1 && tok[0][0] == 'D') {
            if (nt != 2 + L) DIE("D line %llu needs %d numbers", (unsigned long long)nl, 1 + L);
            int d = atoi(tok[1]), j = atoi(tok[nt - 1]);
            if (d < 0 || d >= ndet || j < 0 || j >= HH) DIE("bad D line %llu", (unsigned long long)nl);
            u->ty = 0; u->dw = (u32)d; u->wj = (u8)j;
            int gg[5] = {0};
            for (int l = 0; l < L - 1; l++) { int g = atoi(tok[2 + l]); if (g < 0 || g > 9 + l) DIE("bad D line %llu", (unsigned long long)nl); u->x |= (u64)g << (8 * l); gg[l] = g; }
            if (!dunit_ok(gg)) DIE("D line %llu: its loop has a row of the block", (unsigned long long)nl);
        } else if (nt == 4 && tok[0][0] == 'W') {
            int w = atoi(tok[1]), way = atoi(tok[3]);
            if (w < 0 || w >= nwl || way < 0 || way > 1) DIE("bad W line %llu", (unsigned long long)nl);
            u->ty = 1; u->dw = (u32)w; u->x = strtoull(tok[2], NULL, 10); u->wj = (u8)way;
        } else DIE("bad plan line %llu", (unsigned long long)nl);
        NU++;
    }
    fclose(f);
}
/* constB: every unit of the construction exactly once (small units of dunit_ok loops, every top walk) */
static void check_units(void) {
    u64 ns = small_id_space(), nsu = n_small_units(); char *seen = calloc(ns + (u64)nwl, 1); if (!seen) DIE("oom (unit check)");
    for (u64 i = 0; i < NU; i++) {
        u64 id;
        if (U[i].ty == 0) { int g[5]; for (int l = 0; l < 4; l++) g[l] = (int)(U[i].x >> (8 * l) & 255); id = small_id((int)U[i].dw, g); }
        else id = ns + U[i].dw;
        if (seen[id]++) DIE("unit %llu repeated", (unsigned long long)i);
    }
    free(seen);
    if (NU != nsu + (u64)nwl) DIE("plan has %llu units, the construction %llu", (unsigned long long)NU, (unsigned long long)(nsu + nwl));
    fprintf(stderr, "units: %llu, every unit of the construction once (%llu small, %d walk)\n", (unsigned long long)NU, (unsigned long long)nsu, nwl);
}
static void ugs(const Unit *u, int *g) { for (int l = 0; l < 4; l++) g[l] = (int)(u->x >> (8 * l) & 255); }
static void run_unit(u64 i) { Unit *u = &U[i]; if (u->ty == 0) { int g[5]; ugs(u, g); unit_small((int)u->dw, g, u->wj, u->cap); } else unit_walk((int)u->dw, u->x, u->wj, u->cap); }
/* trail i of unit k (descriptors): its piece is (c, len) */
static void unit_trail(u64 k, int i, size_t *c, size_t *len) {
    Unit *u = &U[k];
    if (u->ty == 0) { int g[5]; ugs(u, g); unit_trail_small((int)u->dw, g, u->wj, i, c, len); }
    else unit_trail_walk((int)u->dw, u->x, u->wj, i, c, len);
}
static void unit_tail(u64 k) { size_t c, len; unit_trail(k, HH - 1, &c, &len); tail_from(c, len); }
/* estimated letters of a unit (for cutting jobs only) */
static double unit_est(u64 i) {
    double sl = 2.0 * (NN - 1) + 1 + (double)K * (NN + 1) - HH;
    if (U[i].ty == 0) return (double)HH * K * sl;
    int w = (int)U[i].dw; double m;
    if (!LAZY) m = (double)(wstart_sh[w + 1] - wstart_sh[w]);
    else {
        int w1 = w; double f2 = 1;
        if (LAZY == 2) { w1 = pre_find(pre2, nw1, w); f2 = (double)(KP + 1) / (pre2[w1 + 1] - pre2[w1]); }
        int v = pre_find(pre1, nst, w1);
        m = (double)(wstart_sh[v + 1] - wstart_sh[v]) * KP / (pre1[v + 1] - pre1[v]) * f2;
    }
    return (double)HH * m * sl;
}

/* jobs */
typedef struct { u64 a, b; CSpan *sp; u32 nsp, cap; u64 k; int ready; u64 ovsum; int pinned; } Job;
/* span buffers: job c writes into pinned pool slot c mod NPOOL (the card copies straight from it); the slot is taken
   again only after the event recorded behind the last copy of the job before it has completed.  A job that outgrows
   its slot moves to ordinary memory (pinned = 0) and goes through the staging slots of gcard17.h. */
static CSpan **pool; static void **poolev; static int *poolused, NPOOL; static u32 POOLCAP = 1u << 20;
static Job *J; static u64 NJ, next_job, fed_jobs; static int INFL, PREDICT, NOCARD;   /* NOCARD: --nocard, host timing only (spans dropped; no check) */
static pthread_mutex_t jmu = PTHREAD_MUTEX_INITIALIZER; static pthread_cond_t jcv = PTHREAD_COND_INITIALIZER;
static __thread Job *cj;
static u64 tot_small, tot_walk;
static void on_span(const SD *z, u32 from, u32 len) {
    if (cj->nsp == cj->cap) {
        u32 nc = cj->cap ? 2 * cj->cap : 1 << 16;
        if (cj->pinned) { CSpan *q = malloc((size_t)nc * sizeof(CSpan)); if (!q) DIE("oom (spans)"); memcpy(q, cj->sp, (size_t)cj->nsp * sizeof(CSpan)); cj->sp = q; cj->pinned = 0; }
        else { cj->sp = realloc(cj->sp, (size_t)nc * sizeof(CSpan)); if (!cj->sp) DIE("oom (spans)"); }
        cj->cap = nc;
    }
    CSpan *s = &cj->sp[cj->nsp++]; s->B = z->B; s->off = cj->k; s->from = (unsigned short)from; s->len = (unsigned short)len; s->s = z->s; s->v = z->v; s->pad0 = s->pad1 = 0;
    cj->k += len;
}
/* --predict: the overlaps of the job's units with the unit before each */
static void predict_job(Job *jb) {
    u64 ov = 0;
    for (u64 i = jb->a; i < jb->b; i++) {
        size_t c, len; u8 hd[24];
        unit_trail(i, 0, &c, &len); head_from(c, hd);
        if (written) ov += (u64)maxov(hd, U[i].cap);
        unit_tail(i); written = 1;
        if (U[i].ty == 0) cnt_small += HH; else cnt_walk += HH;
    }
    jb->ovsum = ov;
}
static void *host_thread(void *arg) {
    (void)arg;
    gs_new();
    if (pool) CCK(cuCtxSetCurrent_(G2.ctx));
    if (!LAZY) { wrow = wrow_sh; wstart = wstart_sh; }
    for (;;) {
        pthread_mutex_lock(&jmu);
        u64 c = next_job;
        while (c < NJ && c >= fed_jobs + INFL) { pthread_cond_wait(&jcv, &jmu); c = next_job; }
        if (c >= NJ) { pthread_mutex_unlock(&jmu); break; }
        next_job++;
        pthread_mutex_unlock(&jmu);
        Job *jb = &J[c];
        tn = 0; nsd = 0; ntail = 0; limited = 0; written = 0;
        if (jb->a > 0) { unit_tail(jb->a - 1); written = 1; }   /* the last h letters before the job */
        cj = jb; u64 cs0 = cnt_small, cw0 = cnt_walk;
        if (pool) { int sl = (int)(c % NPOOL); if (poolused[sl]) CCK(cuEventSynchronize_(poolev[sl])); jb->sp = pool[sl]; jb->cap = POOLCAP; jb->pinned = 1; }
        if (PREDICT) predict_job(jb); else for (u64 i = jb->a; i < jb->b; i++) run_unit(i);
        pthread_mutex_lock(&jmu); jb->ready = 1; tot_small += cnt_small - cs0; tot_walk += cnt_walk - cw0; pthread_cond_broadcast(&jcv); pthread_mutex_unlock(&jmu);
    }
    return NULL;
}
static void feed(Job *jb) {                            /* in pieces of at most a quarter of the card buffer */
    u64 lim = G2.SEG / 4; u32 s0 = 0;
    while (s0 < jb->nsp) {
        u64 base = jb->sp[s0].off; u32 s1 = s0;
        while (s1 < jb->nsp && jb->sp[s1].off + jb->sp[s1].len - base <= lim) s1++;
        u64 k = (s1 < jb->nsp ? jb->sp[s1].off : jb->k) - base;
        if (base) for (u32 i = s0; i < s1; i++) jb->sp[i].off -= base;
        if ((u64)(s1 - s0) > G2.spancap) DIE("too many spans in a piece");
        g2_spans(jb->sp + s0, s1 - s0, k, jb->pinned);
        s0 = s1;
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: gen17p L SEL PLAN [--threads T] [--seg LOG2] [--table LOG2] [--sat S] [--gshard I/K] [--rank I/K] [--plain] [--job LOG2] [--flip POS] [--cut LEN] [--predict]\n"); return 2; }
    double t0 = wall(); t0g = t0; gs_new();
    const char *selp = argv[2], *planp = argv[3];
    int T = 2, segl = 30, tbits = 24, sat = -1, plain = 0, jobl = 26; u64 rI = 0, rK = 0, gI = 0, gK = 1, flipp = ~0ULL, cutp = 0;
    L = atoi(argv[1]); if (L < 1 || L > 5) DIE("L must be 1..5");
    NN = 12 + L; K = 10 + L; HH = NN - 3; SL = K; ZL = K + 1;
    for (int ai = 4; ai < argc; ai++) {
        if (!strcmp(argv[ai], "--threads") && ai + 1 < argc) T = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "--seg") && ai + 1 < argc) segl = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "--table") && ai + 1 < argc) tbits = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "--sat") && ai + 1 < argc) sat = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "--job") && ai + 1 < argc) jobl = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "--rank") && ai + 1 < argc) { if (sscanf(argv[++ai], "%llu/%llu", (unsigned long long *)&rI, (unsigned long long *)&rK) != 2) DIE("bad --rank"); }
        else if (!strcmp(argv[ai], "--gshard") && ai + 1 < argc) { if (sscanf(argv[++ai], "%llu/%llu", (unsigned long long *)&gI, (unsigned long long *)&gK) != 2 || gK < 1 || gI >= gK) DIE("bad --gshard"); }
        else if (!strcmp(argv[ai], "--plain")) plain = 1;
        else if (!strcmp(argv[ai], "--predict")) PREDICT = 1;
        else if (!strcmp(argv[ai], "--nocard")) NOCARD = 1;
        else if (!strcmp(argv[ai], "--flip") && ai + 1 < argc) flipp = strtoull(argv[++ai], NULL, 10);
        else if (!strcmp(argv[ai], "--cut") && ai + 1 < argc) cutp = strtoull(argv[++ai], NULL, 10);
        else DIE("unknown option %s", argv[ai]);
    }
    if (T < 1 || T > 32) DIE("bad --threads");
    for (int i = 0; i < NN; i++) alpha[i] = (u8)"0123456789ABCDEFG"[i];
    sha_selftest();
    read_sel(selp);
    build_walks();
    load_plan(planp);
    if (!getenv("GENB_NOUNITCHECK")) check_units();
    /* jobs of about 2^jobl letters */
    double target = (double)(1ULL << jobl), acc = 0; u64 cap = 1024; J = calloc(cap, sizeof(Job)); NJ = 0; u64 a = 0;
    for (u64 i = 0; i < NU; i++) {
        acc += unit_est(i);
        if (acc >= target || i + 1 == NU) { if (NJ == cap) { cap *= 2; J = realloc(J, cap * sizeof(Job)); memset(J + NJ, 0, (cap - NJ) * sizeof(Job)); } J[NJ].a = a; J[NJ].b = i + 1; NJ++; a = i + 1; acc = 0; }
    }
    INFL = 2 * T + 2;
    NPOOL = INFL + 4;
    fprintf(stderr, "n = %d (L = %d, %d lazy levels): %d lifted walks, %llu units, %llu jobs, %d host threads, group shard %llu/%llu (%.1fs)\n", NN, L, LAZY, nwl,
            (unsigned long long)NU, (unsigned long long)NJ, T, (unsigned long long)gI, (unsigned long long)gK, wall() - t0);
    if (!PREDICT && !NOCARD) {
        g2_init(argv[0], NN, sat, tbits, 1ULL << segl, plain, rI, rK, gI, gK); G2.flip_at = flipp; G2.cut_at = cutp;
        pool = calloc(NPOOL, sizeof(CSpan *)); poolev = calloc(NPOOL, sizeof(void *)); poolused = calloc(NPOOL, sizeof(int));
        for (int i = 0; i < NPOOL; i++) { CCK(cuMemHostAlloc_((void **)&pool[i], (size_t)POOLCAP * sizeof(CSpan), 0)); CCK(cuEventCreate_(&poolev[i], 2)); }
    }
    DESC = 1; span_hook = on_span; dowrite = 0; dosha = 0;
    double tg = wall();
    pthread_t th[32]; for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, host_thread, NULL);
    double lastp = tg; u64 ovtot = 0;
    for (u64 c = 0; c < NJ; c++) {
        pthread_mutex_lock(&jmu); while (!J[c].ready) pthread_cond_wait(&jcv, &jmu); pthread_mutex_unlock(&jmu);
        if (PREDICT) ovtot += J[c].ovsum; else if (NOCARD) G2.total += J[c].k; else feed(&J[c]);
        if (J[c].pinned) { int sl = (int)(c % NPOOL); CCK(cuEventRecord_(poolev[sl], NULL)); poolused[sl] = 1; } else free(J[c].sp);
        J[c].sp = NULL;
        pthread_mutex_lock(&jmu); fed_jobs = c + 1; pthread_cond_broadcast(&jcv); pthread_mutex_unlock(&jmu);
        double t = wall();
        if (t - lastp > 300) {
            double fr = (double)(c + 1) / NJ;
            fprintf(stderr, "  jobs %llu/%llu, letters %llu (%.0fs, %.2f GB/s, about %.0f s left)\n", (unsigned long long)(c + 1), (unsigned long long)NJ,
                    (unsigned long long)G2.total, t - tg, G2.total / (t - tg) / 1e9, (t - tg) * (1 - fr) / fr);
            lastp = t;
        }
    }
    for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
    double tg1 = wall();
    if (NOCARD) { printf("{\"mode\":\"nocard\",\"n\":%d,\"length\":%llu,\"host_threads\":%d,\"generate_seconds\":%.1f,\"host_gb_per_s\":%.2f,\"valid\":\"not checked\"}\n", NN, (unsigned long long)G2.total, T, tg1 - tg, G2.total / (tg1 - tg) / 1e9); return 0; }
    if (PREDICT) {
        u64 nshort = 0; for (int i = 0; i < nsel; i++) nshort += sel[i].ty == 1;
        u64 fact[21]; fact[0] = 1; for (int i = 1; i < 21; i++) fact[i] = fact[i - 1] * i;
        u64 mult = 1; for (int l = 0; l < L; l++) mult *= (u64)(10 + l);
        u64 sR = fact[NN] + fact[NN - 1] + fact[NN - 2] + Qall, nw = 0; (void)nshort; (void)mult;
        for (u64 i = 0; i < NU; i++) nw += U[i].ty;
        u64 len = sR + NU * (u64)(2 * HH - 1) + nw - ovtot;
        printf("{\"mode\":\"predict\",\"n\":%d,\"units\":%llu,\"walk_units\":%llu,\"small_trails\":%llu,\"walk_trails\":%llu,\"sumR\":%llu,\"join_overlaps\":%llu,\"join_cost\":%llu,\"predicted_length\":%llu,\"expect\":\"%s\",\"seconds\":%.1f}\n",
               NN, (unsigned long long)NU, (unsigned long long)nw, (unsigned long long)tot_small, (unsigned long long)tot_walk, (unsigned long long)sR,
               (unsigned long long)ovtot, (unsigned long long)((NU - 1) * (u64)HH - ovtot), (unsigned long long)len,
               expect_len ? (len == expect_len ? "MATCH" : "MISMATCH") : "none", tg1 - t0);
        return 0;
    }
    G2Res o; g2_finish(&o);
    double t1 = wall();
    int complete = o.bits == G2.NGloc;
    int ok = o.missing == 0 && !o.overflow && complete && (!rK || o.rseen == G2.rspan);
    int exp_ok = !expect_len || (o.total == expect_len && (!plain || !expect_sha[0] || !strcmp(expect_sha, o.plain)));
    printf("{\"mode\":\"plan\",\"n\":%d,\"length\":%llu,\"expect\":\"%s\",\"small_trails\":%llu,\"walk_trails\":%llu,\"host_threads\":%d,\"jobs\":%llu,",
           NN, (unsigned long long)o.total, expect_len ? (exp_ok ? "MATCH" : "MISMATCH") : "none", (unsigned long long)tot_small, (unsigned long long)tot_walk, T, (unsigned long long)NJ);
    g2_json(stdout, &o);
    printf(",\"shard_complete\":%s,\"generate_seconds\":%.1f,\"seconds\":%.1f,\"setup_seconds\":%.1f,\"valid\":%s}\n", complete ? "true" : "false", tg1 - tg, t1 - t0, tg - t0, ok ? "true" : "false");
    fflush(stdout);
    if (!ok) return 1;
    if (!exp_ok) return 3;
    return 0;
}
