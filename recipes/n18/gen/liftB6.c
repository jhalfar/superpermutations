/* liftB6.c (agent n18, 2026-10-28) - opt/constB/liftB.c for L <= 6 (on genB6.c), with the DP in chunks, in RAM, on
   T threads instead of one DP over all units with a back file.
   The units (the trails of the lower plan, in its order) are cut into chunks of C consecutive units.  Each chunk gets
   the exact DP of lift17 (openings chosen to minimise the sum of h - overlap over the joins inside the chunk), with a
   free start (every opening of its first unit costs 0) and its back bytes (f - min f per candidate) in memory; the
   backward pass recomputes the predecessors with lift16's tie-breaking, as liftB.  The join between two chunks is
   whatever the two chosen openings give.
   Optimality: let OPT be the least total join cost over all openings (what liftB computes) and c_k the DP optimum of
   chunk k.  OPT restricted to chunk k is a choice for chunk k, so c_k <= that part of OPT, and joins cost >= 0, so
   sum c_k <= OPT.  The plan written costs sum c_k + B (B = the joins between chunks, computed exactly), hence
   plan - OPT <= B <= h (number of chunks - 1).  With one chunk the plan is liftB's (same DP, same tie-breaking).
   Memory: units 12 bytes each (all), opening 4 bytes each (all); per thread the back bytes of one chunk.
   usage: liftB6 lift|liftB L SEL PLAN(n-1) OUT.uplan [--threads T] [--chunk C]   (env GENB_BLOCK, LIFTB_ORDER)
   Prints "LENGTH x" (the length of the word genB6 writes for OUT, from the DP: sumR + h + (h-1) small + h walk + joins),
   "CHUNKS k", "INNER sum c_k", "BETWEEN B".
   build: gcc -O3 -march=native -pthread -o liftB6.exe liftB6.c */
#define GEN15_NO_MAIN
#include <pthread.h>
#include "genB6.c"

/* a unit: a = d (D) or w (W); g = 4 bits a letter g[0..4], bit 31 = walk unit; src = index of its lower unit */
typedef struct { u32 a, src, g; } Unit;
#define UW (1u << 31)
static Unit *U; static u32 NU; static u32 *OPEN;      /* OPEN[u]: the chosen opening (M value: j, or 2 i0 + way) */
static inline int ug(const Unit *u, int l) { return (u->g >> (4 * l)) & 15; }
static inline int uwalk(const Unit *u) { return (u->g & UW) != 0; }
static u64 packh(const u8 *w) { u64 v = 0; for (int i = 0; i < HH; i++) v = v << 4 | w[i]; return v; }

typedef struct { u64 k; u32 f, i; } HE;
typedef struct {                                       /* per-thread DP state */
    u64 *cS, *cE; u32 *cM; size_t ccap;
    HE *ht; int hb; size_t htcap;
    u32 *fprev, *fcur; u64 *Eprev; u8 *fb; size_t pcap;
    u8 *back; size_t bcap, bsize; u32 *fmin, *ncand, *choice; size_t ucap;
    u64 *cS0; size_t cs0cap; u8 *fbp; size_t fbcap; u64 *Ep; size_t epcap;
    u64 hist[17], ccount[8], ccost[8], ncands;
} Ctx;
static void cgrow(Ctx *c, size_t need) { if (need > c->ccap) { c->ccap = 2 * need + 16; c->cS = realloc(c->cS, 8 * c->ccap); c->cE = realloc(c->cE, 8 * c->ccap); c->cM = realloc(c->cM, 4 * c->ccap); if (!c->cS || !c->cE || !c->cM) DIE("oom (cands)"); } }
/* candidates of unit u: start keys S, end keys E, M values (as liftB) */
static int cands_into(Ctx *c, const Unit *u) {
    int n = 0;
    if (!uwalk(u)) {
        int g[6] = {0}; for (int l = 0; l < L - 1; l++) g[l] = ug(u, l);
        u8 y[24], r[24]; small_y((int)u->a, g, y);
        cgrow(c, HH);
        for (int j = 0; j < HH; j++) { rot(r, y, HH, j); c->cS[n] = packh(r); rot(r, y, HH, j - 1); c->cE[n] = packh(r); c->cM[n] = j; n++; }
    } else {
        load_walk((int)u->a); u64 a = wbeg((int)u->a), m = wlen((int)u->a); u8 b[24], t[24];
        cgrow(c, 2 * (size_t)m);
        for (u64 i = 0; i < m; i++) {
            if (rty(wrow[a + i])) continue;
            unpackK(wrow[a + i], b);
            c->cS[n] = packh(b); t[0] = b[K - 1]; memcpy(t + 1, b, HH - 1); c->cE[n] = packh(t); c->cM[n] = (u32)(i * 2); n++;
            c->cS[n] = packh(b + 1); c->cE[n] = packh(b); c->cM[n] = (u32)(i * 2 + 1); n++;
        }
    }
    return n;
}
/* keys: q in bits 60..63 (q <= h <= 15), the last q letters of an end in bits 0..4q-1 (4q <= 60) */
static inline u64 hh_(const Ctx *c, u64 k) { k ^= k >> 31; k *= 0x9E3779B97F4A7C15ULL; return k >> (64 - c->hb); }
static void hinit(Ctx *c, size_t puts) {
    int b = 6; while (((size_t)1 << b) < 2 * puts) b++;
    if (b > 28) DIE("hash too large");
    size_t sz = (size_t)1 << b; if (sz > c->htcap) { free(c->ht); c->ht = malloc(sizeof(HE) * sz); if (!c->ht) DIE("oom (hash)"); c->htcap = sz; }
    c->hb = b; for (size_t p = 0; p < sz; p++) c->ht[p].k = ~0ULL;
}
static inline void hput(Ctx *c, u64 k, u32 f, u32 i) {
    u64 p = hh_(c, k), mk = ((u64)1 << c->hb) - 1; HE *ht = c->ht;
    for (;;) { if (ht[p].k == ~0ULL) { ht[p].k = k; ht[p].f = f; ht[p].i = i; return; }
               if (ht[p].k == k) { if (f < ht[p].f) { ht[p].f = f; ht[p].i = i; } return; } p = (p + 1) & mk; }
}
static inline int hget(const Ctx *c, u64 k, u32 *f, u32 *i) {
    u64 p = hh_(c, k), mk = ((u64)1 << c->hb) - 1; const HE *ht = c->ht;
    for (;;) { if (ht[p].k == ~0ULL) return 0; if (ht[p].k == k) { *f = ht[p].f; *i = ht[p].i; return 1; } p = (p + 1) & mk; }
}
static void bput(Ctx *c, const u8 *p, size_t n) {
    if (c->bsize + n > c->bcap) { c->bcap = c->bsize + n + c->bsize / 4 + (1u << 20); c->back = realloc(c->back, c->bcap); if (!c->back) DIE("oom (back bytes, %llu)", (unsigned long long)c->bcap); }
    memcpy(c->back + c->bsize, p, n); c->bsize += n;
}
/* chunk [u0, u1): the DP of lift17 with a free start; returns its optimum; OPEN[u] for its units; first S / last E */
static u32 dp_chunk(Ctx *c, u32 u0, u32 u1, u64 *firstS, u64 *lastE) {
    u32 nu = u1 - u0;
    if (nu > c->ucap) { c->ucap = nu; c->fmin = realloc(c->fmin, 4 * (size_t)nu); c->ncand = realloc(c->ncand, 4 * (size_t)nu); c->choice = realloc(c->choice, 4 * (size_t)nu); if (!c->fmin || !c->ncand || !c->choice) DIE("oom"); }
    c->bsize = 0;
    int np = 0; u32 pgmin = 0, pgi = 0;
    for (u32 ui = 0; ui < nu; ui++) {
        int n = cands_into(c, &U[u0 + ui]);
        if ((size_t)n > c->pcap) { c->pcap = 2 * (size_t)n + 16; c->fprev = realloc(c->fprev, 4 * c->pcap); c->fcur = realloc(c->fcur, 4 * c->pcap); c->Eprev = realloc(c->Eprev, 8 * c->pcap); c->fb = realloc(c->fb, c->pcap); if (!c->fprev || !c->fcur || !c->Eprev || !c->fb) DIE("oom"); }
        if (ui == 0) { for (int k = 0; k < n; k++) c->fcur[k] = 0; }
        else {
            hinit(c, (size_t)np * HH);
            int have[16] = {0}; u32 qmin[16]; for (int q = 0; q <= HH; q++) qmin[q] = ~0u;
            for (int k = 0; k < np; k++) {
                u32 d = c->fprev[k] - pgmin;
                for (int q = d + 1; q <= HH; q++) {
                    hput(c, (u64)q << 60 | (c->Eprev[k] & ((1ULL << (4 * q)) - 1)), c->fprev[k], k); have[q] = 1;
                    if (c->fprev[k] < qmin[q]) qmin[q] = c->fprev[k];
                }
            }
            for (int k = 0; k < n; k++) {
                u32 best = pgmin + HH, f, i;
                for (int q = 1; q <= HH; q++) {
                    if (!have[q] || qmin[q] + HH - q >= best) continue;
                    if (hget(c, (u64)q << 60 | (c->cS[k] >> (4 * (HH - q))), &f, &i) && f + HH - q < best) best = f + HH - q;
                }
                c->fcur[k] = best;
            }
        }
        u32 gmin = ~0u, gi = 0; for (int k = 0; k < n; k++) if (c->fcur[k] < gmin) { gmin = c->fcur[k]; gi = k; }
        for (int k = 0; k < n; k++) { u32 d = c->fcur[k] - gmin; if (d > 255) DIE("f spread %u", d); c->fb[k] = (u8)d; }
        bput(c, c->fb, n); c->fmin[ui] = gmin; c->ncand[ui] = n; c->ncands += (u64)n;
        { u32 *t = c->fprev; c->fprev = c->fcur; c->fcur = t; }
        memcpy(c->Eprev, c->cE, 8 * (size_t)n); np = n; pgmin = gmin; pgi = gi;
    }
    (void)pgi;
    /* the best end candidate: first with min f */
    { const u8 *tmp = c->back + c->bsize - np; int bc = 0; for (int k = 0; k < np; k++) if (tmp[k] < tmp[bc]) bc = k; c->choice[nu - 1] = bc; }
    u32 opt = c->fmin[nu - 1];
    /* backward (liftB's dp_backward on the chunk) */
    u64 off = c->bsize;
    int n = cands_into(c, &U[u0 + nu - 1]);
    *lastE = c->cE[c->choice[nu - 1]]; OPEN[u1 - 1] = c->cM[c->choice[nu - 1]];
    if ((size_t)n > c->cs0cap) { c->cs0cap = 2 * (size_t)n + 16; c->cS0 = realloc(c->cS0, 8 * c->cs0cap); }
    memcpy(c->cS0, c->cS, 8 * (size_t)n);
    for (u32 ui = nu - 1; ui >= 1; ui--) {
        off -= c->ncand[ui];
        int ch = c->choice[ui];
        u32 fc = c->fmin[ui] + c->back[off + ch];
        int npv = cands_into(c, &U[u0 + ui - 1]);
        if ((size_t)npv > c->fbcap) { c->fbcap = 2 * (size_t)npv + 16; c->fbp = realloc(c->fbp, c->fbcap); }
        if ((size_t)npv > c->epcap) { c->epcap = 2 * (size_t)npv + 16; c->Ep = realloc(c->Ep, 8 * c->epcap); }
        memcpy(c->Ep, c->cE, 8 * (size_t)npv);
        memcpy(c->fbp, c->back + off - npv, npv);
        u32 pg = c->fmin[ui - 1]; int pgi_ = 0; while (c->fbp[pgi_]) pgi_++;
        u32 best = pg + HH, bi = pgi_; int bq = 0;
        for (int q = 1; q <= HH; q++) {
            u64 key = c->cS0[ch] >> (4 * (HH - q)), mask = (1ULL << (4 * q)) - 1; u32 mf = ~0u; int mi = -1;
            for (int j = 0; j < npv; j++) if ((c->Ep[j] & mask) == key) { u32 f = pg + c->fbp[j]; if (f < mf) { mf = f; mi = j; } }
            if (mi >= 0 && mf + HH - q < best) { best = mf + HH - q; bi = mi; bq = q; }
        }
        if (best != fc) DIE("backward: unit %u candidate %d has f %u, recomputed %u", u0 + ui, ch, fc, best);
        c->choice[ui - 1] = bi; OPEN[u0 + ui - 1] = c->cM[bi];
        { int cost = HH - bq; c->hist[cost]++;
          const Unit *ua = &U[u0 + ui - 1], *ub = &U[u0 + ui]; int cl = (ua->src == ub->src ? 0 : 4) + uwalk(ua) * 2 + uwalk(ub);
          c->ccount[cl]++; c->ccost[cl] += cost; }
        if ((size_t)npv > c->cs0cap) { c->cs0cap = 2 * (size_t)npv + 16; c->cS0 = realloc(c->cS0, 8 * c->cs0cap); }
        memcpy(c->cS0, c->cS, 8 * (size_t)npv);
    }
    *firstS = c->cS0[c->choice[0]];
    return opt;
}

/* ------------------------------------------------------------------ lower level */
static u64 *lrbuf, *lrbuf2; static size_t lrcap, lrst[24], lrcap2, lrst2[24]; static int lr_v = -1, lr_w1 = -1;
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
    if (LAZY == 3) {                                                              /* genB6: lower walks are level-2 walks */
        int w1 = pre_find(pre2, nw1, w), a2 = w - pre2[w1], v = pre_find(pre1, nst, w1), a1 = w1 - pre1[v];
        if (v != lr_v) { int no = ptransport(wrow_sh + wstart_sh[v], wstart_sh[v + 1] - wstart_sh[v], KP, &lrbuf, &lrcap, lrst);
                         if (no != pre1[v + 1] - pre1[v]) DIE("stored walk %d: %d orbits", v, no); lr_v = v; lr_w1 = -1; }
        if (w1 != lr_w1) { int no = ptransport(lrbuf + lrst[a1], lrst[a1 + 1] - lrst[a1], KP + 1, &lrbuf2, &lrcap2, lrst2);
                           if (no != pre2[w1 + 1] - pre2[w1]) DIE("level-1 walk %d: %d orbits", w1, no); lr_w1 = w1; }
        const u64 *r = lrbuf2 + lrst2[a2]; *m = lrst2[a2 + 1] - lrst2[a2]; *Kl = KP + 2; *first = pre3[w];
        *g = pre3[w + 1] - pre3[w]; return r;
    }
    DIE("lift needs GEN17_LAZY >= 1"); return NULL;
}
/* constB mode liftB (L = 4, lower plan = C's n = 15 plan): as in liftB.c */
static int liftB_mode; static char *segdone; static int nseg; static int segk[2000], segg[2000][3];
static void read_order(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) DIE("cannot open order %s", path);
    char line[256]; nseg = 0; int nd = 0, nwb = 0; static char sd_[10][11][12]; char sw[64] = {0};
    int totw = 0; for (int k = 0; k < nbw; k++) totw += pre1[bst0 + k + 1] - pre1[bst0 + k];
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#' || line[0] == '\n' || line[0] == '\r') continue;
        int a, b, c; if (nseg == 2000) DIE("order: too long");
        if (sscanf(line, "D %d %d %d", &a, &b, &c) == 3) {
            if (a < 0 || a > 9 || b < 0 || b > 10 || c < 0 || c > 11 || !rowless[a][b][c] || sd_[a][b][c]++) DIE("order: bad D line %s", line);
            segk[nseg] = -1; segg[nseg][0] = a; segg[nseg][1] = b; segg[nseg][2] = c; nseg++; nd++;
        } else if (sscanf(line, "W %d", &a) == 1) {
            if (a < 0 || a >= totw || sw[a]++) DIE("order: bad W line %s", line);
            segk[nseg++] = a; nwb++;
        } else DIE("order: bad line %s", line);
    }
    fclose(f);
    if (nd != nrowless || nwb != totw) DIE("order: %d D and %d W lines, expected %d and %d", nd, nwb, nrowless, totw);
}
static int blockwalk(int d, int b) {
    for (int k = 0; k < nbw; k++) { int v = bst0 + d * nbw + k, g = pre1[v + 1] - pre1[v]; if (b < g) return pre1[v] + b; b -= g; }
    DIE("blockwalk %d", b); return -1;
}
static void emit_segment(int d, u32 *src) {
    if (nseg) {
        for (int i = 0; i < nseg; i++) {
            Unit u; memset(&u, 0, sizeof u); u.src = (*src)++;
            if (segk[i] < 0) { u.a = d; for (int l = 0; l < 3; l++) u.g |= (u32)segg[i][l] << (4 * l); }
            else { u.g = UW; u.a = blockwalk(d, segk[i]); }
            U[NU++] = u;
        }
    } else {
        int totw = 0; for (int k = 0; k < nbw; k++) totw += pre1[bst0 + d * nbw + k + 1] - pre1[bst0 + d * nbw + k];
        for (int b = 0; b < totw; b++) { Unit u; memset(&u, 0, sizeof u); u.src = (*src)++; u.g = UW; u.a = blockwalk(d, b); U[NU++] = u; }
    }
}
static void read_lower(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) DIE("cannot open %s", path);
    char line[512], hdr[32]; u64 nl = 0; sprintf(hdr, "N%d-UNITPLAN", NN - 1);
    u32 src = 0; int h1 = (NN - 1) - 3, L1 = L - 1;
    while (fgets(line, sizeof line, f)) {
        nl++;
        if (nl == 1) { if (strncmp(line, hdr, strlen(hdr))) DIE("not an n = %d unit plan", NN - 1); continue; }
        if (line[0] == '#' || line[0] == '\n' || line[0] == '\r') continue;
        char *tok[16]; int nt = 0; char *sv = NULL;
        for (char *t = strtok_r(line, " \t\r\n", &sv); t && nt < 16; t = strtok_r(NULL, " \t\r\n", &sv)) tok[nt++] = t;
        if (nt && tok[nt - 1][0] == 'o') nt--;
        if (tok[0][0] == 'D') {
            if (nt != 2 + L1) DIE("D line %llu", (unsigned long long)nl);
            int d = atoi(tok[1]), j = atoi(tok[nt - 1]), g[6] = {0};
            for (int l = 0; l < L1 - 1; l++) g[l] = atoi(tok[2 + l]);
            if (liftB_mode) {
                if (!segdone[d]) { segdone[d] = 1; emit_segment(d, &src); }
                if (nseg) { src++; continue; }
            }
            for (int i = 0; i < h1; i++) {
                Unit u; memset(&u, 0, sizeof u); u.a = d; g[L1 - 1] = (j + i) % h1;
                if (liftB_mode && !rowless[g[0]][g[1]][g[2]]) continue;
                for (int l = 0; l < L1; l++) u.g |= (u32)g[l] << (4 * l);
                u.src = src; U[NU++] = u;
            }
            src++;
        } else if (tok[0][0] == 'W' && nt == 4) {
            int w = atoi(tok[1]), way = atoi(tok[3]); u64 i0 = strtoull(tok[2], NULL, 10);
            u64 m; int Kl, first, g; const u64 *lr = low_rows(w, &m, &Kl, &first, &g);
            int H = Kl - 1;
            if (i0 >= m || rty(lr[i0])) DIE("W line %llu: not a full row", (unsigned long long)nl);
            if (H != h1) DIE("lower H %d, h %d", H, h1);
            int dlt = 0; for (u64 r = i0; r < m; r++) dlt = (dlt + (rty(lr[r]) == 0 ? -1 : 1) + H) % H;   /* n18: the port shift to row 0 does not depend on the port */
            for (int i = 0; i < h1; i++) {
                int q = way == 0 ? i : i + 1, port = q == Kl - 1 ? 0 : q;
                int p = (port + dlt) % H;
                Unit u; memset(&u, 0, sizeof u); u.g = UW; u.a = first + p % g; u.src = src; U[NU++] = u;
            }
            src++;
        } else DIE("bad line %llu", (unsigned long long)nl);
        if (nl % 10000000 == 0) fprintf(stderr, "  lower line %llu, units %u (%.0fs)\n", (unsigned long long)nl, NU, wall() - t0g);
    }
    fclose(f);
}

/* ------------------------------------------------------------------ threads over chunks */
static u32 CH = 1u << 17, NCH; static volatile long next_chunk = 0, chunks_done = 0; static pthread_mutex_t mx = PTHREAD_MUTEX_INITIALIZER;
static u32 *copt; static u64 *cfirst, *clast; static Ctx *ctxs;
static void *worker(void *arg) {
    Ctx *c = (Ctx *)arg; gs_new();
    for (;;) {
        long k = __atomic_fetch_add(&next_chunk, 1, __ATOMIC_SEQ_CST);
        if (k >= (long)NCH) break;
        u64 a0 = (u64)k * CH, a1 = a0 + CH < NU ? a0 + CH : NU; u32 u0 = (u32)a0, u1 = (u32)a1;
        copt[k] = dp_chunk(c, u0, u1, &cfirst[k], &clast[k]);
        long d = __atomic_add_fetch(&chunks_done, 1, __ATOMIC_SEQ_CST);
        if (d % 64 == 0 || d == (long)NCH) { pthread_mutex_lock(&mx); fprintf(stderr, "  chunks %ld/%u (%.0fs)\n", d, NCH, wall() - t0g); pthread_mutex_unlock(&mx); }
    }
    return NULL;
}
static int overlap_keys(u64 E, u64 S) { for (int q = HH; q >= 1; q--) if ((E & ((1ULL << (4 * q)) - 1)) == (S >> (4 * (HH - q)))) return q; return 0; }

int main(int argc, char **argv) {
    if (argc < 6 || (strcmp(argv[1], "lift") && strcmp(argv[1], "liftB"))) { fprintf(stderr, "usage: liftB6 lift|liftB L SEL PLAN(n-1) OUT.uplan [--threads T] [--chunk C]   (env GENB_BLOCK, LIFTB_ORDER)\n"); return 2; }
    liftB_mode = !strcmp(argv[1], "liftB");
    int T = 1;
    for (int ai = 6; ai < argc; ai++) {
        if (!strcmp(argv[ai], "--threads") && ai + 1 < argc) T = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "--chunk") && ai + 1 < argc) CH = (u32)strtoul(argv[++ai], NULL, 10);
        else DIE("unknown option %s", argv[ai]);
    }
    if (T < 1 || T > 64 || CH < 1) DIE("bad --threads / --chunk");
    t0g = wall(); gs_new();
    L = atoi(argv[2]); if (L < 2 || L > 6) DIE("L must be 2..6");
    NN = 12 + L; K = 10 + L; HH = NN - 3; SL = K; ZL = K + 1;
    read_sel(argv[3]); build_walks();
    if (!LAZY) DIE("the lift needs GEN17_LAZY >= 1 (L >= 4, or the variable)");
    if (liftB_mode) { if (!blockp || L != 4) DIE("liftB needs GENB_BLOCK and L = 4"); segdone = calloc(ndet, 1); const char *op = getenv("LIFTB_ORDER"); if (op && *op) read_order(op); }
    u64 nsu = n_small_units(), nsp = small_id_space();
    u64 ucap = nsu + (u64)nwl + 16;
    if (ucap > 0xffffffffULL) DIE("too many units");
    U = malloc(sizeof(Unit) * ucap); if (!U) DIE("oom (units)"); NU = 0;
    read_lower(argv[4]);
    fprintf(stderr, "lower plan read: %u units (%.0fs)\n", NU, wall() - t0g);
    int partial = getenv("LIFTB6_PARTIAL") && *getenv("LIFTB6_PARTIAL") == '1';   /* a prefix of a lower plan (tests): no count check, LENGTH meaningless */
    if (!partial && (u64)NU != nsu + (u64)nwl) DIE("plan has %u units, expected %llu", NU, (unsigned long long)(nsu + nwl));
    {   u64 nb = (nsp + (u64)nwl) / 8 + 1; u8 *seen = calloc(nb, 1); if (!seen) DIE("oom (seen)");
        for (u32 i = 0; i < NU; i++) {
            u64 id;
            if (!uwalk(&U[i])) { int g[6] = {0}; for (int l = 0; l < L - 1; l++) g[l] = ug(&U[i], l); if (!dunit_ok(g)) DIE("unit %u: its loop has a row of the block", i); id = small_id((int)U[i].a, g); }
            else id = nsp + U[i].a;
            if (id >= nsp + nwl || (seen[id >> 3] >> (id & 7) & 1)) DIE("unit %u repeated or out of range", i);
            seen[id >> 3] |= (u8)(1u << (id & 7));
        }
        free(seen); }
    fprintf(stderr, "units %u, each once (%.0fs)\n", NU, wall() - t0g);
    OPEN = malloc(4 * (size_t)NU); if (!OPEN) DIE("oom (openings)");
    NCH = (u32)(((u64)NU + CH - 1) / CH);
    copt = calloc(NCH, 4); cfirst = calloc(NCH, 8); clast = calloc(NCH, 8); ctxs = calloc(T, sizeof(Ctx));
    if (!copt || !cfirst || !clast || !ctxs) DIE("oom");
    fprintf(stderr, "DP: %u chunks of %u units, %d threads\n", NCH, CH, T);
    pthread_t th[64]; for (int t = 0; t < T; t++) pthread_create(&th[t], NULL, worker, &ctxs[t]);
    for (int t = 0; t < T; t++) pthread_join(th[t], NULL);
    double tdp = wall() - t0g;
    u64 inner = 0, between = 0, hist[17] = {0}, ccount[8] = {0}, ccost[8] = {0};
    for (u32 k = 0; k < NCH; k++) inner += copt[k];
    for (u32 k = 1; k < NCH; k++) { int ov = overlap_keys(clast[k - 1], cfirst[k]); between += HH - ov; hist[HH - ov]++;
        const Unit *ua = &U[(u64)k * CH - 1], *ub = &U[(u64)k * CH]; int cl = (ua->src == ub->src ? 0 : 4) + uwalk(ua) * 2 + uwalk(ub); ccount[cl]++; ccost[cl] += HH - ov; }
    for (int t = 0; t < T; t++) { for (int q = 0; q <= 16; q++) hist[q] += ctxs[t].hist[q]; for (int c = 0; c < 8; c++) { ccount[c] += ctxs[t].ccount[c]; ccost[c] += ctxs[t].ccost[c]; } }
    u64 hsum = 0, ncands = 0; for (int q = 0; q <= 16; q++) hsum += hist[q] * (u64)q; for (int t = 0; t < T; t++) ncands += ctxs[t].ncands;
    if (hsum != inner + between) DIE("join total %llu from the choices, %llu + %llu from the DP", (unsigned long long)hsum, (unsigned long long)inner, (unsigned long long)between);
    /* the plan */
    long nS = 0, nW = 0;
    FILE *o = fopen(argv[5], "w"); if (!o) DIE("cannot write %s", argv[5]);
    setvbuf(o, NULL, _IOFBF, 1 << 22);
    fprintf(o, "N%d-UNITPLAN 1\n# units in the order of the trails of %s, openings by liftB6 dp (%u chunks of %u units)\n", NN, argv[4], NCH, CH);
    for (u32 ui = 0; ui < NU; ui++) {
        if (!uwalk(&U[ui])) { fprintf(o, "D %u", U[ui].a); for (int l = 0; l < L - 1; l++) fprintf(o, " %d", ug(&U[ui], l)); fprintf(o, " %u\n", OPEN[ui]); nS++; }
        else { fprintf(o, "W %u %u %u\n", U[ui].a, OPEN[ui] >> 1, OPEN[ui] & 1); nW++; }
    }
    if (fclose(o)) DIE("write failed");
    u64 sumR = 0; { u64 fact[21]; fact[0] = 1; for (int i = 1; i < 21; i++) fact[i] = fact[i - 1] * i; sumR = fact[NN] + fact[NN - 1] + fact[NN - 2] + Qall; }
    u64 len = sumR + HH + (u64)(HH - 1) * nS + (u64)HH * nW + inner + between;
    fprintf(stderr, "units %u (small %ld, walk %ld); joins %llu (sum of h - overlap); join costs:", NU, nS, nW, (unsigned long long)(inner + between));
    for (int q = 0; q <= HH; q++) if (hist[q]) fprintf(stderr, " %d:%llu", q, (unsigned long long)hist[q]);
    fprintf(stderr, "\nclasses (same lower unit/other; D/W -> D/W): count cost:");
    for (int c = 0; c < 8; c++) fprintf(stderr, " %d:%llu/%llu", c, (unsigned long long)ccount[c], (unsigned long long)ccost[c]);
    fprintf(stderr, "\nCHUNKS %u\nINNER %llu\nBETWEEN %llu (the plan is at most this much above the exact optimum of liftB)\nLENGTH %llu\n",
            NCH, (unsigned long long)inner, (unsigned long long)between, (unsigned long long)len);
    fprintf(stderr, "CANDIDATES %llu\n(DP %.0fs, total %.0fs)\n", (unsigned long long)ncands, tdp, wall() - t0g);
    return 0;
}
