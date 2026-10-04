/* trailsearch.c - trail-level re-joining of a Pantone-type superpermutation word (C port of connector_splice.py).

   Model (see connector_splice.py): the word is a sequence of closed trails T (cyclic words of length R_T), each
   written once.  Opening T at the cut between consecutive permutation windows p_i -> p_{i+1} (gap g) writes a
   piece of R + n - g letters that starts with the h-word S (first h letters of window p_{i+1}) and ends with the
   h-word E (last h letters of window p_i), h = n - 3.  g = 3 costs nothing, g = 2 costs one letter.
   If window p_{i+1} is a duplicate (it occurs twice in the word) it may be skipped: cut from p_i to p_{i+2}.
   Joining piece A to piece B costs d(E_A, S_B) = h - (largest overlap of the two h-words).
       L = h + sum R_T + sum(opening costs) + sum_joins d.
   Search: destroy/repair with simulated-annealing acceptance (remove a few trails, reinsert each at its best
   position with its best opening; small trails may also be inserted as two segments wrapped around a block).

   Options are not stored as words: an option is (start offset in the cyclic word, gap, skip gap), 6 bytes, and
   S / E are read from the trail when needed (about 1.1 GB for 12 symbols, about 11 GB for 13).

   build: gcc -O2 -fopenmp -o trailsearch trailsearch.c -lm
   usage: trailsearch WORD.txt OUT.txt [--time SEC] [--seed S] [--kmax K] [--T0 TEMP] [--noskip] [--nosplit]
                      [--plan-in FILE] [--ckpt SEC] [--iters N] [--threads T] [--sync SEC] [--focus P] [--bigp P]
   With T threads, T independent searches share the model (temperatures 0.5..1.5 x TEMP); every SEC seconds the
   odd-numbered threads restart from the best sequence found so far.
   A trail is big if it has more than 3000 openings.  --focus P skips (with probability P) iterations that would
   move no big trail; --bigp P keeps a big trail in the removal set only with probability P.
   OUT.txt.plan lists the events of the best sequence (reload with --plan-in to continue). */
#if !defined(_WIN32)
#define _FILE_OFFSET_BITS 64
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <omp.h>
#if defined(_WIN32)
#define fseek64 _fseeki64
#define ftell64 _ftelli64
#else
#define fseek64 fseeko
#define ftell64 ftello
#endif

typedef long long i64;
typedef unsigned long long u64;
typedef unsigned int u32;

static const char *AL = "0123456789ABCDEF";
static unsigned char *W; static i64 L; static int n, h;
#define NL "\n"
#define DIE(...) do { fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); exit(1); } while (0)

/* ---------- h-words packed 4 bits per symbol (first symbol highest) */
static u64 HMASK[17];
static inline int dist(u64 e, u64 s) {            /* h - largest k with suffix_k(e) == prefix_k(s) */
    for (int k = h; k >= 1; k--) if ((e & HMASK[k]) == (s >> (4 * (h - k)))) return h - k;
    return h;
}

/* ---------- trails */
typedef struct { unsigned char *c; i64 R; i64 olo, ohi; int fixed; } Trail;   /* cyclic word, its length, option range */
/* fixed: an open path of R + h letters that is not a closed trail in the word; its pieces are never moved */
static Trail *TR; static i64 NT;
static inline u64 hw_lin(const unsigned char *p) { u64 v = 0; for (int k = 0; k < h; k++) v = (v << 4) | p[k]; return v; }
static inline u64 hw_cyc(const Trail *t, i64 pos) {   /* h-word at cyclic position pos */
    i64 R = t->R; while (pos >= R) pos -= R; while (pos < 0) pos += R;
    if (pos + h <= R) return hw_lin(t->c + pos);
    u64 v = 0; for (int k = 0; k < h; k++) v = (v << 4) | t->c[(pos + k) % R];
    return v;
}
static u64 fact[17];
static inline u64 rank_lin(const unsigned char *p) {
    u64 r = 0; int used = 0;
    for (int k = 0; k < n; k++) { int c = p[k]; r += (u64)(c - __builtin_popcount(used & ((1 << c) - 1))) * fact[n - 1 - k]; used |= 1 << c; }
    return r;
}
static inline u64 rank_cyc(const Trail *t, i64 pos) { /* rank of the permutation window at cyclic position pos */
    u64 r = 0; int used = 0; i64 R = t->R; pos %= R; if (pos < 0) pos += R;
    if (pos + n <= R) {
        const unsigned char *p = t->c + pos;
        for (int k = 0; k < n; k++) { int c = p[k]; r += (u64)(c - __builtin_popcount(used & ((1 << c) - 1))) * fact[n - 1 - k]; used |= 1 << c; }
    } else for (int k = 0; k < n; k++) { int c = t->c[(pos + k) % R]; r += (u64)(c - __builtin_popcount(used & ((1 << c) - 1))) * fact[n - 1 - k]; used |= 1 << c; }
    return r;
}

/* ---------- options: 6 bytes each */
typedef struct __attribute__((packed)) { u32 start; unsigned char g, g1; } Opt;
/* the piece starts at `start`; total gap g; g1 > 0: skip option, the skipped window lies g1 after the previous window.
   The options of a trail are contiguous (TR[t].olo .. ohi), so the trail of an option is found by binary search. */
static Opt *OP; static i64 NO;
static inline u32 otrail(i64 o) { i64 lo = 0, hi = NT - 1; while (lo < hi) { i64 m = (lo + hi + 1) >> 1; if (TR[m].olo <= o) lo = m; else hi = m - 1; } return (u32)lo; }
static inline int oD(i64 o) { return 3 - (int)OP[o].g; }
static inline u64 oS_t(const Trail *T, i64 o) { return hw_cyc(T, OP[o].start); }
static inline u64 oE_t(const Trail *T, i64 o) { return hw_cyc(T, (i64)OP[o].start - OP[o].g + 3); }
static inline i64 oSK_t(const Trail *T, i64 o) { return OP[o].g1 ? (i64)rank_cyc(T, (i64)OP[o].start - OP[o].g + OP[o].g1) : -1; }
static inline u64 oS(i64 o) { return oS_t(&TR[otrail(o)], o); }
static inline u64 oE(i64 o) { return oE_t(&TR[otrail(o)], o); }

/* ---------- events */
enum { EV_PIECE, EV_OPT, EV_SEG };
typedef struct { int kind; u32 t; u64 s, e; i64 l; i64 a; i64 skip; } Ev;
/* EV_PIECE: a = piece index.  EV_OPT: a = option.  EV_SEG: a = start offset in the trail, l letters. */
static i64 *PS, *PL; static i64 NP;      /* pieces of the input word */

static i64 seq_length(const Ev *ev, i64 N) {
    i64 len = 0; for (i64 i = 0; i < N; i++) len += ev[i].l;
    for (i64 i = 0; i + 1 < N; i++) len -= h - dist(ev[i].e, ev[i + 1].s);
    return len;
}
static Ev make_event(i64 o) {
    u32 t = otrail(o); const Trail *T = &TR[t];
    Ev x; x.kind = EV_OPT; x.t = t; x.s = oS_t(T, o); x.e = oE_t(T, o); x.l = T->R + h + oD(o); x.a = o; x.skip = oSK_t(T, o);
    return x;
}
static Ev piece_event(i64 k, i64 trail) {
    Ev x; x.kind = EV_PIECE; x.t = (u32)trail; x.s = hw_lin(W + PS[k]); x.e = hw_lin(W + PS[k] + PL[k] - h); x.l = PL[k]; x.a = k; x.skip = -1;
    return x;
}
/* two events for a trail split at plain cuts c1 (start of segment 1) and c2 (end of segment 1) */
static void seg_events(i64 c1, i64 c2, Ev *e1, Ev *e2) {
    u32 t = otrail(c1); i64 R = TR[t].R;
    i64 st1 = OP[c1].start, en1 = ((i64)OP[c2].start - OP[c2].g + R) % R, l1 = ((en1 - st1) % R + R) % R + n;
    i64 st2 = OP[c2].start, en2 = ((i64)OP[c1].start - OP[c1].g + R) % R, l2 = ((en2 - st2) % R + R) % R + n;
    e1->kind = EV_SEG; e1->t = t; e1->s = oS(c1); e1->e = oE(c2); e1->l = l1; e1->a = st1; e1->skip = -1;
    e2->kind = EV_SEG; e2->t = t; e2->s = oS(c2); e2->e = oE(c1); e2->l = l2; e2->a = st2; e2->skip = -1;
}

/* ---------- output */
static void write_word(const Ev *ev, i64 N, const char *path, i64 expect) {
    FILE *f = fopen(path, "wb"); if (!f) DIE("cannot write %s", path);
    size_t cap = 1 << 22, ob = 0; char *out = malloc(cap); i64 total = 0; u64 tail = 0;
    for (i64 i = 0; i < N; i++) {
        const Ev *x = &ev[i];
        i64 skip = i ? h - dist(tail, x->s) : 0;
        for (i64 r = skip; r < x->l; r++) {
            unsigned char c;
            if (x->kind == EV_PIECE) c = W[PS[x->a] + r];
            else { const Trail *t = &TR[x->t]; i64 st = x->kind == EV_OPT ? (i64)OP[x->a].start : x->a; c = t->c[(st + r) % t->R]; }
            out[ob++] = AL[c]; if (ob == cap) { fwrite(out, 1, ob, f); ob = 0; }
        }
        total += x->l - skip; tail = x->e;
    }
    out[ob++] = '\n'; fwrite(out, 1, ob, f); fclose(f); free(out);
    if (total != expect) DIE("internal error: wrote %lld letters, model says %lld", total, expect);
}
static void write_plan(const Ev *ev, i64 N, const char *path) {
    FILE *f = fopen(path, "w"); if (!f) DIE("cannot write %s", path);
    fprintf(f, "TRAILSEARCH-PLAN %d %lld %lld\n", n, L, N);
    for (i64 i = 0; i < N; i++) {
        const Ev *x = &ev[i];
        if (x->kind == EV_PIECE) fprintf(f, "P %lld\n", x->a);
        else if (x->kind == EV_OPT) fprintf(f, "O %u %u %d %d\n", x->t, OP[x->a].start, OP[x->a].g, OP[x->a].g1);
        else fprintf(f, "S %u %lld %lld\n", x->t, x->a, x->l);
    }
    fclose(f);
}

/* ---------- hash multimap: key -> list of ints */
typedef struct { u64 key; int head; } Slot;
typedef struct { Slot *t; u64 mask; int *next, *val; i64 n, cap; } HTab;
static inline u64 hmix(u64 k) { k ^= k >> 33; k *= 0xFF51AFD7ED558CCDULL; k ^= k >> 33; k *= 0xC4CEB9FE1A85EC53ULL; k ^= k >> 33; return k; }
#define HKEY(word, j, kind) (((u64)(word) << 8) | ((u64)(j) << 4) | (u64)(kind))   /* word < 2^40 */
static void h_reset(HTab *H, i64 entries) {
    u64 need = 1024; while (need < (u64)entries + (u64)entries / 2 + 16) need <<= 1;
    if (!H->t || need - 1 != H->mask) { free(H->t); H->t = malloc(need * sizeof(Slot)); H->mask = need - 1; }
    for (u64 i = 0; i <= H->mask; i++) { H->t[i].head = -1; H->t[i].key = ~0ULL; }
    if (entries > H->cap) { H->cap = entries + entries / 2 + 64; free(H->next); free(H->val); H->next = malloc(H->cap * sizeof(int)); H->val = malloc(H->cap * sizeof(int)); }
    H->n = 0;
}
static inline void h_add(HTab *H, u64 key, int v) {
    u64 i = hmix(key) & H->mask;
    while (H->t[i].key != ~0ULL && H->t[i].key != key) i = (i + 1) & H->mask;
    H->t[i].key = key; H->next[H->n] = H->t[i].head; H->val[H->n] = v; H->t[i].head = (int)H->n++;
}
static inline int h_get(const HTab *H, u64 key) {
    u64 i = hmix(key) & H->mask;
    while (H->t[i].key != ~0ULL) { if (H->t[i].key == key) return H->t[i].head; i = (i + 1) & H->mask; }
    return -1;
}
#define KLEV 3            /* joins of cost <= KLEV are looked up */
#define ENT_PER 12        /* index entries per event */
static double tlimit = 600, T0 = 1.5, ckpt_sec = 600, prel = 0.4, sync_sec = 60;
static double bigp = 1.0;      /* probability of keeping a big trail (more than splitmax options) in the removal set */
static double focus = 0.0;    /* probability of skipping an iteration whose removal set has no big trail */
static int kmax = 6, use_skip = 1, use_split = 1, splitmax = 3000, NTHR = 1; static u64 seed = 1; static i64 maxit = -1;

/* ---------- one search thread: the sequence is a doubly linked list of nodes, so an insertion does not renumber
   anything and the hash index (word -> node) is only ever appended to; dead nodes are skipped at lookup and the
   index is rebuilt when it is mostly garbage.  A rejected move is undone by unlinking / relinking nodes. */
typedef struct { Ev v; int prev, next, alive; u64 lab; } Node;      /* lab: order label (increasing along the list) */
typedef struct { i64 c2; int i, jm; i64 cst; } Pair;
typedef struct {
    int tid; u64 rs[4];
    Node *nd; int ncap, nn, first, last; i64 N; int relabeled;
    HTab H, RELT; u64 *bf, bfmask;      /* bf: one-hash Bloom filter over the keys of H */
    int *order, *dj, *cand, *rid, *rs_, *re_, *rel, *remlog, *inslog; int nremlog, ninslog;
    i64 *skp; int nskp, skpcap;
    i64 *vid; int vcap; Pair *pr; i64 pcap; int *Ib, *Jb; int icap, jcap;
    char *rem; u32 *pend; Ev *tmp;
    i64 cur, best_len, it, acc;
} Ctx;

static inline u64 rotl(u64 x, int k) { return (x << k) | (x >> (64 - k)); }
static inline u64 rnd64(Ctx *c) {        /* xoshiro256** */
    u64 *s = c->rs, r = rotl(s[1] * 5, 7) * 9, t = s[1] << 17;
    s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = rotl(s[3], 45);
    return r;
}
static void rseed(Ctx *c, u64 s) { for (int i = 0; i < 4; i++) { s += 0x9E3779B97F4A7C15ULL; u64 z = s; z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; c->rs[i] = z ^ (z >> 31); } }
static inline double rndu(Ctx *c) { return (rnd64(c) >> 11) * (1.0 / 9007199254740992.0); }
static inline i64 rndn(Ctx *c, i64 m) { return (i64)(rnd64(c) % (u64)m); }          /* 0 .. m-1 */
static inline i64 rndint(Ctx *c, i64 a, i64 b) { return a + rndn(c, b - a + 1); }   /* a .. b */

/* index kinds: 0 = suffix (length h-j) of e, 1 = prefix (length h-j) of s, 2 / 3 = the lookups of best_split */
#define BFH(key) (((u64)(key) * 0x9E3779B97F4A7C15ULL) >> 32)
#define BFBIT(c, key) { u64 b_ = BFH(key) & (c)->bfmask; (c)->bf[b_ >> 6] |= 1ULL << (b_ & 63); }
static inline int bf_has(const Ctx *c, u64 key) { u64 b = BFH(key) & c->bfmask; return (int)((c->bf[b >> 6] >> (b & 63)) & 1); }
static inline void index_add(Ctx *c, int id) {
    const Ev *x = &c->nd[id].v;
    for (int j = 0; j <= KLEV; j++) {
        u64 k0 = HKEY(x->e & HMASK[h - j], j, 0), k1 = HKEY(x->s >> (4 * j), j, 1);
        h_add(&c->H, k0, id); h_add(&c->H, k1, id); BFBIT(c, k0); BFBIT(c, k1);
    }
    if (use_split) { h_add(&c->H, HKEY(x->s, 0, 2), id); h_add(&c->H, HKEY(x->s >> 4, 1, 2), id); h_add(&c->H, HKEY(x->e, 0, 3), id); h_add(&c->H, HKEY(x->e & HMASK[h - 1], 1, 3), id); }
}
static void ctx_load(Ctx *c, const Ev *ev, i64 N) {
    int need = (int)(4 * N + 65536), self = ev == c->tmp;
    if (need > c->ncap) {
        c->ncap = need; c->nd = realloc(c->nd, (size_t)need * sizeof(Node));
        int **arr[] = {&c->order, &c->dj, &c->cand, &c->rid, &c->rs_, &c->re_, &c->rel, &c->remlog, &c->inslog};
        for (int k = 0; k < 9; k++) *arr[k] = realloc(*arr[k], (size_t)need * sizeof(int));
        c->tmp = realloc(c->tmp, (size_t)need * sizeof(Ev)); if (self) ev = c->tmp;
        if (!c->nd || !c->inslog || !c->tmp) DIE("out of memory");
    }
    c->nn = (int)N; c->N = N; c->first = 0; c->last = (int)N - 1;
    for (i64 i = 0; i < N; i++) { Node *q = &c->nd[i]; q->v = ev[i]; q->prev = (int)i - 1; q->next = i + 1 < N ? (int)i + 1 : -1; q->alive = 1; q->lab = (u64)(i + 1) << 32; }
    i64 ecap = (N > 100000 ? 2 : 4) * ENT_PER * N + 65536;      /* live entries plus head-room for dead ones */
    h_reset(&c->H, ecap);
    { u64 bits = 1 << 16; while (bits < (u64)ecap * 16) bits <<= 1;
      if (bits - 1 != c->bfmask || !c->bf) { free(c->bf); c->bf = malloc(bits / 8); c->bfmask = bits - 1; }
      memset(c->bf, 0, bits / 8); }
    for (i64 i = 0; i < N; i++) index_add(c, (int)i);
}
static i64 ctx_export(const Ctx *c, Ev *out) { i64 m = 0; for (int id = c->first; id >= 0; id = c->nd[id].next) out[m++] = c->nd[id].v; return m; }
static i64 ctx_length(const Ctx *c) {
    i64 len = 0;
    for (int id = c->first; id >= 0; ) { const Node *q = &c->nd[id]; len += q->v.l; if (q->next >= 0) len -= h - dist(q->v.e, c->nd[q->next].v.s); id = q->next; }
    return len;
}
static void relabel(Ctx *c) { u64 k = 1; for (int id = c->first; id >= 0; id = c->nd[id].next) c->nd[id].lab = (k++) << 32; c->relabeled = 1; }
static void node_unlink(Ctx *c, int id) {
    Node *q = &c->nd[id];
    if (q->prev >= 0) c->nd[q->prev].next = q->next; else c->first = q->next;
    if (q->next >= 0) c->nd[q->next].prev = q->prev; else c->last = q->prev;
    q->alive = 0; c->N--;
}
static void node_relink(Ctx *c, int id) {
    Node *q = &c->nd[id];
    if (q->prev >= 0) c->nd[q->prev].next = id; else c->first = id;
    if (q->next >= 0) c->nd[q->next].prev = id; else c->last = id;
    q->alive = 1; c->N++;
}
static int node_insert_after(Ctx *c, int a, const Ev *x) {
    int b = c->nd[a].next;
    u64 la = c->nd[a].lab, lb = b >= 0 ? c->nd[b].lab : la + (1ULL << 33);
    if (lb - la < 2) { relabel(c); la = c->nd[a].lab; lb = b >= 0 ? c->nd[b].lab : la + (1ULL << 33); }
    int id = c->nn++; Node *q = &c->nd[id];
    q->v = *x; q->prev = a; q->next = b; q->alive = 1; q->lab = la + (lb - la) / 2;
    c->nd[a].next = id; if (b >= 0) c->nd[b].prev = id; else c->last = id;
    index_add(c, id); c->inslog[c->ninslog++] = id; c->N++;
    return id;
}
static int skp_has(const Ctx *c, i64 r) { for (int i = 0; i < c->nskp; i++) if (c->skp[i] == r) return 1; return 0; }
static void skp_add(Ctx *c, i64 r) { if (c->nskp == c->skpcap) { c->skpcap = c->skpcap ? c->skpcap * 2 : 256; c->skp = realloc(c->skp, c->skpcap * sizeof(i64)); } c->skp[c->nskp++] = r; }

/* ---------- best insertion of trail t: insert after node `after` */
typedef struct { double val; i64 delta; int after; i64 opt; } Ins;
static Ins best_insertion(Ctx *c, u32 t, double noise) {
    Ins best; best.val = 1e18; best.delta = 0; best.after = -1; best.opt = -1;
    const Trail *T = &TR[t]; const Node *nd = c->nd; const HTab *H = &c->H;
    /* options are processed in batches so that the filter words of a whole batch are prefetched before they are tested */
    enum { BATCH = 16, NK = 2 * (KLEV + 1) };
    for (i64 o0 = T->olo; o0 < T->ohi; o0 += BATCH) {
        int m = (int)(T->ohi - o0 < BATCH ? T->ohi - o0 : BATCH);
        u64 Sb[BATCH], Eb[BATCH], key[BATCH][NK], bit[BATCH][NK];
        for (int q = 0; q < m; q++) {
            u64 S = oS_t(T, o0 + q), E = oE_t(T, o0 + q); Sb[q] = S; Eb[q] = E;
            for (int j = 0; j <= KLEV; j++) { key[q][2 * j] = HKEY(S >> (4 * j), j, 0); key[q][2 * j + 1] = HKEY(E & HMASK[h - j], j, 1); }
            for (int k = 0; k < NK; k++) { bit[q][k] = BFH(key[q][k]) & c->bfmask; __builtin_prefetch(&c->bf[bit[q][k] >> 6]); }
        }
        for (int q = 0; q < m; q++) {
            i64 o = o0 + q; u64 S = Sb[q], E = Eb[q]; int D = oD(o), skchecked = 0, skbad = 0;
            for (int k = 0; k < NK && !skbad; k++) {
                if (!((c->bf[bit[q][k] >> 6] >> (bit[q][k] & 63)) & 1)) continue;
                for (int e = h_get(H, key[q][k]); e >= 0; e = H->next[e]) {
                    int x = H->val[e], a, b2;
                    if (!nd[x].alive) continue;
                    if (!(k & 1)) { a = x; b2 = nd[x].next; } else { b2 = x; a = nd[x].prev; }
                    if (a < 0 || b2 < 0) continue;
                    if (!skchecked) { skchecked = 1; if (OP[o].g1 && c->nskp && skp_has(c, oSK_t(T, o))) { skbad = 1; break; } }
                    i64 d = dist(nd[a].v.e, S) + D + dist(E, nd[b2].v.s) - dist(nd[a].v.e, nd[b2].v.s);
                    double v = (double)d + (noise > 0 ? noise * rndu(c) : 0.0);
                    if (v < best.val) { best.val = v; best.delta = d; best.after = a; best.opt = o; }
                }
            }
        }
    }
    if (best.after < 0) {                    /* nothing overlaps: append with the cheapest opening */
        i64 k = T->olo; for (i64 o = T->olo; o < T->ohi; o++) if (oD(o) < oD(k)) k = o;
        best.delta = dist(nd[c->last].v.e, oS_t(T, k)) + oD(k); best.val = (double)best.delta; best.after = c->last; best.opt = k;
    }
    return best;
}

/* ---------- insertion of a small trail as two segments wrapped around a block i .. jm of the sequence:
   ..., prev(i), seg1, i, ..., jm, seg2, next(jm), ...   seg1 ends and seg2 starts at a vertex v of t (plain gap-3
   cut c2); seg1 starts and seg2 ends at any plain cut c1 */
typedef struct { int ok; i64 delta; int i, jm; i64 c1, c2; } Split;
static int pair_cmp(const void *a, const void *b) { i64 x = ((const Pair *)a)->cst, y = ((const Pair *)b)->cst; return x < y ? -1 : x > y; }
static Split best_split(Ctx *c, u32 t, int maxv) {
    Split r; r.ok = 0;
    const Trail *T = &TR[t]; const Node *nd = c->nd; const HTab *H = &c->H;
    int nv = 0;
    for (i64 o = T->olo; o < T->ohi; o++) if (OP[o].g == 3 && !OP[o].g1) { if (nv == c->vcap) { c->vcap = c->vcap ? c->vcap * 2 : 1024; c->vid = realloc(c->vid, c->vcap * sizeof(i64)); } c->vid[nv++] = o; }
    if (nv > maxv) { for (int k = 0; k < maxv; k++) { int m = k + (int)rndn(c, nv - k); i64 x = c->vid[k]; c->vid[k] = c->vid[m]; c->vid[m] = x; } nv = maxv; }
    i64 np = 0;
    for (int a = 0; a < nv; a++) {
        i64 c2 = c->vid[a]; u64 v = oS_t(T, c2);
        int ni = 0, nj = 0;     /* I: inner nodes i with d(v, s_i) <= 1;  J: nodes jm (not the last) with d(e_jm, v) <= 1 */
        for (int lev = 0; lev <= 1; lev++)
            for (int q = h_get(H, HKEY(v & HMASK[h - lev], lev, 2)); q >= 0; q = H->next[q]) {
                int x = H->val[q]; if (!nd[x].alive || nd[x].prev < 0 || nd[x].next < 0) continue;
                if (ni == c->icap) { c->icap = c->icap ? c->icap * 2 : 1024; c->Ib = realloc(c->Ib, c->icap * sizeof(int)); }
                c->Ib[ni++] = x;
            }
        if (!ni) continue;
        for (int lev = 0; lev <= 1; lev++)
            for (int q = h_get(H, HKEY(v >> (4 * lev), lev, 3)); q >= 0; q = H->next[q]) {
                int x = H->val[q]; if (!nd[x].alive || nd[x].next < 0) continue;
                if (nj == c->jcap) { c->jcap = c->jcap ? c->jcap * 2 : 1024; c->Jb = realloc(c->Jb, c->jcap * sizeof(int)); }
                c->Jb[nj++] = x;
            }
        if (!nj) continue;
        for (int x = 0; x < ni; x++) {
            int i = c->Ib[x]; int dvi = dist(v, nd[i].v.s);
            for (int y = 0; y < nj; y++) {
                int jm = c->Jb[y]; if (nd[jm].lab < nd[i].lab) continue;
                i64 cst = dvi + dist(nd[jm].v.e, v) - dist(nd[nd[i].prev].v.e, nd[i].v.s) - dist(nd[jm].v.e, nd[nd[jm].next].v.s);
                if (np == c->pcap) { c->pcap = c->pcap ? c->pcap * 2 : 4096; c->pr = realloc(c->pr, c->pcap * sizeof(Pair)); }
                c->pr[np].c2 = c2; c->pr[np].i = i; c->pr[np].jm = jm; c->pr[np].cst = cst; np++;
            }
        }
    }
    if (!np) return r;
    qsort(c->pr, (size_t)np, sizeof(Pair), pair_cmp);
    if (np > 64) np = 64;
    i64 bd = 1LL << 40, bk = -1, bc1 = -1;
    for (i64 k = 0; k < np; k++) {
        u64 ep = nd[nd[c->pr[k].i].prev].v.e, sn = nd[nd[c->pr[k].jm].next].v.s;
        for (i64 o = T->olo; o < T->ohi; o++) {
            i64 d = dist(ep, oS_t(T, o)) + oD(o) + dist(oE_t(T, o), sn) + c->pr[k].cst;
            if (d < bd) { bd = d; bk = k; bc1 = o; }
        }
    }
    if (bk < 0 || bc1 == c->pr[bk].c2 || OP[bc1].g1) return r;
    r.ok = 1; r.delta = bd; r.i = c->pr[bk].i; r.jm = c->pr[bk].jm; r.c1 = bc1; r.c2 = c->pr[bk].c2;
    return r;
}

/* ---------- what the sequence looks like: openings by kind, joins by cost, runs (maximal chains of joins of cost <= 1) */
static void print_stats(const Ev *ev, i64 N) {
    i64 g2 = 0, g1 = 0, skips = 0, segs = 0, pieces = 0, hist[17] = {0}, runs = 1, inter = 0, inrun = 0, extra = 0;
    for (i64 i = 0; i < N; i++) {
        if (ev[i].kind == EV_SEG) segs++;
        else if (ev[i].kind == EV_PIECE) pieces++;
        else { int g = OP[ev[i].a].g; if (OP[ev[i].a].g1) skips++; else if (g == 2) g2++; else if (g == 1) g1++; }
        if (i + 1 < N) { int d = dist(ev[i].e, ev[i + 1].s); hist[d]++; if (d >= 2) { runs++; inter += d; } else inrun += d; }
    }
    i64 sumR = 0; for (i64 t = 0; t < NT; t++) sumR += TR[t].R;
    extra = seq_length(ev, N) - h - sumR - inter - inrun;
    printf("stats: events %lld (unchanged pieces %lld, segments %lld), gap-2 openings %lld, gap-1 openings %lld, duplicate-skip openings %lld, opening cost %lld" NL, N, pieces, segs, g2, g1, skips, extra);
    printf("stats: runs %lld, join cost between runs %lld, joins inside runs cost %lld; joins by cost:", runs, inter, inrun);
    for (int d = 0; d <= h; d++) if (hist[d]) printf(" %d:%lld", d, hist[d]);
    printf(NL); fflush(stdout);
}

/* ---------- shared best sequence */
static Ev *G_ev; static i64 G_N, G_len; static int G_dirty; static double G_t0, G_last_ck, G_last_log; static i64 G_it[256];
static double wall(void);

static void search(Ctx *c, const Ev *init_ev, i64 initN, const char *outplan) {
    rseed(c, seed * 1000003ULL + (u64)c->tid * 7919ULL);
    c->rem = calloc((size_t)NT + 1, 1); c->pend = malloc(((size_t)NT + 1) * sizeof(u32));
    ctx_load(c, init_ev, initN);
    c->cur = ctx_length(c); c->best_len = c->cur;
    double tf = NTHR > 1 ? 0.5 + (double)c->tid / (NTHR - 1) : 1.0, last_sync = wall();
    int runcap = 2 * kmax + 2;      /* a run longer than this is not removed as a whole */
    Node *nd;
    while ((maxit < 0 || c->it < maxit) && wall() - G_t0 < tlimit) {
        c->it++;
        if (c->H.n > c->H.cap - 40000 || c->nn > c->ncap - 4000) { i64 m = ctx_export(c, c->tmp); ctx_load(c, c->tmp, m); }
        nd = c->nd;
        double frac = (wall() - G_t0) / tlimit, temp = tf * T0 * (1 - frac) + 0.05;
        int *order = c->order, *dj = c->dj, *cand = c->cand, *rs_ = c->rs_, *re_ = c->re_, *rid = c->rid, *rel = c->rel;
        i64 N = 0; for (int id = c->first; id >= 0; id = nd[id].next) order[N++] = id;
#define EVT(i) (nd[order[i]].v)
        i64 ncand = 0; for (i64 i = 0; i + 1 < N; i++) { dj[i] = dist(EVT(i).e, EVT(i + 1).s); if (dj[i] >= 2) cand[ncand++] = (int)i; }
        int k = (int)rndint(c, 1, kmax); i64 nrem = 0;
        double mode = rndu(c);
#define REMOVE(tt) do { u32 t_ = (tt); if (!c->rem[t_] && !TR[t_].fixed) { c->rem[t_] = 1; c->pend[nrem++] = t_; } } while (0)
        if (mode < prel) {
            /* a run plus one or two runs whose end / start words are within one step of an opening of its trails */
            int nrun = 0; rid[0] = 0; for (i64 i = 1; i < N; i++) { if (dj[i - 1] >= 2) nrun++; rid[i] = nrun; } nrun++;
            for (i64 i = 0; i < N; i++) { if (i == 0 || rid[i] != rid[i - 1]) rs_[rid[i]] = (int)i; re_[rid[i]] = (int)i; }
            int X = -1;
            if (rndu(c) < 0.7) { for (int tries = 0; tries < 50; tries++) { int r = (int)rndn(c, nrun); if (re_[r] - rs_[r] + 1 <= 5) { X = r; break; } } }
            if (X < 0) X = (int)rndn(c, nrun);
            i64 xlen = re_[X] - rs_[X] + 1;
            if (xlen > runcap) {                       /* long run: only a window of it */
                i64 lo = rs_[X] + rndn(c, xlen - k + 1 > 0 ? xlen - k + 1 : 1);
                for (i64 i = lo; i <= re_[X] && i < lo + k; i++) REMOVE(EVT(i).t);
            } else {
                i64 nopt = 0; for (int i = rs_[X]; i <= re_[X]; i++) nopt += TR[EVT(i).t].ohi - TR[EVT(i).t].olo;
                int nrel = 0;
                if (nopt <= 600000) {
                    h_reset(&c->RELT, nopt * 4 + 16);
                    for (int i = rs_[X]; i <= re_[X]; i++) for (i64 o = TR[EVT(i).t].olo; o < TR[EVT(i).t].ohi; o++) {
                        u64 S = oS_t(&TR[EVT(i).t], o), E = oE_t(&TR[EVT(i).t], o);
                        h_add(&c->RELT, HKEY(S, 0, 4), 0); h_add(&c->RELT, HKEY(S >> 4, 1, 4), 0); h_add(&c->RELT, HKEY(E, 0, 5), 0); h_add(&c->RELT, HKEY(E & HMASK[h - 1], 1, 5), 0);
                    }
                    for (int r = 0; r < nrun; r++) {
                        if (r == X || re_[r] - rs_[r] + 1 > runcap) continue;
                        u64 e_end = EVT(re_[r]).e, s_st = EVT(rs_[r]).s;
                        if (h_get(&c->RELT, HKEY(e_end, 0, 4)) >= 0 || h_get(&c->RELT, HKEY(e_end & HMASK[h - 1], 1, 4)) >= 0 || h_get(&c->RELT, HKEY(s_st, 0, 5)) >= 0 || h_get(&c->RELT, HKEY(s_st >> 4, 1, 5)) >= 0) rel[nrel++] = r;
                    }
                }
                for (int i = rs_[X]; i <= re_[X]; i++) REMOVE(EVT(i).t);
                int want = (int)rndint(c, 1, 2);
                for (int q = 0; q < want && nrel > 0; q++) { int z = (int)rndn(c, nrel), r = rel[z]; rel[z] = rel[--nrel]; for (int i = rs_[r]; i <= re_[r]; i++) REMOVE(EVT(i).t); }
            }
        } else if (mode < 0.5 + prel / 2) {
            i64 j = ncand ? cand[rndn(c, ncand)] : rndn(c, N - 1);
            i64 lo = j - rndint(c, 0, k); if (lo < 0) lo = 0;
            for (i64 i = lo; i < N && i < lo + k; i++) REMOVE(EVT(i).t);
        } else if (mode < 0.75) {
            for (int q = 0; q < k; q++) REMOVE(EVT(rndn(c, N)).t);
        } else {
            int segs = (int)rndint(c, 2, 3), len = k / 2 > 1 ? k / 2 : 1;
            for (int q = 0; q < segs; q++) { i64 j = rndn(c, N); for (i64 i = j; i < N && i < j + len; i++) REMOVE(EVT(i).t); }
        }
        i64 nbig = 0;
        { double bp = bigp; i64 m = 0;
          for (i64 q = 0; q < nrem; q++) {
              u32 t_ = c->pend[q]; int big = TR[t_].ohi - TR[t_].olo > splitmax;
              if (big && bp < 1.0 && rndu(c) >= bp) { c->rem[t_] = 0; continue; }
              nbig += big; c->pend[m++] = t_;
          }
          nrem = m; }
        if (!nrem) continue;
        if (!nbig && focus > 0 && rndu(c) < focus) { for (i64 q = 0; q < nrem; q++) c->rem[c->pend[q]] = 0; continue; }
        /* destroy */
        c->nremlog = c->ninslog = 0; c->relabeled = 0; c->nskp = 0;
        for (i64 i = 0; i < N; i++) {
            int id = order[i];
            if (c->rem[nd[id].v.t]) { node_unlink(c, id); c->remlog[c->nremlog++] = id; }
            else if (nd[id].v.skip >= 0) skp_add(c, nd[id].v.skip);
        }
        for (i64 q = 0; q < nrem; q++) c->rem[c->pend[q]] = 0;
        int accept = 0; i64 nl = 0;
        if (c->N >= 3) {
            /* repair */
            for (i64 q = nrem - 1; q > 0; q--) { i64 z = rndn(c, q + 1); u32 x = c->pend[q]; c->pend[q] = c->pend[z]; c->pend[z] = x; }
            int greedy = rndu(c) < 0.5; double noise = rndu(c) < 0.5 ? 0.0 : 0.6;
            i64 np = nrem;
            while (np > 0) {
                i64 pick = 0; Ins bi = best_insertion(c, c->pend[0], noise);
                if (greedy) {
                    double br = rndu(c);
                    for (i64 q = 1; q < np; q++) { Ins x = best_insertion(c, c->pend[q], noise); double rr = rndu(c); if (x.val < bi.val || (x.val == bi.val && rr < br)) { br = rr; bi = x; pick = q; } }
                }
                u32 t = c->pend[pick];
                Split sp; sp.ok = 0;
                if (use_split && TR[t].ohi - TR[t].olo <= splitmax) sp = best_split(c, t, 400);
                if (sp.ok && (double)sp.delta < bi.val) {
                    Ev e1, e2; seg_events(sp.c1, sp.c2, &e1, &e2);
                    node_insert_after(c, c->nd[sp.i].prev, &e1); node_insert_after(c, sp.jm, &e2);
                } else {
                    Ev x = make_event(bi.opt);
                    node_insert_after(c, bi.after, &x);
                    if (x.skip >= 0) skp_add(c, x.skip);
                }
                c->pend[pick] = c->pend[--np];
            }
            nl = ctx_length(c);
            i64 d = nl - c->cur;
            accept = d <= 0 || rndu(c) < exp(-(double)d / temp);
        }
        if (accept) {
            c->cur = nl; c->acc++;
            if (nl < c->best_len) {
                c->best_len = nl;
                #pragma omp critical(gbest)
                if (nl < G_len) {
                    printf("t=%.0fs: best %lld -> %lld (thread %d, it %lld, removed %lld trails, %lld big)\n", wall() - G_t0, G_len, nl, c->tid, c->it, nrem, nbig); fflush(stdout);
                    G_N = ctx_export(c, G_ev); G_len = nl; G_dirty = 1;
                }
            }
        } else {
            for (int q = c->ninslog - 1; q >= 0; q--) node_unlink(c, c->inslog[q]);
            for (int q = c->nremlog - 1; q >= 0; q--) node_relink(c, c->remlog[q]);
            if (c->relabeled) relabel(c);
        }
        if ((c->it & 63) == 0) {
            double tn = wall();
            if (tn - last_sync > sync_sec || (c->tid == 0 && tn - G_last_log > 20)) {
                int adopt = 0; i64 an = 0;
                #pragma omp critical(gbest)
                {
                    G_it[c->tid] = c->it;
                    if (tn - last_sync > sync_sec && (c->tid & 1) && G_len < c->best_len) { memcpy(c->tmp, G_ev, (size_t)G_N * sizeof(Ev)); an = G_N; adopt = 1; c->best_len = G_len; c->cur = G_len; }
                    if (c->tid == 0) {
                        if (G_dirty && tn - G_last_ck > ckpt_sec) { write_plan(G_ev, G_N, outplan); G_last_ck = tn; G_dirty = 0; }
                        if (tn - G_last_log > 20) { i64 tot = 0; for (int q = 0; q < NTHR; q++) tot += G_it[q]; printf("it %lld t=%.0fs best %lld (thread 0: cur %lld)\n", tot, tn - G_t0, G_len, c->cur); fflush(stdout); G_last_log = tn; }
                    }
                }
                if (tn - last_sync > sync_sec) last_sync = tn;
                if (adopt) ctx_load(c, c->tmp, an);
            }
        }
    }
    #pragma omp critical(gbest)
    G_it[c->tid] = c->it;
}

/* ---------- loading */
static unsigned char *load_word(const char *path, i64 *len) {
    FILE *f = fopen(path, "rb"); if (!f) DIE("cannot open %s", path);
    fseek64(f, 0, SEEK_END); i64 sz = ftell64(f); fseek64(f, 0, SEEK_SET);
    unsigned char *w = malloc(sz + 16); if (!w) DIE("out of memory"); i64 got = 0;
    while (got < sz) { size_t r = fread(w + got, 1, (size_t)((sz - got) > (1 << 30) ? (1 << 30) : (sz - got)), f); if (!r) break; got += r; }
    fclose(f); while (got > 0 && (w[got - 1] == '\n' || w[got - 1] == '\r')) got--;
    int map[256]; for (int c = 0; c < 256; c++) map[c] = -1;
    for (int c = 0; c < 16; c++) map[(unsigned char)AL[c]] = c;
    for (i64 i = 0; i < got; i++) { int v = map[w[i]]; if (v < 0) DIE("bad symbol in %s", path); w[i] = (unsigned char)v; }
    *len = got; return w;
}
static double wall(void) { struct timespec ts; timespec_get(&ts, TIME_UTC); return ts.tv_sec + ts.tv_nsec * 1e-9; }
static int closes(i64 k, int ex) {
    i64 s = PS[k], l = PL[k], R = l - h - ex;
    return R > 2 * n && !memcmp(W + s + R, W + s, (size_t)(h + ex));
}
/* window positions (in order) of a cyclic word; returns their number */
static i64 trail_windows(const Trail *T, i64 *wp) {
    i64 R = T->R, m = 0; int cnt[16] = {0}, distinct = 0;
    if (T->fixed) {                 /* open path: no wrap-around */
        i64 len = R + h;
        for (i64 i = 0; i < len; i++) {
            if (cnt[T->c[i]]++ == 0) distinct++;
            if (i >= n) { if (--cnt[T->c[i - n]] == 0) distinct--; }
            if (i >= n - 1 && distinct == n) wp[m++] = i - n + 1;
        }
        return m;
    }
    for (int k = 0; k < n - 1; k++) if (cnt[T->c[k % R]]++ == 0) distinct++;
    for (i64 p = 0; p < R; p++) {
        i64 q = p + n - 1; if (q >= R) q -= R;
        if (cnt[T->c[q]]++ == 0) distinct++;
        if (distinct == n) wp[m++] = p;
        if (--cnt[T->c[p]] == 0) distinct--;
    }
    return m;
}

/* openings of trail t in window order; writes them to out (if not NULL) and returns their number */
static i64 trail_options(i64 t, i64 *wp, const u64 *dupb, Opt *out, i64 *hist, i64 *shist) {
    if (TR[t].fixed) return 0;
    i64 R = TR[t].R, m = trail_windows(&TR[t], wp), k = 0;
    for (i64 i = 0; i < m && m >= 2; i++) {
        i64 i1 = i + 1 == m ? 0 : i + 1, i2 = i1 + 1 == m ? 0 : i1 + 1;
        i64 g = (wp[i1] - wp[i] + R) % R;
        if (g >= 2) {
            if (g > 3) DIE("gap %lld inside a trail", g);
            if (out) { out[k].start = (u32)wp[i1]; out[k].g = (unsigned char)g; out[k].g1 = 0; hist[3 - g + 3]++; }
            k++;
        }
        if (use_skip && m >= 3) {
            u64 r = rank_cyc(&TR[t], wp[i1]);
            if ((dupb[r >> 6] >> (r & 63)) & 1) {
                i64 g2 = g + (wp[i2] - wp[i1] + R) % R;
                if (g2 >= 2) {
                    if (out) { out[k].start = (u32)wp[i2]; out[k].g = (unsigned char)g2; out[k].g1 = (unsigned char)g; hist[3 - g2 + 3]++; shist[3 - g2 + 3]++; }
                    k++;
                }
            }
        }
    }
    return k;
}

int main(int argc, char **argv) {
    if (argc < 3) DIE("usage: trailsearch WORD.txt OUT.txt [--time SEC] [--seed S] [--kmax K] [--T0 TEMP] [--noskip] [--nosplit] [--plan-in FILE] [--ckpt SEC] [--iters N] [--threads T] [--sync SEC]");
    const char *plan_in = NULL;
    for (int a = 3; a < argc; a++) {
        if (!strcmp(argv[a], "--time") && a + 1 < argc) tlimit = atof(argv[++a]);
        else if (!strcmp(argv[a], "--seed") && a + 1 < argc) seed = strtoull(argv[++a], 0, 10);
        else if (!strcmp(argv[a], "--kmax") && a + 1 < argc) kmax = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--T0") && a + 1 < argc) T0 = atof(argv[++a]);
        else if (!strcmp(argv[a], "--ckpt") && a + 1 < argc) ckpt_sec = atof(argv[++a]);
        else if (!strcmp(argv[a], "--iters") && a + 1 < argc) maxit = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--plan-in") && a + 1 < argc) plan_in = argv[++a];
        else if (!strcmp(argv[a], "--threads") && a + 1 < argc) NTHR = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--sync") && a + 1 < argc) sync_sec = atof(argv[++a]);
        else if (!strcmp(argv[a], "--bigp") && a + 1 < argc) bigp = atof(argv[++a]);
        else if (!strcmp(argv[a], "--focus") && a + 1 < argc) focus = atof(argv[++a]);
        else if (!strcmp(argv[a], "--noskip")) use_skip = 0;
        else if (!strcmp(argv[a], "--nosplit")) use_split = 0;
        else DIE("unknown option %s", argv[a]);
    }
    if (NTHR < 1 || NTHR > 256) DIE("1 to 256 threads");
    double t00 = wall();
    W = load_word(argv[1], &L);
    int mx = 0; for (i64 i = 0; i < L; i++) if (W[i] > mx) mx = W[i];
    n = mx + 1; h = n - 3;
    if (n < 6 || n > 13) DIE("6 to 13 symbols");
    for (int k = 0; k <= 16; k++) HMASK[k] = k >= 16 ? ~0ULL : ((1ULL << (4 * k)) - 1);
    fact[0] = 1; for (int i = 1; i < 17; i++) fact[i] = fact[i - 1] * i;
    /* permutation windows and pieces (split at gaps >= 4) */
    { int cnt[16] = {0}, distinct = 0; i64 nw = 0, cap = 1 << 16, prev = -1, pstart = -1;
      PS = malloc(cap * 8); PL = malloc(cap * 8); NP = 0;
      for (i64 i = 0; i < L; i++) {
          if (cnt[W[i]]++ == 0) distinct++;
          if (i >= n) { if (--cnt[W[i - n]] == 0) distinct--; }
          if (i < n - 1 || distinct != n) continue;
          i64 p = i - n + 1; nw++;
          if (prev < 0) pstart = p;
          else if (p - prev >= 4) { if (NP == cap) { cap *= 2; PS = realloc(PS, cap * 8); PL = realloc(PL, cap * 8); } PS[NP] = pstart; PL[NP] = prev + n - pstart; NP++; pstart = p; }
          prev = p;
      }
      if (prev < 0) DIE("no permutation in the word");
      if (NP == cap) { cap *= 2; PS = realloc(PS, cap * 8); PL = realloc(PL, cap * 8); }
      PS[NP] = pstart; PL[NP] = prev + n - pstart; NP++;
      printf("n=%d L=%lld perm windows %lld pieces %lld (%.1fs)\n", n, L, nw, NP, wall() - t00); fflush(stdout);
    }
    /* trails: closed pieces, chains of open pieces, single pieces written from a gap-2 / gap-1 opening */
    char *closed = calloc((size_t)NP, 1);
    i64 *trail_of_piece = malloc(NP * 8); for (i64 k = 0; k < NP; k++) trail_of_piece[k] = -1;
    TR = calloc((size_t)NP + 1, sizeof(Trail)); NT = 0;
    i64 nclosed = 0, nopen = 0;
    for (i64 k = 0; k < NP; k++) if (closes(k, 0)) { closed[k] = 1; nclosed++; trail_of_piece[k] = NT; TR[NT].c = W + PS[k]; TR[NT].R = PL[k] - h; NT++; }
    i64 nlinear = 0;
    { i64 no = 0; i64 *op = malloc((NP + 1) * 8); for (i64 k = 0; k < NP; k++) if (!closed[k]) op[no++] = k;
      char *used = calloc((size_t)NP + 1, 1), *haspred = calloc((size_t)NP + 1, 1); i64 *chain = malloc((no + 1) * 8);
      for (i64 a = 0; a < no; a++) { u64 tw = hw_lin(W + PS[op[a]] + PL[op[a]] - h); for (i64 b = 0; b < no; b++) if (b != a && hw_lin(W + PS[op[b]]) == tw) haspred[op[b]] = 1; }
      /* phase 0 starts at the pieces nothing leads to (open paths), phase 1 takes the cycles */
      for (int phase = 0; phase < 2; phase++) for (i64 a = 0; a < no; a++) {
          i64 k = op[a]; if (used[k] || (phase == 0 && haspred[k])) continue;
          i64 nc = 0; chain[nc++] = k; used[k] = 1; u64 hwd = hw_lin(W + PS[k]), tw;
          for (;;) {
              i64 lastp = chain[nc - 1]; tw = hw_lin(W + PS[lastp] + PL[lastp] - h);
              if (tw == hwd) break;
              i64 nx = -1; for (i64 b = 0; b < no; b++) if (!used[op[b]] && hw_lin(W + PS[op[b]]) == tw) { nx = op[b]; break; }
              if (nx < 0) break;
              chain[nc++] = nx; used[nx] = 1;
          }
          int ex = (tw != hwd && nc == 1) ? (closes(k, 1) ? 1 : closes(k, 2) ? 2 : 0) : 0;
          if (ex) {          /* a whole trail written from a gap-2 or gap-1 opening */
              closed[k] = 1; nclosed++; trail_of_piece[k] = NT; TR[NT].c = W + PS[k]; TR[NT].R = PL[k] - h - ex; NT++;
              continue;
          }
          i64 R = 0; for (i64 b = 0; b < nc; b++) R += PL[chain[b]] - h;
          unsigned char *c = malloc((size_t)R + h + 16); i64 q = 0;
          for (i64 b = 0; b < nc; b++) { memcpy(c + q, W + PS[chain[b]], (size_t)(PL[chain[b]] - h)); q += PL[chain[b]] - h; trail_of_piece[chain[b]] = NT; }
          TR[NT].c = c; TR[NT].R = R;
          if (tw != hwd) { i64 lastp = chain[nc - 1]; memcpy(c + q, W + PS[lastp] + PL[lastp] - h, (size_t)h); TR[NT].fixed = 1; nlinear += nc; }
          else nopen += nc;
          NT++;
      }
      free(op); free(used); free(haspred); free(chain);
    }
    i64 sumR = 0, maxR = 0; for (i64 t = 0; t < NT; t++) { sumR += TR[t].R; if (TR[t].R > maxR) maxR = TR[t].R; }
    printf("trails %lld (closed pieces %lld, chained open pieces %lld), sum R %lld\n", NT, nclosed, nopen, sumR);
    if (nlinear) printf("%lld pieces form an open path that is not a closed trail; they stay where they are\n", nlinear);
    fflush(stdout);
    /* duplicate windows, then the openings of every trail (parallel over trails) */
    u64 NF = fact[n];
    u64 *seenb = calloc((size_t)(NF >> 6) + 1, 8), *dupb = calloc((size_t)(NF >> 6) + 1, 8);
    if (!seenb || !dupb) DIE("out of memory");
    int LT = NTHR > 8 ? NTHR : 8; if (LT > omp_get_max_threads()) LT = omp_get_max_threads();
    i64 nwin = 0;
    #pragma omp parallel num_threads(LT) reduction(+:nwin)
    {
        i64 *wp = malloc((size_t)(maxR + 8) * 8); if (!wp) DIE("out of memory");
        #pragma omp for schedule(dynamic, 8)
        for (i64 t = 0; t < NT; t++) {
            i64 m = trail_windows(&TR[t], wp); nwin += m;
            for (i64 i = 0; i < m; i++) {
                u64 r = TR[t].fixed ? rank_lin(TR[t].c + wp[i]) : rank_cyc(&TR[t], wp[i]), bit = 1ULL << (r & 63);
                u64 old = __atomic_fetch_or(&seenb[r >> 6], bit, __ATOMIC_RELAXED);
                if (old & bit) __atomic_fetch_or(&dupb[r >> 6], bit, __ATOMIC_RELAXED);
            }
        }
        free(wp);
    }
    { u64 dcount = 0, scount = 0; for (u64 i = 0; i <= (NF >> 6); i++) { scount += __builtin_popcountll(seenb[i]); dcount += __builtin_popcountll(dupb[i]); }
      printf("trail windows %lld distinct %llu (n! check: %s), duplicated %llu (%.1fs)\n", nwin, scount, scount == NF ? "True" : "False", dcount, wall() - t00); fflush(stdout);
      if (scount != NF) DIE("the trails do not contain every permutation (%llu missing): the model cannot be used on this word", (unsigned long long)(NF - scount));
      free(seenb); }
    /* A window may be skipped only if its permutation really occurs twice in the word.  The cyclic word of a trail
       can contain a window that the word itself does not have (a piece cut open across a duplicate window), so the
       duplicates are counted again on the word and the two sets are intersected. */
    { u64 *ws = calloc((size_t)(NF >> 6) + 1, 8), *wd = calloc((size_t)(NF >> 6) + 1, 8); if (!ws || !wd) DIE("out of memory");
      i64 nwin_word = L - n + 1;
      #pragma omp parallel num_threads(LT)
      {
          int tid = omp_get_thread_num(), nt = omp_get_num_threads();
          i64 a = nwin_word * tid / nt, b = nwin_word * (tid + 1) / nt; int cnt[16] = {0}, distinct = 0;
          for (i64 i = a; i < a + n - 1 && i < L; i++) if (cnt[W[i]]++ == 0) distinct++;
          for (i64 p = a; p < b; p++) {
              if (cnt[W[p + n - 1]]++ == 0) distinct++;
              if (distinct == n) {
                  u64 r = rank_lin(W + p), bit = 1ULL << (r & 63);
                  u64 old = __atomic_fetch_or(&ws[r >> 6], bit, __ATOMIC_RELAXED);
                  if (old & bit) __atomic_fetch_or(&wd[r >> 6], bit, __ATOMIC_RELAXED);
              }
              if (--cnt[W[p]] == 0) distinct--;
          }
      }
      u64 before = 0, after = 0;
      for (u64 i = 0; i <= (NF >> 6); i++) { before += __builtin_popcountll(dupb[i]); dupb[i] &= wd[i]; after += __builtin_popcountll(dupb[i]); }
      if (before != after) { printf("%llu duplicated windows exist only in the cyclic words, not in the word: they will not be skipped" NL, (unsigned long long)(before - after)); fflush(stdout); }
      free(ws); free(wd); }
    { i64 hist[8] = {0}, shist[8] = {0}; i64 *ocnt = calloc((size_t)NT + 1, 8);
      for (int pass = 0; pass < 2; pass++) {
          #pragma omp parallel num_threads(LT)
          {
              i64 *wp = malloc((size_t)(maxR + 8) * 8), lh[8] = {0}, lsh[8] = {0}; if (!wp) DIE("out of memory");
              #pragma omp for schedule(dynamic, 8)
              for (i64 t = 0; t < NT; t++) {
                  i64 k = trail_options(t, wp, dupb, pass ? OP + TR[t].olo : NULL, lh, lsh);
                  if (!pass) ocnt[t] = k; else if (k != ocnt[t]) DIE("internal error: option count");
              }
              free(wp);
              #pragma omp critical
              for (int d = 0; d < 8; d++) { hist[d] += lh[d]; shist[d] += lsh[d]; }
          }
          if (!pass) {
              NO = 0; for (i64 t = 0; t < NT; t++) { TR[t].olo = NO; NO += ocnt[t]; TR[t].ohi = NO; }
              OP = malloc((size_t)(NO + 1) * sizeof(Opt)); if (!OP) DIE("out of memory for %lld options", NO);
          }
      }
      free(ocnt);
      printf("options %lld by extra cost {", NO); for (int d = 0; d < 8; d++) if (hist[d]) printf(" %d: %lld", d - 3, hist[d]);
      printf(" }; dup-skip options {"); for (int d = 0; d < 8; d++) if (shist[d]) printf(" %d: %lld", d - 3, shist[d]);
      printf(" } (%.1fs)\n", wall() - t00); fflush(stdout);
    }
    free(dupb);
    /* current sequence */
    i64 cap = NP * 2 + 1024; Ev *ev = malloc(cap * sizeof(Ev)); i64 N = 0;
    if (!plan_in) {
        for (i64 k = 0; k < NP; k++) ev[N++] = piece_event(k, trail_of_piece[k]);
        i64 L0 = seq_length(ev, N);
        printf("model length of the input sequence: %lld (word %lld)\n", L0, L); fflush(stdout);
        if (L0 != L) DIE("the model does not reproduce the word");
    } else {
        FILE *f = fopen(plan_in, "r"); if (!f) DIE("cannot open %s", plan_in);
        char tag[32]; int pn; i64 pL, pN; if (fscanf(f, "%31s %d %lld %lld", tag, &pn, &pL, &pN) != 4 || pn != n || pL != L) DIE("plan does not match the word");
        for (i64 q = 0; q < pN; q++) {
            char c[4]; if (fscanf(f, "%3s", c) != 1) DIE("bad plan");
            Ev x;
            if (c[0] == 'P') { i64 k; if (fscanf(f, "%lld", &k) != 1 || k < 0 || k >= NP) DIE("bad plan"); x = piece_event(k, trail_of_piece[k]); }
            else if (c[0] == 'O') {
                u32 t, st; int g, g1; if (fscanf(f, "%u %u %d %d", &t, &st, &g, &g1) != 4 || t >= NT) DIE("bad plan");
                i64 o = -1; for (i64 z = TR[t].olo; z < TR[t].ohi; z++) if (OP[z].start == st && OP[z].g == g && OP[z].g1 == g1) { o = z; break; }
                if (o < 0) DIE("plan option not found"); x = make_event(o);
            } else { u32 t; i64 st, l; if (fscanf(f, "%u %lld %lld", &t, &st, &l) != 3 || t >= NT) DIE("bad plan"); x.kind = EV_SEG; x.t = t; x.a = st; x.l = l; x.s = hw_cyc(&TR[t], st); x.e = hw_cyc(&TR[t], st + l - h); x.skip = -1; }
            if (N + 2 >= cap) { cap *= 2; ev = realloc(ev, cap * sizeof(Ev)); }
            ev[N++] = x;
        }
        fclose(f);
        printf("model length of the plan: %lld (%lld events)\n", seq_length(ev, N), N); fflush(stdout);
    }
    /* ---------- destroy / repair search */
    char outplan[4096]; snprintf(outplan, sizeof outplan, "%s.plan", argv[2]);
    G_ev = malloc((size_t)(4 * N + 65536) * sizeof(Ev)); memcpy(G_ev, ev, (size_t)N * sizeof(Ev)); G_N = N; G_len = seq_length(ev, N);
    G_t0 = G_last_ck = G_last_log = wall();
    #pragma omp parallel num_threads(NTHR)
    {
        Ctx *c = calloc(1, sizeof(Ctx)); c->tid = omp_get_thread_num();
        search(c, ev, N, outplan);
    }
    i64 tot = 0; for (int q = 0; q < NTHR; q++) tot += G_it[q];
    printf("LNS done: %lld iterations on %d threads, best %lld\n", tot, NTHR, G_len); fflush(stdout);
    print_stats(G_ev, G_N);
    write_plan(G_ev, G_N, outplan);
    write_word(G_ev, G_N, argv[2], G_len);
    printf("wrote %s length %lld (%.0fs)\n", argv[2], G_len, wall() - t00);
    return 0;
}
