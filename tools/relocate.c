/* relocate.c - relocation with re-cutting: a window of neighbouring closed trails is moved to another place of the
   sequence, and the trails around both places are cut again.

   Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.  The closed trails are
   those of Jay Pantone's construction (github.com/jaypantone/superperm-upper-43-80).

   What it does.  The search of trailsearch.c never moves a trail and re-cuts its neighbours at the same time.  This
   pass does, without any random search.  From the fixed-order pass of recut.c run forwards and backwards it has,
   for every cut o of every piece i, F_i(o) = the cheapest way to write pieces 0 to i with piece i cut at o, and
   B_i(o) = the cheapest way to write pieces i to the end.  From these tables it gets exactly
     * rho(W): what is saved by taking a window W of consecutive trails out when all other cuts may change;
     * iota(t, place): what it costs to put trail t between two neighbouring pieces when both may be cut again
       (only cuts of the neighbours that are within dpa_tau letters of their best are looked at).
   A window is a candidate if every trail in it has a place that costs at most --dpa-imax and rho is larger than the
   sum of the iota.  Each candidate is tried for real: the trails are moved, the fixed-order pass runs on the pieces
   around every changed place (12, then 48, then 192 on either side, then the whole sequence) and the move is kept
   if the word is shorter.  Several moves are kept per sweep; later candidates of the sweep must lie clear of the
   places already changed.  Sweeps repeat until one gains nothing.  OUT.txt.plan is written after every sweep that
   gained, and the length the pass promises is checked against the sequence.

   Build:  gcc -O2 -mpopcnt -fopenmp -o relocate relocate.c -lm
   Use:    relocate BASE.txt OUT.txt --plan-in PLAN --threads 1 --time 0 --dpa --dpa-thr 4 --dpa-v
           n = 13: add --dpa-full 2

   Options of the pass.
     --dpa             run the pass before the search (with --time 0: nothing else) and on the best sequence after it
     --dpa-thr T       T threads look for the places of the trails (the rest of a sweep is one thread)
     --dpa-v           one line per step of a sweep (--dpa-vv: also every trial); --as-v is the old name
     --dpa-lmax L      longest window, in trails (default 24, at most 64)
     --dpa-imax C      a trail takes part only if it has another place that costs at most C (default 2)
     --dpa-tau S       cuts of the neighbours within S letters of their best are indexed (default 1; 0 makes the
                       index about ten times smaller)
     --dpa-theta T     every place cheaper than T is found (default 3)
     --dpa-cap M       at most M cuts per piece in the index (default 64)
     --dpa-win W       the pass after a move starts with W pieces on either side (default 12)
     --dpa-full M      at most M trials per sweep end with the pass on the whole sequence (default 10; 2 for n = 13)
     --dpa-maxtry M    at most M trials per sweep (default 2000)
     --dpa-sec S       inside the search: the pass on the current sequence of thread 0 every S seconds
     --co, --co-skip   the fixed-order pass alone, as in recut.c
     and all options of trailsearch.c.

   Memory and time (measured).  n = 11: a sweep takes 2 to 21 seconds; on words that have been through the other
   passes it finds no candidate.  n = 12, one thread: 522,745,526 to 522,745,483 in 751 seconds, 11 sweeps of 45 to
   72 seconds, moves of 2 to 7 trails.  n = 13, 8 threads: about 12.5 GB; 6,747,917,824 to 6,747,917,498 took 15
   sweeps of 330 to 460 seconds.
   Limits: every trail of a window goes to its cheapest place only, and a trail without a place that costs at most
   --dpa-imax ends a window.

   Words.  The comments say "cut" for the place where a closed trail is cut open.  The names in the code and the
   text the program prints use two older words for it: "opening" and "option" (struct Opt, the table OP, "gap-2
   openings").  The "gap" g of a cut is the weight of the step that is cut: 3 is the usual cut and costs nothing, 2
   is a cut between two 2-cycles and costs one letter, 1 is a cut inside a 1-cycle and costs two letters.
   An "event" is one piece as it is written into the word: a whole trail from one cut, a segment of a trail, or a
   piece of the input word left as it is.  The "h-word" of a piece end is its first or last h = n - 3 letters; two
   pieces are joined with the largest overlap of these words.  A "skip" is a cut that also drops one of the two
   occurrences of a permutation that the trails contain twice.  "Cluster optimisation" is the fixed-order pass.

   Layout of this file.  It is a copy of the present trailsearch.c (the model, the plan, the fast search, the
   loader) with two parts added, marked by lines of equal signs: the fixed-order pass of recut.c (co_run, co_full;
   without --coit) and the relocation.  Removed from the working version: an assignment neighbourhood (--as: the
   trails of a set put back by one linear assignment problem into the places the others leave, cuts of the others
   fixed) and a removal rule guided by the symmetries of the trails (--sym).  Both gained nothing: the assignment
   0 letters on the three plans it was tried on (43,930,623, 522,745,531, 522,745,526), the symmetry rule 0 new
   best words in 54 trials. */
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
static unsigned char *W;
static i64 L;
static int n, h;
#define NL "\n"
#define DIE(...)                      \
    do {                              \
        fprintf(stderr, __VA_ARGS__); \
        fprintf(stderr, "\n");        \
        exit(1);                      \
    } while (0)

/* ==================== shared base (trailsearch.c): model, plan, index, search moves ==================== */
/* ---------- h-words packed 4 bits per symbol (first symbol highest) */
static u64 HMASK[17];
/* h - largest k with suffix_k(e) == prefix_k(s) */
static inline int dist(u64 e, u64 s) {
    for (int k = h; k >= 1; k--)
        if ((e & HMASK[k]) == (s >> (4 * (h - k))))
            return h - k;
    return h;
}

/* ---------- trails */
/* cyclic word, its length, option range */
typedef struct {
    unsigned char *c;
    i64 R;
    i64 olo, ohi;
    int fixed;
} Trail;
/* fixed: an open path of R + h letters that is not a closed trail in the word; its pieces are never moved */
static Trail *TR;
static i64 NT;
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
/* 8 symbols packed with one 8-byte load (all buffers have 16 spare bytes at the end) */
static inline u64 pack8(const unsigned char *p) {
    u64 x;
    memcpy(&x, p, 8);
    x = __builtin_bswap64(x) & 0x0F0F0F0F0F0F0F0FULL;
    x = (x | (x >> 4)) & 0x00FF00FF00FF00FFULL;
    x = (x | (x >> 8)) & 0x0000FFFF0000FFFFULL;
    return (x | (x >> 16)) & 0xFFFFFFFFULL;
}
static inline u64 hw_lin(const unsigned char *p) {
    return h <= 8 ? pack8(p) >> (4 * (8 - h)) : (pack8(p) << (4 * (h - 8))) | (pack8(p + h - 8) & HMASK[h - 8]);
}
#else
static inline u64 hw_lin(const unsigned char *p) {
    u64 v = 0;
    for (int k = 0; k < h; k++)
        v = (v << 4) | p[k];
    return v;
}
#endif
/* h-word at cyclic position pos */
static inline u64 hw_cyc(const Trail *t, i64 pos) {
    i64 R = t->R;
    while (pos >= R)
        pos -= R;
    while (pos < 0)
        pos += R;
    if (pos + h <= R)
        return hw_lin(t->c + pos);
    u64 v = 0;
    for (int k = 0; k < h; k++)
        v = (v << 4) | t->c[(pos + k) % R];
    return v;
}
static u64 fact[17];
/* Rank (0 .. n! - 1, lexicographic) of the permutation in the n letters at p.  p must hold n different letters. */
static inline u64 rank_lin(const unsigned char *p) {
    u64 r = 0;
    int used = 0;
    for (int k = 0; k < n; k++) {
        int c = p[k];
        r += (u64)(c - __builtin_popcount(used & ((1 << c) - 1))) * fact[n - 1 - k];
        used |= 1 << c;
    }
    return r;
}
/* rank of the permutation window at cyclic position pos */
static inline u64 rank_cyc(const Trail *t, i64 pos) {
    u64 r = 0;
    int used = 0;
    i64 R = t->R;
    pos %= R;
    if (pos < 0)
        pos += R;
    if (pos + n <= R) {
        const unsigned char *p = t->c + pos;
        for (int k = 0; k < n; k++) {
            int c = p[k];
            r += (u64)(c - __builtin_popcount(used & ((1 << c) - 1))) * fact[n - 1 - k];
            used |= 1 << c;
        }
    } else
        for (int k = 0; k < n; k++) {
            int c = t->c[(pos + k) % R];
            r += (u64)(c - __builtin_popcount(used & ((1 << c) - 1))) * fact[n - 1 - k];
            used |= 1 << c;
        }
    return r;
}

/* ---------- options: 6 bytes each */
typedef struct __attribute__((packed)) {
    u32 start;
    unsigned char g, g1;
} Opt;
/* the piece starts at `start`; total gap g; g1 > 0: skip option, the skipped window lies g1 after the previous window.
   The options of a trail are contiguous (TR[t].olo .. ohi), so the trail of an option is found by binary search. */
static Opt *OP;
static i64 NO;
/* The trail of cut o (binary search in the first cuts of the trails). */
static inline u32 otrail(i64 o) {
    i64 lo = 0, hi = NT - 1;
    while (lo < hi) {
        i64 m = (lo + hi + 1) >> 1;
        if (TR[m].olo <= o)
            lo = m;
        else
            hi = m - 1;
    }
    return (u32)lo;
}
static inline int oD(i64 o) {
    return 3 - (int)OP[o].g;
}
static inline u64 oS_t(const Trail *T, i64 o) {
    return hw_cyc(T, OP[o].start);
}
static inline u64 oE_t(const Trail *T, i64 o) {
    return hw_cyc(T, (i64)OP[o].start - OP[o].g + 3);
}
static inline i64 oSK_t(const Trail *T, i64 o) {
    return OP[o].g1 ? (i64)rank_cyc(T, (i64)OP[o].start - OP[o].g + OP[o].g1) : -1;
}
static inline u64 oS(i64 o) {
    return oS_t(&TR[otrail(o)], o);
}
static inline u64 oE(i64 o) {
    return oE_t(&TR[otrail(o)], o);
}

/* ---------- events */
enum { EV_PIECE, EV_OPT, EV_SEG };
typedef struct {
    int kind;
    u32 t;
    u64 s, e;
    i64 l;
    i64 a;
    i64 skip;
} Ev;
/* EV_PIECE: a = piece index.  EV_OPT: a = option.  EV_SEG: a = start offset in the trail, l letters. */
static i64 *PS, *PL;
static i64 NP; /* pieces of the input word */

/* Length of the word of a sequence: the letters of all events minus the overlaps at the joins. */
static i64 seq_length(const Ev *ev, i64 N) {
    i64 len = 0;
    for (i64 i = 0; i < N; i++)
        len += ev[i].l;
    for (i64 i = 0; i + 1 < N; i++)
        len -= h - dist(ev[i].e, ev[i + 1].s);
    return len;
}
/* The event for cut o: its trail written once from that cut.  Start word, end word, length R + h + cost of the
   cut, and the rank of the occurrence it drops (-1: none). */
static Ev make_event(i64 o) {
    u32 t = otrail(o);
    const Trail *T = &TR[t];
    Ev x;
    x.kind = EV_OPT;
    x.t = t;
    x.s = oS_t(T, o);
    x.e = oE_t(T, o);
    x.l = T->R + h + oD(o);
    x.a = o;
    x.skip = oSK_t(T, o);
    return x;
}
/* The event for piece k of the input word, left as it is. */
static Ev piece_event(i64 k, i64 trail) {
    Ev x;
    x.kind = EV_PIECE;
    x.t = (u32)trail;
    x.s = hw_lin(W + PS[k]);
    x.e = hw_lin(W + PS[k] + PL[k] - h);
    x.l = PL[k];
    x.a = k;
    x.skip = -1;
    return x;
}
/* two events for a trail split at plain cuts c1 (start of segment 1) and c2 (end of segment 1) */
static void seg_events(i64 c1, i64 c2, Ev *e1, Ev *e2) {
    u32 t = otrail(c1);
    i64 R = TR[t].R;
    i64 st1 = OP[c1].start, en1 = ((i64)OP[c2].start - OP[c2].g + R) % R, l1 = ((en1 - st1) % R + R) % R + n;
    i64 st2 = OP[c2].start, en2 = ((i64)OP[c1].start - OP[c1].g + R) % R, l2 = ((en2 - st2) % R + R) % R + n;
    e1->kind = EV_SEG;
    e1->t = t;
    e1->s = oS(c1);
    e1->e = oE(c2);
    e1->l = l1;
    e1->a = st1;
    e1->skip = -1;
    e2->kind = EV_SEG;
    e2->t = t;
    e2->s = oS(c2);
    e2->e = oE(c1);
    e2->l = l2;
    e2->a = st2;
    e2->skip = -1;
}

/* ---------- output */
static void write_word(const Ev *ev, i64 N, const char *path, i64 expect) {
    FILE *f = fopen(path, "wb");
    if (!f)
        DIE("cannot write %s", path);
    size_t cap = 1 << 22, ob = 0;
    char *out = malloc(cap);
    i64 total = 0;
    u64 tail = 0;
    for (i64 i = 0; i < N; i++) {
        const Ev *x = &ev[i];
        i64 skip = i ? h - dist(tail, x->s) : 0;
        for (i64 r = skip; r < x->l; r++) {
            unsigned char c;
            if (x->kind == EV_PIECE)
                c = W[PS[x->a] + r];
            else {
                const Trail *t = &TR[x->t];
                i64 st = x->kind == EV_OPT ? (i64)OP[x->a].start : x->a;
                c = t->c[(st + r) % t->R];
            }
            out[ob++] = AL[c];
            if (ob == cap) {
                fwrite(out, 1, ob, f);
                ob = 0;
            }
        }
        total += x->l - skip;
        tail = x->e;
    }
    out[ob++] = '\n';
    fwrite(out, 1, ob, f);
    fclose(f);
    free(out);
    if (total != expect)
        DIE("internal error: wrote %lld letters, model says %lld", total, expect);
}
/* Writes the sequence as a plan: a head line, then one line per event (P, O or S), with LF line ends. */
static void write_plan(const Ev *ev, i64 N, const char *path) {
    FILE *f = fopen(path, "wb");
    if (!f)
        DIE("cannot write %s", path); /* "wb": LF line ends on every system */
    fprintf(f, "TRAILSEARCH-PLAN %d %lld %lld\n", n, L, N);
    for (i64 i = 0; i < N; i++) {
        const Ev *x = &ev[i];
        if (x->kind == EV_PIECE)
            fprintf(f, "P %lld\n", x->a);
        else if (x->kind == EV_OPT)
            fprintf(f, "O %u %u %d %d\n", x->t, OP[x->a].start, OP[x->a].g, OP[x->a].g1);
        else
            fprintf(f, "S %u %lld %lld\n", x->t, x->a, x->l);
    }
    fclose(f);
}

/* ---------- hash multimap: key -> list of ints */
typedef struct {
    u64 key;
    int head;
} Slot;
typedef struct {
    Slot *t;
    u64 mask;
    int *next, *val;
    i64 n, cap;
} HTab;
static inline u64 hmix(u64 k) {
    k ^= k >> 33;
    k *= 0xFF51AFD7ED558CCDULL;
    k ^= k >> 33;
    k *= 0xC4CEB9FE1A85EC53ULL;
    k ^= k >> 33;
    return k;
}
#define HKEY(word, j, kind) (((u64)(word) << 8) | ((u64)(j) << 4) | (u64)(kind)) /* word < 2^40 */
static void h_reset(HTab *H, i64 entries) {
    u64 need = 1024;
    while (need < (u64)entries + (u64)entries / 2 + 16)
        need <<= 1;
    if (!H->t || need - 1 != H->mask) {
        free(H->t);
        H->t = malloc(need * sizeof(Slot));
        H->mask = need - 1;
    }
    for (u64 i = 0; i <= H->mask; i++) {
        H->t[i].head = -1;
        H->t[i].key = ~0ULL;
    }
    if (entries > H->cap) {
        H->cap = entries + entries / 2 + 64;
        free(H->next);
        free(H->val);
        H->next = malloc(H->cap * sizeof(int));
        H->val = malloc(H->cap * sizeof(int));
    }
    H->n = 0;
}
/* Adds value v to the list of key (open addressing with linear probing; the new entry becomes the head of its
   list).  The caller guarantees room: h_reset / h_init were called with enough entries. */
static inline void h_add(HTab *H, u64 key, int v) {
    u64 i = hmix(key) & H->mask;
    while (H->t[i].key != ~0ULL && H->t[i].key != key)
        i = (i + 1) & H->mask;
    H->t[i].key = key;
    H->next[H->n] = H->t[i].head;
    H->val[H->n] = v;
    H->t[i].head = (int)H->n++;
}
/* unlinks entry e of an existing key; the other entries keep their order */
static inline void h_del(HTab *H, u64 key, int e) {
    u64 i = hmix(key) & H->mask;
    while (H->t[i].key != key)
        i = (i + 1) & H->mask;
    int *p = &H->t[i].head;
    while (*p != e)
        p = &H->next[*p];
    *p = H->next[e];
}
/* First entry of the list of key, or -1.  The list is walked with H->next[], the values are in H->val[]. */
static inline int h_get(const HTab *H, u64 key) {
    u64 i = hmix(key) & H->mask;
    while (H->t[i].key != ~0ULL) {
        if (H->t[i].key == key)
            return H->t[i].head;
        i = (i + 1) & H->mask;
    }
    return -1;
}
#define KLEV 3     /* joins of cost <= KLEV are looked up */
#define ENT_PER 12 /* index entries per event */
static double tlimit = 600, T0 = 1.5, ckpt_sec = 600, prel = 0.4, sync_sec = 60;
static double bigp = 1.0;  /* probability of keeping a big trail (more than splitmax options) in the removal set */
static double focus = 0.0; /* probability of skipping an iteration whose removal set has no big trail */
static int kmax = 6, use_skip = 1, use_split = 1, splitmax = 3000, NTHR = 1;
static u64 seed = 1;
static i64 maxit = -1;

/* ---------- one search thread: the sequence is a doubly linked list of nodes, so an insertion does not renumber
   anything and the hash index (word -> node) is only ever appended to; dead nodes are skipped at lookup and the
   index is rebuilt when it is mostly garbage.  A rejected move is undone by unlinking / relinking nodes. */
/* lab: order label (increasing along the list); ent: its first index entry */
typedef struct {
    Ev v;
    int prev, next, alive, ent;
    u64 lab;
} Node;
typedef struct {
    i64 c2;
    int i, jm;
    i64 cst;
} Pair;
/* visit list of a trail: every (option, key, node) that best_insertion looks at, in the order it looks at them,
   with its cost.  The greedy repair evaluates every pending trail again after each insertion; one insertion changes
   only the visits at the new node and at its two neighbours, so the list is patched and read again (vc_update). */
/* option - olo, node found by key k, cost */
typedef struct {
    u32 oo;
    int x;
    short d;
    unsigned char k;
} Vis;
/* sp / es: first / last h - KLEV symbols of S / E */
typedef struct {
    int ok;
    u32 t;
    Vis *v;
    i64 nv, vcap;
    u32 *sp, *es;
    i64 kcap;
} VC;
/* ok: 0 = empty, 1 = the visits with their costs, 2 = raw: all live nodes found by the keys, recorded before the
   destroy step (the removal selection scans the trails of the chosen run anyway); best_insertion drops what has
   gone since and adds the costs.  Lists belong to trails (vct: trail -> list + 1) for one iteration. */
typedef struct {
    int tid;
    u64 rs[4];
    Node *nd;
    int ncap, nn, first, last;
    i64 N;
    int relabeled;
    HTab H;
    u64 *bf, bfmask;  /* bf: one-hash Bloom filter over the keys of H */
    u32 *mk, mkstamp; /* mark_near: stamp << 2 | bits */
    int *order, *cand, *tnx, *wk, *wc, *rel, *remlog, *inslog;
    int nremlog, ninslog;
    i64 ncand;
    int *thead, *rth;
    i64 *rk;
    int rkcap;
    struct Iv *iv;
    int ivcap; /* see seq_build */
    i64 *skp;
    int nskp, skpcap;
    i64 *vid;
    int vcap;
    Pair *pr;
    i64 pcap;
    int *Ib, *Jb;
    int icap, jcap;
    u64 *wS, *wE;
    i64 wcap; /* best_split: S / E of the cuts of the trail */
    char *rem;
    u32 *pend;
    Ev *tmp;
    VC *vc;
    i64 nvc, nvu;
    int *vct;
    Vis *vtmp;
    i64 vtcap;
    i64 cur, best_len, it, acc;
} Ctx;

static inline u64 rotl(u64 x, int k) {
    return (x << k) | (x >> (64 - k));
}
/* xoshiro256** */
static inline u64 rnd64(Ctx *c) {
    u64 *s = c->rs, r = rotl(s[1] * 5, 7) * 9, t = s[1] << 17;
    s[2] ^= s[0];
    s[3] ^= s[1];
    s[1] ^= s[2];
    s[0] ^= s[3];
    s[2] ^= t;
    s[3] = rotl(s[3], 45);
    return r;
}
/* Seeds the random generator of a search thread from s (splitmix64). */
static void rseed(Ctx *c, u64 s) {
    for (int i = 0; i < 4; i++) {
        s += 0x9E3779B97F4A7C15ULL;
        u64 z = s;
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
        z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
        c->rs[i] = z ^ (z >> 31);
    }
}
static inline double rndu(Ctx *c) {
    return (rnd64(c) >> 11) * (1.0 / 9007199254740992.0);
}
/* 0 .. m-1 */
static inline i64 rndn(Ctx *c, i64 m) {
    return (i64)(rnd64(c) % (u64)m);
}
/* a .. b */
static inline i64 rndint(Ctx *c, i64 a, i64 b) {
    return a + rndn(c, b - a + 1);
}

/* index kinds: 0 = suffix (length h-j) of e, 1 = prefix (length h-j) of s, 2 / 3 = the lookups of best_split */
#define BFH(key) (((u64)(key) * 0x9E3779B97F4A7C15ULL) >> 32)
#define BFBIT(c, key)                          \
    {                                          \
        u64 b_ = BFH(key) & (c)->bfmask;       \
        (c)->bf[b_ >> 6] |= 1ULL << (b_ & 63); \
    }
/* Enters node id into the index of the thread: for overlaps h down to h - KLEV the end of its end word and the
   beginning of its start word, and (with two-segment insertion on) the four keys best_split looks up.
   Sets the bits of the Bloom filter.  The keys and their order are what index_del relies on. */
static inline void index_add(Ctx *c, int id) {
    const Ev *x = &c->nd[id].v;
    c->nd[id].ent = (int)c->H.n;
    for (int j = 0; j <= KLEV; j++) {
        u64 k0 = HKEY(x->e & HMASK[h - j], j, 0), k1 = HKEY(x->s >> (4 * j), j, 1);
        h_add(&c->H, k0, id);
        h_add(&c->H, k1, id);
        BFBIT(c, k0);
        BFBIT(c, k1);
    }
    if (use_split) {
        h_add(&c->H, HKEY(x->s, 0, 2), id);
        h_add(&c->H, HKEY(x->s >> 4, 1, 2), id);
        h_add(&c->H, HKEY(x->e, 0, 3), id);
        h_add(&c->H, HKEY(x->e & HMASK[h - 1], 1, 3), id);
    }
}
/* a node that is dead for good leaves the index (same keys in the same order as index_add; H.n is not reduced, so the
   index is rebuilt at the same moments as without this), so the lists that best_insertion walks hold live nodes only */
static void index_del(Ctx *c, int id) {
    const Ev *x = &c->nd[id].v;
    int e = c->nd[id].ent;
    for (int j = 0; j <= KLEV; j++) {
        h_del(&c->H, HKEY(x->e & HMASK[h - j], j, 0), e++);
        h_del(&c->H, HKEY(x->s >> (4 * j), j, 1), e++);
    }
    if (use_split) {
        h_del(&c->H, HKEY(x->s, 0, 2), e);
        h_del(&c->H, HKEY(x->s >> 4, 1, 2), e + 1);
        h_del(&c->H, HKEY(x->e, 0, 3), e + 2);
        h_del(&c->H, HKEY(x->e & HMASK[h - 1], 1, 3), e + 3);
    }
}
static void seq_build(Ctx *c);
/* Loads a sequence of N events into the thread: nodes, order labels, index, Bloom filter and the kept arrays
   (seq_build).  Buffers grow when needed.  ev may be the thread's own c->tmp. */
static void ctx_load(Ctx *c, const Ev *ev, i64 N) {
    int need = (int)(4 * N + 65536), self = ev == c->tmp;
    if (need > c->ncap) {
        c->ncap = need;
        c->nd = realloc(c->nd, (size_t)need * sizeof(Node));
        int **arr[] = {&c->order, &c->cand, &c->tnx, &c->wk, &c->wc, &c->rel, &c->remlog, &c->inslog};
        for (int k = 0; k < 8; k++)
            *arr[k] = realloc(*arr[k], (size_t)need * sizeof(int));
        c->tmp = realloc(c->tmp, (size_t)need * sizeof(Ev));
        if (self)
            ev = c->tmp;
        free(c->mk);
        c->mk = calloc((size_t)need, sizeof(u32));
        c->mkstamp = 0;
        if (!c->mk)
            DIE("out of memory");
        if (!c->nd || !c->inslog || !c->tmp)
            DIE("out of memory");
    }
    c->nn = (int)N;
    c->N = N;
    c->first = 0;
    c->last = (int)N - 1;
    for (i64 i = 0; i < N; i++) {
        Node *q = &c->nd[i];
        q->v = ev[i];
        q->prev = (int)i - 1;
        q->next = i + 1 < N ? (int)i + 1 : -1;
        q->alive = 1;
        q->lab = (u64)(i + 1) << 32;
    }
    i64 ecap = (N > 100000 ? 2 : 4) * ENT_PER * N + 65536; /* live entries plus head-room for dead ones */
    h_reset(&c->H, ecap);
    {
        u64 bits = 1 << 16;
        while (bits < (u64)ecap * 16)
            bits <<= 1;
        if (bits - 1 != c->bfmask || !c->bf) {
            free(c->bf);
            c->bf = malloc(bits / 8);
            c->bfmask = bits - 1;
        }
        memset(c->bf, 0, bits / 8);
    }
    for (i64 i = 0; i < N; i++)
        index_add(c, (int)i);
    seq_build(c);
}
static i64 ctx_export(const Ctx *c, Ev *out) {
    i64 m = 0;
    for (int id = c->first; id >= 0; id = c->nd[id].next)
        out[m++] = c->nd[id].v;
    return m;
}
/* Length of the word of the current sequence, by walking the list. */
static i64 ctx_length(const Ctx *c) {
    i64 len = 0;
    for (int id = c->first; id >= 0;) {
        const Node *q = &c->nd[id];
        len += q->v.l;
        if (q->next >= 0)
            len -= h - dist(q->v.e, c->nd[q->next].v.s);
        id = q->next;
    }
    return len;
}
static void relabel(Ctx *c) {
    u64 k = 1;
    for (int id = c->first; id >= 0; id = c->nd[id].next)
        c->nd[id].lab = (k++) << 32;
    c->relabeled = 1;
}
/* Takes node id out of the list.  Its prev / next stay as they were, so node_relink can undo it. */
static void node_unlink(Ctx *c, int id) {
    Node *q = &c->nd[id];
    if (q->prev >= 0)
        c->nd[q->prev].next = q->next;
    else
        c->first = q->next;
    if (q->next >= 0)
        c->nd[q->next].prev = q->prev;
    else
        c->last = q->prev;
    q->alive = 0;
    c->N--;
}
/* Puts back a node that node_unlink took out.  Nodes must come back in the reverse order of their removal. */
static void node_relink(Ctx *c, int id) {
    Node *q = &c->nd[id];
    if (q->prev >= 0)
        c->nd[q->prev].next = id;
    else
        c->first = id;
    if (q->next >= 0)
        c->nd[q->next].prev = id;
    else
        c->last = id;
    q->alive = 1;
    c->N++;
}
/* Inserts a new node with event x after node a: a label between its neighbours (the list is relabelled if
   there is no room), an index entry, a line in the insertion log for undo.  Returns the node. */
static int node_insert_after(Ctx *c, int a, const Ev *x) {
    int b = c->nd[a].next;
    u64 la = c->nd[a].lab, lb = b >= 0 ? c->nd[b].lab : la + (1ULL << 33);
    if (lb - la < 2) {
        relabel(c);
        la = c->nd[a].lab;
        lb = b >= 0 ? c->nd[b].lab : la + (1ULL << 33);
    }
    int id = c->nn++;
    Node *q = &c->nd[id];
    q->v = *x;
    q->prev = a;
    q->next = b;
    q->alive = 1;
    q->lab = la + (lb - la) / 2;
    c->nd[a].next = id;
    if (b >= 0)
        c->nd[b].prev = id;
    else
        c->last = id;
    index_add(c, id);
    c->inslog[c->ninslog++] = id;
    c->N++;
    c->tnx[id] = c->thead[x->t];
    c->thead[x->t] = id;
    return id;
}
static int skp_has(const Ctx *c, i64 r) {
    for (int i = 0; i < c->nskp; i++)
        if (c->skp[i] == r)
            return 1;
    return 0;
}
/* Adds permutation r to the list of duplicates dropped by the skip cuts of the move under way. */
static void skp_add(Ctx *c, i64 r) {
    if (c->nskp == c->skpcap) {
        c->skpcap = c->skpcap ? c->skpcap * 2 : 256;
        c->skp = realloc(c->skp, c->skpcap * sizeof(i64));
    }
    c->skp[c->nskp++] = r;
}
static void skp_del(Ctx *c, i64 r) {
    for (int i = 0; i < c->nskp; i++)
        if (c->skp[i] == r) {
            c->skp[i] = c->skp[--c->nskp];
            return;
        }
}

/* ---------- what the search keeps about the sequence between iterations, so that an iteration does not walk the
   whole list: order[] (position -> node), cand[] (the positions i whose join i -> i+1 costs >= 2, increasing; they
   are also the ends of the runs), the nodes of every trail (thead[t], then tnx[]) and skp[] (the skipped windows of
   the sequence, in any order).  Built here after every load, patched after an accepted move (seq_patch); a
   rejected move restores the list exactly, so nothing has to be done for it. */
static void seq_build(Ctx *c) {
    const Node *nd = c->nd;
    i64 N = 0, nc = 0;
    memset(c->thead, 0xff, ((size_t)NT + 1) * sizeof(int));
    c->nskp = 0;
    for (int id = c->first; id >= 0; id = nd[id].next) {
        if (N && dist(nd[c->order[N - 1]].v.e, nd[id].v.s) >= 2)
            c->cand[nc++] = (int)N - 1;
        c->order[N++] = id;
        c->tnx[id] = c->thead[nd[id].v.t];
        c->thead[nd[id].v.t] = id;
        if (nd[id].v.skip >= 0)
            skp_add(c, nd[id].v.skip);
    }
    c->ncand = nc;
}
/* position of node id in order[0 .. N-1], by its label */
static inline i64 seq_pos(const Ctx *c, int id, i64 N) {
    u64 lab = c->nd[id].lab;
    i64 lo = 0, hi = N - 1;
    while (lo < hi) {
        i64 m = (lo + hi) >> 1;
        if (c->nd[c->order[m]].lab < lab)
            lo = m + 1;
        else
            hi = m;
    }
    return lo;
}
/* number of entries of cand[] below p */
static inline i64 cand_lb(const Ctx *c, i64 p) {
    i64 lo = 0, hi = c->ncand;
    while (lo < hi) {
        i64 m = (lo + hi) >> 1;
        if (c->cand[m] < p)
            lo = m + 1;
        else
            hi = m;
    }
    return lo;
}
/* what node id adds to the length where it stands */
static inline i64 node_len(const Ctx *c, int id) {
    const Node *nd = c->nd, *x = &nd[id];
    int a = x->prev, b = x->next;
    i64 d = x->v.l;
    if (a >= 0)
        d -= h - dist(nd[a].v.e, x->v.s);
    if (b >= 0)
        d -= h - dist(x->v.e, nd[b].v.s);
    if (a >= 0 && b >= 0)
        d += h - dist(nd[a].v.e, nd[b].v.s);
    return d;
}
/* After an accepted move: the nodes at positions rk[] >> 32 of order[0 .. N0-1] were removed and the nodes with
   id >= nn0 were inserted (no relabelling in between, so the old labels still sort order[]).  The changes are
   merged into intervals (l, r) of old positions whose ends are untouched nodes (-1 / N0: the ends of the list);
   between them the list is walked, outside them order[] and cand[] are only shifted. */
typedef struct Iv {
    int l, r, w, ia, ib, nc;
    i64 sh, ish;
} Iv;
static int iv_cmp(const void *a, const void *b) {
    int x = ((const Iv *)a)->l, y = ((const Iv *)b)->l;
    return x < y ? -1 : x > y;
}
static int i64_cmp(const void *a, const void *b) {
    i64 x = *(const i64 *)a, y = *(const i64 *)b;
    return x < y ? -1 : x > y;
}
/* Brings order[] and cand[] up to date after an accepted move (see the comment above the type Iv). */
static void seq_patch(Ctx *c, i64 N0, int nn0) {
    const Node *nd = c->nd;
    int *order = c->order, *cand = c->cand, *wk = c->wk, *wc = c->wc;
    int m = 0, k = 0;
    if (c->nremlog + c->ninslog > c->ivcap) {
        c->ivcap = 2 * (c->nremlog + c->ninslog) + 64;
        c->iv = realloc(c->iv, (size_t)c->ivcap * sizeof(Iv));
    }
    Iv *iv = c->iv;
    for (int q = 0; q < c->nremlog; q++) {
        int p = (int)(c->rk[q] >> 32);
        iv[m].l = p - 1;
        iv[m].r = p + 1;
        m++;
    }
    for (int q = 0; q < c->ninslog; q++) {
        int a = nd[c->inslog[q]].prev;
        if (a >= nn0)
            continue; /* only the first node of a chain of new nodes */
        int p = a < 0 ? -1 : (int)seq_pos(c, a, N0);
        iv[m].l = p;
        iv[m].r = p + 1;
        m++;
    }
    if (!m)
        return;
    qsort(iv, (size_t)m, sizeof(Iv), iv_cmp);
    for (int q = 1; q < m; q++) {
        if (iv[q].l <= iv[k].r) {
            if (iv[q].r > iv[k].r)
                iv[k].r = iv[q].r;
        } else
            iv[++k] = iv[q];
    }
    m = k + 1;
    i64 nw = 0, sh = 0, ish = 0, z = 0;
    for (int q = 0; q < m; q++) { /* the new nodes between l and r */
        int id = iv[q].l < 0 ? c->first : nd[order[iv[q].l]].next, stop = iv[q].r >= N0 ? -1 : order[iv[q].r];
        for (iv[q].w = 0; id != stop; id = nd[id].next) {
            wk[nw++] = id;
            iv[q].w++;
        }
        sh += iv[q].w - (iv[q].r - iv[q].l - 1);
        iv[q].sh = sh; /* shift of everything from r to the next l */
        iv[q].ia = (int)cand_lb(c, iv[q].l);
        iv[q].ib = (int)cand_lb(c, iv[q].r);
    }
#define SEG_A(q) ((i64)iv[q].r)
#define SEG_B(q) ((q) + 1 < m ? (i64)iv[(q) + 1].l : N0 - 1)
    /* in place: the segments that move left from left to right, then those that move right from right to left */
    for (int q = 0; q < m; q++)
        if (iv[q].sh < 0 && SEG_B(q) >= SEG_A(q))
            memmove(order + SEG_A(q) + iv[q].sh, order + SEG_A(q), (size_t)(SEG_B(q) - SEG_A(q) + 1) * sizeof(int));
    for (int q = m - 1; q >= 0; q--)
        if (iv[q].sh > 0 && SEG_B(q) >= SEG_A(q))
            memmove(order + SEG_A(q) + iv[q].sh, order + SEG_A(q), (size_t)(SEG_B(q) - SEG_A(q) + 1) * sizeof(int));
    for (int q = 0; q < m; q++) {
        memcpy(order + iv[q].l + 1 + (q ? iv[q - 1].sh : 0), wk + z, (size_t)iv[q].w * sizeof(int));
        z += iv[q].w;
    }
    /* cand[]: the joins from l to r are computed again, the others keep their place in the list */
    nw = 0;
    for (int q = 0; q < m; q++) {
        i64 lo = iv[q].l + (q ? iv[q - 1].sh : 0), hi = lo + iv[q].w;
        if (lo < 0)
            lo = 0;
        if (hi > c->N - 2)
            hi = c->N - 2;
        iv[q].nc = 0;
        for (i64 j = lo; j <= hi; j++)
            if (dist(nd[order[j]].v.e, nd[order[j + 1]].v.s) >= 2) {
                wc[nw++] = (int)j;
                iv[q].nc++;
            }
        ish += iv[q].nc - (iv[q].ib - iv[q].ia);
        iv[q].ish = ish;
    }
#define CSEG_B(q) ((q) + 1 < m ? (i64)iv[(q) + 1].ia : c->ncand)
    for (int q = 0; q < m; q++)
        if (iv[q].ish <= 0 && (iv[q].ish || iv[q].sh))
            for (i64 i = iv[q].ib, b = CSEG_B(q); i < b; i++)
                cand[i + iv[q].ish] = cand[i] + (int)iv[q].sh;
    for (int q = m - 1; q >= 0; q--)
        if (iv[q].ish > 0)
            for (i64 i = CSEG_B(q) - 1; i >= iv[q].ib; i--)
                cand[i + iv[q].ish] = cand[i] + (int)iv[q].sh;
    z = 0;
    for (int q = 0; q < m; q++) {
        memcpy(cand + iv[q].ia + (q ? iv[q - 1].ish : 0), wc + z, (size_t)iv[q].nc * sizeof(int));
        z += iv[q].nc;
    }
    c->ncand += ish;
#undef SEG_A
#undef SEG_B
#undef CSEG_B
}
#ifdef TS_CHECK /* -DTS_CHECK=1: print the final state of every thread; =2: also verify the kept arrays at every iteration */
static void seq_check(Ctx *c) {
    const Node *nd = c->nd;
    i64 N = 0, nc = 0, ns = 0;
    for (int id = c->first; id >= 0; id = nd[id].next) {
        if (N && dist(nd[c->order[N - 1]].v.e, nd[id].v.s) >= 2) {
            if (nc >= c->ncand || c->cand[nc] != N - 1)
                DIE("check: cand[%lld] at it %lld", nc, c->it);
            nc++;
        }
        if (c->order[N] != id)
            DIE("check: order[%lld] at it %lld", N, c->it);
        if (N && nd[c->order[N - 1]].lab >= nd[id].lab)
            DIE("check: labels at it %lld", c->it);
        int z = c->thead[nd[id].v.t];
        while (z >= 0 && z != id)
            z = c->tnx[z];
        if (z < 0)
            DIE("check: trail chain at it %lld", c->it);
        if (nd[id].v.skip >= 0) {
            ns++;
            if (!skp_has(c, nd[id].v.skip))
                DIE("check: skp at it %lld", c->it);
        }
        N++;
    }
    if (N != c->N || nc != c->ncand || ns != c->nskp)
        DIE("check: N %lld/%lld ncand %lld/%lld nskp %lld/%d at it %lld", N, c->N, nc, c->ncand, ns, c->nskp, c->it);
    for (i64 t = 0; t < NT; t++)
        for (int z = c->thead[t]; z >= 0; z = c->tnx[z]) {
            if (!nd[z].alive || nd[z].v.t != t)
                DIE("check: dead node in a trail chain at it %lld", c->it);
            N--;
        }
    if (N)
        DIE("check: trail chains at it %lld", c->it);
    if (c->cur != ctx_length(c))
        DIE("check: length %lld, kept %lld at it %lld", ctx_length(c), c->cur, c->it);
}
#endif

/* marks the nodes whose e (bit 1) or s (bit 2) is within one step of S or E of an cut of trail T */
static void mark_near(Ctx *c, const Trail *T) {
    const Node *nd = c->nd;
    const HTab *H = &c->H;
    u32 st = c->mkstamp << 2;
    enum { BATCH = 16 };
    for (i64 o0 = T->olo; o0 < T->ohi; o0 += BATCH) {
        int m = (int)(T->ohi - o0 < BATCH ? T->ohi - o0 : BATCH);
        u64 key[BATCH][4], bit[BATCH][4];
        for (int q = 0; q < m; q++) {
            u64 S = oS_t(T, o0 + q), E = oE_t(T, o0 + q);
            key[q][0] = HKEY(S, 0, 0);
            key[q][1] = HKEY(E, 0, 1);
            key[q][2] = HKEY(S >> 4, 1, 0);
            key[q][3] = HKEY(E & HMASK[h - 1], 1, 1);
            for (int k = 0; k < 4; k++) {
                bit[q][k] = BFH(key[q][k]) & c->bfmask;
                __builtin_prefetch(&c->bf[bit[q][k] >> 6]);
            }
        }
        for (int q = 0; q < m; q++)
            for (int k = 0; k < 4; k++) {
                if (!((c->bf[bit[q][k] >> 6] >> (bit[q][k] & 63)) & 1))
                    continue;
                for (int e = h_get(H, key[q][k]); e >= 0; e = H->next[e]) {
                    int x = H->val[e];
                    if (!nd[x].alive)
                        continue;
                    if ((c->mk[x] & ~3u) != st)
                        c->mk[x] = st;
                    c->mk[x] |= 1u << (k & 1);
                }
            }
    }
}

/* ---------- best insertion of trail t: insert after node `after` */
typedef struct {
    double val;
    i64 delta;
    int after;
    i64 opt;
} Ins;
/* Appends one visit (cut, key, node, cost) to a visit list. */
static inline void vis_add(VC *vc, i64 oo, int k, int x, i64 d) {
    if (vc->nv == vc->vcap) {
        vc->vcap = vc->vcap ? vc->vcap * 2 : 4096;
        vc->v = realloc(vc->v, (size_t)vc->vcap * sizeof(Vis));
    }
    Vis *p = &vc->v[vc->nv++];
    p->oo = (u32)oo;
    p->k = (unsigned char)k;
    p->x = x;
    p->d = (short)d;
}
/* the list of trail t; make: start one if there is none */
static VC *vc_get(Ctx *c, u32 t, int make) {
    if (c->vct[t])
        return &c->vc[c->vct[t] - 1];
    if (!make)
        return NULL;
    if (c->nvu == c->nvc) {
        i64 m = c->nvc ? 2 * c->nvc : 64;
        c->vc = realloc(c->vc, (size_t)m * sizeof(VC));
        memset(c->vc + c->nvc, 0, (size_t)(m - c->nvc) * sizeof(VC));
        c->nvc = m;
    }
    VC *vc = &c->vc[c->nvu++];
    vc->t = t;
    vc->ok = 0;
    c->vct[t] = (int)c->nvu;
    return vc;
}
/* vc != NULL: the visits are recorded in vc, or read from it if it is up to date (same result, same random numbers);
   raw: only record the nodes found (nothing is evaluated, no random numbers are used) */
static Ins best_insertion(Ctx *c, u32 t, double noise, VC *vc, int raw) {
    Ins best;
    best.val = 1e18;
    best.delta = 0;
    best.after = -1;
    best.opt = -1;
    const Trail *T = &TR[t];
    const Node *nd = c->nd;
    const HTab *H = &c->H;
    if (vc && vc->ok == 2) {
        i64 m = 0, cur = -1;
        int skbad = 0;
        u64 S = 0, E = 0;
        for (i64 i = 0; i < vc->nv; i++) {
            Vis *p = &vc->v[i];
            int x = p->x, a, b2;
            i64 o = T->olo + p->oo;
            if (!nd[x].alive)
                continue;
            if (!(p->k & 1)) {
                a = x;
                b2 = nd[x].next;
            } else {
                b2 = x;
                a = nd[x].prev;
            }
            if (a < 0 || b2 < 0)
                continue;
            if ((i64)p->oo != cur) {
                cur = p->oo;
                skbad = OP[o].g1 && c->nskp && skp_has(c, oSK_t(T, o));
                S = oS_t(T, o);
                E = oE_t(T, o);
            }
            if (skbad)
                continue;
            p->d = (short)(dist(nd[a].v.e, S) + oD(o) + dist(E, nd[b2].v.s) - dist(nd[a].v.e, nd[b2].v.s));
            vc->v[m++] = *p;
        }
        vc->nv = m;
        vc->ok = 1;
    }
    if (vc && vc->ok) {
        for (i64 i = 0; i < vc->nv; i++) {
            const Vis *p = &vc->v[i];
            double v = (double)p->d + (noise > 0 ? noise * rndu(c) : 0.0);
            if (v < best.val) {
                best.val = v;
                best.delta = p->d;
                best.after = (p->k & 1) ? nd[p->x].prev : p->x;
                best.opt = T->olo + p->oo;
            }
        }
        goto done;
    }
    if (vc) {
        vc->nv = 0;
        vc->ok = 1;
        if (T->ohi - T->olo > vc->kcap) {
            vc->kcap = T->ohi - T->olo + 1024;
            free(vc->sp);
            free(vc->es);
            vc->sp = malloc((size_t)vc->kcap * sizeof(u32));
            vc->es = malloc((size_t)vc->kcap * sizeof(u32));
        }
    }
    /* options are processed in batches so that the filter words of a whole batch are prefetched before they are tested */
    enum { BATCH = 16, NK = 2 * (KLEV + 1) };
    for (i64 o0 = T->olo; o0 < T->ohi; o0 += BATCH) {
        int m = (int)(T->ohi - o0 < BATCH ? T->ohi - o0 : BATCH);
        u64 Sb[BATCH], Eb[BATCH], key[BATCH][NK], bit[BATCH][NK];
        for (int q = 0; q < m; q++) {
            u64 S = oS_t(T, o0 + q), E = oE_t(T, o0 + q);
            Sb[q] = S;
            Eb[q] = E;
            if (vc) {
                vc->sp[o0 + q - T->olo] = (u32)(S >> (4 * KLEV));
                vc->es[o0 + q - T->olo] = (u32)(E & HMASK[h - KLEV]);
            }
            for (int j = 0; j <= KLEV; j++) {
                key[q][2 * j] = HKEY(S >> (4 * j), j, 0);
                key[q][2 * j + 1] = HKEY(E & HMASK[h - j], j, 1);
            }
            for (int k = 0; k < NK; k++) {
                bit[q][k] = BFH(key[q][k]) & c->bfmask;
                __builtin_prefetch(&c->bf[bit[q][k] >> 6]);
            }
        }
        for (int q = 0; q < m; q++) {
            i64 o = o0 + q;
            u64 S = Sb[q], E = Eb[q];
            int D = oD(o), skchecked = 0, skbad = 0;
            for (int k = 0; k < NK && !skbad; k++) {
                if (!((c->bf[bit[q][k] >> 6] >> (bit[q][k] & 63)) & 1))
                    continue;
                for (int e = h_get(H, key[q][k]); e >= 0; e = H->next[e]) {
                    int x = H->val[e], a, b2;
                    if (!nd[x].alive)
                        continue;
                    if (raw) {
                        vis_add(vc, o - T->olo, k, x, 0);
                        continue;
                    }
                    if (!(k & 1)) {
                        a = x;
                        b2 = nd[x].next;
                    } else {
                        b2 = x;
                        a = nd[x].prev;
                    }
                    if (a < 0 || b2 < 0)
                        continue;
                    if (!skchecked) {
                        skchecked = 1;
                        if (OP[o].g1 && c->nskp && skp_has(c, oSK_t(T, o))) {
                            skbad = 1;
                            break;
                        }
                    }
                    i64 d = dist(nd[a].v.e, S) + D + dist(E, nd[b2].v.s) - dist(nd[a].v.e, nd[b2].v.s);
                    double v = (double)d + (noise > 0 ? noise * rndu(c) : 0.0);
                    if (v < best.val) {
                        best.val = v;
                        best.delta = d;
                        best.after = a;
                        best.opt = o;
                    }
                    if (vc)
                        vis_add(vc, o - T->olo, k, x, d);
                }
            }
        }
    }
    if (raw) {
        vc->ok = 2;
        return best;
    }
done:
    if (best.after < 0) { /* nothing overlaps: append with the cheapest cut */
        i64 k = T->olo;
        for (i64 o = T->olo; o < T->ohi; o++)
            if (oD(o) < oD(k))
                k = o;
        best.delta = dist(nd[c->last].v.e, oS_t(T, k)) + oD(k);
        best.val = (double)best.delta;
        best.after = c->last;
        best.opt = k;
    }
    return best;
}

/* node id has just been inserted: bring the lists of the pending trails pend[0 .. np-1] (except pick) up to date */
static void vc_update(Ctx *c, int id, i64 pick, i64 np) {
    const Node *nd = c->nd;
    const Ev *x = &nd[id].v;
    int a = nd[id].prev, b = nd[id].next;
    u32 ts[KLEV + 1], te[KLEV + 1]; /* a match at level j needs sp == ts[j] (kind 0) or es == te[j] (kind 1) */
    for (int j = 0; j <= KLEV; j++) {
        ts[j] = (u32)((x->e >> (4 * (KLEV - j))) & HMASK[h - KLEV]);
        te[j] = (u32)((x->s >> (4 * j)) & HMASK[h - KLEV]);
    }
    for (i64 q = 0; q < np; q++) {
        VC *vc = q == pick ? NULL : vc_get(c, c->pend[q], 0);
        if (!vc || !vc->ok)
            continue;
        int rawl = vc->ok == 2;
        if (b < 0 && !rawl) {
            vc->ok = 0;
            continue;
        } /* appended: the old last node becomes a position; scan again */
        const Trail *T = &TR[c->pend[q]];
        i64 no = T->ohi - T->olo, m = 0;
        /* the visits found through a (by its e) and through b (by its s) now have the new node on the other side;
           options that skip the window the new piece skips are no longer allowed */
        for (i64 i = 0; i < vc->nv && !rawl; i++) {
            Vis *p = &vc->v[i];
            i64 o = T->olo + p->oo;
            if (x->skip >= 0 && OP[o].g1 && oSK_t(T, o) == x->skip)
                continue;
            if ((p->x == a && !(p->k & 1)) || (p->x == b && (p->k & 1))) {
                u64 S = oS_t(T, o), E = oE_t(T, o), ea = (p->k & 1) ? x->e : nd[a].v.e,
                    sb = (p->k & 1) ? nd[b].v.s : x->s;
                p->d = (short)(dist(ea, S) + oD(o) + dist(E, sb) - dist(ea, sb));
            }
            vc->v[m++] = *p;
        }
        if (!rawl)
            vc->nv = m;
        /* visits at the new node: it is the newest entry of its keys, so it comes first among equal (option, key) */
        i64 nw = 0, i = 0;
        if (vc->nv + 2 * (KLEV + 1) * 64 > c->vtcap) {
            c->vtcap = 2 * vc->nv + 65536;
            free(c->vtmp);
            c->vtmp = malloc((size_t)c->vtcap * sizeof(Vis));
        }
        for (i64 o0 = 0; o0 < no; o0 += 64) {
            i64 o1 = o0 + 64 < no ? o0 + 64 : no;
            int hit = 0;
            for (i64 oo = o0; oo < o1; oo++) {
                u32 sp = vc->sp[oo], es = vc->es[oo];
                for (int j = 0; j <= KLEV; j++)
                    hit |= (sp == ts[j]) | (es == te[j]);
            }
            if (!hit)
                continue;
            for (i64 oo = o0; oo < o1; oo++) {
                u32 sp = vc->sp[oo], es = vc->es[oo];
                int any = 0;
                for (int j = 0; j <= KLEV; j++)
                    any |= (sp == ts[j]) | (es == te[j]);
                if (!any)
                    continue;
                i64 o = T->olo + oo;
                u64 S = oS_t(T, o), E = oE_t(T, o);
                int skchecked = 0;
                for (int k = 0; k < 2 * (KLEV + 1); k++) {
                    int j = k >> 1;
                    if (!(k & 1) ? (S >> (4 * j)) != (x->e & HMASK[h - j]) : (E & HMASK[h - j]) != (x->s >> (4 * j)))
                        continue;
                    if (!rawl && !skchecked) {
                        skchecked = 1;
                        if (OP[o].g1 && c->nskp && skp_has(c, oSK_t(T, o)))
                            break;
                    }
                    while (i < vc->nv && (vc->v[i].oo < (u32)oo || (vc->v[i].oo == (u32)oo && vc->v[i].k < k)))
                        c->vtmp[nw++] = vc->v[i++];
                    Vis *p = &c->vtmp[nw++];
                    p->oo = (u32)oo;
                    p->k = (unsigned char)k;
                    p->x = id;
                    p->d = 0;
                    if (!rawl) {
                        u64 ea = (k & 1) ? nd[a].v.e : x->e, sb = (k & 1) ? x->s : nd[b].v.s;
                        p->d = (short)(dist(ea, S) + oD(o) + dist(E, sb) - dist(ea, sb));
                    }
                }
            }
            if (nw + (vc->nv - i) + 2 * (KLEV + 1) * 64 > c->vtcap) {
                c->vtcap = 2 * (nw + vc->nv) + 65536;
                c->vtmp = realloc(c->vtmp, (size_t)c->vtcap * sizeof(Vis));
            }
        }
        if (!nw)
            continue;
        while (i < vc->nv)
            c->vtmp[nw++] = vc->v[i++];
        if (nw > vc->vcap) {
            vc->vcap = nw + nw / 2;
            free(vc->v);
            vc->v = malloc((size_t)vc->vcap * sizeof(Vis));
        }
        memcpy(vc->v, c->vtmp, (size_t)nw * sizeof(Vis));
        vc->nv = nw;
    }
}

/* ---------- insertion of a small trail as two segments wrapped around a block i .. jm of the sequence:
   ..., prev(i), seg1, i, ..., jm, seg2, next(jm), ...   seg1 ends and seg2 starts at a vertex v of t (plain gap-3
   cut c2); seg1 starts and seg2 ends at any plain cut c1 */
typedef struct {
    int ok;
    i64 delta;
    int i, jm;
    i64 c1, c2;
} Split;
static int pair_cmp(const void *a, const void *b) {
    i64 x = ((const Pair *)a)->cst, y = ((const Pair *)b)->cst;
    return x < y ? -1 : x > y;
}
/* Best way to write small trail t as two segments around a block i .. jm of the sequence (see the comment
   above the type Split).  At most maxv of its free cuts are tried as the inner cut.  ok = 0: nothing found. */
static Split best_split(Ctx *c, u32 t, int maxv) {
    Split r;
    r.ok = 0;
    const Trail *T = &TR[t];
    const Node *nd = c->nd;
    const HTab *H = &c->H;
    int nv = 0;
    for (i64 o = T->olo; o < T->ohi; o++)
        if (OP[o].g == 3 && !OP[o].g1) {
            if (nv == c->vcap) {
                c->vcap = c->vcap ? c->vcap * 2 : 1024;
                c->vid = realloc(c->vid, c->vcap * sizeof(i64));
            }
            c->vid[nv++] = o;
        }
    if (nv > maxv) {
        for (int k = 0; k < maxv; k++) {
            int m = k + (int)rndn(c, nv - k);
            i64 x = c->vid[k];
            c->vid[k] = c->vid[m];
            c->vid[m] = x;
        }
        nv = maxv;
    }
    i64 np = 0;
    for (int a = 0; a < nv; a++) {
        i64 c2 = c->vid[a];
        u64 v = oS_t(T, c2);
        int ni = 0, nj = 0; /* I: inner nodes i with d(v, s_i) <= 1;  J: nodes jm (not the last) with d(e_jm, v) <= 1 */
        for (int lev = 0; lev <= 1; lev++)
            for (int q = h_get(H, HKEY(v & HMASK[h - lev], lev, 2)); q >= 0; q = H->next[q]) {
                int x = H->val[q];
                if (!nd[x].alive || nd[x].prev < 0 || nd[x].next < 0)
                    continue;
                if (ni == c->icap) {
                    c->icap = c->icap ? c->icap * 2 : 1024;
                    c->Ib = realloc(c->Ib, c->icap * sizeof(int));
                }
                c->Ib[ni++] = x;
            }
        if (!ni)
            continue;
        for (int lev = 0; lev <= 1; lev++)
            for (int q = h_get(H, HKEY(v >> (4 * lev), lev, 3)); q >= 0; q = H->next[q]) {
                int x = H->val[q];
                if (!nd[x].alive || nd[x].next < 0)
                    continue;
                if (nj == c->jcap) {
                    c->jcap = c->jcap ? c->jcap * 2 : 1024;
                    c->Jb = realloc(c->Jb, c->jcap * sizeof(int));
                }
                c->Jb[nj++] = x;
            }
        if (!nj)
            continue;
        for (int x = 0; x < ni; x++) {
            int i = c->Ib[x];
            int dvi = dist(v, nd[i].v.s);
            for (int y = 0; y < nj; y++) {
                int jm = c->Jb[y];
                if (nd[jm].lab < nd[i].lab)
                    continue;
                i64 cst = dvi + dist(nd[jm].v.e, v) - dist(nd[nd[i].prev].v.e, nd[i].v.s) -
                          dist(nd[jm].v.e, nd[nd[jm].next].v.s);
                if (np == c->pcap) {
                    c->pcap = c->pcap ? c->pcap * 2 : 4096;
                    c->pr = realloc(c->pr, c->pcap * sizeof(Pair));
                }
                c->pr[np].c2 = c2;
                c->pr[np].i = i;
                c->pr[np].jm = jm;
                c->pr[np].cst = cst;
                np++;
            }
        }
    }
    if (!np)
        return r;
    qsort(c->pr, (size_t)np, sizeof(Pair), pair_cmp);
    if (np > 64)
        np = 64;
    i64 bd = 1LL << 40, bk = -1, bc1 = -1, no = T->ohi - T->olo, dmin = 1 << 20;
    if (no > c->wcap) {
        c->wcap = no + 1024;
        free(c->wS);
        free(c->wE);
        c->wS = malloc((size_t)c->wcap * 8);
        c->wE = malloc((size_t)c->wcap * 8);
    }
    for (i64 q = 0; q < no; q++) {
        c->wS[q] = oS_t(T, T->olo + q);
        c->wE[q] = oE_t(T, T->olo + q);
        if (oD(T->olo + q) < dmin)
            dmin = oD(T->olo + q);
    }
    for (i64 k = 0; k < np; k++) {
        if (c->pr[k].cst + dmin >= bd)
            break; /* pr is sorted by cst and an cut adds at least dmin */
        u64 ep = nd[nd[c->pr[k].i].prev].v.e, sn = nd[nd[c->pr[k].jm].next].v.s;
        for (i64 q = 0; q < no; q++) {
            i64 d = dist(ep, c->wS[q]) + oD(T->olo + q) + dist(c->wE[q], sn) + c->pr[k].cst;
            if (d < bd) {
                bd = d;
                bk = k;
                bc1 = T->olo + q;
            }
        }
    }
    if (bk < 0 || bc1 == c->pr[bk].c2 || OP[bc1].g1)
        return r;
    r.ok = 1;
    r.delta = bd;
    r.i = c->pr[bk].i;
    r.jm = c->pr[bk].jm;
    r.c1 = bc1;
    r.c2 = c->pr[bk].c2;
    return r;
}

/* ---------- what the sequence looks like: cuts by kind, joins by cost, runs (maximal chains of joins of cost <= 1) */
static void print_stats(const Ev *ev, i64 N) {
    i64 g2 = 0, g1 = 0, skips = 0, segs = 0, pieces = 0, hist[17] = {0}, runs = 1, inter = 0, inrun = 0, extra = 0;
    for (i64 i = 0; i < N; i++) {
        if (ev[i].kind == EV_SEG)
            segs++;
        else if (ev[i].kind == EV_PIECE)
            pieces++;
        else {
            int g = OP[ev[i].a].g;
            if (OP[ev[i].a].g1)
                skips++;
            else if (g == 2)
                g2++;
            else if (g == 1)
                g1++;
        }
        if (i + 1 < N) {
            int d = dist(ev[i].e, ev[i + 1].s);
            hist[d]++;
            if (d >= 2) {
                runs++;
                inter += d;
            } else
                inrun += d;
        }
    }
    i64 sumR = 0;
    for (i64 t = 0; t < NT; t++)
        sumR += TR[t].R;
    extra = seq_length(ev, N) - h - sumR - inter - inrun;
    printf(
        "stats: events %lld (unchanged pieces %lld, segments %lld), gap-2 openings %lld, gap-1 openings %lld, duplicate-skip openings %lld, opening cost %lld" NL,
        N, pieces, segs, g2, g1, skips, extra);
    printf("stats: runs %lld, join cost between runs %lld, joins inside runs cost %lld; joins by cost:", runs, inter,
           inrun);
    for (int d = 0; d <= h; d++)
        if (hist[d])
            printf(" %d:%lld", d, hist[d]);
    printf(NL);
    fflush(stdout);
}

/* ==================== from recut.c: the fixed-order pass (co_run, co_full) ==================== */
/* ---------- cluster optimisation: for a fixed order of the events, the best cuts of all trails at once.
   Shortest path through layers, one per event: cost[p] = D(p) + min over the cuts o of the previous event of
   cost[o] + dist(E(o), S(p)).  The minimum is not taken over pairs: for k = h..1 a table holds the cheapest o for
   every suffix of length k of E(o) (a hash table, for k <= 3 an array) and prefix_k(S(p)) is looked up; only o with cost[o] - min < k can beat the
   join without overlap (h + min), so few o enter the tables of small k.  Costs are kept relative to the minimum of
   their layer (one byte per option) and the cuts are recovered backwards without back-pointers.
   One option only: segments, pieces of chained trails and of the open path, events outside lo..hi.  An unchanged
   piece that is a whole closed trail is the cut `start 0` of that trail and is free like any other.
   Skip cuts: an event may only take the skip it already uses (co_skip = 0); with co_skip = 1 every skip is
   allowed and the pass is repeated with bans while two events skip the same window. */
static double wall(void);
typedef struct {
    u64 key;
    u32 gen, val;
} CSlot;
typedef struct {
    CSlot *t;
    u64 cap;
    u32 gen;
    u64 *S, *E, *Ep;
    int *mv;
    i64 wcap;         /* current layer: start words, end words, cheapest way in; Ep: end words of the previous layer */
    unsigned char *d; /* direct tables for k = 1, 2, 3 */
    unsigned char *rel;
    i64 rcap;                    /* cost of every option relative to the minimum of its layer; 255: not allowed */
    i64 *off, *lmin, *cur, lcap; /* per layer: offset into rel, minimum cost, current option (-1: one option only) */
    i64 *ban;
    int nban, bancap;      /* co_skip = 1: (event, window) pairs that are not allowed */
    i64 nfree, nopt, maxm; /* statistics of the last pass: free events, their options, largest layer */
} CO;
static int co_skip = 0;
/* Table of one layer step: keeps for key (the last k letters of an end word) the smallest relative cost. */
static inline void co_put(CO *q, u64 mask, u64 key, u32 val) {
    u64 i = hmix(key) & mask;
    while (q->t[i].gen == q->gen) {
        if (q->t[i].key == key) {
            if (val < q->t[i].val)
                q->t[i].val = val;
            return;
        }
        i = (i + 1) & mask;
    }
    q->t[i].key = key;
    q->t[i].gen = q->gen;
    q->t[i].val = val;
}
/* The smallest relative cost stored for key in this generation of the table, or -1. */
static inline int co_get(const CO *q, u64 mask, u64 key) {
    u64 i = hmix(key) & mask;
    while (q->t[i].gen == q->gen) {
        if (q->t[i].key == key)
            return (int)q->t[i].val;
        i = (i + 1) & mask;
    }
    return -1;
}
/* the option an event is, or -1 */
static i64 co_cur(const Ev *x) {
    if (x->kind == EV_OPT)
        return x->a;
    if (x->kind != EV_PIECE)
        return -1;
    const Trail *T = &TR[x->t];
    if (T->fixed || T->c != W + PS[x->a])
        return -1;
    for (i64 o = T->ohi - 1; o >= T->olo; o--)
        if (!OP[o].start && !OP[o].g1)
            return (x->l == T->R + h + oD(o) && x->s == oS_t(T, o) && x->e == oE_t(T, o)) ? o : -1;
    return -1;
}
/* May event i take cut o, which drops an occurrence?  Without anyskip only the occurrence the event drops
   now; with anyskip any occurrence that is not banned for this event. */
static inline int co_skip_ok(const CO *q, const Ev *x, i64 i, const Trail *T, i64 o, int anyskip) {
    i64 r = oSK_t(T, o);
    if (!anyskip)
        return r == x->skip;
    for (int k = 0; k < q->nban; k++)
        if (q->ban[2 * k] == i && q->ban[2 * k + 1] == r)
            return 0;
    return 1;
}
/* events lo..hi may change their cut (their neighbours lo-1 and hi+1 stay); returns the gain in letters */
static i64 co_run(CO *q, Ev *ev, i64 N, i64 lo, i64 hi, int anyskip, int *nchg) {
    i64 a = lo > 0 ? lo - 1 : 0, b = hi + 1 < N ? hi + 1 : N - 1, nl = b - a + 1;
    if (nl > q->lcap) {
        q->lcap = nl + nl / 2 + 64;
        q->off = realloc(q->off, q->lcap * 8);
        q->lmin = realloc(q->lmin, q->lcap * 8);
        q->cur = realloc(q->cur, q->lcap * 8);
    }
    i64 roff = 0, poff = 0, pm = 0, pmin = 0, oldc = 0;
    int pfree = 0;
    u64 pe = 0;
    q->nfree = q->nopt = q->maxm = 0;
    if (nl == N && q->rcap < NO) {
        q->rcap = NO;
        q->rel = realloc(q->rel, (size_t)NO + 1);
    } /* whole sequence: one byte per option, no more */
    for (i64 i = a; i <= b; i++) {
        const Ev *x = &ev[i];
        i64 li = i - a, o0 = (i >= lo && i <= hi) ? co_cur(x) : -1;
        q->cur[li] = o0;
        q->off[li] = roff;
        if (i > a)
            oldc += dist(ev[i - 1].e, x->s);
        if (o0 < 0) { /* one option */
            i64 cst = 0;
            if (i > a && !pfree)
                cst = pmin + dist(pe, x->s);
            else if (i > a) {
                const unsigned char *prel = q->rel + poff;
                int best = h;
                for (i64 j = 0; j < pm; j++)
                    if (prel[j] < best) {
                        int v = prel[j] + dist(q->Ep[j], x->s);
                        if (v < best)
                            best = v;
                    }
                cst = pmin + best;
            }
            q->lmin[li] = pmin = cst;
            pe = x->e;
            pfree = 0;
            continue;
        }
        oldc += oD(o0);
        const Trail *T = &TR[x->t];
        i64 m = T->ohi - T->olo;
        if (m > q->wcap) {
            q->wcap = m + m / 2 + 64;
            q->S = realloc(q->S, q->wcap * 8);
            q->E = realloc(q->E, q->wcap * 8);
            q->Ep = realloc(q->Ep, q->wcap * 8);
            q->mv = realloc(q->mv, q->wcap * sizeof(int));
        }
        if (roff + m > q->rcap) {
            q->rcap = (roff + m) * 2 + 4096;
            q->rel = realloc(q->rel, q->rcap);
        }
        if (!q->d)
            q->d = malloc(16 + 256 + 4096);
        if (!q->S || !q->E || !q->Ep || !q->mv || !q->rel || !q->d)
            DIE("out of memory");
        unsigned char *rel = q->rel + roff;
        const unsigned char *prel = q->rel + poff;
        u64 *S = q->S, *E = q->E;
        int *mv = q->mv;
        for (i64 j = 0; j < m; j++) {
            i64 o = T->olo + j;
            if (OP[o].g1 && !co_skip_ok(q, x, i, T, o, anyskip)) {
                rel[j] = 255;
                continue;
            }
            S[j] = oS_t(T, o);
            E[j] = oE_t(T, o);
            rel[j] = 0;
            mv[j] = i == a ? 0 : !pfree ? dist(pe, S[j]) : h;
        }
        if (i > a && pfree) {
            u64 need = 16;
            while (need < 2 * (u64)pm)
                need <<= 1;
            if (need > q->cap) {
                free(q->t);
                q->t = calloc(need, sizeof(CSlot));
                q->cap = need;
                q->gen = 0;
                if (!q->t)
                    DIE("out of memory");
            }
            u64 mask = need - 1;
            for (int k = h; k >= 4; k--) {
                i64 cnt = 0;
                int sh = 4 * (h - k);
                q->gen++;
                for (i64 j = 0; j < pm; j++)
                    if (prel[j] < k) {
                        co_put(q, mask, q->Ep[j] & HMASK[k], prel[j]);
                        cnt++;
                    }
                if (!cnt)
                    break;
                for (i64 j = 0; j < m; j++) {
                    if (rel[j] == 255 || mv[j] <= h - k)
                        continue;
                    int v = co_get(q, mask, S[j] >> sh);
                    if (v >= 0 && v + h - k < mv[j])
                        mv[j] = v + h - k;
                }
            }
            /* k = 3, 2, 1: tables indexed by the word */
            unsigned char *d1 = q->d, *d2 = d1 + 16, *d3 = d2 + 256;
            int any = 0;
            memset(q->d, 255, 16 + 256 + 4096);
            for (i64 j = 0; j < pm; j++) {
                int r = prel[j];
                if (r >= 3)
                    continue;
                u64 e = q->Ep[j];
                any = 1;
                if (r < d3[e & 4095])
                    d3[e & 4095] = (unsigned char)r;
                if (r < 2 && r < d2[e & 255])
                    d2[e & 255] = (unsigned char)r;
                if (r < 1)
                    d1[e & 15] = 0;
            }
            if (any)
                for (i64 j = 0; j < m; j++) {
                    if (rel[j] == 255 || mv[j] <= h - 3)
                        continue;
                    int v = d3[S[j] >> (4 * (h - 3))];
                    if (v + h - 3 < mv[j])
                        mv[j] = v + h - 3;
                    if (mv[j] <= h - 2)
                        continue;
                    v = d2[S[j] >> (4 * (h - 2))];
                    if (v + h - 2 < mv[j])
                        mv[j] = v + h - 2;
                    if (mv[j] == h && !d1[S[j] >> (4 * (h - 1))])
                        mv[j] = h - 1;
                }
        }
        int mn = 1 << 20;
        for (i64 j = 0; j < m; j++)
            if (rel[j] != 255) {
                mv[j] += oD(T->olo + j);
                if (mv[j] < mn)
                    mn = mv[j];
            }
        for (i64 j = 0; j < m; j++)
            if (rel[j] != 255)
                rel[j] = (unsigned char)(mv[j] - mn);
        q->lmin[li] = pmin = pmin + mn;
        pfree = 1;
        pm = m;
        poff = roff;
        roff += m;
        q->E = q->Ep;
        q->Ep = E;
        q->nfree++;
        q->nopt += m;
        if (m > q->maxm)
            q->maxm = m;
    }
    /* backwards: the option of layer i that reaches the cost wanted by layer i+1 (the current one if it does) */
    i64 newc = q->lmin[nl - 1], want = 0;
    u64 ns = 0;
    int chg = 0;
    for (i64 i = b; i >= a; i--) {
        i64 li = i - a, o0 = q->cur[li];
        Ev *x = &ev[i];
        if (o0 < 0) {
            if (i < b && q->lmin[li] + dist(x->e, ns) != want)
                DIE("internal error: cluster optimisation (event %lld)", i);
            ns = x->s;
            want = q->lmin[li];
            continue;
        }
        const Trail *T = &TR[x->t];
        const unsigned char *rel = q->rel + q->off[li];
        i64 m = T->ohi - T->olo, pick = -1;
        i64 tgt = i < b ? want : q->lmin[li];
#define COV(j) (q->lmin[li] + rel[j] + (i < b ? dist(oE_t(T, T->olo + (j)), ns) : 0))
        if (rel[o0 - T->olo] != 255 && COV(o0 - T->olo) == tgt)
            pick = o0 - T->olo;
        for (int pass = 0; pass < 2 && pick < 0; pass++) /* plain cuts first */
            for (i64 j = 0; j < m; j++)
                if (rel[j] != 255 && (pass || !OP[T->olo + j].g1) && COV(j) == tgt) {
                    pick = j;
                    break;
                }
#undef COV
        if (pick < 0)
            DIE("internal error: cluster optimisation (event %lld)", i);
        i64 o = T->olo + pick;
        if (o != o0) {
            *x = make_event(o);
            chg++;
        }
        ns = x->s;
        want = q->lmin[li] + rel[pick] - oD(o);
    }
    if (nchg)
        *nchg = chg;
    return oldc - newc;
}
/* co_skip = 1: bans for events that took a skip another event uses; returns the number of new bans */
static int i64pair_cmp(const void *a, const void *b) {
    const i64 *x = a, *y = b;
    return x[0] < y[0] ? -1 : x[0] > y[0] ? 1 : x[1] < y[1] ? -1 : x[1] > y[1];
}
/* After a pass with free choice of the dropped occurrences: every permutation dropped by two or more events
   is banned for all of them but one (the event that dropped it before the pass, if there is one).
   Returns the number of new bans; 0 means the result is valid. */
static int co_clash(CO *q, const Ev *orig, const Ev *ev, i64 N) {
    i64 ns = 0, *sk = NULL;
    int added = 0;
    for (int pass = 0; pass < 2; pass++) {
        if (pass)
            sk = malloc((size_t)(ns + 1) * 16);
        ns = 0;
        for (i64 i = 0; i < N; i++)
            if (ev[i].skip >= 0) {
                if (pass) {
                    sk[2 * ns] = ev[i].skip;
                    sk[2 * ns + 1] = i;
                }
                ns++;
            }
    }
    qsort(sk, (size_t)ns, 16, i64pair_cmp);
    for (i64 x = 0; x < ns;) {
        i64 y = x;
        while (y < ns && sk[2 * y] == sk[2 * x])
            y++;
        if (y - x > 1) {
            i64 keep = sk[2 * x + 1];
            for (i64 z = x; z < y; z++)
                if (orig[sk[2 * z + 1]].skip == sk[2 * x])
                    keep = sk[2 * z + 1];
            for (i64 z = x; z < y; z++)
                if (sk[2 * z + 1] != keep) {
                    if (q->nban == q->bancap) {
                        q->bancap = q->bancap ? q->bancap * 2 : 64;
                        q->ban = realloc(q->ban, (size_t)q->bancap * 16);
                    }
                    q->ban[2 * q->nban] = sk[2 * z + 1];
                    q->ban[2 * q->nban + 1] = sk[2 * x];
                    q->nban++;
                    added++;
                }
        }
        x = y;
    }
    free(sk);
    return added;
}
/* the whole sequence */
static void co_full(Ev *ev, i64 N) {
    double t0 = wall();
    CO q;
    memset(&q, 0, sizeof q);
    Ev *orig = malloc((size_t)N * sizeof(Ev));
    memcpy(orig, ev, (size_t)N * sizeof(Ev));
    i64 l0 = seq_length(ev, N), l1;
    int chg, rounds = 0;
    for (;;) {
        i64 gain = co_run(&q, ev, N, 0, N - 1, co_skip, &chg);
        l1 = seq_length(ev, N);
        rounds++;
        if (l0 - l1 != gain)
            DIE("internal error: cluster optimisation promised %lld, got %lld", gain, l0 - l1);
        if (!co_skip || !co_clash(&q, orig, ev, N))
            break;
        memcpy(ev, orig, (size_t)N * sizeof(Ev));
    }
    printf(
        "cluster optimisation: %lld -> %lld (%d openings changed; %lld of %lld events free, %lld options, at most %lld per event, %d pass%s, %d bans, %.1fs)\n",
        l0, l1, chg, q.nfree, N, q.nopt, q.maxm, rounds, rounds > 1 ? "es" : "", q.nban, wall() - t0);
    fflush(stdout);
    free(orig);
    free(q.t);
    free(q.S);
    free(q.E);
    free(q.Ep);
    free(q.mv);
    free(q.d);
    free(q.rel);
    free(q.off);
    free(q.lmin);
    free(q.cur);
    free(q.ban);
}

/* ==================== own part of this file: relocation with re-cutting (--dpa) ==================== */
/* ---------- relocation with re-cutting (option --dpa): what a trail costs where it stands and what it would cost
   elsewhere when all other trails may change their cuts.
   Forward / backward tables of the fixed-order DP: F_i(o) = cheapest way to write events 0..i with event i cut open
   at o, B_i(o) = cheapest way to write events i..N-1 (both count D(o)); OPT = min F_{N-1} = min B_0.
   slack_i(o) = F_i(o) + B_i(o) - D(o) - OPT is what cut o costs more than the best sequence of cuts.
   Removal of event i saves   rho_i = OPT - min over (p, q) of F_{i-1}(p) + d(E_p, S_q) + B_{i+1}(q).
   Insertion of trail t (cut o) into the gap between events x, y = x + 1 costs
       iota = min over (p, q) of F_x(p) + d(E_p, S_o) + D(o) + d(E_o, S_q) + B_y(q) - OPT  >=  max(slack_x(p), slack_y(q)),
   so only the cuts of x and y with slack <= dpa_tau matter: they are indexed by their words (the ends of E and
   the beginnings of S, as the nodes are in the index of the search) and every cut of t looks itself up.  A
   relocation with rho - iota > 0 is tried for real (the trail is moved, the DP is run on the two windows) and kept
   if the sequence gets shorter. */
static int dpa_on = 0, dpa_tau = 1, dpa_theta = 3, dpa_win = 12, dpa_cap = 64, dpa_verbose = 0;
static i64 dpa_maxtry = 2000;
static CO DPA_co;
static Ev *DPA_tmp;
static i64 DPA_cap; /* work area of a sweep: the table of the fixed-order pass, a second copy of the sequence */
static Ev *dpa_buf(i64 N) {
    if (N > DPA_cap) {
        DPA_cap = N + N / 4 + 64;
        DPA_tmp = realloc(DPA_tmp, (size_t)DPA_cap * sizeof(Ev));
        if (!DPA_tmp)
            DIE("out of memory");
    }
    return DPA_tmp;
}
typedef struct {
    i64 *cur, *off, *fmin, *bmin;
    int *mm, *rho;
    unsigned char *fr, *br;
    i64 cap, rcap, opt, curcost;
    u64 *S, *E, *Wp, *Wq;
    unsigned char *ban, *dd;
    int *mv;
    i64 wcap;
    CO q;
} DPT;
/* words, cut costs and bans of the options of event x (one option if o0 < 0); returns their number */
static i64 dp_words(DPT *D, const Ev *x, i64 o0, u64 *S, u64 *E) {
    if (o0 < 0) {
        S[0] = x->s;
        E[0] = x->e;
        D->ban[0] = 0;
        D->dd[0] = 0;
        return 1;
    }
    const Trail *T = &TR[x->t];
    i64 m = T->ohi - T->olo;
    for (i64 j = 0; j < m; j++) {
        i64 o = T->olo + j;
        D->dd[j] = (unsigned char)oD(o);
        if (OP[o].g1 && oSK_t(T, o) != x->skip) {
            D->ban[j] = 1;
            S[j] = E[j] = 0;
            continue;
        }
        D->ban[j] = 0;
        S[j] = oS_t(T, o);
        E[j] = oE_t(T, o);
    }
    return m;
}
/* mv[j] = min over the options p of the neighbouring layer of prel[p] + d; dir 0: d(Wp[p], Wc[j]), dir 1: d(Wc[j], Wp[p]) */
static void dp_step(DPT *D, int dir, i64 pm, const u64 *Wp, const unsigned char *prel, i64 m, const u64 *Wc,
                    const unsigned char *ban, int *mv) {
    for (i64 j = 0; j < m; j++)
        mv[j] = h;
    if (pm <= 4) {
        for (i64 p = 0; p < pm; p++)
            if (prel[p] < h)
                for (i64 j = 0; j < m; j++) {
                    if (ban[j])
                        continue;
                    int v = prel[p] + (dir ? dist(Wc[j], Wp[p]) : dist(Wp[p], Wc[j]));
                    if (v < mv[j])
                        mv[j] = v;
                }
        return;
    }
    CO *q = &D->q;
    u64 need = 16;
    while (need < 2 * (u64)pm)
        need <<= 1;
    if (need > q->cap) {
        free(q->t);
        q->t = calloc(need, sizeof(CSlot));
        q->cap = need;
        q->gen = 0;
        if (!q->t)
            DIE("out of memory");
    }
    u64 mask = need - 1;
    for (int k = h; k >= 1; k--) {
        i64 cnt = 0;
        int sh = 4 * (h - k);
        q->gen++;
        for (i64 p = 0; p < pm; p++)
            if (prel[p] < k) {
                co_put(q, mask, dir ? Wp[p] >> sh : Wp[p] & HMASK[k], prel[p]);
                cnt++;
            }
        if (!cnt)
            break;
        for (i64 j = 0; j < m; j++) {
            if (ban[j] || mv[j] <= h - k)
                continue;
            int v = co_get(q, mask, dir ? Wc[j] & HMASK[k] : Wc[j] >> sh);
            if (v >= 0 && v + h - k < mv[j])
                mv[j] = v + h - k;
        }
    }
}
/* Forward and backward tables of the fixed-order pass for the whole sequence: for every cut of every event
   its cost relative to the minimum of its layer (fr, br; 255: not allowed), the minima fmin / bmin, and opt, the
   cost of the best choice of cuts for this order.  The two directions must agree. */
static void dp_tables(DPT *D, const Ev *ev, i64 N) {
    if (N + 2 > D->cap) {
        D->cap = N + N / 4 + 64;
        size_t m = (size_t)D->cap;
        D->cur = realloc(D->cur, m * 8);
        D->off = realloc(D->off, m * 8);
        D->fmin = realloc(D->fmin, m * 8);
        D->bmin = realloc(D->bmin, m * 8);
        D->mm = realloc(D->mm, m * sizeof(int));
        D->rho = realloc(D->rho, m * sizeof(int));
    }
    i64 tot = 0, maxm = 1, cc = 0;
    for (i64 i = 0; i < N; i++) {
        D->cur[i] = co_cur(&ev[i]);
        D->off[i] = tot;
        i64 m = D->cur[i] < 0 ? 1 : TR[ev[i].t].ohi - TR[ev[i].t].olo;
        D->mm[i] = (int)m;
        tot += m;
        if (m > maxm)
            maxm = m;
        cc += (D->cur[i] >= 0 ? oD(D->cur[i]) : 0) + (i + 1 < N ? dist(ev[i].e, ev[i + 1].s) : 0);
    }
    D->curcost = cc;
    if (tot > D->rcap) {
        D->rcap = tot + tot / 8 + 64;
        D->fr = realloc(D->fr, (size_t)D->rcap);
        D->br = realloc(D->br, (size_t)D->rcap);
        if (!D->fr || !D->br)
            DIE("out of memory");
    }
    if (maxm > D->wcap) {
        D->wcap = maxm + 64;
        size_t m = (size_t)D->wcap;
        D->S = realloc(D->S, m * 8);
        D->E = realloc(D->E, m * 8);
        D->Wp = realloc(D->Wp, m * 8);
        D->Wq = realloc(D->Wq, m * 8);
        D->ban = realloc(D->ban, m);
        D->dd = realloc(D->dd, m);
        D->mv = realloc(D->mv, m * sizeof(int));
        if (!D->S || !D->E || !D->Wp || !D->Wq || !D->ban || !D->dd || !D->mv)
            DIE("out of memory");
    }
    for (int dir = 0; dir < 2; dir++) {
        unsigned char *rel = dir ? D->br : D->fr;
        i64 *lmin = dir ? D->bmin : D->fmin;
        i64 pm = 0;
        const unsigned char *prel = NULL;
        for (i64 z = 0; z < N; z++) {
            i64 i = dir ? N - 1 - z : z, m = dp_words(D, &ev[i], D->cur[i], D->S, D->E);
            int *mv = D->mv, mn = 1 << 20;
            if (!z)
                for (i64 j = 0; j < m; j++)
                    mv[j] = 0;
            else
                dp_step(D, dir, pm, D->Wp, prel, m, dir ? D->E : D->S, D->ban, mv);
            for (i64 j = 0; j < m; j++)
                if (!D->ban[j]) {
                    mv[j] += D->dd[j];
                    if (mv[j] < mn)
                        mn = mv[j];
                }
            unsigned char *r = rel + D->off[i];
            for (i64 j = 0; j < m; j++)
                r[j] = D->ban[j] ? 255 : (unsigned char)(mv[j] - mn > 254 ? 254 : mv[j] - mn);
            lmin[i] = (z ? lmin[dir ? i + 1 : i - 1] : 0) + mn;
            memcpy(D->Wp, dir ? D->S : D->E, (size_t)m * 8);
            prel = r;
            pm = m;
        }
    }
    D->opt = D->fmin[N - 1];
    if (D->opt != D->bmin[0])
        DIE("internal error: forward DP %lld, backward DP %lld", D->opt, D->bmin[0]);
}
#define DP_SLACK(D, i, j, dj) \
    ((D)->fmin[i] + (D)->fr[(D)->off[i] + (j)] + (D)->bmin[i] + (D)->br[(D)->off[i] + (j)] - (dj) - (D)->opt)
/* rho for every free event that has both neighbours (others: 0) */
static void dp_rho(DPT *D, const Ev *ev, i64 N) {
    for (i64 i = 0; i < N; i++)
        D->rho[i] = 0;
    for (i64 i = 1; i + 1 < N; i++) {
        if (D->cur[i] < 0)
            continue;
        i64 pm = dp_words(D, &ev[i - 1], D->cur[i - 1], D->S, D->Wp); /* E of the left neighbour */
        i64 m =
            dp_words(D, &ev[i + 1], D->cur[i + 1], D->Wq, D->E); /* S of the right neighbour; its bans stay in D->ban */
        dp_step(D, 0, pm, D->Wp, D->fr + D->off[i - 1], m, D->Wq, D->ban, D->mv);
        int best = 1 << 20;
        const unsigned char *b = D->br + D->off[i + 1];
        for (i64 j = 0; j < m; j++)
            if (!D->ban[j] && D->mv[j] + b[j] < best)
                best = D->mv[j] + b[j];
        D->rho[i] = (int)(D->opt - (D->fmin[i - 1] + best + D->bmin[i + 1]));
    }
}
/* the cuts with slack <= tau of both sides of every gap, indexed by their words */
/* gap, word (E of the left event or S of the right event), F or B of the cut relative to the minimum of its layer */
typedef struct {
    int g;
    u64 w;
    int c;
} DpE;
typedef struct {
    DpE *L, *R;
    i64 nL, nR, capL, capR;
    i64 *ls, *rs2;
    HTab H;
    u64 *bf, bfmask;
    i64 gcap;
    int kmax;
    u32 *stamp, st;
    int *bc, *tl;
    u32 *bo;
} DpX;
/* The index of the places a trail could go to: for every gap between two events, the cuts of both neighbours
   that are within dpa_tau of their best (at most dpa_cap per event), hashed by the ends of their words. */
static void dpx_build(DpX *X, DPT *D, const Ev *ev, i64 N) {
    if (N + 2 > X->gcap) {
        X->gcap = N + N / 4 + 64;
        size_t m = (size_t)X->gcap;
        X->ls = realloc(X->ls, (m + 1) * 8);
        X->rs2 = realloc(X->rs2, (m + 1) * 8);
        free(X->stamp);
        X->stamp = calloc(m, sizeof(u32));
        X->st = 0;
        X->bc = realloc(X->bc, m * sizeof(int));
        X->tl = realloc(X->tl, m * sizeof(int));
        X->bo = realloc(X->bo, m * sizeof(u32));
    }
    X->nL = X->nR = 0;
    /* gap g lies between events g and g + 1; L: cuts of event g with their forward cost, R: cuts of event g + 1 with their backward cost */
    for (i64 i = 0; i < N; i++) {
        i64 m = dp_words(D, &ev[i], D->cur[i], D->S, D->E), kept = 0;
        X->ls[i] = X->nL;
        X->rs2[i] = X->nR;
        for (int pass = 0; pass <= dpa_tau && kept < dpa_cap; pass++) /* smallest slack first */
            for (i64 j = 0; j < m && kept < dpa_cap; j++) {
                if (D->ban[j])
                    continue;
                i64 sl = DP_SLACK(D, i, j, D->dd[j]);
                if (sl != pass)
                    continue;
                kept++;
                if (X->nL == X->capL) {
                    X->capL = X->capL ? X->capL * 2 : 65536;
                    X->L = realloc(X->L, (size_t)X->capL * sizeof(DpE));
                }
                if (X->nR == X->capR) {
                    X->capR = X->capR ? X->capR * 2 : 65536;
                    X->R = realloc(X->R, (size_t)X->capR * sizeof(DpE));
                }
                if (!X->L || !X->R)
                    DIE("out of memory");
                /* as the left side of gap i: F_i(o); as the right side of gap i - 1: B_i(o) */
                X->L[X->nL].g = (int)i;
                X->L[X->nL].w = D->E[j];
                X->L[X->nL].c = D->fr[D->off[i] + j];
                X->nL++;
                X->R[X->nR].g = (int)i - 1;
                X->R[X->nR].w = D->S[j];
                X->R[X->nR].c = D->br[D->off[i] + j];
                X->nR++;
            }
    }
    X->ls[N] = X->nL;
    X->rs2[N] = X->nR;
    /* depth of the index of gap g: ceil((c_g + 2 tau + theta) / 2) - 1 levels, c_g = the cost of its join, so that every insertion
       cheaper than dpa_theta is found (one that is not found overlaps by too little on both sides) */
#define DPX_K(g)                                                                       \
    ({                                                                                 \
        int k_ = (dist(ev[g].e, ev[(g) + 1].s) + 2 * dpa_tau + dpa_theta + 1) / 2 - 1; \
        k_<0 ? 0 : k_> h - 1 ? h - 1 : k_;                                             \
    })
    i64 nidx = 0;
    X->kmax = 0;
    for (i64 e = 0; e < X->nL; e++)
        if (X->L[e].g < N - 1)
            nidx += DPX_K(X->L[e].g) + 1;
    for (i64 e = 0; e < X->nR; e++)
        if (X->R[e].g >= 0)
            nidx += DPX_K(X->R[e].g) + 1;
    h_reset(&X->H, nidx);
    {
        u64 bits = 1 << 16;
        while (bits < (u64)nidx * 16)
            bits <<= 1;
        if (bits - 1 != X->bfmask || !X->bf) {
            free(X->bf);
            X->bf = malloc(bits / 8);
            X->bfmask = bits - 1;
            if (!X->bf)
                DIE("out of memory");
        }
        memset(X->bf, 0, bits / 8);
    }
    for (i64 e = 0; e < X->nL; e++) {
        if (X->L[e].g >= N - 1)
            continue;
        int kk = DPX_K(X->L[e].g);
        if (kk > X->kmax)
            X->kmax = kk;
        for (int j = 0; j <= kk; j++) {
            u64 k0 = HKEY(X->L[e].w & HMASK[h - j], j, 0), b = BFH(k0) & X->bfmask;
            h_add(&X->H, k0, (int)e);
            X->bf[b >> 6] |= 1ULL << (b & 63);
        }
    }
    for (i64 e = 0; e < X->nR; e++) {
        if (X->R[e].g < 0)
            continue;
        int kk = DPX_K(X->R[e].g);
        for (int j = 0; j <= kk; j++) {
            u64 k1 = HKEY(X->R[e].w >> (4 * j), j, 1), b = BFH(k1) & X->bfmask;
            h_add(&X->H, k1, (int)e);
            X->bf[b >> 6] |= 1ULL << (b & 63);
        }
    }
}
/* cheapest insertions of the trail of event i: gaps in tl[0 ..], cost bc[gap] (iota), cut bo[gap]; returns their number */
static int dpx_row(DpX *X, const DPT *D, const Ev *x, i64 N) {
    const Trail *T = &TR[x->t];
    const HTab *H = &X->H;
    int nt = 0;
    if (++X->st == 0) {
        memset(X->stamp, 0, (size_t)X->gcap * sizeof(u32));
        X->st = 1;
    }
    u32 st = X->st;
#define DPX_CAND(g_, c_, o_)           \
    do {                               \
        int g__ = (g_), c__ = (c_);    \
        if (X->stamp[g__] != st) {     \
            X->stamp[g__] = st;        \
            X->bc[g__] = c__;          \
            X->bo[g__] = (u32)(o_);    \
            X->tl[nt++] = g__;         \
        } else if (c__ < X->bc[g__]) { \
            X->bc[g__] = c__;          \
            X->bo[g__] = (u32)(o_);    \
        }                              \
    } while (0)
    for (i64 o = T->olo; o < T->ohi; o++) {
        if (OP[o].g1 && oSK_t(T, o) != x->skip)
            continue;
        u64 S = oS_t(T, o), E = oE_t(T, o);
        int Dq = oD(o);
        for (int j = 0; j <= X->kmax; j++) {
            u64 k0 = HKEY(S >> (4 * j), j, 0), k1 = HKEY(E & HMASK[h - j], j, 1), b0 = BFH(k0) & X->bfmask,
                b1 = BFH(k1) & X->bfmask;
            if ((X->bf[b0 >> 6] >> (b0 & 63)) & 1)
                for (int e = h_get(H, k0); e >= 0; e = H->next[e]) {
                    const DpE *l = &X->L[H->val[e]];
                    int g = l->g;
                    if (dist(l->w, S) != j)
                        continue;
                    int best = 1 << 20;
                    for (i64 r = X->rs2[g + 1]; r < X->rs2[g + 2]; r++) {
                        int v = dist(E, X->R[r].w) + X->R[r].c;
                        if (v < best)
                            best = v;
                    }
                    if (best >= (1 << 20))
                        continue;
                    /* F_g(p) + j + D + d(E, S_q) + B_{g+1}(q) - OPT */
                    DPX_CAND(g, (int)(D->fmin[g] + l->c + j + Dq + best + D->bmin[g + 1] - D->opt), o - T->olo);
                }
            if ((X->bf[b1 >> 6] >> (b1 & 63)) & 1)
                for (int e = h_get(H, k1); e >= 0; e = H->next[e]) {
                    const DpE *rr = &X->R[H->val[e]];
                    int g = rr->g;
                    if (dist(E, rr->w) != j)
                        continue;
                    int best = 1 << 20;
                    for (i64 l = X->ls[g]; l < X->ls[g + 1]; l++) {
                        int v = dist(X->L[l].w, S) + X->L[l].c;
                        if (v < best)
                            best = v;
                    }
                    if (best >= (1 << 20))
                        continue;
                    DPX_CAND(g, (int)(D->fmin[g] + best + Dq + j + rr->c + D->bmin[g + 1] - D->opt), o - T->olo);
                }
        }
    }
#undef DPX_CAND
    (void)N;
    return nt;
}
/* cheapest insertions (with re-cutting) of every trail: up to DPA_RK gaps per event, cheapest first */
#define DPA_RK 4
typedef struct {
    int g, c;
    u32 oo;
} DpI;
/* window i..j of the sequence and the estimate of its gain */
typedef struct {
    int i, j, est, rho;
} DpC;
/* Order of the candidate windows: by falling estimate, then shorter windows first, then by position. */
static int dpc_cmp(const void *a, const void *b) {
    const DpC *x = a, *y = b;
    int lx = x->j - x->i, ly = y->j - y->i;
    return x->est != y->est ? (x->est > y->est ? -1 : 1)
           : lx != ly       ? (lx < ly ? -1 : 1)
                            : (x->i < y->i ? -1 : x->i > y->i);
}
static DPT G_dpt;
static DpX G_dpx;
static DpI *G_dpi;
static int *G_dpn;
static i64 G_dpicap;
static int dpa_imax = 2, dpa_lmax = 24, dpa_full = 10, dpa_thr = 1, dpa_quiet = 0;
static double dpa_sec = 0;
static const char *dpa_ckpt = NULL; /* dpa_ckpt: plan written after every sweep that gained */
/* the window i..j is taken out and member z goes into gap gp[z] with cut op[z]; then the DP is run on the W
   events on either side of every changed place (W <= 0: on the whole sequence).  The new sequence is left in tmp,
   the changed places (the hole first) in pos[0 .. j - i + 1]; returns the length. */
static i64 dpa_build(const Ev *ev, i64 N, int i, int j, const int *gp, const u32 *op, Ev *tmp, CO *co, i64 W,
                     i64 *pos) {
    i64 m = 0;
    int k = j - i + 1, chg;
    pos[0] = 0;
    for (i64 q = 0; q < N; q++) {
        if (q < i || q > j)
            tmp[m++] = ev[q];
        if (q == i - 1)
            pos[0] = m;
        for (int z = 0; z < k; z++)
            if (gp[z] == q) {
                pos[z + 1] = m;
                tmp[m++] = make_event(TR[ev[i + z].t].olo + op[z]);
            }
    }
    if (m != N)
        DIE("internal error: dpa_build wrote %lld of %lld events", m, N);
    if (W <= 0)
        co_run(co, tmp, N, 0, N - 1, 0, &chg);
    else
        for (int z = 0; z <= k; z++) {
            i64 a = pos[z] - W, b = pos[z] + W;
            if (a < 0)
                a = 0;
            if (b > N - 1)
                b = N - 1;
            co_run(co, tmp, N, a, b, 0, &chg);
        }
    return seq_length(tmp, N);
}
/* one sweep: tables, candidates (single trails and windows of consecutive trails), trials.  Returns the gain. */
static i64 dpa_sweep(Ev *ev, i64 N, CO *co, Ev *tmp) {
    DPT *D = &G_dpt;
    DpX *X = &G_dpx;
    double t0 = wall(), t1;
    int chg;
    if (dpa_lmax > 64)
        dpa_lmax = 64;
    {
        i64 g0 = co_run(co, ev, N, 0, N - 1, 0, &chg);
        if (g0 > 0) {
            if (!dpa_quiet) {
                printf("dpa: fixed-order DP gains %lld\n", g0);
                fflush(stdout);
            }
            return g0;
        }
    }
    dp_tables(D, ev, N);
    i64 hs[5] = {0}, nfree = 0, z0 = 0, z1 = 0;
    for (i64 i = 0; i < N; i++) {
        if (D->cur[i] < 0)
            continue;
        const Trail *T = &TR[ev[i].t];
        i64 c0 = 0, c1 = 0;
        nfree++;
        for (i64 j = 0; j < D->mm[i]; j++) {
            if (D->fr[D->off[i] + j] == 255)
                continue;
            i64 sl = DP_SLACK(D, i, j, oD(T->olo + j));
            c0 += sl == 0;
            c1 += sl == 1;
        }
        z0 += c0;
        z1 += c1;
        hs[c0 <= 1 ? 0 : c0 == 2 ? 1 : c0 <= 5 ? 2 : c0 <= 20 ? 3 : 4]++;
    }
    t1 = wall();
    if (dpa_verbose)
        printf(
            "dpa: cost now %lld, best for this order %lld; %lld free events; openings without slack: %lld (events with 1: %lld, 2: %lld, 3-5: %lld, 6-20: %lld, more: %lld), with slack 1: %lld (%.1fs)\n",
            D->curcost, D->opt, nfree, z0, hs[0], hs[1], hs[2], hs[3], hs[4], z1, t1 - t0);
    dp_rho(D, ev, N);
    i64 hr[5] = {0}, sr = 0;
    for (i64 i = 1; i + 1 < N; i++)
        if (D->cur[i] >= 0) {
            int r = D->rho[i];
            hr[r < 0 ? 0 : r > 3 ? 4 : r]++;
            sr += r;
        }
    if (dpa_verbose) {
        printf(
            "dpa: taking one trail out (the others re-opened) saves 0: %lld trails, 1: %lld, 2: %lld, 3: %lld, more: %lld (sum %lld) (%.1fs)\n",
            hr[0], hr[1], hr[2], hr[3], hr[4], sr, wall() - t1);
        fflush(stdout);
    }
    t1 = wall();
    dpx_build(X, D, ev, N);
    if (N > G_dpicap) {
        G_dpicap = N + N / 4 + 64;
        G_dpi = realloc(G_dpi, (size_t)G_dpicap * DPA_RK * sizeof(DpI));
        G_dpn = realloc(G_dpn, (size_t)G_dpicap * sizeof(int));
        if (!G_dpi || !G_dpn)
            DIE("out of memory");
    }
    i64 hi[5] = {0};
#pragma omp parallel num_threads(dpa_thr)
    {
        DpX Y = *X;
        size_t gm = (size_t)X->gcap;
        i64 lh[5] = {0}; /* the index is shared, the scratch arrays are not */
        Y.stamp = calloc(gm, sizeof(u32));
        Y.st = 0;
        Y.bc = malloc(gm * sizeof(int));
        Y.tl = malloc(gm * sizeof(int));
        Y.bo = malloc(gm * sizeof(u32));
        if (!Y.stamp || !Y.bc || !Y.tl || !Y.bo)
            DIE("out of memory");
#pragma omp for schedule(dynamic, 16)
        for (i64 i = 0; i < N; i++) {
            G_dpn[i] = 0;
            if (i < 1 || i + 1 >= N || D->cur[i] < 0)
                continue;
            int nt = dpx_row(&Y, D, &ev[i], N), nk = 0;
            DpI *I = G_dpi + (size_t)i * DPA_RK;
            for (int k = 0; k < nt; k++) {
                int g = Y.tl[k], c = Y.bc[g], p;
                if ((g >= i - 2 && g <= i + 1) || c > dpa_imax)
                    continue; /* not next to itself */
                if (nk < DPA_RK)
                    p = nk++;
                else if (I[DPA_RK - 1].c <= c)
                    continue;
                else
                    p = DPA_RK - 1;
                while (p > 0 && I[p - 1].c > c) {
                    I[p] = I[p - 1];
                    p--;
                }
                I[p].g = g;
                I[p].c = c;
                I[p].oo = Y.bo[g];
            }
            G_dpn[i] = nk;
            lh[!nk ? 4 : I[0].c < 0 ? 0 : I[0].c > 3 ? 4 : I[0].c]++;
        }
#pragma omp critical(dpa)
        for (int k = 0; k < 5; k++)
            hi[k] += lh[k];
        free(Y.stamp);
        free(Y.bc);
        free(Y.tl);
        free(Y.bo);
    }
    if (dpa_verbose) {
        printf(
            "dpa: %lld + %lld indexed openings (slack <= %d, levels <= %d); the cheapest other place of a trail (the others re-opened) costs 0: %lld trails, 1: %lld, 2: %lld, 3: %lld, more: %lld (%.1fs)\n",
            X->nL, X->nR, dpa_tau, X->kmax, hi[0], hi[1], hi[2], hi[3], hi[4], wall() - t1);
        fflush(stdout);
    }
    t1 = wall();
    /* candidates */
    DpC *cd = NULL;
    i64 nc = 0, ccap = 0, nwin = 0, nrho = 0;
    for (i64 i = 1; i + 1 < N; i++) {
        for (i64 j = i; j + 1 < N && j - i < dpa_lmax; j++) {
            if (D->cur[j] < 0 || !G_dpn[j])
                break;
            /* cheapest place of every member outside the window */
            i64 sum = 0;
            int ok = 1;
            for (i64 t = i; t <= j && ok; t++) {
                const DpI *I = G_dpi + (size_t)t * DPA_RK;
                int f = -1;
                for (int k = 0; k < G_dpn[t]; k++)
                    if (I[k].g < i - 2 || I[k].g > j + 1) {
                        f = k;
                        break;
                    }
                if (f < 0)
                    ok = 0;
                else
                    sum += I[f].c;
            }
            if (!ok)
                continue;
            nwin++;
            i64 mid = D->opt - D->fmin[i - 1] - D->bmin[j + 1];
            int rho;
            if (sum >= mid)
                continue;
            if (j == i)
                rho = D->rho[i];
            else {
                i64 pm = dp_words(D, &ev[i - 1], D->cur[i - 1], D->S, D->Wp),
                    m = dp_words(D, &ev[j + 1], D->cur[j + 1], D->Wq, D->E);
                dp_step(D, 0, pm, D->Wp, D->fr + D->off[i - 1], m, D->Wq, D->ban, D->mv);
                int best = 1 << 20;
                const unsigned char *b = D->br + D->off[j + 1];
                for (i64 q = 0; q < m; q++)
                    if (!D->ban[q] && D->mv[q] + b[q] < best)
                        best = D->mv[q] + b[q];
                rho = (int)(D->opt - (D->fmin[i - 1] + best + D->bmin[j + 1]));
                nrho++;
            }
            if (rho - sum <= 0)
                continue;
            if (nc == ccap) {
                ccap = ccap ? ccap * 2 : 1024;
                cd = realloc(cd, (size_t)ccap * sizeof(DpC));
            }
            cd[nc].i = (int)i;
            cd[nc].j = (int)j;
            cd[nc].est = (int)(rho - sum);
            cd[nc].rho = rho;
            nc++;
        }
    }
    if (nc)
        qsort(cd, (size_t)nc, sizeof(DpC), dpc_cmp);
    if (dpa_verbose) {
        printf("dpa: %lld windows of trails that have a cheap other place, %lld evaluated, %lld candidates (%.1fs)\n",
               nwin, nrho, nc, wall() - t1);
        fflush(stdout);
    }
    t1 = wall();
    /* trials, best estimate first.  A trial that gains is kept; the trails near its changed places are marked, and
       later candidates of this sweep must lie clear of them (their numbers come from tables that are now out of
       date there).  A trial without a gain is repeated with wider DP windows; after a DP on the whole sequence the
       sweep ends. */
    i64 total = 0, ntry = 0, nfull = 0, napp = 0, l0 = seq_length(ev, N), lc = l0;
    int stop = 0;
    int *tid0 = malloc((size_t)N * sizeof(int)), *where = malloc(((size_t)NT + 1) * sizeof(int));
    char *dirty = calloc((size_t)NT + 1, 1);
    for (i64 q = 0; q < N; q++) {
        tid0[q] = (int)ev[q].t;
        where[ev[q].t] = (int)q;
    }
    for (i64 k = 0; k < nc && ntry < dpa_maxtry && !stop; k++) {
        const DpC *c = &cd[k];
        int gp[72], kk = c->j - c->i + 1, ok = 1;
        u32 op[72];
        i64 pos[73];
        int p0 = where[tid0[c->i]];
        if (p0 < 1 || p0 + kk >= N || dirty[ev[p0 - 1].t] || dirty[ev[p0 + kk].t])
            continue;
        for (int z = 0; z < kk && ok; z++) {
            int t = c->i + z, p = where[tid0[t]];
            const DpI *I = G_dpi + (size_t)t * DPA_RK;
            int f = -1;
            if (p != p0 + z || dirty[tid0[t]] || co_cur(&ev[p]) < 0) {
                ok = 0;
                break;
            }
            for (int q = 0; q < G_dpn[t]; q++)
                if (I[q].g < c->i - 2 || I[q].g > c->j + 1) {
                    f = q;
                    break;
                }
            if (f < 0) {
                ok = 0;
                break;
            }
            int gl = tid0[I[f].g], gr = tid0[I[f].g + 1];
            if (dirty[gl] || dirty[gr] || where[gr] != where[gl] + 1) {
                ok = 0;
                break;
            }
            gp[z] = where[gl];
            op[z] = I[f].oo;
        }
        if (!ok)
            continue;
        ntry++;
        i64 W = dpa_win, l1;
        for (;;) {
            l1 = dpa_build(ev, N, p0, p0 + kk - 1, gp, op, tmp, co, W, pos);
            if (l1 < lc || W <= 0)
                break;
            if (W < 16 * (i64)dpa_win && 4 * W < N)
                W *= 4;
            else if (nfull < dpa_full) {
                nfull++;
                W = 0;
            } else
                break;
        }
        if (dpa_verbose > 1 || l1 < lc) {
            printf(
                "  dpa: window %d..%d (%d trails, first trail %u to gap %d): saves %d, estimate %d, length %lld -> %lld (DP %lld events around)\n",
                p0, p0 + kk - 1, kk, ev[p0].t, gp[0], c->rho, c->est, lc, l1, W);
            fflush(stdout);
        }
        if (l1 >= lc)
            continue;
        memcpy(ev, tmp, (size_t)N * sizeof(Ev));
        total += lc - l1;
        lc = l1;
        napp++;
        if (W <= 0)
            stop = 1;
        else
            for (int z = 0; z <= kk; z++)
                for (i64 q = pos[z] - W - 2; q <= pos[z] + W + 2; q++)
                    if (q >= 0 && q < N)
                        dirty[ev[q].t] = 1;
        for (i64 q = 0; q < N; q++)
            where[ev[q].t] = (int)q;
    }
    free(tid0);
    free(where);
    free(dirty);
    if (total) {
        i64 g1 = co_run(co, ev, N, 0, N - 1, 0, &chg);
        total += g1;
        if (dpa_ckpt)
            write_plan(ev, N, dpa_ckpt);
    }
    if (!dpa_quiet || total) {
        printf(
            "dpa: %lld -> %lld (%lld candidates, %lld tried, %lld applied, %lld with the DP on the whole sequence; %.1fs)\n",
            l0, l0 - total, nc, ntry, napp, nfull, wall() - t0);
        fflush(stdout);
    }
    free(cd);
    return total;
}

/* ==================== shared base again: the search (it calls the pass for --dpa-sec), the loader, main (it calls dpa_sweep) ==================== */
/* ---------- shared best sequence */
static Ev *G_ev;
static i64 G_N, G_len;
static int G_dirty;
static double G_t0, G_last_ck, G_last_log, G_last_dpa;
static i64 G_it[256];
static double wall(void);

/* One search thread.  Until the time or the iteration limit: choose trails to remove, take them out, put each
   back (greedy order or random order, with or without noise), accept or undo by the annealing rule.  A new best
   sequence goes to the shared copy G_ev under the lock gbest; odd threads adopt the shared best at sync time. */
static void search(Ctx *c, const Ev *init_ev, i64 initN, const char *outplan) {
    rseed(c, seed * 1000003ULL + (u64)c->tid * 7919ULL);
    c->rem = calloc((size_t)NT + 1, 1);
    c->pend = malloc(((size_t)NT + 1) * sizeof(u32));
    c->vct = calloc((size_t)NT + 1, sizeof(int));
    c->thead = malloc(((size_t)NT + 1) * sizeof(int));
    c->rth = malloc(((size_t)NT + 1) * 2 * sizeof(int));
    ctx_load(c, init_ev, initN);
    c->cur = ctx_length(c);
    c->best_len = c->cur;
    double tf = NTHR > 1 ? 0.5 + (double)c->tid / (NTHR - 1) : 1.0, last_sync = wall();
    int runcap = 2 * kmax + 2; /* a run longer than this is not removed as a whole */
    Node *nd;
    while ((maxit < 0 || c->it < maxit) && wall() - G_t0 < tlimit) {
        c->it++;
        if (c->H.n > c->H.cap - 40000 || c->nn > c->ncap - 4000) {
            i64 m = ctx_export(c, c->tmp);
            ctx_load(c, c->tmp, m);
        }
        nd = c->nd;
        double frac = (wall() - G_t0) / tlimit, temp = tf * T0 * (1 - frac) + 0.05;
#if defined(TS_CHECK) && TS_CHECK > 1
        seq_check(c);
#endif
        int *order = c->order, *cand = c->cand, *rel = c->rel;
        i64 N = c->N, ncand = c->ncand;
#define EVT(i) (nd[order[i]].v)
#define RS(r) ((r) ? cand[(r) - 1] + 1 : 0) /* run r: positions RS(r) .. RE(r) */
#define RE(r) ((r) < ncand ? cand[r] : (int)N - 1)
        int k = (int)rndint(c, 1, kmax);
        i64 nrem = 0;
        for (i64 q = 0; q < c->nvu; q++)
            c->vct[c->vc[q].t] = 0;
        c->nvu = 0;
        double mode = rndu(c);
#define REMOVE(tt)                          \
    do {                                    \
        u32 t_ = (tt);                      \
        if (!c->rem[t_] && !TR[t_].fixed) { \
            c->rem[t_] = 1;                 \
            c->pend[nrem++] = t_;           \
        }                                   \
    } while (0)
        if (mode < prel) {
            /* a run plus one or two runs whose end / start words are within one step of an cut of its trails */
            int nrun = (int)ncand + 1, X = -1;
            if (rndu(c) < 0.7) {
                for (int tries = 0; tries < 50; tries++) {
                    int r = (int)rndn(c, nrun);
                    if (RE(r) - RS(r) + 1 <= 5) {
                        X = r;
                        break;
                    }
                }
            }
            if (X < 0)
                X = (int)rndn(c, nrun);
            i64 xlen = RE(X) - RS(X) + 1;
            if (xlen > runcap) { /* long run: only a window of it */
                i64 lo = RS(X) + rndn(c, xlen - k + 1 > 0 ? xlen - k + 1 : 1);
                for (i64 i = lo; i <= RE(X) && i < lo + k; i++)
                    REMOVE(EVT(i).t);
            } else {
                i64 nopt = 0;
                for (int i = RS(X); i <= RE(X); i++)
                    nopt += TR[EVT(i).t].ohi - TR[EVT(i).t].olo;
                int nrel = 0;
                if (nopt <= 600000) {
                    /* the index of the sequence already knows which nodes are within one step of an cut */
                    if (++c->mkstamp >> 30) {
                        memset(c->mk, 0, (size_t)c->ncap * sizeof(u32));
                        c->mkstamp = 1;
                    }
                    u32 st = c->mkstamp << 2;
                    for (int i = RS(X); i <= RE(X); i++) {
                        u32 t_ = EVT(i).t;
                        const Trail *T = &TR[t_];
                        if (T->fixed || c->vct[t_])
                            continue;
                        if (bigp < 0.5 && T->ohi - T->olo > splitmax) {
                            mark_near(c, T);
                            continue;
                        } /* likely to be kept out of the removal set */
                        VC *vc = vc_get(c, t_, 1);
                        best_insertion(c, t_, 0.0, vc, 1); /* the full scan, kept for the repair step */
                        for (i64 q = 0; q < vc->nv; q++)
                            if (vc->v[q].k < 4) {
                                int x = vc->v[q].x;
                                if ((c->mk[x] & ~3u) != st)
                                    c->mk[x] = st;
                                c->mk[x] |= 1u << (vc->v[q].k & 1);
                            }
                    }
                    for (int r = 0; r < nrun; r++) {
                        if (r == X || RE(r) - RS(r) + 1 > runcap)
                            continue;
                        if (c->mk[order[RE(r)]] == (st | 1) || c->mk[order[RE(r)]] == (st | 3) ||
                            (c->mk[order[RS(r)]] & ~1u) == (st | 2))
                            rel[nrel++] = r;
                    }
                }
                for (int i = RS(X); i <= RE(X); i++)
                    REMOVE(EVT(i).t);
                int want = (int)rndint(c, 1, 2);
                for (int q = 0; q < want && nrel > 0; q++) {
                    int z = (int)rndn(c, nrel), r = rel[z];
                    rel[z] = rel[--nrel];
                    for (int i = RS(r); i <= RE(r); i++)
                        REMOVE(EVT(i).t);
                }
            }
        } else if (mode < 0.5 + prel / 2) {
            i64 j = ncand ? cand[rndn(c, ncand)] : rndn(c, N - 1);
            i64 lo = j - rndint(c, 0, k);
            if (lo < 0)
                lo = 0;
            for (i64 i = lo; i < N && i < lo + k; i++)
                REMOVE(EVT(i).t);
        } else if (mode < 0.75) {
            for (int q = 0; q < k; q++)
                REMOVE(EVT(rndn(c, N)).t);
        } else {
            int segs = (int)rndint(c, 2, 3), len = k / 2 > 1 ? k / 2 : 1;
            for (int q = 0; q < segs; q++) {
                i64 j = rndn(c, N);
                for (i64 i = j; i < N && i < j + len; i++)
                    REMOVE(EVT(i).t);
            }
        }
        i64 nbig = 0;
        {
            double bp = bigp;
            i64 m = 0;
            for (i64 q = 0; q < nrem; q++) {
                u32 t_ = c->pend[q];
                int big = TR[t_].ohi - TR[t_].olo > splitmax;
                if (big && bp < 1.0 && rndu(c) >= bp) {
                    c->rem[t_] = 0;
                    continue;
                }
                nbig += big;
                c->pend[m++] = t_;
            }
            nrem = m;
        }
        if (!nrem)
            continue;
        if (!nbig && focus > 0 && rndu(c) < focus) {
            for (i64 q = 0; q < nrem; q++)
                c->rem[c->pend[q]] = 0;
            continue;
        }
        /* destroy: the nodes of the removed trails, in the order of the sequence */
        c->nremlog = c->ninslog = 0;
        c->relabeled = 0;
        int nn0 = c->nn, nrk = 0;
        i64 dl = 0; /* dl: change of the length */
        for (i64 q = 0; q < nrem; q++) {
            u32 t_ = c->pend[q];
            c->rem[t_] = 0;
            c->rth[2 * q] = (int)t_;
            c->rth[2 * q + 1] = c->thead[t_];
            for (int id = c->thead[t_]; id >= 0; id = c->tnx[id]) {
                if (nrk == c->rkcap) {
                    c->rkcap = c->rkcap ? c->rkcap * 2 : 256;
                    c->rk = realloc(c->rk, (size_t)c->rkcap * sizeof(i64));
                }
                c->rk[nrk++] = (seq_pos(c, id, N) << 32) | id;
            }
            c->thead[t_] = -1;
        }
        qsort(c->rk, (size_t)nrk, sizeof(i64), i64_cmp);
        for (int q = 0; q < nrk; q++) {
            int id = (int)(c->rk[q] & 0xffffffff);
            dl -= node_len(c, id);
            if (nd[id].v.skip >= 0)
                skp_del(c, nd[id].v.skip);
            node_unlink(c, id);
            c->remlog[c->nremlog++] = id;
        }
        int nskp0 = c->nskp;
        int accept = 0;
        i64 nl = 0;
        if (c->N >= 3) {
            /* repair */
            for (i64 q = nrem - 1; q > 0; q--) {
                i64 z = rndn(c, q + 1);
                u32 x = c->pend[q];
                c->pend[q] = c->pend[z];
                c->pend[z] = x;
            }
            int greedy = rndu(c) < 0.5;
            double noise = rndu(c) < 0.5 ? 0.0 : 0.6;
            i64 np = nrem;
            int uvc = greedy && np > 1; /* new visit lists pay only if trails are evaluated more than once */
            while (np > 0) {
                i64 pick = 0;
                Ins bi = best_insertion(c, c->pend[0], noise, vc_get(c, c->pend[0], uvc), 0);
                if (greedy) {
                    double br = rndu(c);
                    for (i64 q = 1; q < np; q++) {
                        Ins x = best_insertion(c, c->pend[q], noise, vc_get(c, c->pend[q], uvc), 0);
                        double rr = rndu(c);
                        if (x.val < bi.val || (x.val == bi.val && rr < br)) {
                            br = rr;
                            bi = x;
                            pick = q;
                        }
                    }
                }
                u32 t = c->pend[pick];
                Split sp;
                sp.ok = 0;
                if (use_split && TR[t].ohi - TR[t].olo <= splitmax)
                    sp = best_split(c, t, 400);
                if (sp.ok && (double)sp.delta < bi.val) {
                    Ev e1, e2;
                    seg_events(sp.c1, sp.c2, &e1, &e2);
                    int id = node_insert_after(c, c->nd[sp.i].prev, &e1);
                    dl += node_len(c, id);
                    if (c->nvu)
                        vc_update(c, id, pick, np);
                    id = node_insert_after(c, sp.jm, &e2);
                    dl += node_len(c, id);
                    if (c->nvu)
                        vc_update(c, id, pick, np);
                } else {
                    Ev x = make_event(bi.opt);
                    int id = node_insert_after(c, bi.after, &x);
                    dl += node_len(c, id);
                    if (x.skip >= 0)
                        skp_add(c, x.skip);
                    if (c->nvu)
                        vc_update(c, id, pick, np);
                }
                c->pend[pick] = c->pend[--np];
            }
            nl = c->cur + dl;
#if defined(TS_CHECK) && TS_CHECK > 1
            if (nl != ctx_length(c))
                DIE("check: length %lld, by differences %lld at it %lld", ctx_length(c), nl, c->it);
#endif
            i64 d = nl - c->cur;
            accept = d <= 0 || rndu(c) < exp(-(double)d / temp);
        }
        if (accept) {
            c->cur = nl;
            c->acc++;
            if (c->relabeled)
                seq_build(c);
            else
                seq_patch(c, N, nn0);
            for (int q = 0; q < c->nremlog; q++)
                index_del(c, c->remlog[q]);
            if (nl < c->best_len) {
                c->best_len = nl;
#pragma omp critical(gbest)
                if (nl < G_len) {
                    printf("t=%.0fs: best %lld -> %lld (thread %d, it %lld, removed %lld trails, %lld big)\n",
                           wall() - G_t0, G_len, nl, c->tid, c->it, nrem, nbig);
                    fflush(stdout);
                    G_N = ctx_export(c, G_ev);
                    G_len = nl;
                    G_dirty = 1;
                }
            }
        } else {
            for (int q = c->ninslog - 1; q >= 0; q--) {
                node_unlink(c, c->inslog[q]);
                index_del(c, c->inslog[q]);
            }
            for (int q = c->nremlog - 1; q >= 0; q--)
                node_relink(c, c->remlog[q]);
            if (c->relabeled)
                relabel(c);
            for (i64 q = 0; q < nrem; q++)
                c->thead[c->rth[2 * q]] = c->rth[2 * q + 1];
            c->nskp = nskp0;
            for (int q = 0; q < c->nremlog; q++)
                if (nd[c->remlog[q]].v.skip >= 0)
                    skp_add(c, nd[c->remlog[q]].v.skip);
        }
        if ((c->it & 63) == 0) {
            double tn = wall();
            if (tn - last_sync > sync_sec || (c->tid == 0 && tn - G_last_log > 20)) {
                int adopt = 0;
                i64 an = 0;
#pragma omp critical(gbest)
                {
                    G_it[c->tid] = c->it;
                    if (tn - last_sync > sync_sec && (c->tid & 1) && G_len < c->best_len) {
                        memcpy(c->tmp, G_ev, (size_t)G_N * sizeof(Ev));
                        an = G_N;
                        adopt = 1;
                        c->best_len = G_len;
                        c->cur = G_len;
                    }
                    if (c->tid == 0) {
                        if (G_dirty && tn - G_last_ck > ckpt_sec) {
                            write_plan(G_ev, G_N, outplan);
                            G_last_ck = tn;
                            G_dirty = 0;
                        }
                        if (tn - G_last_log > 20) {
                            i64 tot = 0;
                            for (int q = 0; q < NTHR; q++)
                                tot += G_it[q];
                            printf("it %lld t=%.0fs best %lld (thread 0: cur %lld)\n", tot, tn - G_t0, G_len, c->cur);
                            fflush(stdout);
                            G_last_log = tn;
                        }
                    }
                }
                if (tn - last_sync > sync_sec)
                    last_sync = tn;
                if (adopt)
                    ctx_load(c, c->tmp, an);
            }
            if (dpa_sec > 0 && c->tid == 0 &&
                tn - G_last_dpa > dpa_sec) { /* relocation with re-cutting on the current sequence of thread 0 */
                i64 m = ctx_export(c, c->tmp), g, tg = 0;
                const char *ck = dpa_ckpt;
                dpa_ckpt = NULL;
                dpa_quiet = 1;
                while ((g = dpa_sweep(c->tmp, m, &DPA_co, dpa_buf(m))) > 0)
                    tg += g;
                dpa_ckpt = ck;
                dpa_quiet = 0;
                if (tg > 0) {
                    ctx_load(c, c->tmp, m);
                    c->cur -= tg;
                    if (c->cur < c->best_len) {
                        c->best_len = c->cur;
#pragma omp critical(gbest)
                        if (c->cur < G_len) {
                            printf("t=%.0fs: best %lld -> %lld (thread %d, it %lld, relocation with re-opening)\n",
                                   wall() - G_t0, G_len, c->cur, c->tid, c->it);
                            fflush(stdout);
                            G_N = ctx_export(c, G_ev);
                            G_len = c->cur;
                            G_dirty = 1;
                        }
                    }
                }
                G_last_dpa = wall();
            }
        }
    }
#pragma omp critical(gbest)
    G_it[c->tid] = c->it;
#ifdef TS_CHECK
    {
        u64 hsh = 0;
        for (int id = c->first; id >= 0; id = c->nd[id].next) {
            const Ev *x = &c->nd[id].v;
            hsh = hmix(hsh ^ ((u64)x->kind << 60) ^ ((u64)x->t << 36) ^ (u64)x->a) + (u64)x->l;
        }
#pragma omp critical(gbest)
        {
            printf(
                "STATE it %lld cur %lld best %lld acc %lld N %lld seq %016llx rng %016llx %016llx %016llx %016llx" NL,
                c->it, c->cur, c->best_len, c->acc, c->N, hsh, c->rs[0], c->rs[1], c->rs[2], c->rs[3]);
            fflush(stdout);
        }
    }
#endif
}

/* ---------- loading */
static unsigned char *load_word(const char *path, i64 *len) {
    FILE *f = fopen(path, "rb");
    if (!f)
        DIE("cannot open %s", path);
    fseek64(f, 0, SEEK_END);
    i64 sz = ftell64(f);
    fseek64(f, 0, SEEK_SET);
    unsigned char *w = malloc(sz + 16);
    if (!w)
        DIE("out of memory");
    i64 got = 0;
    while (got < sz) {
        size_t r = fread(w + got, 1, (size_t)((sz - got) > (1 << 30) ? (1 << 30) : (sz - got)), f);
        if (!r)
            break;
        got += r;
    }
    fclose(f);
    while (got > 0 && (w[got - 1] == '\n' || w[got - 1] == '\r'))
        got--;
    int map[256];
    for (int c = 0; c < 256; c++)
        map[c] = -1;
    for (int c = 0; c < 16; c++)
        map[(unsigned char)AL[c]] = c;
    for (i64 i = 0; i < got; i++) {
        int v = map[w[i]];
        if (v < 0)
            DIE("bad symbol in %s", path);
        w[i] = (unsigned char)v;
    }
    *len = got;
    return w;
}
static double wall(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static int closes(i64 k, int ex) {
    i64 s = PS[k], l = PL[k], R = l - h - ex;
    return R > 2 * n && !memcmp(W + s + R, W + s, (size_t)(h + ex));
}
/* window positions (in order) of a cyclic word; returns their number */
static i64 trail_windows(const Trail *T, i64 *wp) {
    i64 R = T->R, m = 0;
    int cnt[16] = {0}, distinct = 0;
    if (T->fixed) { /* open path: no wrap-around */
        i64 len = R + h;
        for (i64 i = 0; i < len; i++) {
            if (cnt[T->c[i]]++ == 0)
                distinct++;
            if (i >= n) {
                if (--cnt[T->c[i - n]] == 0)
                    distinct--;
            }
            if (i >= n - 1 && distinct == n)
                wp[m++] = i - n + 1;
        }
        return m;
    }
    for (int k = 0; k < n - 1; k++)
        if (cnt[T->c[k % R]]++ == 0)
            distinct++;
    for (i64 p = 0; p < R; p++) {
        i64 q = p + n - 1;
        if (q >= R)
            q -= R;
        if (cnt[T->c[q]]++ == 0)
            distinct++;
        if (distinct == n)
            wp[m++] = p;
        if (--cnt[T->c[p]] == 0)
            distinct--;
    }
    return m;
}

/* cuts of trail t in window order; writes them to out (if not NULL) and returns their number */
static i64 trail_options(i64 t, i64 *wp, const u64 *dupb, Opt *out, i64 *hist, i64 *shist) {
    if (TR[t].fixed)
        return 0;
    i64 R = TR[t].R, m = trail_windows(&TR[t], wp), k = 0;
    for (i64 i = 0; i < m && m >= 2; i++) {
        i64 i1 = i + 1 == m ? 0 : i + 1, i2 = i1 + 1 == m ? 0 : i1 + 1;
        i64 g = (wp[i1] - wp[i] + R) % R;
        if (g >= 2) {
            if (g > 3)
                DIE("gap %lld inside a trail", g);
            if (out) {
                out[k].start = (u32)wp[i1];
                out[k].g = (unsigned char)g;
                out[k].g1 = 0;
                hist[3 - g + 3]++;
            }
            k++;
        }
        if (use_skip && m >= 3) {
            u64 r = rank_cyc(&TR[t], wp[i1]);
            if ((dupb[r >> 6] >> (r & 63)) & 1) {
                i64 g2 = g + (wp[i2] - wp[i1] + R) % R;
                if (g2 >= 2) {
                    if (out) {
                        out[k].start = (u32)wp[i2];
                        out[k].g = (unsigned char)g2;
                        out[k].g1 = (unsigned char)g;
                        hist[3 - g2 + 3]++;
                        shist[3 - g2 + 3]++;
                    }
                    k++;
                }
            }
        }
    }
    return k;
}

/* Reads the options, loads the base word, splits it into pieces and closed trails, builds the table of cuts,
   loads the plan, runs the passes that were asked for and the search, and writes the plan and the word. */
int main(int argc, char **argv) {
    if (argc < 3)
        DIE("usage: relocate BASE.txt OUT.txt --plan-in PLAN --threads 1 --time 0 --dpa --dpa-thr T   (see the comment at the top of relocate.c)");
    const char *plan_in = NULL;
    int co_first = 0;
    for (int a = 3; a < argc; a++) {
        if (!strcmp(argv[a], "--time") && a + 1 < argc)
            tlimit = atof(argv[++a]);
        else if (!strcmp(argv[a], "--seed") && a + 1 < argc)
            seed = strtoull(argv[++a], 0, 10);
        else if (!strcmp(argv[a], "--kmax") && a + 1 < argc)
            kmax = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--T0") && a + 1 < argc)
            T0 = atof(argv[++a]);
        else if (!strcmp(argv[a], "--ckpt") && a + 1 < argc)
            ckpt_sec = atof(argv[++a]);
        else if (!strcmp(argv[a], "--iters") && a + 1 < argc)
            maxit = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--plan-in") && a + 1 < argc)
            plan_in = argv[++a];
        else if (!strcmp(argv[a], "--threads") && a + 1 < argc)
            NTHR = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--sync") && a + 1 < argc)
            sync_sec = atof(argv[++a]);
        else if (!strcmp(argv[a], "--bigp") && a + 1 < argc)
            bigp = atof(argv[++a]);
        else if (!strcmp(argv[a], "--focus") && a + 1 < argc)
            focus = atof(argv[++a]);
        else if (!strcmp(argv[a], "--co"))
            co_first = 1;
        else if (!strcmp(argv[a], "--dpa"))
            dpa_on = 1;
        else if (!strcmp(argv[a], "--dpa-tau") && a + 1 < argc)
            dpa_tau = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--dpa-theta") && a + 1 < argc)
            dpa_theta = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--dpa-imax") && a + 1 < argc)
            dpa_imax = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--dpa-lmax") && a + 1 < argc)
            dpa_lmax = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--dpa-full") && a + 1 < argc)
            dpa_full = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--dpa-thr") && a + 1 < argc)
            dpa_thr = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--dpa-sec") && a + 1 < argc)
            dpa_sec = atof(argv[++a]);
        else if (!strcmp(argv[a], "--dpa-win") && a + 1 < argc)
            dpa_win = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--dpa-cap") && a + 1 < argc)
            dpa_cap = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--dpa-maxtry") && a + 1 < argc)
            dpa_maxtry = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--dpa-vv") || !strcmp(argv[a], "--as-vv"))
            dpa_verbose = 2;
        else if (!strcmp(argv[a], "--dpa-v") || !strcmp(argv[a], "--as-v"))
            dpa_verbose = 1;
        else if (!strcmp(argv[a], "--co-skip"))
            co_first = co_skip = 1;
        else if (!strcmp(argv[a], "--noskip"))
            use_skip = 0;
        else if (!strcmp(argv[a], "--nosplit"))
            use_split = 0;
        else
            DIE("unknown option %s", argv[a]);
    }
    if (NTHR < 1 || NTHR > 256)
        DIE("1 to 256 threads");
    double t00 = wall();
    W = load_word(argv[1], &L);
    int mx = 0;
    for (i64 i = 0; i < L; i++)
        if (W[i] > mx)
            mx = W[i];
    n = mx + 1;
    h = n - 3;
    if (n < 6 || n > 13)
        DIE("6 to 13 symbols");
    for (int k = 0; k <= 16; k++)
        HMASK[k] = k >= 16 ? ~0ULL : ((1ULL << (4 * k)) - 1);
    fact[0] = 1;
    for (int i = 1; i < 17; i++)
        fact[i] = fact[i - 1] * i;
    /* permutation windows and pieces (split at gaps >= 4) */
    {
        int cnt[16] = {0}, distinct = 0;
        i64 nw = 0, cap = 1 << 16, prev = -1, pstart = -1;
        PS = malloc(cap * 8);
        PL = malloc(cap * 8);
        NP = 0;
        for (i64 i = 0; i < L; i++) {
            if (cnt[W[i]]++ == 0)
                distinct++;
            if (i >= n) {
                if (--cnt[W[i - n]] == 0)
                    distinct--;
            }
            if (i < n - 1 || distinct != n)
                continue;
            i64 p = i - n + 1;
            nw++;
            if (prev < 0)
                pstart = p;
            else if (p - prev >= 4) {
                if (NP == cap) {
                    cap *= 2;
                    PS = realloc(PS, cap * 8);
                    PL = realloc(PL, cap * 8);
                }
                PS[NP] = pstart;
                PL[NP] = prev + n - pstart;
                NP++;
                pstart = p;
            }
            prev = p;
        }
        if (prev < 0)
            DIE("no permutation in the word");
        if (NP == cap) {
            cap *= 2;
            PS = realloc(PS, cap * 8);
            PL = realloc(PL, cap * 8);
        }
        PS[NP] = pstart;
        PL[NP] = prev + n - pstart;
        NP++;
        printf("n=%d L=%lld perm windows %lld pieces %lld (%.1fs)\n", n, L, nw, NP, wall() - t00);
        fflush(stdout);
    }
    /* trails: closed pieces, chains of open pieces, single pieces written from a gap-2 / gap-1 cut */
    char *closed = calloc((size_t)NP, 1);
    i64 *trail_of_piece = malloc(NP * 8);
    for (i64 k = 0; k < NP; k++)
        trail_of_piece[k] = -1;
    TR = calloc((size_t)NP + 1, sizeof(Trail));
    NT = 0;
    i64 nclosed = 0, nopen = 0;
    for (i64 k = 0; k < NP; k++)
        if (closes(k, 0)) {
            closed[k] = 1;
            nclosed++;
            trail_of_piece[k] = NT;
            TR[NT].c = W + PS[k];
            TR[NT].R = PL[k] - h;
            NT++;
        }
    i64 nlinear = 0;
    {
        i64 no = 0;
        i64 *op = malloc((NP + 1) * 8);
        for (i64 k = 0; k < NP; k++)
            if (!closed[k])
                op[no++] = k;
        char *used = calloc((size_t)NP + 1, 1), *haspred = calloc((size_t)NP + 1, 1);
        i64 *chain = malloc((no + 1) * 8);
        for (i64 a = 0; a < no; a++) {
            u64 tw = hw_lin(W + PS[op[a]] + PL[op[a]] - h);
            for (i64 b = 0; b < no; b++)
                if (b != a && hw_lin(W + PS[op[b]]) == tw)
                    haspred[op[b]] = 1;
        }
        /* phase 0 starts at the pieces nothing leads to (open paths), phase 1 takes the cycles */
        for (int phase = 0; phase < 2; phase++)
            for (i64 a = 0; a < no; a++) {
                i64 k = op[a];
                if (used[k] || (phase == 0 && haspred[k]))
                    continue;
                i64 nc = 0;
                chain[nc++] = k;
                used[k] = 1;
                u64 hwd = hw_lin(W + PS[k]), tw;
                for (;;) {
                    i64 lastp = chain[nc - 1];
                    tw = hw_lin(W + PS[lastp] + PL[lastp] - h);
                    if (tw == hwd)
                        break;
                    i64 nx = -1;
                    for (i64 b = 0; b < no; b++)
                        if (!used[op[b]] && hw_lin(W + PS[op[b]]) == tw) {
                            nx = op[b];
                            break;
                        }
                    if (nx < 0)
                        break;
                    chain[nc++] = nx;
                    used[nx] = 1;
                }
                int ex = (tw != hwd && nc == 1) ? (closes(k, 1) ? 1 : closes(k, 2) ? 2 : 0) : 0;
                if (ex) { /* a whole trail written from a gap-2 or gap-1 cut */
                    closed[k] = 1;
                    nclosed++;
                    trail_of_piece[k] = NT;
                    TR[NT].c = W + PS[k];
                    TR[NT].R = PL[k] - h - ex;
                    NT++;
                    continue;
                }
                i64 R = 0;
                for (i64 b = 0; b < nc; b++)
                    R += PL[chain[b]] - h;
                unsigned char *c = malloc((size_t)R + h + 16);
                i64 q = 0;
                for (i64 b = 0; b < nc; b++) {
                    memcpy(c + q, W + PS[chain[b]], (size_t)(PL[chain[b]] - h));
                    q += PL[chain[b]] - h;
                    trail_of_piece[chain[b]] = NT;
                }
                TR[NT].c = c;
                TR[NT].R = R;
                if (tw != hwd) {
                    i64 lastp = chain[nc - 1];
                    memcpy(c + q, W + PS[lastp] + PL[lastp] - h, (size_t)h);
                    TR[NT].fixed = 1;
                    nlinear += nc;
                } else
                    nopen += nc;
                NT++;
            }
        free(op);
        free(used);
        free(haspred);
        free(chain);
    }
    i64 sumR = 0, maxR = 0;
    for (i64 t = 0; t < NT; t++) {
        sumR += TR[t].R;
        if (TR[t].R > maxR)
            maxR = TR[t].R;
    }
    printf("trails %lld (closed pieces %lld, chained open pieces %lld), sum R %lld\n", NT, nclosed, nopen, sumR);
    if (nlinear)
        printf("%lld pieces form an open path that is not a closed trail; they stay where they are\n", nlinear);
    fflush(stdout);
    /* duplicate windows, then the cuts of every trail (parallel over trails) */
    u64 NF = fact[n];
    u64 *seenb = calloc((size_t)(NF >> 6) + 1, 8), *dupb = calloc((size_t)(NF >> 6) + 1, 8);
    if (!seenb || !dupb)
        DIE("out of memory");
    int LT = NTHR > 8 ? NTHR : 8;
    if (LT > omp_get_max_threads())
        LT = omp_get_max_threads();
    i64 nwin = 0;
#pragma omp parallel num_threads(LT) reduction(+ : nwin)
    {
        i64 *wp = malloc((size_t)(maxR + 8) * 8);
        if (!wp)
            DIE("out of memory");
#pragma omp for schedule(dynamic, 8)
        for (i64 t = 0; t < NT; t++) {
            i64 m = trail_windows(&TR[t], wp);
            nwin += m;
            for (i64 i = 0; i < m; i++) {
                u64 r = TR[t].fixed ? rank_lin(TR[t].c + wp[i]) : rank_cyc(&TR[t], wp[i]), bit = 1ULL << (r & 63);
                u64 old = __atomic_fetch_or(&seenb[r >> 6], bit, __ATOMIC_RELAXED);
                if (old & bit)
                    __atomic_fetch_or(&dupb[r >> 6], bit, __ATOMIC_RELAXED);
            }
        }
        free(wp);
    }
    {
        u64 dcount = 0, scount = 0;
        for (u64 i = 0; i <= (NF >> 6); i++) {
            scount += __builtin_popcountll(seenb[i]);
            dcount += __builtin_popcountll(dupb[i]);
        }
        printf("trail windows %lld distinct %llu (n! check: %s), duplicated %llu (%.1fs)\n", nwin, scount,
               scount == NF ? "True" : "False", dcount, wall() - t00);
        fflush(stdout);
        if (scount != NF)
            DIE("the trails do not contain every permutation (%llu missing): the model cannot be used on this word",
                (unsigned long long)(NF - scount));
        free(seenb);
    }
    /* A window may be skipped only if its permutation really occurs twice in the word.  The cyclic word of a trail
       can contain a window that the word itself does not have (a piece cut open across a duplicate window), so the
       duplicates are counted again on the word and the two sets are intersected. */
    {
        u64 *ws = calloc((size_t)(NF >> 6) + 1, 8), *wd = calloc((size_t)(NF >> 6) + 1, 8);
        if (!ws || !wd)
            DIE("out of memory");
        i64 nwin_word = L - n + 1;
#pragma omp parallel num_threads(LT)
        {
            int tid = omp_get_thread_num(), nt = omp_get_num_threads();
            i64 a = nwin_word * tid / nt, b = nwin_word * (tid + 1) / nt;
            int cnt[16] = {0}, distinct = 0;
            for (i64 i = a; i < a + n - 1 && i < L; i++)
                if (cnt[W[i]]++ == 0)
                    distinct++;
            for (i64 p = a; p < b; p++) {
                if (cnt[W[p + n - 1]]++ == 0)
                    distinct++;
                if (distinct == n) {
                    u64 r = rank_lin(W + p), bit = 1ULL << (r & 63);
                    u64 old = __atomic_fetch_or(&ws[r >> 6], bit, __ATOMIC_RELAXED);
                    if (old & bit)
                        __atomic_fetch_or(&wd[r >> 6], bit, __ATOMIC_RELAXED);
                }
                if (--cnt[W[p]] == 0)
                    distinct--;
            }
        }
        u64 before = 0, after = 0;
        for (u64 i = 0; i <= (NF >> 6); i++) {
            before += __builtin_popcountll(dupb[i]);
            dupb[i] &= wd[i];
            after += __builtin_popcountll(dupb[i]);
        }
        if (before != after) {
            printf(
                "%llu duplicated windows exist only in the cyclic words, not in the word: they will not be skipped" NL,
                (unsigned long long)(before - after));
            fflush(stdout);
        }
        free(ws);
        free(wd);
    }
    {
        i64 hist[8] = {0}, shist[8] = {0};
        i64 *ocnt = calloc((size_t)NT + 1, 8);
        for (int pass = 0; pass < 2; pass++) {
#pragma omp parallel num_threads(LT)
            {
                i64 *wp = malloc((size_t)(maxR + 8) * 8), lh[8] = {0}, lsh[8] = {0};
                if (!wp)
                    DIE("out of memory");
#pragma omp for schedule(dynamic, 8)
                for (i64 t = 0; t < NT; t++) {
                    i64 k = trail_options(t, wp, dupb, pass ? OP + TR[t].olo : NULL, lh, lsh);
                    if (!pass)
                        ocnt[t] = k;
                    else if (k != ocnt[t])
                        DIE("internal error: option count");
                }
                free(wp);
#pragma omp critical
                for (int d = 0; d < 8; d++) {
                    hist[d] += lh[d];
                    shist[d] += lsh[d];
                }
            }
            if (!pass) {
                NO = 0;
                for (i64 t = 0; t < NT; t++) {
                    TR[t].olo = NO;
                    NO += ocnt[t];
                    TR[t].ohi = NO;
                }
                OP = malloc((size_t)(NO + 1) * sizeof(Opt));
                if (!OP)
                    DIE("out of memory for %lld options", NO);
            }
        }
        free(ocnt);
        printf("options %lld by extra cost {", NO);
        for (int d = 0; d < 8; d++)
            if (hist[d])
                printf(" %d: %lld", d - 3, hist[d]);
        printf(" }; dup-skip options {");
        for (int d = 0; d < 8; d++)
            if (shist[d])
                printf(" %d: %lld", d - 3, shist[d]);
        printf(" } (%.1fs)\n", wall() - t00);
        fflush(stdout);
    }
    free(dupb);
    /* current sequence */
    i64 cap = NP * 2 + 1024;
    Ev *ev = malloc(cap * sizeof(Ev));
    i64 N = 0;
    if (!plan_in) {
        for (i64 k = 0; k < NP; k++)
            ev[N++] = piece_event(k, trail_of_piece[k]);
        i64 L0 = seq_length(ev, N);
        printf("model length of the input sequence: %lld (word %lld)\n", L0, L);
        fflush(stdout);
        if (L0 != L)
            DIE("the model does not reproduce the word");
    } else {
        FILE *f = fopen(plan_in, "r");
        if (!f)
            DIE("cannot open %s", plan_in);
        char tag[32];
        int pn;
        i64 pL, pN;
        if (fscanf(f, "%31s %d %lld %lld", tag, &pn, &pL, &pN) != 4 || pn != n || pL != L)
            DIE("plan does not match the word");
        for (i64 q = 0; q < pN; q++) {
            char c[4];
            if (fscanf(f, "%3s", c) != 1)
                DIE("bad plan");
            Ev x;
            if (c[0] == 'P') {
                i64 k;
                if (fscanf(f, "%lld", &k) != 1 || k < 0 || k >= NP)
                    DIE("bad plan");
                x = piece_event(k, trail_of_piece[k]);
            } else if (c[0] == 'O') {
                u32 t, st;
                int g, g1;
                if (fscanf(f, "%u %u %d %d", &t, &st, &g, &g1) != 4 || t >= NT)
                    DIE("bad plan");
                i64 o = -1;
                for (i64 z = TR[t].olo; z < TR[t].ohi; z++)
                    if (OP[z].start == st && OP[z].g == g && OP[z].g1 == g1) {
                        o = z;
                        break;
                    }
                if (o < 0)
                    DIE("plan option not found");
                x = make_event(o);
            } else {
                u32 t;
                i64 st, l;
                if (fscanf(f, "%u %lld %lld", &t, &st, &l) != 3 || t >= NT)
                    DIE("bad plan");
                x.kind = EV_SEG;
                x.t = t;
                x.a = st;
                x.l = l;
                x.s = hw_cyc(&TR[t], st);
                x.e = hw_cyc(&TR[t], st + l - h);
                x.skip = -1;
            }
            if (N + 2 >= cap) {
                cap *= 2;
                ev = realloc(ev, cap * sizeof(Ev));
            }
            ev[N++] = x;
        }
        fclose(f);
        printf("model length of the plan: %lld (%lld events)\n", seq_length(ev, N), N);
        fflush(stdout);
    }
    if (co_first)
        co_full(ev, N);
    /* ---------- destroy / repair search */
    char outplan[4096];
    snprintf(outplan, sizeof outplan, "%s.plan", argv[2]);
    if (dpa_on) {
        dpa_ckpt = outplan;
        while (dpa_sweep(ev, N, &DPA_co, dpa_buf(N)) > 0)
            ;
    }
    G_ev = malloc((size_t)(4 * N + 65536) * sizeof(Ev));
    memcpy(G_ev, ev, (size_t)N * sizeof(Ev));
    G_N = N;
    G_len = seq_length(ev, N);
    G_t0 = G_last_ck = G_last_log = G_last_dpa = wall();
#pragma omp parallel num_threads(NTHR)
    {
        Ctx *c = calloc(1, sizeof(Ctx));
        c->tid = omp_get_thread_num();
        search(c, ev, N, outplan);
    }
    i64 tot = 0;
    for (int q = 0; q < NTHR; q++)
        tot += G_it[q];
    printf("LNS done: %lld iterations on %d threads, best %lld\n", tot, NTHR, G_len);
    fflush(stdout);
    if (tot > 0 && co_first) {
        co_full(G_ev, G_N);
        G_len = seq_length(G_ev, G_N);
    }
    if (tot > 0 && (dpa_on || dpa_sec > 0)) {
        dpa_ckpt = outplan;
        while (dpa_sweep(G_ev, G_N, &DPA_co, dpa_buf(G_N)) > 0)
            ;
        G_len = seq_length(G_ev, G_N);
    }
    print_stats(G_ev, G_N);
    write_plan(G_ev, G_N, outplan);
    write_word(G_ev, G_N, argv[2], G_len);
    printf("wrote %s length %lld (%.0fs)\n", argv[2], G_len, wall() - t00);
    return 0;
}
