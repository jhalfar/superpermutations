/* segins.c - segment insertion: the sequence of pieces is cut at three to six joins and the blocks of pieces between
   the cuts are put together in another order.  Every such move is judged with the best cuts of the whole new
   sequence.

   Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.  The closed trails are
   those of Jay Pantone's construction (github.com/jaypantone/superperm-upper-43-80).

   What it does.  With three cuts the move is a 3-opt move without reversal: A B C D becomes A C B D, two
   neighbouring blocks of any length change places.  Four cuts add A D C B E, five and six cuts the orders whose
   new joins form one cycle.  No block is reversed, because a piece cannot be read backwards.
   The word "cut" has two uses here.  A move cuts the sequence at some of its joins: "three cuts", "--or3 5".  Every
   closed trail is cut open at one place to make it a piece: "the cuts of a piece", "the best cuts".
   A round has five steps.
     1. Tables: for every piece the cost of each of its cuts with the best of everything before it, and with the
        best of everything after it (the fixed-order pass of recut.c run from both ends).
     2. Pairs: from the tables, V(x, y) = what the join of piece x to piece y costs when the cuts of both may change
        and everything before x and after y stays.  V is listed for all pairs with V <= TH, and for the pairs
        between the two sides of expensive joins up to h - 1.
     3. Candidates: moves whose cut joins are worth more than their new joins, or at most S letters less (S is the
        slack).  They are found as in the method of Lin and Kernighan: cut a join, give its left piece a new
        successor from the lists, cut the join before that successor, and so on, and close the chain.
     4. Judging: every candidate is judged exactly.  From each new join the dynamic programme runs through the
        block that follows until the costs of a piece's cuts are what they were before, a few layers per move.
     5. All shorter moves that do not disturb each other are made (their cuts lie more than G pieces apart), the
        word is checked against the promised length and OUT.txt.plan is written.
   Rounds repeat until none makes the word shorter.  The estimate of step 3 is a filter and not a bound: several of
   the moves that gave records needed a slack of 3 or 4.

   Build:  gcc -O2 -mpopcnt -fopenmp -o segins segins.c -lm
   Use:    n = 11   segins BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 2 --or3 5 --or3-slack 4
           n = 12   segins BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 4 --or3 5 --or3-slack 1
           n = 13   segins BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 8 --or3 3 --or3-slack 0
                           --or3-maxcand 3000 --or3-sec 14400 --or3-stop STOPFILE

   Options of the pass.
     --or3 C            moves with 3 to C cuts (C <= 6); without this option the pass does not run
     --or3-slack S      step 3 keeps a move if its estimate is above -S (default 2).  The cost rises steeply with S
     --or3-v TH         pairs are listed up to V = TH (default 6)
     --or3-x T          joins with V >= T count as expensive and get the long lists (default 3; at most 8000 joins)
     --or3-maxcand M    only the M candidates with the best estimate are judged (needed at n = 13)
     --or3-maxlay L     a candidate that needs more than L layers after one join is given up (default 4096; 0: no limit)
     --or3-margin G     moves made in the same round have cuts more than G pieces apart (default 8)
     --or3-rounds R, --or3-sec SEC, --or3-stop FILE
                        stop after R rounds, after SEC seconds (a round under way judges no further candidate and
                        makes the moves it has), or when FILE exists (looked at between rounds).  The word and the
                        plan are written in every case
     --or3-plateau P    when no move is shorter, up to P sequences of equal length are tried as new starting points
                        (this found 43,930,615; do not use it at n = 13)
     --or3-dip D        inside a chain the sum may fall to -S - D (default 2)
     --or3-dry          list the candidates of one round and stop
     --or3-zone Z       a move keeps others away from at most Z pieces of each of its blocks.  More moves per
                        round, but they disturb each other: the runs I made with it ended on longer words
     --or3-old          candidates and rounds as in the first version of this pass (cubic in the number of expensive
                        joins: it does not finish a round at n = 13).  Kept to compare with earlier runs
   Other passes in this file.
     --co, --co-skip    the fixed-order pass, exactly as in recut.c
     --bs K             the best of all sequences in which piece i stays before piece j whenever i + K <= j (the
                        neighbourhood of Balas and Simonetti), with all cuts free.  It runs before --or3 and again
                        after a round that gained.  K = 3 takes Pantone's n = 11 word from 43,930,680 to 43,930,674
                        in seconds; on words that have been through the other passes it finds nothing up to K = 9
     --bs-test N        compares --bs with plain enumeration on N random windows
     and all options of trailsearch.c.  With --time 0 no search runs.

   Memory and time (measured).  n = 11, 2 threads: tables 2.5 seconds per round, candidates 3 to 7 seconds for up to
   4 cuts and about 2 minutes for 5 cuts at slack 4.  n = 12, 4 threads: about 10 seconds per round for tables and
   pairs; 522,745,445 to 522,745,383 took 18 rounds and 492 seconds with three cuts; with five cuts and slack 1 a
   round takes 45 to 75 seconds on 2 threads.  n = 13, 8 threads,
   --or3 3 --or3-slack 0 --or3-maxcand 3000: 12.6 GB at the peak, the first round 270 seconds (tables 56 seconds,
   79 million pairs, 22,390 candidates), later rounds 70 to 120 seconds.

   Words.  The comments say "cut" for the place where a closed trail is cut open.  The names in the code and the
   text the program prints use two older words for it: "opening" and "option" (struct Opt, the table OP, "gap-2
   openings").  The "gap" g of a cut is the weight of the step that is cut: 3 is the usual cut and costs nothing, 2
   is a cut between two 2-cycles and costs one letter, 1 is a cut inside a 1-cycle and costs two letters.
   An "event" is one piece as it is written into the word: a whole trail from one cut, a segment of a trail, or a
   piece of the input word left as it is.  The "h-word" of a piece end is its first or last h = n - 3 letters; two
   pieces are joined with the largest overlap of these words.  A "skip" is a cut that also drops one of the two
   occurrences of a permutation that the trails contain twice.  "Cluster optimisation" is the fixed-order pass.

   Layout of this file.  It is a copy of the first published version of trailsearch.c (the model, the plan, the
   search, the loader) with three parts added, marked by lines of equal signs: the fixed-order pass of recut.c, the
   neighbourhood of --bs and segment insertion.  Removed from the working version: the options --cow and --copre
   (see recut.c). */
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

/* ==================== shared base (first published trailsearch.c): model, plan, index, search moves ==================== */
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
static inline u64 hw_lin(const unsigned char *p) {
    u64 v = 0;
    for (int k = 0; k < h; k++)
        v = (v << 4) | p[k];
    return v;
}
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
/* lab: order label (increasing along the list) */
typedef struct {
    Ev v;
    int prev, next, alive;
    u64 lab;
} Node;
typedef struct {
    i64 c2;
    int i, jm;
    i64 cst;
} Pair;
typedef struct {
    int tid;
    u64 rs[4];
    Node *nd;
    int ncap, nn, first, last;
    i64 N;
    int relabeled;
    HTab H, RELT;
    u64 *bf, bfmask; /* bf: one-hash Bloom filter over the keys of H */
    int *order, *dj, *cand, *rid, *rs_, *re_, *rel, *remlog, *inslog;
    int nremlog, ninslog;
    i64 *skp;
    int nskp, skpcap;
    i64 *vid;
    int vcap;
    Pair *pr;
    i64 pcap;
    int *Ib, *Jb;
    int icap, jcap;
    char *rem;
    u32 *pend;
    Ev *tmp;
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
/* Loads a sequence of N events into the thread: nodes, order labels, index, Bloom filter and the kept arrays
   (seq_build).  Buffers grow when needed.  ev may be the thread's own c->tmp. */
static void ctx_load(Ctx *c, const Ev *ev, i64 N) {
    int need = (int)(4 * N + 65536), self = ev == c->tmp;
    if (need > c->ncap) {
        c->ncap = need;
        c->nd = realloc(c->nd, (size_t)need * sizeof(Node));
        int **arr[] = {&c->order, &c->dj, &c->cand, &c->rid, &c->rs_, &c->re_, &c->rel, &c->remlog, &c->inslog};
        for (int k = 0; k < 9; k++)
            *arr[k] = realloc(*arr[k], (size_t)need * sizeof(int));
        c->tmp = realloc(c->tmp, (size_t)need * sizeof(Ev));
        if (self)
            ev = c->tmp;
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

/* ---------- best insertion of trail t: insert after node `after` */
typedef struct {
    double val;
    i64 delta;
    int after;
    i64 opt;
} Ins;
/* Best place and cut for trail t in the current sequence.  Every cut of t is looked up in the index by the ends
   of its two words, so only places where it overlaps a neighbour are tried; if there is none the trail is appended.
   noise > 0 adds a random amount below noise to every candidate.  Returns the node to insert after, the cut and
   the change of length. */
static Ins best_insertion(Ctx *c, u32 t, double noise) {
    Ins best;
    best.val = 1e18;
    best.delta = 0;
    best.after = -1;
    best.opt = -1;
    const Trail *T = &TR[t];
    const Node *nd = c->nd;
    const HTab *H = &c->H;
    /* options are processed in batches so that the filter words of a whole batch are prefetched before they are tested */
    enum { BATCH = 16, NK = 2 * (KLEV + 1) };
    for (i64 o0 = T->olo; o0 < T->ohi; o0 += BATCH) {
        int m = (int)(T->ohi - o0 < BATCH ? T->ohi - o0 : BATCH);
        u64 Sb[BATCH], Eb[BATCH], key[BATCH][NK], bit[BATCH][NK];
        for (int q = 0; q < m; q++) {
            u64 S = oS_t(T, o0 + q), E = oE_t(T, o0 + q);
            Sb[q] = S;
            Eb[q] = E;
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
                }
            }
        }
    }
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
    i64 bd = 1LL << 40, bk = -1, bc1 = -1;
    for (i64 k = 0; k < np; k++) {
        u64 ep = nd[nd[c->pr[k].i].prev].v.e, sn = nd[nd[c->pr[k].jm].next].v.s;
        for (i64 o = T->olo; o < T->ohi; o++) {
            i64 d = dist(ep, oS_t(T, o)) + oD(o) + dist(oE_t(T, o), sn) + c->pr[k].cst;
            if (d < bd) {
                bd = d;
                bk = k;
                bc1 = o;
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
static i64 coit = 0;
/* --coit N: every N iterations of a thread the whole current sequence (one pass at a time, the table is shared) */
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
/* passes of --coit in a thread: passes, passes with a gain, letters; seconds */
typedef struct {
    i64 st[3];
    double sec;
} CLog;
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

/* ==================== own part of this file, 1: reordering inside windows of K pieces (--bs) ==================== */
/* ---------- order and cuts together.  The neighbourhood of Balas and Simonetti: all sequences in which event
   i stays before event j whenever i + K <= j in the current order (K = 1: the order as it is, i.e. co_run),
   searched exactly together with the cuts.  Layer p holds the states after p events: the set V of the events
   written so far (0 .. u-1 and a subset `mask` of u+1 .. u+K-1, where u is the first event not yet written), the
   last event j (j in V, j > max V - K) and, as in co_run, the cost of every cut of j: one byte relative to
   the minimum mu of the state.  A layer has 2^(K-1) sets and (K+1) 2^(K-2) states.  All states of one set are
   extended together: the cuts of their last events are one pool of (end word, cost) for the overlap tables of
   co_run, and every event c that may come next (u, or one of u+1 .. u+K-1 not in mask) looks its cuts up
   once.  So a state costs about as much as a layer of co_run, and the pass (K+1) 2^(K-2) times co_run.
   Two layers are kept and one in every `blk`; only if the result is shorter the layers are computed again, block
   by block from the end, and the sequence is read off backwards (no back-pointers).
   Slot of a state in its layer: mask * 2K + (j - u + K). */
/* minimum, table (offset in the pool of the layer), its size (0: no such state), mask of the set it came from */
typedef struct {
    i64 mu, off;
    int m, pm;
} BSt;
typedef struct {
    BSt *st;
    unsigned char *pool;
    i64 used, cap;
} BLay;
/* the cuts an event may take (o = -1: the event as it is) */
typedef struct {
    i64 id, cap;
    int m;
    u64 *S, *E;
    signed char *D;
    i64 *o;
} BEv;
typedef struct {
    CSlot *t;
    u64 cap;
    u32 gen;
    u64 *UE;
    i64 ucap;
    int *mv;
    i64 mcap;
    unsigned char d[16 + 256 + 4096];
} BScr;
typedef struct {
    int K, nm, ns, anyskip, nthr, count;
    const Ev *ev;
    i64 N;
    BEv *ec;
    int ecn;
    BScr *scr;
    CO *q;                   /* q: only the bans of co_skip */
    i64 nst, nbytes, maxlay; /* statistics of the last pass: states, bytes of their tables, largest layer */
} BS;
static int bsK = 0, bs_ntest = 0;
/* The cuts an event may take, cached: start words, end words, costs and cut numbers (one entry if the event
   cannot be cut again). */
static BEv *bs_ev(BS *b, i64 i) {
    BEv *e = &b->ec[i % b->ecn];
    if (e->id == i)
        return e;
    const Ev *x = &b->ev[i];
    const Trail *T = &TR[x->t];
    i64 o0 = co_cur(x), m = o0 < 0 ? 1 : T->ohi - T->olo;
    if (m > e->cap) {
        e->cap = m + m / 2 + 16;
        e->S = realloc(e->S, e->cap * 8);
        e->E = realloc(e->E, e->cap * 8);
        e->o = realloc(e->o, e->cap * 8);
        e->D = realloc(e->D, e->cap);
        if (!e->S || !e->E || !e->o || !e->D)
            DIE("out of memory");
    }
    if (o0 < 0) {
        e->S[0] = x->s;
        e->E[0] = x->e;
        e->D[0] = 0;
        e->o[0] = -1;
    } else {
        m = 0;
        for (i64 o = T->olo; o < T->ohi; o++) {
            if (OP[o].g1 && !co_skip_ok(b->q, x, i, T, o, b->anyskip))
                continue;
            e->S[m] = oS_t(T, o);
            e->E[m] = oE_t(T, o);
            e->D[m] = (signed char)oD(o);
            e->o[m++] = o;
        }
    }
    e->m = (int)m;
    e->id = i;
    return e;
}
/* Is (p events written, set mask) a state of the neighbourhood?  *u = the first event not yet written. */
static inline int bs_valid(const BS *b, i64 p, int mask, i64 *u) {
    *u = p - __builtin_popcount(mask);
    if (*u < 0)
        return 0;
    return mask ? *u + 32 - __builtin_clz(mask) <= b->N - 1 : *u <= b->N;
}
/* event c = u (z = -1) or c = u + 1 + z comes next: the slot of the new state in the next layer, or -1 */
static inline int bs_succ(const BS *b, i64 u, int mask, int z, i64 *c) {
    int K = b->K;
    if (z < 0) {
        int t = __builtin_ctz(~mask);
        *c = u;
        return (mask >> (t + 1)) * 2 * K + K - 1 - t;
    }
    if (((mask >> z) & 1) || u + 1 + z > b->N - 1)
        return -1;
    *c = u + 1 + z;
    return (mask | (1 << z)) * 2 * K + K + 1 + z;
}
/* As co_put, in the scratch table of a thread. */
static inline void bs_put(BScr *w, u64 mask, u64 key, u32 val) {
    u64 i = hmix(key) & mask;
    while (w->t[i].gen == w->gen) {
        if (w->t[i].key == key) {
            if (val < w->t[i].val)
                w->t[i].val = val;
            return;
        }
        i = (i + 1) & mask;
    }
    w->t[i].key = key;
    w->t[i].gen = w->gen;
    w->t[i].val = val;
}
/* As co_get, in the scratch table of a thread. */
static inline int bs_get(const BScr *w, u64 mask, u64 key) {
    u64 i = hmix(key) & mask;
    while (w->t[i].gen == w->gen) {
        if (w->t[i].key == key)
            return (int)w->t[i].val;
        i = (i + 1) & mask;
    }
    return -1;
}
/* The join cost lives in two functions that must agree: bs_dist, the cost of writing an cut that starts with s
   after one that ends with e, and bs_join, the same for many at once: mv[j] = min(h, min over a pool of cuts of
   their cost v + bs_dist(E, S[j])) for every cut j of the events ce[0 .. nc-1].  The pool is given by its end
   words UE sorted by cost (cost v: UE[bnd[v]] .. UE[bnd[v+1]-1], only v < h).  As in co_run: for k = h .. 4 a hash
   table of the cheapest pool entry for every suffix of length k, for k <= 3 arrays.
   rev: the pool is written after the events instead: UE holds start words and mv[j] = min(h, min v + bs_dist(E[j], S)). */
static inline int bs_dist(u64 e, u64 s) {
    return dist(e, s);
}
/* One layer step for several events at once: mv[j] = min over the pooled cuts of (their cost + join to cut j),
   through tables by the last k letters for k = h .. 1 (see the comment above bs_dist). */
static void bs_join(BScr *w, const i64 *bnd, BEv **ce, int nc, int *mv, int rev) {
    for (int k = h; k >= 4 && bnd[k]; k--) {
        u64 need = 16;
        while (need < 2 * (u64)bnd[k])
            need <<= 1;
        if (need > w->cap) {
            free(w->t);
            w->t = calloc(need, sizeof(CSlot));
            w->cap = need;
            w->gen = 0;
            if (!w->t)
                DIE("out of memory");
        }
        u64 hm = need - 1;
        int sh = 4 * (h - k), *m2 = mv;
        w->gen++;
        for (int v = 0; v < k; v++)
            for (i64 e = bnd[v]; e < bnd[v + 1]; e++)
                bs_put(w, hm, rev ? w->UE[e] >> sh : w->UE[e] & HMASK[k], (u32)v);
        for (int q = 0; q < nc; q++) {
            const u64 *S = rev ? ce[q]->E : ce[q]->S;
            int m = ce[q]->m;
            for (int j = 0; j < m; j++) {
                if (m2[j] <= h - k)
                    continue;
                int v = bs_get(w, hm, rev ? S[j] & HMASK[k] : S[j] >> sh);
                if (v >= 0 && v + h - k < m2[j])
                    m2[j] = v + h - k;
            }
            m2 += m;
        }
    }
    if (!bnd[h < 3 ? h : 3])
        return;
    unsigned char *d1 = w->d, *d2 = d1 + 16, *d3 = d2 + 256;
    int *m2 = mv; /* k = 3, 2, 1: tables indexed by the word */
    memset(w->d, 255, sizeof w->d);
    int s3 = 4 * (h - 3), s2 = 4 * (h - 2), s1 = 4 * (h - 1);
    for (int v = 0; v < 3 && v < h; v++)
        for (i64 e = bnd[v]; e < bnd[v + 1]; e++) {
            u64 E = w->UE[e], k3 = rev ? E >> s3 : E & 4095, k2 = rev ? E >> s2 : E & 255, k1 = rev ? E >> s1 : E & 15;
            if (v < d3[k3])
                d3[k3] = (unsigned char)v;
            if (v < 2 && v < d2[k2])
                d2[k2] = (unsigned char)v;
            if (!v)
                d1[k1] = 0;
        }
    for (int q = 0; q < nc; q++) {
        const u64 *S = rev ? ce[q]->E : ce[q]->S;
        int m = ce[q]->m;
        for (int j = 0; j < m; j++) {
            if (m2[j] <= h - 3)
                continue;
            int v = d3[rev ? S[j] & 4095 : S[j] >> s3];
            if (v + h - 3 < m2[j])
                m2[j] = v + h - 3;
            if (m2[j] <= h - 2)
                continue;
            v = d2[rev ? S[j] & 255 : S[j] >> s2];
            if (v + h - 2 < m2[j])
                m2[j] = v + h - 2;
            if (m2[j] == h && !d1[rev ? S[j] & 15 : S[j] >> s1])
                m2[j] = h - 1;
        }
        m2 += m;
    }
}
/* the states of the set (u, mask) of layer A (after p events) -> their successors in layer Bn (tables already placed) */
static void bs_group(BS *b, BScr *w, const BLay *A, BLay *Bn, i64 p, int mask, i64 u) {
    int K = b->K;
    const BSt *as = A->st + (i64)mask * 2 * K;
    i64 muV = 0, bnd[18] = {0}, pos[17];
    if (p) { /* the pool: end words of all cuts that cost less than h more than the cheapest, sorted by that cost */
        muV = 1LL << 60;
        for (int cd = 0; cd < 2 * K; cd++)
            if (as[cd].m && as[cd].mu < muV)
                muV = as[cd].mu;
        for (int pass = 0; pass < 2; pass++) {
            for (int cd = 0; cd < 2 * K; cd++) {
                if (!as[cd].m || as[cd].mu - muV >= h)
                    continue;
                int base = (int)(as[cd].mu - muV), lim = h - base, m = as[cd].m;
                const unsigned char *rel = A->pool + as[cd].off;
                if (!pass) {
                    for (int j = 0; j < m; j++)
                        if (rel[j] < lim)
                            bnd[base + rel[j] + 1]++;
                } else {
                    const u64 *E = bs_ev(b, u - K + cd)->E;
                    for (int j = 0; j < m; j++)
                        if (rel[j] < lim)
                            w->UE[pos[base + rel[j]]++] = E[j];
                }
            }
            if (pass)
                break;
            for (int v = 0; v < h; v++)
                bnd[v + 1] += bnd[v];
            if (bnd[h] > w->ucap) {
                w->ucap = bnd[h] + bnd[h] / 2 + 64;
                free(w->UE);
                w->UE = malloc(w->ucap * 8);
                if (!w->UE)
                    DIE("out of memory");
            }
            for (int v = 0; v < h; v++)
                pos[v] = bnd[v];
        }
    }
    int nc = 0, ts[32];
    BEv *ce[32];
    i64 tot = 0, c;
    for (int z = -1; z < K - 1; z++) {
        int s = bs_succ(b, u, mask, z, &c);
        if (s < 0)
            continue;
        ts[nc] = s;
        ce[nc] = bs_ev(b, c);
        tot += ce[nc++]->m;
    }
    if (tot > w->mcap) {
        w->mcap = tot + tot / 2 + 64;
        free(w->mv);
        w->mv = malloc(w->mcap * sizeof(int));
        if (!w->mv)
            DIE("out of memory");
    }
    int *mv = w->mv;
    for (i64 j = 0; j < tot; j++)
        mv[j] = p ? h : 0;
    if (p)
        bs_join(w, bnd, ce, nc, mv, 0);
    for (int q = 0; q < nc; q++) {
        BSt *s = &Bn->st[ts[q]];
        unsigned char *rel = Bn->pool + s->off;
        const signed char *D = ce[q]->D;
        int m = ce[q]->m, mn = 1 << 20;
        for (int j = 0; j < m; j++) {
            mv[j] += D[j];
            if (mv[j] < mn)
                mn = mv[j];
        }
        for (int j = 0; j < m; j++)
            rel[j] = (unsigned char)(mv[j] - mn);
        s->mu = muV + mn;
        mv += m;
    }
}
/* layer p -> layer p + 1 */
static void bs_layer(BS *b, const BLay *A, BLay *Bn, i64 p) {
    int K = b->K;
    i64 N = b->N, used = 0, u, c, nst = 0;
    for (i64 i = p - 2 * K + 1 > 0 ? p - 2 * K + 1 : 0; i <= p + K - 1 && i < N; i++)
        bs_ev(b, i);
    if (!Bn->st) {
        Bn->st = malloc((size_t)b->ns * sizeof(BSt));
        if (!Bn->st)
            DIE("out of memory");
    }
    memset(Bn->st, 0, (size_t)b->ns * sizeof(BSt));
    for (int mask = 0; mask < b->nm; mask++) {
        if (!bs_valid(b, p, mask, &u) || u >= N)
            continue;
        for (int z = -1; z < K - 1; z++) {
            int s = bs_succ(b, u, mask, z, &c);
            if (s < 0)
                continue;
            BSt *x = &Bn->st[s];
            x->m = bs_ev(b, c)->m;
            x->off = used;
            x->pm = mask;
            used += x->m;
            nst++;
        }
    }
    if (used > Bn->cap) {
        Bn->cap = used + used / 4 + 64;
        free(Bn->pool);
        Bn->pool = malloc((size_t)Bn->cap);
        if (!Bn->pool)
            DIE("out of memory");
    }
    Bn->used = used;
#pragma omp parallel for schedule(dynamic, 1) num_threads(b->nthr) if (b->nthr > 1 && b->nm > 1)
    for (int mask = 0; mask < b->nm; mask++) {
        i64 u2;
        if (!bs_valid(b, p, mask, &u2) || u2 >= N)
            continue;
        bs_group(b, &b->scr[omp_get_thread_num()], A, Bn, p, mask, u2);
    }
    if (b->count) {
        b->nst += nst;
        b->nbytes += used;
        if (used > b->maxlay)
            b->maxlay = used;
    }
}
/* the best sequence of the neighbourhood: perm[k] = the event (its place in ev) that comes k-th, opt[i] = the
   cut of event i (-1: as it is).  Returns the gain in letters; 0: perm and opt describe ev as it is. */
static i64 bs_run(BS *b, const Ev *ev, i64 N, i64 *perm, i64 *opt) {
    int K = b->K, SL = 2 * K;
    b->ev = ev;
    b->N = N;
    b->nst = b->nbytes = b->maxlay = 0;
    for (int k = 0; k < b->ecn; k++)
        b->ec[k].id = -1;
    i64 blk = 16;
    while (blk * blk < N)
        blk++;
    i64 nsnap = (N - 1) / blk + 1, old = 0;
    BLay *snap = calloc((size_t)nsnap, sizeof(BLay)), L2[2];
    memset(L2, 0, sizeof L2);
    L2[0].st = calloc((size_t)b->ns, sizeof(BSt));
    if (!snap || !L2[0].st)
        DIE("out of memory");
    for (i64 i = 0; i < N; i++) {
        opt[i] = co_cur(&ev[i]);
        perm[i] = i;
        if (opt[i] >= 0)
            old += oD(opt[i]);
        if (i)
            old += bs_dist(ev[i - 1].e, ev[i].s);
    }
    b->count = 1;
    for (i64 p = 0; p < N; p++) {
        if (p % blk == 0) {
            BLay *s = &snap[p / blk], *x = &L2[p & 1];
            s->st = malloc((size_t)b->ns * sizeof(BSt));
            s->pool = malloc((size_t)x->used + 1);
            if (!s->st || !s->pool)
                DIE("out of memory");
            memcpy(s->st, x->st, (size_t)b->ns * sizeof(BSt));
            if (x->used)
                memcpy(s->pool, x->pool, (size_t)x->used);
            s->used = s->cap = x->used;
        }
        bs_layer(b, &L2[p & 1], &L2[(p + 1) & 1], p);
    }
    b->count = 0;
    const BSt *fs = L2[N & 1].st;
    i64 best = 1LL << 60;
    int slot = -1;
    for (int cd = K - 1; cd >= 0; cd--)
        if (fs[cd].m && fs[cd].mu < best) {
            best = fs[cd].mu;
            slot = cd;
        }
    if (best > old)
        DIE("internal error: order optimisation (%lld > %lld)", best, old);
    if (best < old) {
        BLay *lay = calloc((size_t)blk + 1, sizeof(BLay));
        int oi = -1;
        if (!lay)
            DIE("out of memory");
        for (i64 q = nsnap - 1; q >= 0; q--) {
            i64 a = q * blk, e = a + blk < N ? a + blk : N;
            BLay keep = lay[0];
            lay[0] = snap[q];
            for (i64 p = a; p < e; p++)
                bs_layer(b, &lay[p - a], &lay[p - a + 1], p);
            for (i64 p = e; p > a;
                 p--) { /* state `slot` of layer p; from layer N - 1 down also the cut oi of its last event */
                const BLay *X = &lay[p - a], *Y = &lay[p - a - 1];
                const BSt *s = &X->st[slot];
                i64 c = p - __builtin_popcount(slot / SL) - K + slot % SL;
                BEv *ce = bs_ev(b, c);
                const unsigned char *rel = X->pool + s->off;
                if (p == N) {
                    for (int t = 0; t < ce->m; t++)
                        if (!rel[t] && (oi < 0 || ce->o[t] == opt[c]))
                            oi = t;
                }
                if (!s->m || oi < 0 || oi >= ce->m)
                    DIE("internal error: order optimisation (layer %lld)", p);
                i64 need = s->mu + rel[oi] - ce->D[oi], cur_c = opt[c];
                u64 Sc = ce->S[oi];
                perm[p - 1] = c;
                opt[c] = ce->o[oi];
                (void)cur_c;
                if (p == 1) {
                    if (need)
                        DIE("internal error: order optimisation (first event)");
                    break;
                }
                int pm = s->pm, fcd = -1, ft = -1;
                i64 u = p - 1 - __builtin_popcount(pm);
                for (int pass = 0; pass < 2 && fcd < 0;
                     pass++) /* the event before c in ev first, and for every event its present cut first */
                    for (int cd = SL - 1; cd >= 0 && fcd < 0; cd--) {
                        const BSt *y = &Y->st[pm * SL + cd];
                        i64 j = u - K + cd;
                        if (!y->m || (j == c - 1) == pass)
                            continue;
                        BEv *je = bs_ev(b, j);
                        const unsigned char *yr = Y->pool + y->off;
                        i64 oj = co_cur(&ev[j]);
                        for (int t = 0; t < je->m; t++)
                            if (y->mu + yr[t] + bs_dist(je->E[t], Sc) == need) {
                                fcd = cd;
                                if (ft < 0 || je->o[t] == oj)
                                    ft = t;
                                if (je->o[t] == oj)
                                    break;
                            }
                    }
                if (fcd < 0)
                    DIE("internal error: order optimisation (no way into layer %lld)", p);
                slot = pm * SL + fcd;
                oi = ft;
            }
            lay[0] = keep;
        }
        for (i64 k = 0; k <= blk; k++) {
            free(lay[k].st);
            free(lay[k].pool);
        }
        free(lay);
    }
    for (i64 k = 0; k < nsnap; k++) {
        free(snap[k].st);
        free(snap[k].pool);
    }
    free(snap);
    free(L2[0].st);
    free(L2[0].pool);
    free(L2[1].st);
    free(L2[1].pool);
    return old - best;
}
/* Sets up the neighbourhood for window size K (1 to 12): number of sets and states per layer, caches, one
   scratch table per thread. */
static void bs_init(BS *b, CO *q, int K) {
    memset(b, 0, sizeof *b);
    memset(q, 0, sizeof *q);
    if (K < 1 || K > 12)
        DIE("--bs K: 1 to 12");
    b->K = K;
    b->nm = 1 << (K - 1);
    b->ns = b->nm * 2 * K;
    b->ecn = 4 * K + 4;
    b->nthr = NTHR;
    b->q = q;
    b->anyskip = co_skip;
    b->ec = calloc((size_t)b->ecn, sizeof(BEv));
    b->scr = calloc((size_t)NTHR, sizeof(BScr));
    if (!b->ec || !b->scr)
        DIE("out of memory");
}
/* Frees what bs_init and the passes allocated. */
static void bs_free(BS *b) {
    for (int k = 0; k < b->ecn; k++) {
        free(b->ec[k].S);
        free(b->ec[k].E);
        free(b->ec[k].D);
        free(b->ec[k].o);
    }
    for (int k = 0; k < b->nthr; k++) {
        free(b->scr[k].t);
        free(b->scr[k].UE);
        free(b->scr[k].mv);
    }
    free(b->ec);
    free(b->scr);
    free(b->q->ban);
}
/* one pass on ev (with co_skip: repeated with bans while two events skip the same window); returns the gain */
static i64 bs_once(BS *b, Ev *ev, i64 N, Ev *orig, Ev *evo, i64 *perm, i64 *opt, i64 *moved, i64 *chg, int *passes) {
    memcpy(orig, ev, (size_t)N * sizeof(Ev));
    b->q->nban = 0;
    *passes = 0;
    i64 l0 = seq_length(ev, N), gain;
    for (;;) {
        gain = bs_run(b, orig, N, perm, opt);
        (*passes)++;
        for (i64 i = 0; i < N; i++) {
            evo[i] = orig[i];
            if (opt[i] >= 0 && opt[i] != co_cur(&orig[i]))
                evo[i] = make_event(opt[i]);
        }
        if (!b->anyskip || !co_clash(b->q, orig, evo, N))
            break;
    }
    *moved = *chg = 0;
    for (i64 k = 0; k < N; k++) {
        i64 i = perm[k];
        ev[k] = evo[i];
        *moved += i != k;
        *chg += evo[i].kind != orig[i].kind || evo[i].a != orig[i].a;
    }
    i64 l1 = seq_length(ev, N);
    if (l0 - l1 != gain)
        DIE("internal error: order optimisation promised %lld, got %lld", gain, l0 - l1);
    return gain;
}
/* the whole sequence, repeated while it gets shorter (a new order has a new neighbourhood) */
static i64 bs_full(Ev *ev, i64 N, int K) {
    BS b;
    CO q;
    bs_init(&b, &q, K);
    Ev *orig = malloc((size_t)N * sizeof(Ev)), *evo = malloc((size_t)N * sizeof(Ev));
    i64 *perm = malloc((size_t)N * 8), *opt = malloc((size_t)N * 8), total = 0;
    if (!orig || !evo || !perm || !opt)
        DIE("out of memory");
    for (;;) {
        double t0 = wall();
        i64 l0 = seq_length(ev, N), moved, chg;
        int passes;
        i64 gain = bs_once(&b, ev, N, orig, evo, perm, opt, &moved, &chg, &passes);
        printf(
            "order optimisation (K=%d): %lld -> %lld (%lld events moved, %lld openings changed; %lld states, tables %lld bytes, largest layer %lld; %d pass%s, %d bans, %.1fs)\n",
            K, l0, l0 - gain, moved, chg, b.nst, b.nbytes, b.maxlay, passes, passes > 1 ? "es" : "", q.nban,
            wall() - t0);
        fflush(stdout);
        total += gain;
        if (gain <= 0)
            break;
    }
    free(orig);
    free(evo);
    free(perm);
    free(opt);
    bs_free(&b);
    return total;
}
/* check against plain enumeration on random windows of at most 8 events: every sequence of the neighbourhood, each with co_run */
static void bs_enum(Ev *sub, int w, int K, int *pm, int d, int used, CO *q, Ev *tmp, i64 *best, i64 *cnt) {
    if (d == w) {
        for (int k = 0; k < w; k++)
            tmp[k] = sub[pm[k]];
        co_run(q, tmp, w, 0, w - 1, 0, NULL);
        i64 l = seq_length(tmp, w);
        if (l < *best)
            *best = l;
        (*cnt)++;
        return;
    }
    int u = 0;
    while ((used >> u) & 1)
        u++;
    for (int c = u; c < w && c < u + K; c++)
        if (!((used >> c) & 1)) {
            pm[d] = c;
            bs_enum(sub, w, K, pm, d + 1, used | (1 << c), q, tmp, best, cnt);
        }
}
/* Self-test of --bs: on random windows of at most 8 events the result of bs_run is compared with plain
   enumeration (bs_enum).  Prints the number of differences. */
static void bs_test(const Ev *ev, i64 N, int K, int trials) {
    BS b;
    CO q, q2;
    bs_init(&b, &q, K);
    b.anyskip = 0;
    memset(&q2, 0, sizeof q2);
    Ev sub[8], s1[8], orig[8], evo[8], tmp[8];
    i64 perm[8], opt[8], bad = 0, gains = 0, nmoved = 0;
    u64 r = seed * 0x9E3779B97F4A7C15ULL + 12345;
    for (int t = 0; t < trials; t++) {
        r = r * 6364136223846793005ULL + 1442695040888963407ULL;
        int w = 2 + (int)((r >> 33) % 7);
        if (w > N)
            w = (int)N;
        r = r * 6364136223846793005ULL + 1442695040888963407ULL;
        i64 a = (i64)((r >> 33) % (u64)(N - w + 1));
        if (K > 5 && w > 7)
            w = 7;
        memcpy(sub, ev + a, (size_t)w * sizeof(Ev));
        if (t & 1)
            for (int k = w - 1; k > 0; k--) {
                r = r * 6364136223846793005ULL + 1442695040888963407ULL;
                int z = (int)((r >> 33) % (u64)(k + 1));
                Ev x = sub[k];
                sub[k] = sub[z];
                sub[z] = x;
            } /* every other window in a random order */
        memcpy(s1, sub, (size_t)w * sizeof(Ev));
        i64 l0 = seq_length(sub, w), moved, chg, best = 1LL << 60, cnt = 0;
        int passes, pm[8];
        i64 gain = bs_once(&b, s1, w, orig, evo, perm, opt, &moved, &chg, &passes);
        bs_enum(sub, w, K, pm, 0, 0, &q2, tmp, &best, &cnt);
        if (l0 - gain != best) {
            bad++;
            printf(
                "bs-test: MISMATCH at %lld (%d events): order optimisation %lld, enumeration %lld (%lld sequences)\n",
                a, w, l0 - gain, best, cnt);
        }
        gains += gain > 0;
        nmoved += moved > 0;
    }
    printf("bs-test K=%d: %d windows, %lld with a gain, %lld with a new order, %lld mismatches\n", K, trials, gains,
           nmoved, bad);
    fflush(stdout);
    bs_free(&b);
}

/* ==================== own part of this file, 2: segment insertion (--or3) ==================== */
/* ---------- segment insertion with re-cutting.  The sequence is cut at k joins (3 <= k <= C of --or3 C) and its
   stretches are put together in another order, none of them reversed.  k = 3: A B C D becomes A C B D, two
   neighbouring stretches of any length change places (a block that moves to another place is the case of a short
   B or C); k = 4 adds A D C B E; k = 5 and 6 add the orders whose new joins form one cycle (see below).
   What a join is worth when the cuts may change: fw is the cost of every cut of every event with the
   best of everything before it, bw with the best of everything after it, both relative to their minimum (fmin,
   gmin), and V(x, y) = min over the cuts of fw_x + join + bw_y is what the join x -> y costs if all before x
   and all after y stay as they are.  The length is fmin[p] + V(p, p+1) + gmin[p+1] + a constant for every p.
   V is listed for every pair with V <= th (only cuts with fw <= th and bw <= th take part), and for the
   pairs between the two sides of expensive joins (V >= T of --or3-x T; at most O3XMAX joins) up to h - 1.
   Candidates: moves with   V of the joins cut - V of the new joins + slack > 0,   found as in Lin and
   Kernighan's method: cut a join, give its left event a new successor y, cut the join before y, give the event
   before y a new successor, ..., and close by joining the last such event to the right event of the first cut;
   after every new join the sum so far must be above -slack (every move has a first cut for which it is).
   The new joins of the chain are listed pairs, each list sorted by V, so a step looks only at the pairs it can
   use.  The closing join may be any pair: if it is not listed its V is computed from the two tables.  A move
   with one join that is not listed is therefore found only from the cut after that join; --or3-dip D lets the
   sum inside the chain go down to -slack - D, so that such a move is found although its cheap cuts come first.
   (The first version, kept as --or3-old, also took pairs that are not listed inside the chain, each as worth
   th + 1, by loops over all events: cubic in the number of expensive joins.)
   Every candidate is judged exactly, that is with the best cuts of the whole new sequence (o3_gain): from
   each new join on, the dynamic programme of co_run is run through the stretch that follows until the costs of
   an event's cuts are what they were before.  That takes a few layers per candidate, and the candidates do
   not depend on each other. */
#define O3KM 6 /* most cuts of a move */
/* for every event: (event, V) */
typedef struct {
    i64 *off;
    int *to;
    unsigned char *c;
} JG;
typedef struct {
    i64 *off, *fmin, *gmin;
    unsigned char *fw, *bw;
} POT;
/* a move: the joins after the events c[0] < ... < c[k-1] are cut (-1: before the first event, N-1: after the last)
   and the stretch that ends at c[i] is followed by the one that starts after c[nx[i]]; est: its gain by the V of
   its joins; ux -> uy: the closing join if it is not listed (-2: none); gx: its gain; zx, zl, zh: see o3_gain */
typedef struct {
    int k, c[O3KM], nx[O3KM], est, ux, uy, zx[O3KM], zl[O3KM], zh[O3KM];
    i64 gx;
} O3M;
/* the stretches in their new order: first event, length, new place */
typedef struct {
    int ns;
    i64 lo[O3KM + 1], len[O3KM + 1], at[O3KM + 2];
} O3P;
typedef struct {
    u64 key;
    i64 zr, cum;
} O3C;
typedef struct {
    O3C *t;
    u64 mask;
    i64 n;
} O3Memo;
/* what a thread needs to judge candidates */
typedef struct {
    BS b;
    CO qb;
    unsigned char *T0, *T1;
    i64 st[4];
} O3T;
typedef struct {
    i64 N;
    int th, slack, kc, quiet;
    JG out, in;
    int *old; /* out: by V, then event (--or3-old: by event); in: by event */
    O3M *mv;
    i64 nc, cap, ntried, budget, nnode[O3KM + 2];
    O3Memo memo;
    POT P;
    const Ev *ev;
    O3T *tc;
    int ntc;
    double tprep;
} O3;
static int o3cuts = 0, o3slack = 2, o3th = 6, o3dry = 0, o3plat = 0, o3old = 0, o3rounds = 0, o3margin = 8, o3dip = 2,
           o3xt = 3, o3zone = 0;
#define O3XMAX 8000 /* most expensive joins with the long lists */
static double o3sec = 0;
static i64 o3maxcand = 0, o3maxlay = -1; /* o3maxlay < 0: 4096, with --or3-old no limit */
static const char *o3stopfile = NULL, *o3plan = NULL;
static int o3_nround = 0;
static double o3_t0 = 0; /* rounds made, start of the pass */
#define O3NOW() (wall() - o3_t0)
/* --or3-rounds R, --or3-sec S (seconds since the pass began), --or3-stop FILE (stop when FILE exists) */
static int o3_stop(void) {
    if (o3rounds > 0 && o3_nround >= o3rounds)
        return 1;
    if (o3sec > 0 && O3NOW() > o3sec)
        return 1;
    if (o3stopfile) {
        FILE *f = fopen(o3stopfile, "rb");
        if (f) {
            fclose(f);
            return 1;
        }
    }
    return 0;
}
static int u64_cmp(const void *a, const void *b) {
    u64 x = *(const u64 *)a, y = *(const u64 *)b;
    return x < y ? -1 : x > y;
}
static int int_cmp(const void *a, const void *b) {
    int x = *(const int *)a, y = *(const int *)b;
    return x < y ? -1 : x > y;
}
/* by the move */
static int o3k_cmp(const void *a, const void *b) {
    const O3M *x = a, *y = b;
    if (x->k != y->k)
        return x->k < y->k ? -1 : 1;
    for (int i = 0; i < x->k; i++)
        if (x->c[i] != y->c[i])
            return x->c[i] < y->c[i] ? -1 : 1;
    for (int i = 0; i < x->k; i++)
        if (x->nx[i] != y->nx[i])
            return x->nx[i] < y->nx[i] ? -1 : 1;
    return 0;
}
/* by falling gain */
static int o3m_cmp(const void *a, const void *b) {
    const O3M *x = a, *y = b;
    return x->gx > y->gx ? -1 : x->gx < y->gx ? 1 : o3k_cmp(a, b);
}
/* by falling estimate */
static int o3e_cmp(const void *a, const void *b) {
    const O3M *x = a, *y = b;
    return x->est > y->est ? -1 : x->est < y->est ? 1 : o3k_cmp(a, b);
}
/* Frees the tables of a fixed-order pass. */
static void o3_cofree(CO *q) {
    free(q->t);
    free(q->S);
    free(q->E);
    free(q->Ep);
    free(q->mv);
    free(q->d);
    free(q->rel);
    free(q->off);
    free(q->lmin);
    free(q->cur);
    free(q->ban);
}
/* the cuts an event may take, in the order of bs_ev (no free skips): o3_it(&it, x); while (o3_next(&it)) ... it.j */
typedef struct {
    const Ev *x;
    const Trail *T;
    i64 o, end;
    int j, fixed;
} O3It;
static inline void o3_it(O3It *it, const Ev *x) {
    it->x = x;
    it->T = &TR[x->t];
    it->fixed = co_cur(x) < 0;
    it->o = it->T->olo - 1;
    it->end = it->T->ohi;
    it->j = -1;
}
/* Next cut the event of the iterator may take; 0 at the end.  An event that cannot be cut again has one. */
static inline int o3_next(O3It *it) {
    if (it->fixed) {
        if (it->j >= 0)
            return 0;
        it->j = 0;
        return 1;
    }
    for (it->o++; it->o < it->end; it->o++)
        if (!OP[it->o].g1 || oSK_t(it->T, it->o) == it->x->skip) {
            it->j++;
            return 1;
        }
    return 0;
}
static inline u64 o3_S(const O3It *it) {
    return it->fixed ? it->x->s : oS_t(it->T, it->o);
}
static inline u64 o3_E(const O3It *it) {
    return it->fixed ? it->x->e : oE_t(it->T, it->o);
}
/* From the lists of successors (out: for x the pairs x -> y) the lists of predecessors (in). */
static void o3_transpose(const JG *out, JG *in, i64 N) {
    i64 cnt = out->off[N];
    in->off = calloc((size_t)(N + 2), 8);
    in->to = malloc((size_t)(cnt + 1) * sizeof(int));
    in->c = malloc((size_t)cnt + 1);
    if (!in->off || !in->to || !in->c)
        DIE("out of memory");
    for (i64 e = 0; e < cnt; e++)
        in->off[out->to[e] + 2]++;
    for (i64 y = 0; y < N; y++)
        in->off[y + 2] += in->off[y + 1];
    for (i64 x = 0; x < N; x++)
        for (i64 e = out->off[x]; e < out->off[x + 1]; e++) {
            i64 z = in->off[out->to[e] + 1]++;
            in->to[z] = (int)x;
            in->c[z] = out->c[e];
        }
}
/* Sorts the cuts of one event by relative cost into the pool UE of the thread: bnd[v] .. bnd[v+1] hold the
   words of the cuts with cost v.  Cuts with cost h or more are left out. */
static void o3_pool1(BScr *w, const unsigned char *rel, const u64 *word, int m, i64 *bnd) {
    i64 pos[17];
    for (int v = 0; v <= h; v++)
        bnd[v] = 0;
    for (int j = 0; j < m; j++)
        if (rel[j] < h)
            bnd[rel[j] + 1]++;
    for (int v = 0; v < h; v++)
        bnd[v + 1] += bnd[v];
    if (bnd[h] > w->ucap) {
        w->ucap = bnd[h] + bnd[h] / 2 + 64;
        free(w->UE);
        w->UE = malloc((size_t)w->ucap * 8);
        if (!w->UE)
            DIE("out of memory");
    }
    for (int v = 0; v < h; v++)
        pos[v] = bnd[v];
    for (int j = 0; j < m; j++)
        if (rel[j] < h)
            w->UE[pos[rel[j]]++] = word[j];
}
/* fw (dir 0) or bw (dir 1) of the whole sequence */
static void o3_sweep(BS *b, const Ev *ev, i64 N, POT *P, int dir) {
    BScr *w = &b->scr[0];
    i64 bnd[18];
    b->ev = ev;
    b->N = N;
    for (int k = 0; k < b->ecn; k++)
        b->ec[k].id = -1;
    for (i64 z = 0; z < N; z++) {
        i64 p = dir ? N - 1 - z : z, pp = dir ? p + 1 : p - 1;
        BEv *e = bs_ev(b, p);
        int m = e->m, mn = 1 << 20;
        unsigned char *rel = (dir ? P->bw : P->fw) + P->off[p];
        if (m != P->off[p + 1] - P->off[p])
            DIE("internal error: segment insertion (openings of event %lld)", p);
        if (m > w->mcap) {
            w->mcap = m + m / 2 + 64;
            free(w->mv);
            w->mv = malloc((size_t)w->mcap * sizeof(int));
            if (!w->mv)
                DIE("out of memory");
        }
        int *mv = w->mv;
        for (int j = 0; j < m; j++)
            mv[j] = z ? h : 0;
        if (z) {
            BEv *x = bs_ev(b, pp);
            o3_pool1(w, (dir ? P->bw : P->fw) + P->off[pp], dir ? x->S : x->E, x->m, bnd);
            bs_join(w, bnd, &e, 1, mv, dir);
        }
        for (int j = 0; j < m; j++) {
            mv[j] += e->D[j];
            if (mv[j] < mn)
                mn = mv[j];
        }
        for (int j = 0; j < m; j++)
            rel[j] = (unsigned char)(mv[j] - mn < h ? mv[j] - mn : h); /* h: h or more (such an cut is never needed) */
        if (dir)
            P->gmin[p] = (z ? P->gmin[p + 1] : 0) + mn;
        else
            P->fmin[p] = (z ? P->fmin[p - 1] : 0) + mn;
    }
}
/* The two tables of a round: for every cut of every event its cost with the best of everything before it
   (fw) and after it (bw), relative to the minima fmin / gmin.  The two sweeps run in parallel. */
static void o3_pot(const Ev *ev, i64 N, POT *P) {
    P->off = malloc((size_t)(N + 1) * 8);
    P->fmin = malloc((size_t)(N + 1) * 8);
    P->gmin = malloc((size_t)(N + 1) * 8);
    if (!P->off || !P->fmin || !P->gmin)
        DIE("out of memory");
#pragma omp parallel for schedule(dynamic, 64) num_threads(NTHR)
    for (i64 p = 0; p < N; p++) {
        O3It it;
        i64 m = 0;
        o3_it(&it, &ev[p]);
        while (o3_next(&it))
            m++;
        P->off[p + 1] = m;
    }
    P->off[0] = 0;
    for (i64 p = 0; p < N; p++)
        P->off[p + 1] += P->off[p];
    P->fw = malloc((size_t)P->off[N] + 1);
    P->bw = malloc((size_t)P->off[N] + 1);
    if (!P->fw || !P->bw)
        DIE("out of memory");
#pragma omp parallel for schedule(static, 1) num_threads(NTHR > 1 ? 2 : 1)
    for (int dir = 0; dir < 2; dir++) {
        BS b;
        CO q;
        bs_init(&b, &q, 1);
        b.anyskip = 0;
        o3_sweep(&b, ev, N, P, dir);
        bs_free(&b);
    }
    if (P->fmin[N - 1] != P->gmin[0])
        DIE("internal error: forward %lld, backward %lld", P->fmin[N - 1], P->gmin[0]);
}
/* The pairs with V <= th.  A[b]: the start words of the cuts with bw = b as (word << 20 | event), sorted; dir:
   where every pair of leading symbols begins.  An cut of x with fw = f and end word E takes, for every overlap
   kk >= h - (th - f) and every b <= th - f - (h - kk), the entries of A[b] that begin with the last kk symbols of
   E: all of them are pairs with V <= th.
   Pairs between the two sides of expensive joins are listed up to th2 > th: xl[x] says that the join after x is
   expensive, xr[y] that the join before y is, and A[16 + b] holds the cuts of the events y with xr[y].
   st: cuts with fw <= th, with bw <= th, entries looked at. */
typedef struct {
    u64 *a;
    i64 n, dir[258];
} O3A;
typedef struct {
    int *to;
    unsigned char *c;
    i64 n, cap;
} O3Buf;
/* For end word E with relative cost rf: every cut on the other side whose start word overlaps it and whose
   cost keeps the sum at th or less, found in the sorted arrays A[b] (b = cost of the cut).  Updates best[] for
   the events found and lists them in touched. */
static inline void o3_vscan(const O3A *A, int th, int rf, u64 E, int x, unsigned char *best, int *touched, int *nt,
                            i64 *nscan) {
    for (int kk = h; kk >= h - (th - rf) && kk >= 1; kk--) {
        u64 wd = E & HMASK[kk], klo = (wd << (4 * (h - kk))) << 20, khi = ((wd + 1) << (4 * (h - kk))) << 20;
        int v0 = rf + h - kk;
        for (int b = 0; b <= th - v0; b++) {
            const O3A *a = &A[b];
            i64 lo, hi;
            if (kk == 1) {
                lo = a->dir[wd << 4];
                hi = a->dir[(wd + 1) << 4];
            } else {
                u64 bk = wd >> (4 * (kk - 2));
                lo = a->dir[bk];
                hi = a->dir[bk + 1];
            }
            if (kk > 2) {
                i64 z = hi;
                while (lo < z) {
                    i64 mid = (lo + z) >> 1;
                    if (a->a[mid] < klo)
                        lo = mid + 1;
                    else
                        z = mid;
                }
            }
            for (; lo < hi && a->a[lo] < khi; lo++) {
                int y = (int)(a->a[lo] & 0xFFFFF), v = v0 + b;
                (*nscan)++;
                if (y == x || v >= best[y])
                    continue;
                if (best[y] == 255)
                    touched[(*nt)++] = y;
                best[y] = (unsigned char)v;
            }
        }
    }
}
/* The pair lists of a round: V(x, y) for every pair of events with V <= th, and up to th2 for pairs between
   the two sides of expensive joins (xl, xr).  out: successors of x sorted by V; in: predecessors of y. */
static void o3_vbuild(const Ev *ev, i64 N, const POT *P, int th, int byev, const char *xl, const char *xr, int th2,
                      JG *out, JG *in, i64 *st) {
    int nthr = NTHR;
    O3A A[32];
    i64 nf = 0, nscan = 0;
    if (N >= (1 << 20) || th > 15 || th2 > 15)
        DIE("too many events");
    i64 *cnt = calloc((size_t)nthr * 32 * 256, 8), *xpos = malloc((size_t)(N + 1) * 8);
    int *xthr = malloc((size_t)(N + 1) * sizeof(int));
    O3Buf *buf = calloc((size_t)nthr, sizeof(O3Buf));
    out->off = malloc((size_t)(N + 1) * 8);
    if (!cnt || !xpos || !xthr || !buf || !out->off)
        DIE("out of memory");
    memset(A, 0, sizeof A);
#pragma omp parallel num_threads(nthr)
    {
        int t = omp_get_thread_num(), nt = omp_get_num_threads();
        i64 lo = N * t / nt, hi = N * (t + 1) / nt, *ct = cnt + (size_t)t * 32 * 256;
        for (i64 y = lo; y < hi; y++) {
            const unsigned char *bw = P->bw + P->off[y];
            int ext = xr && xr[y];
            O3It it;
            o3_it(&it, &ev[y]);
            while (o3_next(&it)) {
                int b = bw[it.j];
                if (b > th && !(ext && b <= th2))
                    continue;
                int k = (int)(o3_S(&it) >> (4 * (h - 2)));
                if (b <= th)
                    ct[b * 256 + k]++;
                if (ext && b <= th2)
                    ct[(16 + b) * 256 + k]++;
            }
        }
#pragma omp barrier
#pragma omp single
        {
            for (int b = 0; b < 32; b++) {
                i64 at = 0;
                for (int k = 0; k < 256; k++) {
                    A[b].dir[k] = at;
                    for (int z = 0; z < nt; z++) {
                        i64 c = cnt[((size_t)z * 32 + b) * 256 + k];
                        cnt[((size_t)z * 32 + b) * 256 + k] = at;
                        at += c;
                    }
                }
                A[b].dir[256] = A[b].dir[257] = at;
                A[b].n = at;
                A[b].a = malloc((size_t)(at + 1) * 8);
                if (!A[b].a)
                    DIE("out of memory");
            }
        }
        for (i64 y = lo; y < hi; y++) {
            const unsigned char *bw = P->bw + P->off[y];
            int ext = xr && xr[y];
            O3It it;
            o3_it(&it, &ev[y]);
            while (o3_next(&it)) {
                int b = bw[it.j];
                if (b > th && !(ext && b <= th2))
                    continue;
                u64 S = o3_S(&it);
                int k = (int)(S >> (4 * (h - 2)));
                if (b <= th)
                    A[b].a[ct[b * 256 + k]++] = (S << 20) | (u64)y;
                if (ext && b <= th2)
                    A[16 + b].a[ct[(16 + b) * 256 + k]++] = (S << 20) | (u64)y;
            }
        }
#pragma omp barrier
#pragma omp for schedule(dynamic, 4)
        for (int q = 0; q < 32 * 256; q++) {
            const O3A *a = &A[q >> 8];
            int k = q & 255;
            if (a->dir[k + 1] - a->dir[k] > 1)
                qsort(a->a + a->dir[k], (size_t)(a->dir[k + 1] - a->dir[k]), 8, u64_cmp);
        }
    }
#pragma omp parallel num_threads(nthr) reduction(+ : nf, nscan)
    {
        O3Buf *B = &buf[omp_get_thread_num()];
        unsigned char *best = malloc((size_t)N + 1);
        int *touched = malloc((size_t)(N + 1) * sizeof(int));
        if (!best || !touched)
            DIE("out of memory");
        memset(best, 255, (size_t)N + 1);
#pragma omp for schedule(dynamic, 16)
        for (i64 x = 0; x < N; x++) {
            const unsigned char *fw = P->fw + P->off[x];
            int nt = 0, ext = xl && xl[x];
            O3It it;
            o3_it(&it, &ev[x]);
            while (o3_next(&it)) {
                int rf = fw[it.j];
                if (rf > th && !(ext && rf <= th2))
                    continue;
                u64 E = o3_E(&it);
                if (rf <= th) {
                    nf++;
                    o3_vscan(A, th, rf, E, (int)x, best, touched, &nt, &nscan);
                }
                if (ext && rf <= th2)
                    o3_vscan(A + 16, th2, rf, E, (int)x, best, touched, &nt, &nscan);
            }
            if (!byev)
                for (int t = 0; t < nt; t++)
                    touched[t] |= best[touched[t]] << 20;
            qsort(touched, (size_t)nt, sizeof(int), int_cmp);
            if (B->n + nt > B->cap) {
                B->cap = (B->n + nt) * 2 + 4096;
                B->to = realloc(B->to, (size_t)B->cap * sizeof(int));
                B->c = realloc(B->c, (size_t)B->cap);
                if (!B->to || !B->c)
                    DIE("out of memory");
            }
            xthr[x] = omp_get_thread_num();
            xpos[x] = B->n;
            out->off[x + 1] = nt;
            for (int t = 0; t < nt; t++) {
                int y = touched[t] & 0xFFFFF;
                B->to[B->n] = y;
                B->c[B->n++] = best[y];
                best[y] = 255;
            }
        }
        free(best);
        free(touched);
    }
    st[0] = nf;
    st[1] = 0;
    for (int b = 0; b < 16; b++)
        st[1] += A[b].n;
    st[2] = nscan;
    for (int b = 0; b < 32; b++)
        free(A[b].a);
    out->off[0] = 0;
    for (i64 x = 0; x < N; x++)
        out->off[x + 1] += out->off[x];
    out->to = malloc((size_t)(out->off[N] + 1) * sizeof(int));
    out->c = malloc((size_t)out->off[N] + 1);
    if (!out->to || !out->c)
        DIE("out of memory");
#pragma omp parallel for schedule(static) num_threads(nthr)
    for (i64 x = 0; x < N; x++) {
        i64 m = out->off[x + 1] - out->off[x];
        const O3Buf *B = &buf[xthr[x]];
        if (m) {
            memcpy(out->to + out->off[x], B->to + xpos[x], (size_t)m * sizeof(int));
            memcpy(out->c + out->off[x], B->c + xpos[x], (size_t)m);
        }
    }
    for (int t = 0; t < nthr; t++) {
        free(buf[t].to);
        free(buf[t].c);
    }
    free(buf);
    free(cnt);
    free(xpos);
    free(xthr);
    o3_transpose(out, in, N);
}
/* V of x -> y if the pair is listed, else -1 */
static inline int o3_look(const O3 *o, i64 x, i64 y) {
    const JG *g = &o->in;
    i64 a = g->off[y], b = g->off[y + 1];
    while (a < b) {
        i64 m = (a + b) >> 1;
        if (g->to[m] < x)
            a = m + 1;
        else
            b = m;
    }
    return a < g->off[y + 1] && g->to[a] == x ? g->c[a] : -1;
}
/* V of the join of piece x to piece y, from the lists. */
/* x = -1: nothing before y; y = N: nothing after x; not listed: th + 1 */
static inline int o3_v(const O3 *o, i64 x, i64 y) {
    if (x < 0 || y >= o->N)
        return 0;
    int v = o3_look(o, x, y);
    return v < 0 ? o->th + 1 : v;
}
static inline int o3_old(const O3 *o, i64 c) {
    return c < 0 || c >= o->N - 1 ? 0 : o->old[c];
}
/* V of x -> y from the tables (h: h or more) */
static int o3_exactv(BS *b, const POT *P, i64 x, i64 y) {
    BScr *w = &b->scr[0];
    i64 bnd[18];
    {
        BEv *ex = bs_ev(b, x);
        o3_pool1(w, P->fw + P->off[x], ex->E, ex->m, bnd);
    }
    BEv *e = bs_ev(b, y);
    int mm = e->m, mn = 1 << 20;
    const unsigned char *bw = P->bw + P->off[y];
    if (mm > w->mcap) {
        w->mcap = mm + mm / 2 + 64;
        free(w->mv);
        w->mv = malloc((size_t)w->mcap * sizeof(int));
        if (!w->mv)
            DIE("out of memory");
    }
    int *mv = w->mv;
    for (int q = 0; q < mm; q++)
        mv[q] = h;
    bs_join(w, bnd, &e, 1, mv, 0);
    for (int q = 0; q < mm; q++)
        if (mv[q] + bw[q] < mn)
            mn = mv[q] + bw[q];
    return mn < h ? mn : h;
}
/* the stretches of a move in their new order; 0: they do not form one sequence */
static int o3_order(const O3M *m, i64 N, O3P *P) {
    int k = m->k, s = 0, n = 0;
    i64 at = 0;
    for (;;) {
        i64 lo = s ? m->c[s - 1] + 1 : 0, hi = s < k ? m->c[s] : N - 1;
        if (n > k)
            return 0;
        P->lo[n] = lo;
        P->len[n] = hi - lo + 1;
        P->at[n] = at;
        at += hi - lo + 1;
        n++;
        if (s == k)
            break;
        s = m->nx[s] + 1;
    }
    P->ns = n;
    P->at[n] = at;
    return n == k + 1;
}
/* Writes into ev2 the sequence that move m makes of ev. */
static void o3_permute(const Ev *ev, Ev *ev2, i64 N, const O3M *m) {
    O3P P;
    if (!o3_order(m, N, &P))
        DIE("internal error: segment insertion (order)");
    for (int j = 0; j < P.ns; j++)
        memcpy(ev2 + P.at[j], ev + P.lo[j], (size_t)P.len[j] * sizeof(Ev));
}
/* r[0 .. k-1]: the cuts in the order they were made; the stretch that ends at r[i] is followed by the one that starts after r[i+1], the last by the one after r[0] */
static void o3_emit(O3 *o, const int *r, int k, int est, int ux, int uy) {
    O3M m;
    O3P P;
    int ord[O3KM], rank[O3KM];
    memset(&m, 0, sizeof m);
    m.k = k;
    m.est = est;
    m.ux = ux;
    m.uy = uy;
    for (int i = 0; i < k; i++) {
        int z = i;
        while (z > 0 && r[ord[z - 1]] > r[i]) {
            ord[z] = ord[z - 1];
            z--;
        }
        ord[z] = i;
    }
    for (int z = 0; z < k; z++) {
        m.c[z] = r[ord[z]];
        rank[ord[z]] = z;
    }
    for (int i = 0; i < k; i++)
        m.nx[rank[i]] = rank[(i + 1) % k];
    if (!o3_order(&m, o->N, &P))
        return;
    if (o->nc == o->cap) {
        o->cap = o->cap ? o->cap * 2 : 1 << 14;
        o->mv = realloc(o->mv, (size_t)o->cap * sizeof(O3M));
        if (!o->mv)
            DIE("out of memory");
    }
    o->mv[o->nc++] = m;
}
/* the chains: g is V of the cuts r[0 .. d] minus V of the joins made */
static void o3_dfs(O3 *o, int *r, int d, int g);
/* the new join r[d] -> y, worth v; then the join before y is cut */
static inline void o3_step(O3 *o, int *r, int d, int g, i64 y, int v) {
    int c = (int)y - 1, p = g - v, sl = o->slack;
    if (p <= -sl - o3dip || c == r[d])
        return;
    for (int z = 0; z < d; z++)
        if (r[z] == c)
            return;
    r[d + 1] = c;
    p += o3_old(o, c);
    if (d + 2 >= 3) { /* close it: c -> the event after the first cut */
        i64 y0 = (i64)r[0] + 1;
        int v2 = c < 0 || y0 >= o->N ? 0 : o3_look(o, c, y0);
        if (v2 >= 0) {
            if (p - v2 > -sl)
                o3_emit(o, r, d + 2, p - v2, -2, -2);
        } else if (p - (o->th + 1) > -sl)
            o3_emit(o, r, d + 2, p - (o->th + 1), c, (int)y0);
    }
    if (d + 2 < o->kc)
        o3_dfs(o, r, d + 1, p);
}
/* Chain search, one level: the left event of the last cut (r[d]) gets each listed successor in turn, as long
   as the sum so far stays above -slack - dip.  g: V of the cuts made minus V of the joins made. */
static void o3_dfs(O3 *o, int *r, int d, int g) {
    i64 N = o->N;
    int x = r[d], lim = g + o->slack + o3dip;
    o->nnode[d]++;
    if (o->ntried++ > o->budget)
        return;
    if (x < 0) {
        for (i64 y = 1; y < N; y++)
            o3_step(o, r, d, g, y, 0);
        return;
    } /* y becomes the first event */
    const JG *out = &o->out;
    for (i64 f = out->off[x], e1 = out->off[x + 1]; f < e1 && out->c[f] < lim; f++)
        o3_step(o, r, d, g, out->to[f], out->c[f]);
    if (x < N - 1)
        o3_step(o, r, d, g, N, 0); /* x becomes the last event */
}
/* --or3-old: the same with pairs that are not listed inside the chain (worth th + 1) and no values computed; lists by event */
static void o3_dfs0(O3 *o, int *r, int d, int g);
/* As o3_step, for --or3-old: a closing join that is not listed counts as th + 1. */
static inline void o3_step0(O3 *o, int *r, int d, int g, i64 y, int v) {
    int c = (int)y - 1, p = g - v;
    if (p <= -o->slack || c == r[d])
        return;
    for (int z = 0; z <= d; z++)
        if (r[z] == c)
            return;
    r[d + 1] = c;
    p += o3_old(o, c);
    if (d + 2 >= 3 && p - o3_v(o, c, (i64)r[0] + 1) > -o->slack)
        o3_emit(o, r, d + 2, p - o3_v(o, c, (i64)r[0] + 1), -2, -2);
    if (d + 2 < o->kc)
        o3_dfs0(o, r, d + 1, p);
}
/* As o3_dfs, for --or3-old: also tries every successor that is not listed, as worth th + 1. */
static void o3_dfs0(O3 *o, int *r, int d, int g) {
    i64 N = o->N;
    int x = r[d], U = o->th + 1;
    o->nnode[d]++;
    if (o->ntried++ > o->budget)
        return;
    if (x < 0) {
        for (i64 y = 1; y < N; y++)
            o3_step0(o, r, d, g, y, 0);
        return;
    }
    const JG *out = &o->out;
    i64 e = out->off[x], e1 = out->off[x + 1];
    for (i64 f = e; f < e1; f++)
        o3_step0(o, r, d, g, out->to[f], out->c[f]);
    if (x < N - 1)
        o3_step0(o, r, d, g, N, 0);
    if (g - U > -o->slack)
        for (i64 y = 0; y < N; y++) { /* pairs that are not listed */
            while (e < e1 && out->to[e] < y)
                e++;
            if (!(e < e1 && out->to[e] == y))
                o3_step0(o, r, d, g, y, U);
        }
}
/* A D C B E is not found that way: its new joins are two pairs, a -> b+1 with b -> a+1 and c -> d+1 with d -> c+1
   for cuts a < c < b < d, and neither pair alone leaves one sequence.  All pairs (a, b) with a listed join are
   collected with their value e = V(a, a+1) + V(b, b+1) - V(a, b+1) - V(b, a+1) (a join that is not listed: th + 1);
   a candidate has a pair with 2e > -slack, and for each of those the pairs that cross it are looked through:
   they are kept by falling e, and within one e by their first cut (X) and by their second cut (Y), so only
   pairs with e high enough and a cut inside the span are touched. */
typedef struct {
    int a, b, e;
} O3X;
/* Order of the pairs for two-pair moves: by falling value e, then by first cut, then by second cut. */
static int o3xa_cmp(const void *x, const void *y) {
    const O3X *p = x, *q = y;
    return p->e != q->e   ? (p->e > q->e ? -1 : 1)
           : p->a != q->a ? (p->a < q->a ? -1 : 1)
           : p->b < q->b  ? -1
                          : p->b > q->b;
}
/* The same order with the second cut before the first. */
static int o3xb_cmp(const void *x, const void *y) {
    const O3X *p = x, *q = y;
    return p->e != q->e   ? (p->e > q->e ? -1 : 1)
           : p->b != q->b ? (p->b < q->b ? -1 : 1)
           : p->a < q->a  ? -1
                          : p->a > q->a;
}
/* Puts the four-cut move made of the pairs x and y on the list of candidates. */
/* x.a < y.a < x.b < y.b */
static void o3_cross4(O3 *o, const O3X *x, const O3X *y) {
    O3M m;
    O3P P;
    memset(&m, 0, sizeof m);
    m.k = 4;
    m.c[0] = x->a;
    m.c[1] = y->a;
    m.c[2] = x->b;
    m.c[3] = y->b;
    m.nx[0] = 2;
    m.nx[2] = 0;
    m.nx[1] = 3;
    m.nx[3] = 1;
    m.est = x->e + y->e;
    m.ux = m.uy = -2;
    if (!o3_order(&m, o->N, &P))
        DIE("internal error: segment insertion (two pairs)");
    if (o->nc == o->cap) {
        o->cap = o->cap ? o->cap * 2 : 1 << 14;
        o->mv = realloc(o->mv, (size_t)o->cap * sizeof(O3M));
        if (!o->mv)
            DIE("out of memory");
    }
    o->mv[o->nc++] = m;
}
/* The moves with two crossing pairs of joins (A D C B E), which the chain search cannot find (see the comment
   above the type O3X). */
static void o3_cross(O3 *o) {
    i64 N = o->N, n = 0, cap = 1 << 16, ng = 0;
    int emax = -1000, U = o->th + 1, sl = o->slack;
    const JG *out = &o->out, *in = &o->in;
    O3X *X = malloc((size_t)cap * sizeof(O3X)), *Y;
    if (!X)
        DIE("out of memory");
#define O3PUSH(A, B, E)                                \
    do {                                               \
        if (n == cap) {                                \
            cap *= 2;                                  \
            X = realloc(X, (size_t)cap * sizeof(O3X)); \
            if (!X)                                    \
                DIE("out of memory");                  \
        }                                              \
        X[n].a = (int)(A);                             \
        X[n].b = (int)(B);                             \
        X[n].e = (E);                                  \
        if (X[n].e > emax)                             \
            emax = X[n].e;                             \
        n++;                                           \
    } while (0)
    for (i64 a = 0; a < N - 1; a++) {
        for (i64 f = out->off[a]; f < out->off[a + 1]; f++) {
            i64 b = (i64)out->to[f] - 1;
            if (b > a)
                O3PUSH(a, b, o3_old(o, a) + o3_old(o, b) - out->c[f] - o3_v(o, b, a + 1));
        }
        O3PUSH(a, N - 1, o3_old(o, a) - o3_v(o, N - 1, a + 1)); /* a becomes the last event */
        for (i64 f = in->off[a + 1]; f < in->off[a + 2]; f++) {
            i64 b = in->to[f];
            if (b > a && b < N - 1 && o3_look(o, a, b + 1) < 0)
                O3PUSH(a, b, o3_old(o, a) + o3_old(o, b) - U - in->c[f]);
        }
    }
    for (i64 b = 0; b < N - 1; b++)
        O3PUSH(-1, b, o3_old(o, b) - o3_v(o, b, 0)); /* b + 1 becomes the first event */
#undef O3PUSH
    {
        i64 m = 0;
        for (i64 k = 0; k < n; k++)
            if (X[k].e + emax > -sl)
                X[m++] = X[k];
        n = m;
    }
    Y = malloc((size_t)(n + 1) * sizeof(O3X));
    if (!Y)
        DIE("out of memory");
    memcpy(Y, X, (size_t)n * sizeof(O3X));
    qsort(X, (size_t)n, sizeof(O3X), o3xa_cmp);
    qsort(Y, (size_t)n, sizeof(O3X), o3xb_cmp);
    for (i64 i = 0; i < n && 2 * X[i].e > -sl; i++) { /* X is sorted by falling e */
        const O3X *g = &X[i];
        ng++;
        for (i64 s = 0; s < n && g->e + X[s].e > -sl;) { /* one group of equal e after the other */
            i64 t = s, lo, hi;
            int e = X[s].e;
            {
                i64 a = s, z = n;
                while (a < z) {
                    i64 mid = (a + z) >> 1;
                    if (X[mid].e == e)
                        a = mid + 1;
                    else
                        z = mid;
                }
                t = a;
            }
            lo = s;
            hi = t;
            while (lo < hi) {
                i64 mid = (lo + hi) >> 1;
                if (X[mid].a <= g->a)
                    lo = mid + 1;
                else
                    hi = mid;
            }
            for (i64 j = lo; j < t && X[j].a < g->b; j++) {
                o->ntried++;
                if (X[j].b > g->b)
                    o3_cross4(o, g, &X[j]);
            }
            lo = s;
            hi = t;
            while (lo < hi) {
                i64 mid = (lo + hi) >> 1;
                if (Y[mid].b <= g->a)
                    lo = mid + 1;
                else
                    hi = mid;
            }
            for (i64 j = lo; j < t && Y[j].b < g->b; j++) {
                o->ntried++;
                if (Y[j].a < g->a)
                    o3_cross4(o, &Y[j], g);
            }
            s = t;
        }
    }
    o->nnode[O3KM + 1] = ng;
    free(X);
    free(Y);
}
/* All candidates of the round: a chain search from every cut, then the two-pair moves. */
static void o3_scan(O3 *o) {
    int r[O3KM + 1];
    for (int d = 0; d <= O3KM + 1; d++)
        o->nnode[d] = 0;
    for (i64 a = -1; a < o->N; a++) {
        r[0] = (int)a;
        int g = o3_old(o, a);
        if (g > -o->slack) {
            if (o3old)
                o3_dfs0(o, r, 0, g);
            else
                o3_dfs(o, r, 0, g);
        }
    }
    if (o->kc >= 4)
        o3_cross(o);
}
/* Prints a move: its cuts, the lengths of its blocks and the V of its old and new joins. */
static void o3_print(const O3 *o, const O3M *m, i64 N) {
    O3P P;
    o3_order(m, N, &P);
    printf("cuts after");
    for (int i = 0; i < m->k; i++)
        printf(" %d", m->c[i]);
    printf(", stretches of");
    for (int j = 0; j < P.ns; j++)
        printf(" %lld", P.len[j]);
    printf(" events");
    if (o) {
        printf(", V of the new joins");
        for (int i = 0; i < m->k; i++) {
            i64 x = m->c[i], y = (i64)m->c[m->nx[i]] + 1;
            int v = x < 0 || y >= N ? 0 : o3_look(o, x, y);
            if (v < 0)
                printf(" -");
            else
                printf(" %d", v);
        }
        printf(" for");
        for (int i = 0; i < m->k; i++)
            printf(" %d", o3_old(o, m->c[i]));
    }
}
/* The exact gain of a move.  The stretch before the first cut stays as it is (its costs are fw).  From each new join
   on, the dynamic programme of co_run is run through the stretch that follows, but only until the costs of an
   event's cuts are again what they were (relative to their minimum, and h standing for h or more): the rest
   of the stretch is then as before and its old costs are taken.  The last stretch needs its first event only:
   bw says what follows.  With fwd the last stretch is treated like the others: then nothing here looks ahead,
   and two moves do not disturb each other when neither changes what the other one has read (see o3_place).
   Many candidates share a new join x -> y; when the stretch that ends with x has its old costs
   at x, what follows y does not depend on the candidate and is kept (O3Memo, shared by the threads: where the old
   costs are back and the cost up to there; for a last stretch its cost).  T0, T1: two tables for the largest
   event.  st: layers computed, most layers after one join, joins computed, joins taken from the memo.
   The move gets its zones: for the j-th new join, zl[j] .. zh[j] are the events whose costs were computed again.
   O3BAD: given up (--or3-maxlay: more than that many layers after one join) or not judged. */
#define O3BAD (-(1LL << 40))
/* Looks up what follows a new join x -> y when the block before x has its old costs (shared by the threads). */
static int o3_memo_get(O3Memo *M, u64 key, i64 *zr, i64 *cum) {
    int f = 0;
#pragma omp critical(o3memo)
    if (M->t) {
        u64 i = hmix(key) & M->mask;
        while (M->t[i].key != ~0ULL) {
            if (M->t[i].key == key) {
                *zr = M->t[i].zr;
                *cum = M->t[i].cum;
                f = 1;
                break;
            }
            i = (i + 1) & M->mask;
        }
    }
    return f;
}
/* Stores that; the table doubles when it is half full. */
static void o3_memo_put(O3Memo *M, u64 key, i64 zr, i64 cum) {
#pragma omp critical(o3memo)
    {
        if (!M->t || 2 * (u64)(M->n + 1) > M->mask + 1) {
            O3C *old = M->t;
            u64 om = M->mask;
            M->mask = old ? 2 * om + 1 : (1 << 12) - 1;
            M->t = malloc((size_t)(M->mask + 1) * sizeof(O3C));
            if (!M->t)
                DIE("out of memory");
            for (u64 z = 0; z <= M->mask; z++)
                M->t[z].key = ~0ULL;
            if (old)
                for (u64 z = 0; z <= om; z++)
                    if (old[z].key != ~0ULL) {
                        u64 q = hmix(old[z].key) & M->mask;
                        while (M->t[q].key != ~0ULL)
                            q = (q + 1) & M->mask;
                        M->t[q] = old[z];
                    }
            free(old);
        }
        u64 i = hmix(key) & M->mask;
        while (M->t[i].key != ~0ULL && M->t[i].key != key)
            i = (i + 1) & M->mask;
        if (M->t[i].key == ~0ULL)
            M->n++;
        M->t[i].key = key;
        M->t[i].zr = zr;
        M->t[i].cum = cum;
    }
}
/* Exact gain of move m: the best cuts of the whole new sequence, computed block by block as described in
   the comment above.  Fills the zones of the move.  O3BAD: given up. */
static i64 o3_gain(BS *b, const POT *P, i64 N, O3M *m, unsigned char *T0, unsigned char *T1, O3Memo *M, i64 *st,
                   int fwd) {
    O3P R;
    BScr *w = &b->scr[0];
    i64 bnd[18], tot = 0, pe = -1, zr, mc;
    const unsigned char *pt = NULL;
    unsigned char *T = T0;
    int nz = 0;
    if (!o3_order(m, N, &R))
        DIE("internal error: segment insertion (order)");
    for (int j = 0; j < O3KM; j++) {
        m->zx[j] = m->zl[j] = 0;
        m->zh[j] = -1;
    }
    for (int j = 0; j < R.ns; j++) {
        i64 lo = R.lo[j], hi = lo + R.len[j] - 1;
        if (hi < lo)
            continue;
        if (!j) {
            tot = P->fmin[hi];
            pt = P->fw + P->off[hi];
            pe = hi;
            continue;
        }
        int clean = pe >= 0 && pt == P->fw + P->off[pe], last = !fwd && j == R.ns - 1 && pe >= 0,
            zi = nz < O3KM ? nz++ : O3KM - 1;
        u64 key = ((u64)last << 62) | ((u64)(pe + 1) << 24) | (u64)lo;
        m->zx[zi] = (int)pe;
        m->zl[zi] = (int)lo;
        m->zh[zi] = (int)lo;
        if (clean && o3_memo_get(M, key, &zr, &mc)) {
            if (last) {
                st[3]++;
                return P->fmin[N - 1] - (tot + mc + P->gmin[lo]);
            }
            if (zr <= hi) {
                st[3]++;
                m->zh[zi] = (int)zr;
                tot += mc + P->fmin[hi] - P->fmin[zr];
                pt = P->fw + P->off[hi];
                pe = hi;
                continue;
            }
        }
        st[2]++;
        if (last) {
            {
                BEv *x = bs_ev(b, pe);
                o3_pool1(w, pt, x->E, x->m, bnd);
            }
            BEv *e = bs_ev(b, lo);
            int mm = e->m, mn = 1 << 20;
            const unsigned char *bw = P->bw + P->off[lo];
            if (mm > w->mcap) {
                w->mcap = mm + mm / 2 + 64;
                free(w->mv);
                w->mv = malloc((size_t)w->mcap * sizeof(int));
                if (!w->mv)
                    DIE("out of memory");
            }
            int *mv = w->mv;
            for (int q = 0; q < mm; q++)
                mv[q] = h;
            bs_join(w, bnd, &e, 1, mv, 0);
            for (int q = 0; q < mm; q++)
                if (mv[q] + bw[q] < mn)
                    mn = mv[q] + bw[q];
            st[0]++;
            if (clean)
                o3_memo_put(M, key, lo, mn);
            return P->fmin[N - 1] - (tot + mn + P->gmin[lo]);
        }
        i64 cum = 0, nl = 0;
        for (i64 z = lo;; z++) {
            if (pe >= 0) {
                BEv *x = bs_ev(b, pe);
                o3_pool1(w, pt, x->E, x->m, bnd);
            }
            BEv *e = bs_ev(b, z);
            int mm = e->m, mn = 1 << 20;
            if (mm > w->mcap) {
                w->mcap = mm + mm / 2 + 64;
                free(w->mv);
                w->mv = malloc((size_t)w->mcap * sizeof(int));
                if (!w->mv)
                    DIE("out of memory");
            }
            int *mv = w->mv;
            for (int q = 0; q < mm; q++)
                mv[q] = pe >= 0 ? h : 0;
            if (pe >= 0)
                bs_join(w, bnd, &e, 1, mv, 0);
            for (int q = 0; q < mm; q++) {
                mv[q] += e->D[q];
                if (mv[q] < mn)
                    mn = mv[q];
            }
            for (int q = 0; q < mm; q++)
                T[q] = (unsigned char)(mv[q] - mn < h ? mv[q] - mn : h);
            tot += mn;
            cum += mn;
            st[0]++;
            nl++;
            m->zh[zi] = (int)z;
            if (!memcmp(T, P->fw + P->off[z], (size_t)mm)) {
                if (clean)
                    o3_memo_put(M, key, z, cum);
                tot += P->fmin[hi] - P->fmin[z];
                pt = P->fw + P->off[hi];
                pe = hi;
                break;
            }
            pt = T;
            pe = z;
            T = T == T0 ? T1 : T0;
            if (z == hi)
                break;
            if (nl >= (o3maxlay > 0 ? o3maxlay : o3maxlay < 0 && !o3old ? 4096 : N + 1)) {
                if (nl > st[1])
                    st[1] = nl;
                return O3BAD;
            }
        }
        if (nl > st[1])
            st[1] = nl;
    }
    return P->fmin[N - 1] - tot;
}
/* A fresh pass for a sequence of N events, with the options as given. */
static void o3_init(O3 *o, i64 N) {
    memset(o, 0, sizeof *o);
    o->N = N;
    o->th = o3th < h ? o3th : h - 1;
    o->slack = o3slack;
    o->budget = 400000000;
    o->kc = o3cuts < 3 ? 3 : o3cuts > O3KM ? O3KM : o3cuts;
    o->old = malloc((size_t)N * sizeof(int));
    if (!o->old)
        DIE("out of memory");
}
/* what a round leaves behind */
static void o3_clear(O3 *o) {
    free(o->out.off);
    free(o->out.to);
    free(o->out.c);
    free(o->in.off);
    free(o->in.to);
    free(o->in.c);
    free(o->memo.t);
    memset(&o->out, 0, sizeof o->out);
    memset(&o->in, 0, sizeof o->in);
    memset(&o->memo, 0, sizeof o->memo);
    free(o->P.off);
    free(o->P.fmin);
    free(o->P.gmin);
    free(o->P.fw);
    free(o->P.bw);
    memset(&o->P, 0, sizeof o->P);
    for (int t = 0; t < o->ntc; t++) {
        free(o->tc[t].T0);
        free(o->tc[t].T1);
        bs_free(&o->tc[t].b);
    }
    free(o->tc);
    o->tc = NULL;
    o->ntc = 0;
}
static void o3_done(O3 *o) {
    o3_clear(o);
    free(o->old);
    free(o->mv);
}
/* Tables, pairs and candidates of ev: o->mv[0 .. nc-1], by falling estimate (--or3-old: by the move), not yet judged */
static void o3_prepare(O3 *o, const Ev *ev) {
    double t1 = wall();
    i64 N = o->N, ng[3], hist[16] = {0}, vh[18] = {0}, more = 0, maxm = 0;
    int *old = o->old, th = o->th, sl = o->slack;
    POT *P = &o->P;
    o3_clear(o);
    o->ev = ev;
    o->tprep = t1;
    o3_pot(ev, N, P);
    double t2 = wall();
    if (!o->quiet) {
        printf("segment insertion, round %d (%.0fs): costs of %lld openings from both ends, %.1fs\n", o3_nround + 1,
               O3NOW(), P->off[N], t2 - t1);
        fflush(stdout);
    }
    for (i64 i = 0; i < N; i++) {
        old[i] = i + 1 < N ? (int)(P->fmin[N - 1] - P->fmin[i] - P->gmin[i + 1]) : 0;
        if (i + 1 < N) {
            vh[old[i] <= h ? old[i] : h]++;
            more += old[i] > dist(ev[i].e, ev[i + 1].s);
        }
        if (P->off[i + 1] - P->off[i] > maxm)
            maxm = P->off[i + 1] - P->off[i];
    }
    char *xl = NULL, *xr = NULL;
    int th2 = h - 1, xt = o3xt;
    i64 nx = 0;
    if (!o3old && xt > 0 && th2 > th) { /* the expensive joins: long lists between their sides (and the two ends) */
        for (; xt <= h; xt++) {
            nx = 0;
            for (int v = xt; v <= h; v++)
                nx += vh[v];
            if (nx <= O3XMAX)
                break;
        }
        xl = calloc((size_t)N + 1, 1);
        xr = calloc((size_t)N + 1, 1);
        if (!xl || !xr)
            DIE("out of memory");
        for (i64 i = 0; i + 1 < N; i++)
            if (old[i] >= xt)
                xl[i] = xr[i + 1] = 1;
        xr[0] = xl[N - 1] = 1;
    }
    o3_vbuild(ev, N, P, th, o3old, xl, xr, th2, &o->out, &o->in, ng);
    for (i64 e = 0; e < o->out.off[N]; e++)
        hist[o->out.c[e] & 15]++;
    double t3 = wall();
    if (!o->quiet) {
        printf(
            "segment insertion: %lld openings within %d of the best before them, %lld after them; %lld pairs of events with V <= %d",
            ng[0], th, ng[1], o->out.off[N], th);
        if (xl)
            printf(" or between the %lld joins with V >= %d", nx, xt);
        printf(" (");
        for (int c = 0, f = 0; c < 16; c++)
            if (hist[c])
                printf("%s%d: %lld", f++ ? ", " : "", c, hist[c]);
        printf("); present joins by V:");
        for (int c = 0; c <= h; c++)
            if (vh[c])
                printf(" %d:%lld", c, vh[c]);
        printf(" (%lld above their cost); %lld entries looked at, %.1fs\n", more, ng[2], t3 - t2);
        fflush(stdout);
    }
    free(xl);
    free(xr);
    /* one set of tables for every thread that judges */
    o->ntc = NTHR;
    o->tc = calloc((size_t)o->ntc, sizeof(O3T));
    if (!o->tc)
        DIE("out of memory");
    for (int t = 0; t < o->ntc; t++) {
        O3T *c = &o->tc[t];
        bs_init(&c->b, &c->qb, 1);
        c->b.anyskip = 0;
        c->b.ev = ev;
        c->b.N = N;
        free(c->b.ec);
        c->b.ecn = 64;
        c->b.ec = calloc((size_t)c->b.ecn, sizeof(BEv));
        c->T0 = malloc((size_t)maxm + 1);
        c->T1 = malloc((size_t)maxm + 1);
        if (!c->b.ec || !c->T0 || !c->T1)
            DIE("out of memory");
        for (int k = 0; k < c->b.ecn; k++)
            c->b.ec[k].id = -1;
    }
    o->nc = o->ntried = 0;
    o3_scan(o);
    if (o->ntried > o->budget)
        printf("segment insertion: the search for candidates was cut short\n");
    i64 nraw = o->nc, npend = 0, nval = 0, nkept = 0;
    if (o->nc)
        qsort(o->mv, (size_t)o->nc, sizeof(O3M), o3k_cmp);
    {
        i64 m = 0;
        for (i64 k = 0; k < o->nc; k++)
            if (!k || o3k_cmp(&o->mv[k], &o->mv[k - 1]))
                o->mv[m++] = o->mv[k];
        o->nc = m;
    }
    double t4 = wall();
    i64 ndiff = o->nc;
    /* closing joins that are not listed: their V from the tables */
    for (i64 k = 0; k < o->nc; k++)
        npend += o->mv[k].ux > -2;
    if (npend && !o3dry) {
        u64 *pk = malloc((size_t)npend * 8);
        unsigned char *pv;
        i64 m = 0;
        if (!pk)
            DIE("out of memory");
        for (i64 k = 0; k < o->nc; k++)
            if (o->mv[k].ux > -2)
                pk[m++] = ((u64)(o->mv[k].ux + 1) << 24) | (u64)o->mv[k].uy;
        qsort(pk, (size_t)m, 8, u64_cmp);
        nval = 0;
        for (i64 k = 0; k < m; k++)
            if (!k || pk[k] != pk[k - 1])
                pk[nval++] = pk[k];
        pv = malloc((size_t)nval + 1);
        if (!pv)
            DIE("out of memory");
#pragma omp parallel for schedule(dynamic, 16) num_threads(NTHR)
        for (i64 k = 0; k < nval; k++)
            pv[k] = (unsigned char)o3_exactv(&o->tc[omp_get_thread_num()].b, P, (i64)(pk[k] >> 24) - 1,
                                             (i64)(pk[k] & 0xFFFFFF));
        m = 0;
        for (i64 k = 0; k < o->nc; k++) {
            O3M *c = &o->mv[k];
            if (c->ux > -2) {
                u64 key = ((u64)(c->ux + 1) << 24) | (u64)c->uy;
                i64 a = 0, z = nval;
                while (a < z) {
                    i64 mid = (a + z) >> 1;
                    if (pk[mid] < key)
                        a = mid + 1;
                    else
                        z = mid;
                }
                c->est += th + 1 - pv[a];
                if (c->est <= -sl)
                    continue;
                nkept++;
            }
            o->mv[m++] = *c;
        }
        o->nc = m;
        free(pk);
        free(pv);
    }
    if (!o3old && o->nc)
        qsort(o->mv, (size_t)o->nc, sizeof(O3M), o3e_cmp);
    i64 nall = o->nc;
    if (!o3old && o3maxcand > 0 && o->nc > o3maxcand)
        o->nc = o3maxcand;
    double t5 = wall();
    i64 byk[O3KM + 1] = {0};
    for (i64 k = 0; k < o->nc; k++) {
        byk[o->mv[k].k]++;
        o->mv[k].gx = O3BAD;
    }
    if (!o->quiet || o3dry) {
        printf("segment insertion (th %d, slack %d): chains by number of joins:", th, sl);
        for (int d = 0; d < o->kc; d++)
            printf(" %lld", o->nnode[d]);
        if (o->kc >= 4)
            printf(", %lld pairs for two pairs", o->nnode[O3KM + 1]);
        printf(
            "; %lld moves, %lld different (%.1fs); %lld closing joins not listed, %lld valued, %lld moves kept (%.1fs); %lld candidates",
            nraw, ndiff, t4 - t3, npend, nval, nkept, t5 - t4, nall);
        if (o->nc < nall)
            printf(", only the %lld with the best estimate (%d and more) are looked at", o->nc, o->mv[o->nc - 1].est);
        printf(" (");
        for (int k = 3; k <= o->kc; k++)
            printf("%s%lld with %d cuts", k > 3 ? ", " : "", byk[k], k);
        printf(")\n");
        fflush(stdout);
    }
}
/* the exact gains of the candidates idx[0 .. n-1]; fwd: with their zones */
static void o3_judge(O3 *o, const i64 *idx, i64 n, int fwd) {
#pragma omp parallel for schedule(dynamic, 1) num_threads(NTHR)
    for (i64 q = 0; q < n; q++) {
        O3T *c = &o->tc[omp_get_thread_num()];
        O3M *m = &o->mv[idx[q]];
        i64 g = o3_gain(&c->b, &o->P, o->N, m, c->T0, c->T1, &o->memo, c->st, fwd);
        if (fwd && m->gx != O3BAD && g != O3BAD && g != m->gx)
            DIE("internal error: segment insertion (gain %lld, with its zones %lld)", m->gx, g);
        m->gx = g;
    }
}
/* Adds up the counters of the search threads (st[1] is their maximum). */
static void o3_stats(const O3 *o, i64 *st) {
    for (int k = 0; k < 4; k++)
        st[k] = 0;
    for (int t = 0; t < o->ntc; t++) {
        const i64 *s = o->tc[t].st;
        st[0] += s[0];
        if (s[1] > st[1])
            st[1] = s[1];
        st[2] += s[2];
        st[3] += s[3];
    }
}
/* all candidates of ev with their exact gains, the best first; returns the best gain (0: none) */
static i64 o3_round(O3 *o, const Ev *ev) {
    o3_prepare(o, ev);
    if (o3dry)
        return 0;
    double t5 = wall(), tlast = t5;
    i64 N = o->N, npos = 0, nzero = 0, gh[5] = {0}, best = 0, st[4], nbad = 0, njud = 0;
    int sl = o->slack;
    for (i64 a = 0; a < o->nc; a += 256) { /* in pieces, so that the time limit is seen */
        if (o3sec > 0 && O3NOW() > o3sec)
            break;
        i64 n = o->nc - a < 256 ? o->nc - a : 256;
        i64 idx[256];
        for (i64 q = 0; q < n; q++)
            idx[q] = a + q;
        o3_judge(o, idx, n, 0);
        njud += n;
        if (!o->quiet && wall() - tlast > 60) {
            tlast = wall();
            printf("segment insertion: %lld of %lld candidates judged (%.0fs)\n", njud, o->nc, tlast - t5);
            fflush(stdout);
        }
    }
    /* what the shorter ones look like: by estimate, and by the largest V of their new joins */
    i64 et[2][24], vt[2][20];
    memset(et, 0, sizeof et);
    memset(vt, 0, sizeof vt);
    for (i64 k = 0; k < njud; k++) {
        const O3M *c = &o->mv[k];
        i64 g = c->gx;
        int mxv = 0, nu = 0, e = c->est + sl;
        if (e < 0)
            e = 0;
        if (e > 23)
            e = 23;
        if (g == O3BAD) {
            nbad++;
            continue;
        }
        if (g > 0)
            npos++;
        if (g == 0)
            nzero++;
        if (g >= -4 && g < 0)
            gh[-g]++;
        for (int i = 0; i < c->k; i++) {
            i64 x = c->c[i], y = (i64)c->c[c->nx[i]] + 1;
            int v = x < 0 || y >= N ? 0 : o3_look(o, x, y);
            if (v < 0)
                nu++;
            else if (v > mxv)
                mxv = v;
        }
        et[0][e]++;
        vt[0][nu ? 15 + (nu > 3 ? 3 : nu) : mxv]++;
        if (g > 0) {
            et[1][e]++;
            vt[1][nu ? 15 + (nu > 3 ? 3 : nu) : mxv]++;
        }
    }
    if (o->nc)
        qsort(o->mv, (size_t)o->nc, sizeof(O3M), o3m_cmp);
    if (o->nc && o->mv[0].gx != O3BAD)
        best = o->mv[0].gx;
    o3_stats(o, st);
    if (!o->quiet) {
        printf("segment insertion: shorter / judged by estimate:");
        for (int e = 0; e < 24; e++)
            if (et[0][e])
                printf(" %d: %lld/%lld", e - sl, et[1][e], et[0][e]);
        printf("; by the largest V of the new joins:");
        for (int v = 0; v < 15; v++)
            if (vt[0][v])
                printf(" %d: %lld/%lld", v, vt[1][v], vt[0][v]);
        for (int u = 1; u <= 3; u++)
            if (vt[0][15 + u])
                printf(" %d not listed: %lld/%lld", u, vt[1][15 + u], vt[0][15 + u]);
        printf(
            "\nsegment insertion: %lld judged: %lld shorter, %lld equal, one to four longer: %lld %lld %lld %lld; best gain %lld; %.1f layers per candidate, at most %lld after one join, %lld joins computed, %lld from the memo",
            njud, npos, nzero, gh[1], gh[2], gh[3], gh[4], best, njud ? (double)st[0] / njud : 0.0, st[1], st[2],
            st[3]);
        if (nbad)
            printf(", %lld given up", nbad);
        if (njud < o->nc)
            printf(", %lld not judged (time)", o->nc - njud);
        printf(" (%.1fs; round %.1fs)\n", wall() - t5, wall() - o->tprep);
        fflush(stdout);
    }
    return best > 0 ? best : 0;
}
/* Several moves at once.  Every move says which stretch follows each of its cuts; all cuts are different.  Returns 0
   if the stretches do not come out as one sequence; with ev2 the new sequence is written (only for a set that
   has been tested).  cut: room for all cuts; nxt: as many ints. */
typedef struct {
    int c, nx;
} O3Cut;
static int o3cut_cmp(const void *a, const void *b) {
    int x = ((const O3Cut *)a)->c, y = ((const O3Cut *)b)->c;
    return x < y ? -1 : x > y;
}
/* Several moves at once (see the comment above the type O3Cut): 0 if their blocks do not form one sequence. */
static int o3_compose(const O3M *mv, i64 n, const O3M *extra, i64 N, const Ev *ev, Ev *ev2, O3Cut *cut, int *nxt) {
    i64 K = 0, cnt = 0, at = 0, s = 0;
    for (i64 q = 0; q < n + (extra != NULL); q++) {
        const O3M *m = q < n ? &mv[q] : extra;
        for (int i = 0; i < m->k; i++) {
            cut[K].c = m->c[i];
            cut[K].nx = m->c[m->nx[i]];
            K++;
        }
    }
    qsort(cut, (size_t)K, sizeof(O3Cut), o3cut_cmp);
    for (i64 i = 0; i < K; i++) {
        i64 a = 0, z = K;
        while (a < z) {
            i64 mid = (a + z) >> 1;
            if (cut[mid].c < cut[i].nx)
                a = mid + 1;
            else
                z = mid;
        }
        nxt[i] = (int)a + 1;
    }
    for (;;) {
        i64 lo = s ? cut[s - 1].c + 1 : 0, hi = s < K ? cut[s].c : N - 1;
        if (++cnt > K + 1)
            return 0;
        if (ev2 && hi >= lo)
            memcpy(ev2 + at, ev + lo, (size_t)(hi - lo + 1) * sizeof(Ev));
        at += hi - lo + 1;
        if (s == K)
            break;
        s = nxt[s];
    }
    return cnt == K + 1 && at == N;
}
/* The place of a move: mg events on either side of its cuts and, once it is judged, its zones (--or3-zone Z: only
   their first Z events) and mg events after them.  mark[e + 1] belongs to event e (-1 .. N).  what = 0: is the place free?  1: take it.  2: give it back. */
static int o3_place(char *mark, const O3M *m, i64 N, int mg, int what, int judged) {
    for (int i = 0; i < m->k + (judged ? O3KM : 0); i++) {
        i64 a, b;
        if (i < m->k) {
            a = (i64)m->c[i] - mg;
            b = (i64)m->c[i] + 1 + mg;
        } else {
            int j = i - m->k;
            if (m->zh[j] < m->zl[j])
                continue;
            a = m->zl[j];
            b = (o3zone > 0 && m->zh[j] - m->zl[j] > o3zone ? (i64)m->zl[j] + o3zone : (i64)m->zh[j]) + mg;
        }
        if (a < -1)
            a = -1;
        if (b > N)
            b = N;
        if (what)
            memset(mark + a + 1, what == 1, (size_t)(b - a + 1));
        else
            for (i64 z = a; z <= b; z++)
                if (mark[z + 1])
                    return 0;
    }
    return 1;
}
/* The gains are counted from the sequence with its best cuts: a sequence that comes without them gets them first
   (one that has them stays as it is). */
static i64 o3_first(CO *q, Ev *ev, i64 N) {
    i64 a0 = seq_length(ev, N);
    co_run(q, ev, N, 0, N - 1, 0, NULL);
    i64 a1 = seq_length(ev, N);
    if (a1 < a0) {
        printf("segment insertion: best openings of the sequence as it came: %lld -> %lld\n", a0, a1);
        fflush(stdout);
        if (o3plan)
            write_plan(ev, N, o3plan);
    }
    return a0 - a1;
}
/* A round: tables, pairs, candidates, and the gain of every candidate.  Then the shorter ones are taken, the best
   first, if their place is free: a move is judged once more without looking ahead, which gives its zones, and
   taken if its cuts and zones are more than --or3-margin events away from those of the moves already taken and
   the moves together still give one sequence.  The moves are then made together and the whole sequence is
   cut again; that gives the sum of their gains (if it ever gives less than nine tenths of it, the first half of
   them is tried, and so on; one move alone gives what it promised).  The plan is written after every round that
   made the word shorter. */
static i64 o3_full(Ev *ev, i64 N) {
    O3 o;
    o3_init(&o, N);
    CO q;
    memset(&q, 0, sizeof q);
    enum { MAXSEL = 8192 };
    int nbmax = 4 * NTHR, mg = o3margin;
    Ev *ev2 = malloc((size_t)N * sizeof(Ev));
    i64 total = 0, *batch = malloc((size_t)nbmax * 8);
    O3Cut *cut = malloc((size_t)(MAXSEL + 1) * O3KM * sizeof(O3Cut));
    int *nxt = malloc((size_t)(MAXSEL + 1) * O3KM * sizeof(int));
    char *mark = malloc((size_t)N + 3), *bm = calloc((size_t)N + 3, 1);
    O3M *sel = malloc((size_t)MAXSEL * sizeof(O3M));
    if (!ev2 || !batch || !cut || !nxt || !mark || !bm || !sel)
        DIE("out of memory");
    total += o3_first(&q, ev, N);
    for (;;) {
        if (o3_stop()) {
            printf("segment insertion: stopped after %d rounds, %.0fs\n", o3_nround, O3NOW());
            fflush(stdout);
            break;
        }
        double t0 = wall();
        i64 l0 = seq_length(ev, N), l1, g = o3_round(&o, ev);
        o3_nround++;
        if (g <= 0)
            break;
        double t1 = wall();
        i64 nshort = 0, first = 0, nsel = 0, njud = 0, ndrop = 0, ncyc = 0, promised = 0;
        O3M *mv = o.mv;
        while (nshort < o.nc && mv[nshort].gx > 0)
            nshort++;
        char *cs = calloc((size_t)nshort + 1, 1);
        if (!cs)
            DIE("out of memory");
        memset(mark, 0, (size_t)N + 3);
        while (nsel < MAXSEL) {
            int nb = 0;
            while (first < nshort && cs[first])
                first++;
            for (i64 k = first; k < nshort && nb < nbmax; k++) {
                if (cs[k])
                    continue;
                if (!o3_place(mark, &mv[k], N, mg, 0, 0)) {
                    cs[k] = 1;
                    ndrop++;
                    continue;
                }
                if (!o3_place(bm, &mv[k], N, mg, 0, 0))
                    continue; /* next to one of this batch: later */
                batch[nb++] = k;
                o3_place(bm, &mv[k], N, mg, 1, 0);
            }
            if (!nb)
                break;
            o3_judge(&o, batch, nb, 1);
            for (int z = 0; z < nb; z++) {
                O3M *m = &mv[batch[z]];
                cs[batch[z]] = 1;
                njud++;
                o3_place(bm, m, N, mg, 2, 0);
                if (m->gx == O3BAD || m->gx <= 0)
                    continue;
                if (!o3_place(mark, m, N, mg, 0, 1)) {
                    ndrop++;
                    continue;
                }
                if (nsel && !o3_compose(sel, nsel, m, N, NULL, NULL, cut, nxt)) {
                    ncyc++;
                    continue;
                }
                sel[nsel++] = *m;
                promised += m->gx;
                o3_place(mark, m, N, mg, 1, 1);
                if (nsel == MAXSEL)
                    break;
            }
        }
        free(cs);
        printf(
            "segment insertion: %lld moves taken of %lld shorter (%lld judged with their zones, %lld next to a move taken, %lld would not give one sequence), %.1fs\n",
            nsel, nshort, njud, ndrop, ncyc, wall() - t1);
        fflush(stdout);
        if (!nsel)
            break;
        i64 nall = nsel;
        for (;;) {
            if (!o3_compose(sel, nsel, NULL, N, ev, ev2, cut, nxt))
                DIE("internal error: segment insertion (moves together)");
            co_run(&q, ev2, N, 0, N - 1, 0, NULL);
            l1 = seq_length(ev2, N);
            if (nsel == 1) {
                if (l0 - l1 != promised)
                    DIE("internal error: segment insertion promised %lld, got %lld", promised, l0 - l1);
                break;
            }
            if ((l0 - l1) * 10 >= promised * 9)
                break;
            printf(
                "segment insertion: %lld moves together give %lld instead of %lld; the first half of them is tried\n",
                nsel, l0 - l1, promised);
            fflush(stdout);
            nsel = (nsel + 1) / 2;
            promised = 0;
            for (i64 k = 0; k < nsel; k++)
                promised += sel[k].gx;
        }
        if (l1 >= l0)
            DIE("internal error: segment insertion made the word longer");
        printf("segment insertion: %lld move%s", nsel, nsel > 1 ? "s" : "");
        if (nsel < nall)
            printf(" of the %lld taken", nall);
        printf(", %lld -> %lld", l0, l1);
        if (l0 - l1 != promised)
            printf(" (%lld promised)", promised);
        printf(":");
        for (i64 k = 0; k < nsel && k < 4; k++) {
            printf(k ? "; " : " ");
            o3_print(&o, &sel[k], N);
            printf(", gain %lld", sel[k].gx);
        }
        printf("%s\n", nsel > 4 ? "; ..." : "");
        memcpy(ev, ev2, (size_t)N * sizeof(Ev));
        total += l0 - l1;
        if (o3plan)
            write_plan(ev, N, o3plan);
        printf("segment insertion: round %d done in %.0fs, %.0fs since the pass began; plan written\n", o3_nround,
               wall() - t0, O3NOW());
        fflush(stdout);
    }
    free(ev2);
    free(batch);
    free(cut);
    free(nxt);
    free(mark);
    free(bm);
    free(sel);
    o3_cofree(&q);
    o3_done(&o);
    return total;
}
/* --or3-old: every candidate is judged; then the shorter ones are taken, the best first: of two moves the one with
   the shorter span must lie inside one of the stretches of the other, 8 events away from its cuts.  The shorter
   spans are made first, so the cuts of the others stay where they were.  The whole sequence is then cut again;
   if it is not as short as promised, only the best move is made. */
static int o3_span_cmp(const void *a, const void *b) {
    const O3M *x = a, *y = b;
    i64 u = x->c[x->k - 1] - x->c[0], v = y->c[y->k - 1] - y->c[0];
    return u < v ? -1 : u > v ? 1 : o3k_cmp(a, b);
}
/* Does the whole of move q lie inside one block of move p, at least mg pieces from its cuts? */
/* the span of q inside one stretch of p */
static int o3_inside(const O3M *q, const O3M *p, i64 N, int mg) {
    i64 a = q->c[0], b = q->c[q->k - 1];
    for (int j = 0; j <= p->k; j++) {
        i64 lo = j ? p->c[j - 1] + 1 : 0, hi = j < p->k ? p->c[j] : N - 1;
        if (a + 1 >= lo + (j ? mg : 0) && b <= hi - (j < p->k ? mg : 0))
            return 1;
    }
    return 0;
}
/* The pass as in the first version (--or3-old): per round the best move, then every further shorter move
   that still fits, each confirmed by the fixed-order pass on the whole sequence. */
static i64 o3_full_old(Ev *ev, i64 N) {
    O3 o;
    o3_init(&o, N);
    CO q;
    memset(&q, 0, sizeof q);
    Ev *ev2 = malloc((size_t)N * sizeof(Ev)), *ev3 = malloc((size_t)N * sizeof(Ev));
    i64 total = 0;
    if (!ev2 || !ev3)
        DIE("out of memory");
    total += o3_first(&q, ev, N);
    for (;;) {
        if (o3_stop()) {
            printf("segment insertion: stopped after %d rounds, %.0fs\n", o3_nround, O3NOW());
            fflush(stdout);
            break;
        }
        double t0 = wall();
        i64 l0 = seq_length(ev, N), l1, g = o3_round(&o, ev), nsel = 0, promised = 0, nshort = 0;
        O3M *mv = o.mv;
        o3_nround++;
        if (g <= 0)
            break;
        while (nshort < o.nc && mv[nshort].gx > 0)
            nshort++;
        for (i64 k = 0; k < nshort; k++) {
            O3M x = mv[k];
            int ok = 1;
            for (i64 z = 0; z < nsel && ok; z++) {
                const O3M *y = &mv[z];
                ok =
                    x.c[x.k - 1] - x.c[0] <= y->c[y->k - 1] - y->c[0] ? o3_inside(&x, y, N, 8) : o3_inside(y, &x, N, 8);
            }
            if (ok) {
                mv[k] = mv[nsel];
                mv[nsel++] = x;
                promised += x.gx;
            }
        }
        O3M first = mv[0];
        qsort(mv, (size_t)nsel, sizeof(O3M), o3_span_cmp);
        memcpy(ev2, ev, (size_t)N * sizeof(Ev));
        for (i64 k = 0; k < nsel; k++) {
            o3_permute(ev2, ev3, N, &mv[k]);
            Ev *t = ev2;
            ev2 = ev3;
            ev3 = t;
        }
        co_run(&q, ev2, N, 0, N - 1, 0, NULL);
        l1 = seq_length(ev2, N);
        if (nsel > 1 && l1 > l0 - promised) { /* they did disturb each other: the best alone */
            printf("segment insertion: %lld moves together give %lld instead of %lld; only the best is made\n", nsel,
                   l0 - l1, promised);
            nsel = 1;
            promised = first.gx;
            mv[0] = first;
            o3_permute(ev, ev2, N, &first);
            co_run(&q, ev2, N, 0, N - 1, 0, NULL);
            l1 = seq_length(ev2, N);
        }
        if (nsel == 1 && l0 - l1 != promised)
            DIE("internal error: segment insertion promised %lld, got %lld", promised, l0 - l1);
        if (l1 >= l0)
            DIE("internal error: segment insertion made the word longer");
        memcpy(ev, ev2, (size_t)N * sizeof(Ev));
        total += l0 - l1;
        printf("segment insertion: %lld move%s of %lld shorter, %lld -> %lld:", nsel, nsel > 1 ? "s" : "", nshort, l0,
               l1);
        for (i64 k = 0; k < nsel && k < 6; k++) {
            printf(k ? "; " : " ");
            o3_print(&o, &mv[k], N);
        }
        printf("%s\n", nsel > 6 ? "; ..." : "");
        if (o3plan)
            write_plan(ev, N, o3plan);
        printf("segment insertion: round %d done in %.0fs, %.0fs since the pass began; plan written\n", o3_nround,
               wall() - t0, O3NOW());
        fflush(stdout);
    }
    free(ev2);
    free(ev3);
    o3_cofree(&q);
    o3_done(&o);
    return total;
}
/* When nothing is shorter: the moves that keep the length lead to other sequences of the same length; these are
   searched breadth first (at most `limit` of them are expanded, each with --bs K if given and a full round of
   segment insertions) until one of them has a shorter neighbour.  Returns the gain; ev changes only then. */
/* of the order only */
static u64 o3_hash(const Ev *ev, i64 N) {
    u64 x = 1469598103934665603ULL;
    for (i64 i = 0; i < N; i++) {
        x = (x ^ ev[i].t) * 1099511628211ULL;
        x = (x ^ (u64)(ev[i].kind == EV_OPT ? 0 : ev[i].kind == EV_SEG ? ev[i].a + 2 : 1)) * 1099511628211ULL;
    }
    return x;
}
/* When no move is shorter: breadth-first search over sequences of equal length, at most `limit` of them,
   until one has a shorter neighbour.  Returns the gain; ev is the new sequence then. */
static i64 o3_plateau(Ev *ev, i64 N, int limit) {
    O3 o;
    o3_init(&o, N);
    o.quiet = 1;
    CO q;
    memset(&q, 0, sizeof q);
    i64 cap = 16384, nq = 0, head = 0, nseen = 0, scap = 1 << 16, l0 = seq_length(ev, N), gain = 0;
    double t0 = wall();
    Ev **Q = malloc((size_t)cap * sizeof(Ev *)), *ev2 = malloc((size_t)N * sizeof(Ev));
    u64 *seen = malloc((size_t)scap * 8);
    if (!Q || !ev2 || !seen)
        DIE("out of memory");
    Q[nq] = malloc((size_t)N * sizeof(Ev));
    if (!Q[nq])
        DIE("out of memory");
    memcpy(Q[nq++], ev, (size_t)N * sizeof(Ev));
    seen[nseen++] = o3_hash(ev, N);
    while (head < nq && head < limit && !gain && !o3_stop()) {
        Ev *cur = Q[head++];
        if (bsK > 1 && head > 1) {
            BS b;
            CO qb;
            bs_init(&b, &qb, bsK);
            b.anyskip = 0;
            Ev *orig = malloc((size_t)N * sizeof(Ev)), *evo = malloc((size_t)N * sizeof(Ev));
            i64 *perm = malloc((size_t)N * 8), *opt = malloc((size_t)N * 8), moved, chg;
            int passes;
            if (!orig || !evo || !perm || !opt)
                DIE("out of memory");
            memcpy(ev2, cur, (size_t)N * sizeof(Ev));
            i64 g = bs_once(&b, ev2, N, orig, evo, perm, opt, &moved, &chg, &passes);
            free(orig);
            free(evo);
            free(perm);
            free(opt);
            bs_free(&b);
            if (g > 0) {
                gain = g;
                memcpy(ev, ev2, (size_t)N * sizeof(Ev));
                printf("sequences of equal length: number %lld has a shorter one within --bs %d: %lld -> %lld\n", head,
                       bsK, l0, l0 - g);
                break;
            }
        }
        i64 g = o3_round(&o, cur), neq = 0, nz = 0;
        o3_nround++;
        if (g > 0) {
            O3M m = o.mv[0];
            o3_permute(cur, ev2, N, &m);
            co_run(&q, ev2, N, 0, N - 1, 0, NULL);
            i64 l1 = seq_length(ev2, N);
            if (l0 - l1 != g)
                DIE("internal error: segment insertion promised %lld, got %lld", g, l0 - l1);
            gain = g;
            memcpy(ev, ev2, (size_t)N * sizeof(Ev));
            printf("sequences of equal length: number %lld has a shorter neighbour (", head);
            o3_print(&o, &m, N);
            printf("): %lld -> %lld\n", l0, l1);
            if (o3plan)
                write_plan(ev, N, o3plan);
            break;
        }
        for (i64 k = 0; k < o.nc && o.mv[k].gx == 0; k++) {
            const O3M *m = &o.mv[k];
            nz++;
            o3_permute(cur, ev2, N, m);
            u64 hv = o3_hash(ev2, N);
            int dup = 0;
            for (i64 z = 0; z < nseen; z++)
                if (seen[z] == hv) {
                    dup = 1;
                    break;
                }
            if (dup)
                continue;
            if (nseen == scap) {
                scap *= 2;
                seen = realloc(seen, (size_t)scap * 8);
                if (!seen)
                    DIE("out of memory");
            }
            seen[nseen++] = hv;
            neq++;
            if (nq < cap) {
                co_run(&q, ev2, N, 0, N - 1, 0, NULL);
                if (seq_length(ev2, N) != l0)
                    DIE("internal error: segment insertion (equal length)");
                Q[nq] = malloc((size_t)N * sizeof(Ev));
                if (!Q[nq])
                    DIE("out of memory");
                memcpy(Q[nq++], ev2, (size_t)N * sizeof(Ev));
            }
        }
        printf(
            "sequences of equal length: number %lld of %lld: %lld candidates, %lld of equal length, %lld new (%.0fs)\n",
            head, nq, o.nc, nz, neq, wall() - t0);
        fflush(stdout);
    }
    printf("sequences of equal length: %lld expanded, %lld found, gain %lld (%.0fs)\n", head, nq, gain, wall() - t0);
    fflush(stdout);
    for (i64 k = 0; k < nq; k++)
        free(Q[k]);
    free(Q);
    free(ev2);
    free(seen);
    o3_cofree(&q);
    o3_done(&o);
    return gain;
}

/* ==================== shared base again: the search, the loader, main (it runs --co, --bs, --or3 before the search) ==================== */
/* ---------- shared best sequence */
static CO G_co;
static i64 G_cow[3];
static double G_cosec; /* in the search: windows, windows with a gain, letters gained; seconds */
static Ev *G_ev;
static i64 G_N, G_len;
static int G_dirty;
static double G_t0, G_last_ck, G_last_log;
static i64 G_it[256];
static double wall(void);

/* One search thread.  Until the time or the iteration limit: choose trails to remove, take them out, put each
   back (greedy order or random order, with or without noise), accept or undo by the annealing rule.  A new best
   sequence goes to the shared copy G_ev under the lock gbest; odd threads adopt the shared best at sync time. */
static void search(Ctx *c, const Ev *init_ev, i64 initN, const char *outplan) {
    rseed(c, seed * 1000003ULL + (u64)c->tid * 7919ULL);
    c->rem = calloc((size_t)NT + 1, 1);
    c->pend = malloc(((size_t)NT + 1) * sizeof(u32));
    ctx_load(c, init_ev, initN);
    c->cur = ctx_length(c);
    c->best_len = c->cur;
    double tf = NTHR > 1 ? 0.5 + (double)c->tid / (NTHR - 1) : 1.0, last_sync = wall();
    int runcap = 2 * kmax + 2; /* a run longer than this is not removed as a whole */
    Node *nd;
    CLog clog;
    memset(&clog, 0, sizeof clog);
    while ((maxit < 0 || c->it < maxit) && wall() - G_t0 < tlimit) {
        c->it++;
        if (c->H.n > c->H.cap - 40000 || c->nn > c->ncap - 4000) {
            i64 m = ctx_export(c, c->tmp);
            ctx_load(c, c->tmp, m);
        }
        if (coit > 0 && (c->it + coit * c->tid / NTHR) % coit ==
                            0) { /* cluster optimisation of the whole current sequence; the threads take turns */
            i64 m = ctx_export(c, c->tmp), g;
            int chg;
            double t1 = wall();
#pragma omp critical(co)
            g = co_run(&G_co, c->tmp, m, 0, m - 1, 0, &chg);
            clog.st[0]++;
            clog.st[1] += g > 0;
            clog.st[2] += g > 0 ? g : 0;
            clog.sec += wall() - t1;
            if (g > 0) {
                ctx_load(c, c->tmp, m);
                c->cur -= g;
                if (c->cur < c->best_len) {
                    c->best_len = c->cur;
#pragma omp critical(gbest)
                    if (c->cur < G_len) {
                        printf("t=%.0fs: best %lld -> %lld (thread %d, it %lld, cluster optimisation, %d openings)\n",
                               wall() - G_t0, G_len, c->cur, c->tid, c->it, chg);
                        fflush(stdout);
                        G_N = ctx_export(c, G_ev);
                        G_len = c->cur;
                        G_dirty = 1;
                    }
                }
            }
        }
        nd = c->nd;
        double frac = (wall() - G_t0) / tlimit, temp = tf * T0 * (1 - frac) + 0.05;
        int *order = c->order, *dj = c->dj, *cand = c->cand, *rs_ = c->rs_, *re_ = c->re_, *rid = c->rid, *rel = c->rel;
        i64 N = 0;
        for (int id = c->first; id >= 0; id = nd[id].next)
            order[N++] = id;
#define EVT(i) (nd[order[i]].v)
        i64 ncand = 0;
        for (i64 i = 0; i + 1 < N; i++) {
            dj[i] = dist(EVT(i).e, EVT(i + 1).s);
            if (dj[i] >= 2)
                cand[ncand++] = (int)i;
        }
        int k = (int)rndint(c, 1, kmax);
        i64 nrem = 0;
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
            int nrun = 0;
            rid[0] = 0;
            for (i64 i = 1; i < N; i++) {
                if (dj[i - 1] >= 2)
                    nrun++;
                rid[i] = nrun;
            }
            nrun++;
            for (i64 i = 0; i < N; i++) {
                if (i == 0 || rid[i] != rid[i - 1])
                    rs_[rid[i]] = (int)i;
                re_[rid[i]] = (int)i;
            }
            int X = -1;
            if (rndu(c) < 0.7) {
                for (int tries = 0; tries < 50; tries++) {
                    int r = (int)rndn(c, nrun);
                    if (re_[r] - rs_[r] + 1 <= 5) {
                        X = r;
                        break;
                    }
                }
            }
            if (X < 0)
                X = (int)rndn(c, nrun);
            i64 xlen = re_[X] - rs_[X] + 1;
            if (xlen > runcap) { /* long run: only a window of it */
                i64 lo = rs_[X] + rndn(c, xlen - k + 1 > 0 ? xlen - k + 1 : 1);
                for (i64 i = lo; i <= re_[X] && i < lo + k; i++)
                    REMOVE(EVT(i).t);
            } else {
                i64 nopt = 0;
                for (int i = rs_[X]; i <= re_[X]; i++)
                    nopt += TR[EVT(i).t].ohi - TR[EVT(i).t].olo;
                int nrel = 0;
                if (nopt <= 600000) {
                    h_reset(&c->RELT, nopt * 4 + 16);
                    for (int i = rs_[X]; i <= re_[X]; i++)
                        for (i64 o = TR[EVT(i).t].olo; o < TR[EVT(i).t].ohi; o++) {
                            u64 S = oS_t(&TR[EVT(i).t], o), E = oE_t(&TR[EVT(i).t], o);
                            h_add(&c->RELT, HKEY(S, 0, 4), 0);
                            h_add(&c->RELT, HKEY(S >> 4, 1, 4), 0);
                            h_add(&c->RELT, HKEY(E, 0, 5), 0);
                            h_add(&c->RELT, HKEY(E & HMASK[h - 1], 1, 5), 0);
                        }
                    for (int r = 0; r < nrun; r++) {
                        if (r == X || re_[r] - rs_[r] + 1 > runcap)
                            continue;
                        u64 e_end = EVT(re_[r]).e, s_st = EVT(rs_[r]).s;
                        if (h_get(&c->RELT, HKEY(e_end, 0, 4)) >= 0 ||
                            h_get(&c->RELT, HKEY(e_end & HMASK[h - 1], 1, 4)) >= 0 ||
                            h_get(&c->RELT, HKEY(s_st, 0, 5)) >= 0 || h_get(&c->RELT, HKEY(s_st >> 4, 1, 5)) >= 0)
                            rel[nrel++] = r;
                    }
                }
                for (int i = rs_[X]; i <= re_[X]; i++)
                    REMOVE(EVT(i).t);
                int want = (int)rndint(c, 1, 2);
                for (int q = 0; q < want && nrel > 0; q++) {
                    int z = (int)rndn(c, nrel), r = rel[z];
                    rel[z] = rel[--nrel];
                    for (int i = rs_[r]; i <= re_[r]; i++)
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
        /* destroy */
        c->nremlog = c->ninslog = 0;
        c->relabeled = 0;
        c->nskp = 0;
        for (i64 i = 0; i < N; i++) {
            int id = order[i];
            if (c->rem[nd[id].v.t]) {
                node_unlink(c, id);
                c->remlog[c->nremlog++] = id;
            } else if (nd[id].v.skip >= 0)
                skp_add(c, nd[id].v.skip);
        }
        for (i64 q = 0; q < nrem; q++)
            c->rem[c->pend[q]] = 0;
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
            while (np > 0) {
                i64 pick = 0;
                Ins bi = best_insertion(c, c->pend[0], noise);
                if (greedy) {
                    double br = rndu(c);
                    for (i64 q = 1; q < np; q++) {
                        Ins x = best_insertion(c, c->pend[q], noise);
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
                    node_insert_after(c, c->nd[sp.i].prev, &e1);
                    node_insert_after(c, sp.jm, &e2);
                } else {
                    Ev x = make_event(bi.opt);
                    node_insert_after(c, bi.after, &x);
                    if (x.skip >= 0)
                        skp_add(c, x.skip);
                }
                c->pend[pick] = c->pend[--np];
            }
            nl = ctx_length(c);
            i64 d = nl - c->cur;
            accept = d <= 0 || rndu(c) < exp(-(double)d / temp);
        }
        if (accept) {
            c->cur = nl;
            c->acc++;
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
            for (int q = c->ninslog - 1; q >= 0; q--)
                node_unlink(c, c->inslog[q]);
            for (int q = c->nremlog - 1; q >= 0; q--)
                node_relink(c, c->remlog[q]);
            if (c->relabeled)
                relabel(c);
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
        }
    }
#pragma omp critical(gbest)
    {
        G_it[c->tid] = c->it;
        for (int k = 0; k < 3; k++)
            G_cow[k] += clog.st[k];
        G_cosec += clog.sec;
    }
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
        DIE("usage: segins BASE.txt OUT.txt --plan-in PLAN --time 0 --threads T --or3 C --or3-slack S   (see the comment at the top of segins.c)");
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
        else if (!strcmp(argv[a], "--coit") && a + 1 < argc)
            coit = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--co"))
            co_first = 1;
        else if (!strcmp(argv[a], "--co-skip"))
            co_first = co_skip = 1;
        else if (!strcmp(argv[a], "--bs") && a + 1 < argc)
            bsK = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--bs-test") && a + 1 < argc)
            bs_ntest = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3") && a + 1 < argc)
            o3cuts = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-slack") && a + 1 < argc)
            o3slack = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-v") && a + 1 < argc)
            o3th = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-plateau") && a + 1 < argc)
            o3plat = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-dry"))
            o3dry = 1;
        else if (!strcmp(argv[a], "--or3-old"))
            o3old = 1;
        else if (!strcmp(argv[a], "--or3-rounds") && a + 1 < argc)
            o3rounds = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-sec") && a + 1 < argc)
            o3sec = atof(argv[++a]);
        else if (!strcmp(argv[a], "--or3-stop") && a + 1 < argc)
            o3stopfile = argv[++a];
        else if (!strcmp(argv[a], "--or3-maxcand") && a + 1 < argc)
            o3maxcand = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--or3-maxlay") && a + 1 < argc)
            o3maxlay = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--or3-margin") && a + 1 < argc)
            o3margin = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-dip") && a + 1 < argc)
            o3dip = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-x") && a + 1 < argc)
            o3xt = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-zone") && a + 1 < argc)
            o3zone = atoi(argv[++a]);
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
    if (bsK && bs_ntest)
        bs_test(ev, N, bsK, bs_ntest);
    if (bsK)
        bs_full(ev, N, bsK);
    if (o3cuts > 0) {
        static char pp[4096];
        snprintf(pp, sizeof pp, "%s.plan", argv[2]);
        o3plan = pp;
        o3_t0 = wall();
        for (;;) {
            i64 g =
                o3old
                    ? o3_full_old(ev, N)
                    : o3_full(ev, N); /* until nothing is shorter, or stopped; the plan is written after every round */
            if (o3_stop())
                break;
            if (g > 0 && bsK && bs_full(ev, N, bsK) > 0) {
                write_plan(ev, N, pp);
                continue;
            }
            if (o3plat > 0 && o3_plateau(ev, N, o3plat) > 0)
                continue;
            break;
        }
    }
    /* ---------- destroy / repair search */
    char outplan[4096];
    snprintf(outplan, sizeof outplan, "%s.plan", argv[2]);
    G_ev = malloc((size_t)(4 * N + 65536) * sizeof(Ev));
    memcpy(G_ev, ev, (size_t)N * sizeof(Ev));
    G_N = N;
    G_len = seq_length(ev, N);
    G_t0 = G_last_ck = G_last_log = wall();
    if (tlimit > 0 && maxit != 0) { /* with --time 0 no thread loads the sequence */
#pragma omp parallel num_threads(NTHR)
        {
            Ctx *c = calloc(1, sizeof(Ctx));
            c->tid = omp_get_thread_num();
            search(c, ev, N, outplan);
        }
    }
    i64 tot = 0;
    for (int q = 0; q < NTHR; q++)
        tot += G_it[q];
    printf("LNS done: %lld iterations on %d threads, best %lld\n", tot, NTHR, G_len);
    fflush(stdout);
    if (coit > 0)
        printf("cluster optimisation in the search: %lld passes, %lld with a gain, %lld letters, %.1f thread-seconds\n",
               G_cow[0], G_cow[1], G_cow[2], G_cosec);
    if (tot > 0 && (co_first || coit > 0)) {
        co_full(G_ev, G_N);
        G_len = seq_length(G_ev, G_N);
    }
    if (tot > 0 && bsK) {
        bs_full(G_ev, G_N, bsK);
        G_len = seq_length(G_ev, G_N);
    }
    print_stats(G_ev, G_N);
    write_plan(G_ev, G_N, outplan);
    write_word(G_ev, G_N, argv[2], G_len);
    printf("wrote %s length %lld (%.0fs)\n", argv[2], G_len, wall() - t00);
    return 0;
}
