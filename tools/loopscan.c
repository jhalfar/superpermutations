/* loopscan.c - loop moves: a block of consecutive pieces is closed into a loop and hung into another closed
   trail, which is then written in two segments.  An exact scan for all such moves, and rounds that make them.

   Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.  The closed trails are
   those of Jay Pantone's construction (github.com/jaypantone/superperm-upper-43-80).

   Why this is allowed.  The trails and joins of a word form a balanced directed graph, and any connected balanced
   graph spells a word (section 5 of Pantone's summary).  So a trail does not have to be written in one piece: it
   may be cut at a second place, with other pieces written between its two segments.

   Model, as in trailsearch.c.  The word is a sequence of events; an event writes letters st .. st+l-1 of the cyclic
   word of a closed trail (a whole trail from one cut, or a segment of it); it starts and ends with a permutation
   window; consecutive events are joined with the largest overlap of their h-words, h = n - 3:
       L = h + sum R_T + sum over ports (3 - g) + sum over joins d(E, S).
   A "port" is what this file calls a cut that is in use: a cut between two consecutive windows of a trail, at
   positions a and b = a + g (g = 1, 2, 3): the event before it ends with the window at a (E = h-word at a + 3), the
   event after it starts with the window at b (S = h-word at b; E lies 3 - g shifts after S).  Splitting an event
   there adds n - g letters and one join: 3 - g plus the two new joins.  A trail written in m events has m ports;
   every window lies whole in one event, because no window starts between a and b.

   Moves.  Cut a block Y = y_1 .. y_m of consecutive events out of the sequence (p, q: its neighbours) and close it
   into a loop (the closing join always exists; it costs d(E_ym, S_y1) <= h):
       f(Y) = d(E_ym, S_y1) + d(E_p, S_q) - d(E_p, S_y1) - d(E_ym, S_q).
   The rest of the sequence (M) and the loop (C) are joined again in one of four ways:
     A  a new port w inside an event H of M, placed on a join u -> v of C (A.close: the closing join y_m -> y_1;
        A.inner: a join inside Y, the block is then rotated):
            delta = f(Y) + d(E_u, S_w) + (3 - g_w) + d(E_w, S_v) - d(E_u, S_v)
        sequence: .. H[.. w], v .. u (cyclic), H[w ..] ..
     B  a new port w inside an event H = y_r of C, placed on a join x -> y of M (B.arc: any join outside Y; B.pq: the
        new join p -> q, i.e. the block is rotated in place around H):
            delta = f(Y) + d(E_x, S_w) + (3 - g_w) + d(E_w, S_y) - d(E_x, S_y)
        sequence: .. x, H[w ..], y_r+1 .. y_m, y_1 .. y_r-1, H[.. w], y ..
     C  new ports at the same gap-3 vertex (equal h-word) of an event of M and an event of C:   delta = f(Y)
     D  no new port: the loop is opened at one of its joins and put into a join of M (D.block: opened at the closing
        join, the plain block move; D.rot: at another join, the block is rotated; D.rot.pq: rotated in place).
   A and B are the loop moves proper (host outside / host inside the block).  The attachment term
   d(E_u, S_w) + (3 - g_w) + d(E_w, S_v) - d(E_u, S_v) is never negative; it is 0 exactly when the letters of the
   trail from S_w to E_w lie on the shortest connector of the join, and at least h - d(E_u, S_v) otherwise (h-words
   of different letters have one overlap at most, any other walk between them has h steps or more).  So a loop move
   pays when a join already passes through a cut of another trail.  That never happens in the n = 11 words I looked
   at; it happens a few times at n = 12 and often enough at n = 13 to give 34 letters.

   What is scanned: A.close and B.pq for blocks of any length (the exchange of two joins and one cut); A.inner,
   B.arc, C, D for blocks of up to --lmax events and (if the sequence has at most 20000 events) for every longer
   block with f <= threshold.  Found: every move in which one of the two new joins at the port costs at most K
   (--klev K; 4 by default, so every attachment of cost <= 9 + (3 - g)).  --brute checks the scan against plain
   enumeration on small words (n = 9: identical lists).
   Events whose cut drops a duplicated permutation are not used as hosts unless --skiphost is given (the S lines of
   a plan cannot say which occurrence is dropped; such a plan must not be searched from).

   Build:  gcc -O2 -mpopcnt -fopenmp -o loopscan loopscan.c
   Use:    loopscan BASE.txt --plan PLAN --only PABD --nogap1 --threads T --quiet --greedy --neutral --nbatch 16
                    --maxrounds 40 --planout OUT.plan --out OUT.txt

   Rounds (--greedy).  Scan; take every improving move of the list, best first (ties: shorter block first); apply
   each one that is still a move of the sequence as it is now and still shortens it (a move is kept as identities of
   events, resolved again and its delta computed again from the current sequence, and the length is checked after
   every single move); scan again; stop when a scan lists no improving move or after --maxrounds R scans.
     --single       one move per round
     --planout F    after every round that changed the sequence the plan is written to F.partial and renamed to F
                    (also at the end); a kill loses one round at most
     --out W        the word (and W.plan) at the end only, written event by event
     --neutral      when no improving move is left: batches of up to M (--nbatch, default 16) moves of kinds A, B, C
                    with delta 0 on disjoint positions are applied on trial and the result is scanned; if improving
                    moves appear, the batch is cut down to the neutral moves they touch (one more scan), the
                    improving moves are applied and the normal rounds go on; otherwise the batch is dropped and the
                    next one is tried.  Every scan counts as a round for --maxrounds
     --quiet        one line per round ("round R: length A -> B ...") and nothing else
     --stress       test: applies every listed move (delta <= --thr D) that is still a move, whatever its sign
   Scan options.
     --plan PLAN    the sequence to scan (without it: the pieces of BASE as they are)
     --only ..      P: A.close and B.pq, A: A.inner, B: B.arc, C, D (I use PABD)
     --nogap1       no port inside a 1-cycle (the scan is about five times cheaper)
     --lmax L       longest block for A.inner, B.arc, C, D (default 2h, at most 64);  --nolong  no longer blocks
     --klev K       see above;  --thr D  list moves with delta <= D (default 0);  --threads T (default 2)
     --wide         joins may overlap in up to n - 1 letters (such joins cost -1 or -2); if one is used, the written
                    plan rebuilds a longer word with the other tools: convert the word with word2plan --rebase
   Looking at single moves (without --greedy): --top M prints the M best, --list FILE writes all, --apply IDX makes
   move IDX of the sorted list, --verify M applies M of the listed moves one at a time and checks length and
   coverage, --probe M applies each of M neutral moves and scans again, --walk STEPS applies the best move or, when
   nothing improves, a random neutral one (--seed S), --watch lists the blocks that can be detached with a gain,
   --dups says where the duplicated permutations lie, --noD leaves out the moves without a port.

   Memory and time (measured).  The base word plus about 100 bytes per event.  n = 11: 9 seconds per scan with all
   kinds of ports, and no improving move of kinds A, B, C on any n = 11 word I tried.  n = 12: 2.6 seconds per scan.
   n = 13: 6.3 GB, about 37 seconds per scan on 8 threads; 6,747,917,498 to 6,747,917,464 took 40 rounds and 27
   minutes.

   Words: "opening" = cut, "gap" = weight of the step that is cut, "event" = one piece as written, "block" = a run
   of consecutive events.  The loader is a copy of the one in trailsearch.c; this file has no search.

   Where the parts start.  Each part begins with a comment line of dashes: trails and the loader (as in
   trailsearch.c); events; hash multimap; options (the table of cuts); the sequence with what the scan needs; moves
   (the scan itself); --brute; applying a move; many moves from one scan (--greedy).  main is at the end. */
#if !defined(_WIN32)
#define _FILE_OFFSET_BITS 64
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
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
#define DIE(...)                      \
    do {                              \
        fprintf(stderr, __VA_ARGS__); \
        fprintf(stderr, "\n");        \
        exit(1);                      \
    } while (0)

static u64 HMASK[17], fact[17];
static int
    OVMAX; /* largest overlap of two events that a join may use: h (the model of trailsearch) or n - 1 (--wide) */
/* e: the last window of an event, s: the first window of the next one (n letters each, 4 bits per letter).
   cost of the join = h - largest k <= OVMAX with suffix_k(e) == prefix_k(s); below 0 for a tight join */
static inline int dist(u64 e, u64 s) {
    for (int k = OVMAX; k >= 1; k--)
        if ((e & HMASK[k]) == (s >> (4 * (n - k))))
            return h - k;
    return h;
}

/* ---------- trails (as in trailsearch.c) */
typedef struct {
    unsigned char *c;
    i64 R;
    int fixed;
} Trail;
static Trail *TR;
static i64 NT;
static i64 *PS, *PL, *POFF, *trail_of_piece;
static i64 NP; /* pieces of the base word; POFF: offset in the trail */
static inline u64 hw_lin(const unsigned char *p) {
    u64 v = 0;
    for (int k = 0; k < h; k++)
        v = (v << 4) | p[k];
    return v;
}
static inline u64 win_lin(const unsigned char *p) {
    u64 v = 0;
    for (int k = 0; k < n; k++)
        v = (v << 4) | p[k];
    return v;
}
/* The window (n letters packed 4 bits each) at cyclic position pos of trail t. */
static inline u64 win_cyc(const Trail *t, i64 pos) {
    i64 R = t->R;
    pos %= R;
    if (pos < 0)
        pos += R;
    if (pos + n <= R)
        return win_lin(t->c + pos);
    u64 v = 0;
    for (int k = 0; k < n; k++)
        v = (v << 4) | t->c[(pos + k) % R];
    return v;
}
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
/* Rank of the permutation window that starts at cyclic position pos of trail t (pos may be negative or beyond R). */
static inline u64 rank_cyc(const Trail *t, i64 pos) {
    u64 r = 0;
    int used = 0;
    i64 R = t->R;
    pos %= R;
    if (pos < 0)
        pos += R;
    for (int k = 0; k < n; k++) {
        int c = t->c[(pos + k) % R];
        r += (u64)(c - __builtin_popcount(used & ((1 << c) - 1))) * fact[n - 1 - k];
        used |= 1 << c;
    }
    return r;
}
/* 1 if the n letters at cyclic position pos of trail T are a permutation. */
static int is_win(const Trail *T, i64 pos) {
    int used = 0;
    i64 R = T->R;
    pos %= R;
    if (pos < 0)
        pos += R;
    for (int k = 0; k < n; k++) {
        used |= 1 << T->c[pos];
        if (++pos == R)
            pos = 0;
    }
    return used == (1 << n) - 1;
}
/* Reads a word file into memory as numbers 0 .. 15 (alphabet 0-9, A-F); a trailing line end is dropped.
   Stops with a message on any other symbol.  16 spare bytes follow the word. */
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
    if (T->fixed)
        return 0;
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

/* ---------- events */
enum { EV_PIECE, EV_OPT, EV_SEG };
/* s, e: first and last window; id: identity (see multi_apply) */
typedef struct {
    int kind;
    u32 t;
    int g, g1;
    u64 s, e;
    i64 l, st, pk, skip;
    int id;
} Ev;
static int next_id;
/* letters st .. st+l-1 of the cyclic word of trail t.  EV_PIECE: piece pk of the base word.  EV_OPT: the whole trail
   from the cut (st, g, g1).  EV_SEG: any other stretch.  skip: rank of the skipped duplicate window or -1 */
static Ev piece_event(i64 k) {
    Ev x;
    memset(&x, 0, sizeof x);
    x.kind = EV_PIECE;
    x.t = (u32)trail_of_piece[k];
    x.s = win_lin(W + PS[k]);
    x.e = win_lin(W + PS[k] + PL[k] - n);
    x.l = PL[k];
    x.st = POFF[k];
    x.pk = k;
    x.skip = -1;
    return x;
}
/* The event for trail t written once from the cut at offset st with gap g (g1 > 0: an occurrence is dropped). */
static Ev opt_event(u32 t, i64 st, int g, int g1) {
    const Trail *T = &TR[t];
    Ev x;
    memset(&x, 0, sizeof x);
    x.kind = EV_OPT;
    x.t = t;
    x.g = g;
    x.g1 = g1;
    x.st = st;
    x.pk = -1;
    x.s = win_cyc(T, st);
    x.e = win_cyc(T, st - g);
    x.l = T->R + h + 3 - g;
    x.skip = g1 ? (i64)rank_cyc(T, st - g + g1) : -1;
    return x;
}
/* The event for l letters of trail t from offset st (a segment; it must start and end with a whole window). */
static Ev seg_event(u32 t, i64 st, i64 l) {
    const Trail *T = &TR[t];
    Ev x;
    memset(&x, 0, sizeof x);
    x.kind = EV_SEG;
    x.t = t;
    x.st = ((st % T->R) + T->R) % T->R;
    x.l = l;
    x.pk = -1;
    x.skip = -1;
    x.s = win_cyc(T, st);
    x.e = win_cyc(T, st + l - n);
    return x;
}
static inline unsigned char ev_letter(const Ev *x, i64 r) {
    if (x->kind == EV_PIECE)
        return W[PS[x->pk] + r];
    const Trail *t = &TR[x->t];
    return t->c[(x->st + r) % t->R];
}
/* Length of the word of a sequence: the letters of all events minus the overlaps at the joins. */
static i64 seq_length(const Ev *ev, i64 N) {
    i64 len = 0;
    for (i64 i = 0; i < N; i++)
        len += ev[i].l;
    for (i64 i = 0; i + 1 < N; i++)
        len -= h - dist(ev[i].e, ev[i + 1].s);
    return len;
}
/* letters as numbers */
static unsigned char *build_word(const Ev *ev, i64 N, i64 *len) {
    i64 total = seq_length(ev, N), o = 0;
    unsigned char *out = malloc((size_t)total + 16);
    if (!out)
        DIE("out of memory");
    u64 tail = 0;
    for (i64 i = 0; i < N; i++) {
        const Ev *x = &ev[i];
        i64 skip = i ? h - dist(tail, x->s) : 0;
        for (i64 r = skip; r < x->l; r++)
            out[o++] = ev_letter(x, r);
        tail = x->e;
    }
    if (o != total)
        DIE("internal error: wrote %lld letters, model says %lld", o, total);
    *len = total;
    return out;
}
/* Writes the sequence as a plan: a head line, then one line per event (P, O or S), with LF line ends. */
static void write_plan(const Ev *ev, i64 N, const char *path) {
    FILE *f = fopen(path, "wb");
    if (!f)
        DIE("cannot write %s", path);
    fprintf(f, "TRAILSEARCH-PLAN %d %lld %lld\n", n, L, N);
    for (i64 i = 0; i < N; i++) {
        const Ev *x = &ev[i];
        if (x->kind == EV_PIECE)
            fprintf(f, "P %lld\n", x->pk);
        else if (x->kind == EV_OPT)
            fprintf(f, "O %u %lld %d %d\n", x->t, x->st, x->g, x->g1);
        else
            fprintf(f, "S %u %lld %lld\n", x->t, x->st, x->l);
    }
    fclose(f);
}
/* does the word of the sequence hold every permutation?  returns the number of missing ones */
static i64 missing_perms(const Ev *ev, i64 N) {
    i64 len;
    unsigned char *w = build_word(ev, N, &len);
    u64 NF = fact[n];
    u64 *seen = calloc((size_t)(NF >> 6) + 1, 8);
    if (!seen)
        DIE("out of memory");
    int cnt[16] = {0}, distinct = 0;
    u64 have = 0;
    for (i64 i = 0; i < len; i++) {
        if (cnt[w[i]]++ == 0)
            distinct++;
        if (i >= n) {
            if (--cnt[w[i - n]] == 0)
                distinct--;
        }
        if (i >= n - 1 && distinct == n) {
            u64 r = rank_lin(w + i - n + 1);
            if (!((seen[r >> 6] >> (r & 63)) & 1)) {
                seen[r >> 6] |= 1ULL << (r & 63);
                have++;
            }
        }
    }
    free(seen);
    free(w);
    return (i64)(NF - have);
}

/* ---------- hash multimap: key -> list of positions */
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
#define HKEY(word, j, kind) (((u64)(word) << 8) | ((u64)(j) << 4) | (u64)(kind))
/* An empty multimap with room for the given number of entries. */
static void h_init(HTab *H, i64 entries) {
    u64 need = 1024;
    while (need < (u64)entries * 2 + 16)
        need <<= 1;
    H->t = malloc(need * sizeof(Slot));
    H->mask = need - 1;
    for (u64 i = 0; i <= H->mask; i++) {
        H->t[i].head = -1;
        H->t[i].key = ~0ULL;
    }
    H->cap = entries + 16;
    H->next = malloc(H->cap * sizeof(int));
    H->val = malloc(H->cap * sizeof(int));
    H->n = 0;
}
static void h_free(HTab *H) {
    free(H->t);
    free(H->next);
    free(H->val);
    memset(H, 0, sizeof *H);
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

/* ---------- options */
static int dupstat = 0; /* --dups: where the duplicated windows lie */
static int watch = 0;   /* --watch: only the blocks that can be detached with a gain (f < 0); see watch_report */
static int longblocks = 1, wide = 0, NLEV,
           MINW; /* NLEV: overlaps OVMAX .. h - KL are indexed; MINW: smallest cost of a join */
static int LMAX = 0, KL = 4, use_gap1 = 1, thr = 0, NTHR = 2, skiphost = 0, useD = 1, quiet = 0;
static char only[32] = "";
#define BIG 20000

/* ---------- the sequence with what the scan needs */
typedef struct {
    int N;
    Ev *ev;
    u64 *S, *E;
    int *J;           /* J[i]: cost of the join i -> i+1 */
    int *thead, *tnx; /* events of every trail */
    short *F, *mfa,
        *mfn; /* F[i * LMAX + m - 1] = f(block i .. i+m-1); minima over the blocks holding an arc / a node (m >= 2) */
    struct LBlk {
        int i, j, f;
    } *LB;
    int nLB, LBmin;           /* blocks longer than LMAX with f <= thr (only if N is small enough to try them all) */
    int *o0, *nb0, *o1, *nb1; /* see seq_neighbours */
    int *byJ,
        nJ[20]; /* the joins -1 .. N-1 (tails; -1 and N-1: the ends, cost 0) by falling cost; nJ[c]: how many cost >= c */
    HTab H;
    u64 *bf, bfmask;
    i64 len;
} Seq;
#define BFH(key) (((u64)(key) * 0x9E3779B97F4A7C15ULL) >> 24)
static inline int Jc(const Seq *q, int x) {
    return (x < 0 || x + 1 >= q->N) ? 0 : q->J[x];
}
static inline int dpq(const Seq *q, int i, int j) {
    return (i - 1 < 0 || j + 1 >= q->N) ? 0 : dist(q->E[i - 1], q->S[j + 1]);
}
static inline int rem_(const Seq *q, int i, int j) {
    return dpq(q, i, j) - Jc(q, i - 1) - Jc(q, j);
}
static inline int Fb(const Seq *q, int i, int j) {
    return q->F[(i64)i * LMAX + (j - i)];
}
/* Frees everything a Seq holds. */
static void seq_free(Seq *q) {
    free(q->o0);
    free(q->nb0);
    free(q->o1);
    free(q->nb1);
    free(q->LB);
    free(q->byJ);
    free(q->S);
    free(q->E);
    free(q->J);
    free(q->thead);
    free(q->tnx);
    free(q->F);
    free(q->mfa);
    free(q->mfn);
    free(q->bf);
    h_free(&q->H);
}
/* Sets up the scan structures of a sequence: start and end windows of the events, join costs, the events of
   every trail, and the table F of the closing costs f of all blocks of up to LMAX events. */
static void seq_make0(Seq *q, Ev *ev, int N) {
    memset(q, 0, sizeof *q);
    q->N = N;
    q->ev = ev;
    q->S = malloc((size_t)N * 8);
    q->E = malloc((size_t)N * 8);
    q->J = malloc((size_t)N * sizeof(int));
    q->thead = malloc(((size_t)NT + 1) * sizeof(int));
    q->tnx = malloc((size_t)N * sizeof(int));
    memset(q->thead, 0xff, ((size_t)NT + 1) * sizeof(int));
    for (int i = 0; i < N; i++) {
        q->S[i] = ev[i].s;
        q->E[i] = ev[i].e;
        q->tnx[i] = q->thead[ev[i].t];
        q->thead[ev[i].t] = i;
    }
    for (int i = 0; i < N; i++)
        q->J[i] = i + 1 < N ? dist(q->E[i], q->S[i + 1]) : 0;
    q->len = seq_length(ev, N);
    q->byJ = malloc(((size_t)N + 2) * sizeof(int));
    {
        int k = 0;
        memset(q->nJ, 0, sizeof q->nJ); /* nJ[c + 2]: joins of cost >= c */
        for (int c = h; c >= -2; c--) {
            for (int x = -1; x < N; x++)
                if (Jc(q, x) == c)
                    q->byJ[k++] = x;
            q->nJ[c + 2] = k;
        }
    }
    q->F = malloc((size_t)N * LMAX * sizeof(short));
    q->mfa = malloc((size_t)N * sizeof(short));
    q->mfn = malloc((size_t)N * sizeof(short));
    for (int i = 0; i < N; i++) {
        q->mfa[i] = q->mfn[i] = BIG;
    }
    for (int i = 0; i < N; i++)
        for (int m = 1; m <= LMAX; m++) {
            int j = i + m - 1, f = BIG;
            if (j < N && !(i == 0 && j == N - 1))
                f = dist(q->E[j], q->S[i]) + rem_(q, i, j);
            q->F[(i64)i * LMAX + m - 1] = (short)f;
            if (f < BIG && m >= 2) {
                for (int x = i; x <= j; x++)
                    if (f < q->mfn[x])
                        q->mfn[x] = (short)f;
                for (int x = i; x < j; x++)
                    if (f < q->mfa[x])
                        q->mfa[x] = (short)f;
            }
        }
    q->LBmin = BIG;
    if (N <= 20000 && longblocks) {
        int cap = 0;
        for (int i = 0; i < N; i++)
            for (int j = i + LMAX; j < N; j++) {
                if (i == 0 && j == N - 1)
                    continue;
                int f = dist(q->E[j], q->S[i]) + rem_(q, i, j);
                if (f > thr || (watch && f >= 0))
                    continue;
                if (q->nLB == cap) {
                    cap = cap ? cap * 2 : 256;
                    q->LB = realloc(q->LB, (size_t)cap * sizeof(struct LBlk));
                }
                q->LB[q->nLB].i = i;
                q->LB[q->nLB].j = j;
                q->LB[q->nLB].f = f;
                q->nLB++;
                if (f < q->LBmin)
                    q->LBmin = f;
            }
    }
    i64 ent = (i64)N * 2 * NLEV;
    h_init(&q->H, ent);
    u64 bits = 1 << 16;
    while (bits < (u64)ent * 32)
        bits <<= 1;
    q->bf = calloc(bits / 64, 8);
    q->bfmask = bits - 1;
    for (int i = 0; i < N; i++)
        for (int j = 0; j < NLEV; j++) {
            int k = OVMAX - j;
            u64 k0 = HKEY(q->E[i] & HMASK[k], k, 0), k1 = HKEY(q->S[i] >> (4 * (n - k)), k, 1), b;
            h_add(&q->H, k0, i);
            h_add(&q->H, k1, i);
            b = BFH(k0) & q->bfmask;
            q->bf[b >> 6] |= 1ULL << (b & 63);
            b = BFH(k1) & q->bfmask;
            q->bf[b >> 6] |= 1ULL << (b & 63);
        }
}

/* ---------- moves */
enum { M_AC, M_AI, M_BO, M_BN, M_C, M_DI, M_DN, M_DC, M_NT };
static const char *MNAME[M_NT] = {"A.close", "A.inner", "B.arc", "B.pq", "C.vertex", "D.rot", "D.rot.pq", "D.block"};
static const char *MDESC[M_NT] = {
    "host outside, port on the closing arc of the block",
    "host outside, port on a join inside the block (block rotated)",
    "host inside, second port on a join elsewhere",
    "host inside, second port on the new join p -> q (block rotated in place around the host)",
    "two new ports at a shared gap-3 vertex",
    "no port: block rotated and moved into another join",
    "no port: block rotated in place",
    "no port: plain block move"};
typedef struct {
    short delta;
    unsigned char type, g, g2;
    int i, j, hp, hp2, cu, mx;
    i64 a, a2;
} Move;
/* block i .. j; hp: host event (A, C: in M; B: in C) cut after the window at a (gap g); hp2, a2, g2: second host (C);
   cu: tail of the arc of C that is cut open (j: the closing arc); mx: tail of the arc of M that takes the loop (i-1: p -> q) */
typedef struct {
    Move *m;
    i64 n, cap;
    i64 cnt[M_NT][8];
    i64 over;
} ML;
static i64 ML_MAX = 4000000;
/* Adds a move to the list (and to the counts by kind and delta); beyond ML_MAX moves only the counts grow. */
static void ml_add(ML *ml, const Move *mv) {
    int d = mv->delta < -3 ? -3 : mv->delta;
    if (d <= 4)
        ml->cnt[mv->type][d + 3]++;
    if (ml->n >= ML_MAX) {
        ml->over++;
        return;
    }
    if (ml->n == ml->cap) {
        ml->cap = ml->cap ? ml->cap * 2 : 1024;
        ml->m = realloc(ml->m, (size_t)ml->cap * sizeof(Move));
        if (!ml->m)
            DIE("out of memory");
    }
    ml->m[ml->n++] = *mv;
}
/* Order of the move list: by delta, then kind, then the block and the cut. */
/* clang-format off */
static int mv_cmp(const void *x, const void *y) {
    const Move *a = x, *b = y;
#define C_(f) if (a->f != b->f) return a->f < b->f ? -1 : 1;
    C_(delta) C_(type) C_(i) C_(j) C_(hp) C_(a) C_(cu) C_(mx) C_(hp2) C_(a2)
#undef C_
    return 0;
}
/* clang-format on */
/* lev: the cost of the join found */
typedef struct {
    int x;
    unsigned char kind;
    signed char lev;
} Hit;
typedef struct {
    Hit *h;
    int n, cap;
} HL;
/* Appends one hit of an index lookup: an event, on which side it was found, and the cost of that join. */
static inline void hl_add(HL *l, int x, int kind, int lev) {
    if (l->n == l->cap) {
        l->cap = l->cap ? l->cap * 2 : 256;
        l->h = realloc(l->h, (size_t)l->cap * sizeof(Hit));
    }
    l->h[l->n].x = x;
    l->h[l->n].kind = (unsigned char)kind;
    l->h[l->n].lev = (signed char)lev;
    l->n++;
}
/* nodes x with d(E_x, Sw) = lev <= K (kind 0: x is the tail of an arc) or d(Ew, S_x) = lev <= K (kind 1: the head) */
static void lookup(const Seq *q, u64 Sw, u64 Ew, HL *l) {
    l->n = 0;
    for (int j = 0; j < NLEV; j++) {
        int k = OVMAX - j, lev = h - k;
        u64 k0 = HKEY(Sw >> (4 * (n - k)), k, 0), k1 = HKEY(Ew & HMASK[k], k, 1), b;
        b = BFH(k0) & q->bfmask;
        if ((q->bf[b >> 6] >> (b & 63)) & 1)
            for (int e = h_get(&q->H, k0); e >= 0; e = q->H.next[e]) {
                int x = q->H.val[e];
                if (dist(q->E[x], Sw) == lev)
                    hl_add(l, x, 0, lev);
            }
        b = BFH(k1) & q->bfmask;
        if ((q->bf[b >> 6] >> (b & 63)) & 1)
            for (int e = h_get(&q->H, k1); e >= 0; e = q->H.next[e]) {
                int x = q->H.val[e];
                if (dist(Ew, q->S[x]) == lev)
                    hl_add(l, x, 1, lev);
            }
    }
}
#define WHOLE(i, j) ((i) == 0 && (j) == N - 1)
#define ADD(ty, ii, jj, cu_, mx_, dl)                                 \
    do {                                                              \
        if (watch && dist(q->E[jj], q->S[ii]) + rem_(q, ii, jj) >= 0) \
            break;                                                    \
        Move mv_ = *proto;                                            \
        mv_.type = (unsigned char)(ty);                               \
        mv_.i = (ii);                                                 \
        mv_.j = (jj);                                                 \
        mv_.cu = (cu_);                                               \
        mv_.mx = (mx_);                                               \
        mv_.delta = (short)(dl);                                      \
        ml_add(ml, &mv_);                                             \
    } while (0)

/* A (joins inside the block): the cut (Sw, Ew, D) lies in event hp, which stays in M; the hits are arcs of the loop */
static void scanA(const Seq *q, int hp, u64 Sw, u64 Ew, int D, const HL *l, ML *ml, const Move *proto) {
    int N = q->N;
    for (int z = 0; z < l->n; z++) {
        int x = l->h[z].x, lev = l->h[z].lev;
        if (l->h[z].kind == 0) { /* x = tail, d1 = lev */
            if (x + 1 < N) {     /* the join x -> x+1 inside a block */
                int e = lev + D + dist(Ew, q->S[x + 1]) - q->J[x];
                if (e + q->mfa[x] <= thr)
                    for (int i = x; i >= 0 && x + 2 - i <= LMAX; i--)
                        for (int j = x + 1; j < N && j - i + 1 <= LMAX; j++) {
                            if ((hp >= i && hp <= j) || WHOLE(i, j))
                                continue;
                            int dl = Fb(q, i, j) + e;
                            if (dl <= thr)
                                ADD(M_AI, i, j, x, -2, dl);
                        }
                if (e + q->LBmin <= thr)
                    for (int b = 0; b < q->nLB; b++) {
                        int i = q->LB[b].i, j = q->LB[b].j;
                        if (i > x || j < x + 1 || (hp >= i && hp <= j))
                            continue;
                        int dl = q->LB[b].f + e;
                        if (dl <= thr)
                            ADD(M_AI, i, j, x, -2, dl);
                    }
            }
        } else { /* x = head, d2 = lev; only what kind 0 does not find */
            if (x >= 1) {
                int d1 = dist(q->E[x - 1], Sw);
                if (d1 > KL) {
                    int e = d1 + D + lev - q->J[x - 1];
                    if (e + q->mfa[x - 1] <= thr)
                        for (int i = x - 1; i >= 0 && x + 1 - i <= LMAX; i--)
                            for (int j = x; j < N && j - i + 1 <= LMAX; j++) {
                                if ((hp >= i && hp <= j) || WHOLE(i, j))
                                    continue;
                                int dl = Fb(q, i, j) + e;
                                if (dl <= thr)
                                    ADD(M_AI, i, j, x - 1, -2, dl);
                            }
                    if (e + q->LBmin <= thr)
                        for (int b = 0; b < q->nLB; b++) {
                            int i = q->LB[b].i, j = q->LB[b].j;
                            if (i > x - 1 || j < x || (hp >= i && hp <= j))
                                continue;
                            int dl = q->LB[b].f + e;
                            if (dl <= thr)
                                ADD(M_AI, i, j, x - 1, -2, dl);
                        }
                }
            }
        }
    }
}
/* for every join x -> x+1: the nodes z with d(E_z, S_x+1) <= K (nb0 of x) and the nodes v with d(E_x, S_v) <= K
   (nb1 of y = x+1).  They are the partners of a port move whose third join (from the tail of one of its joins to the
   head of the other) is cheap; see scanP */
static void seq_neighbours(Seq *q) {
    int N = q->N;
    HL hl;
    memset(&hl, 0, sizeof hl);
    i64 c0 = 0, c1 = 0, cap0 = 4 * (i64)N + 64, cap1 = cap0;
    q->o0 = malloc(((size_t)N + 2) * sizeof(int));
    q->o1 = malloc(((size_t)N + 2) * sizeof(int));
    q->nb0 = malloc((size_t)cap0 * sizeof(int));
    q->nb1 = malloc((size_t)cap1 * sizeof(int));
    q->o0[0] = 0;
    q->o1[0] = 0;
    q->o1[1] = 0;
    for (int x = 0; x + 1 < N; x++) {
        lookup(q, q->S[x + 1], q->E[x], &hl);
        for (int z = 0; z < hl.n; z++) {
            if (hl.h[z].kind == 0) {
                if (c0 == cap0) {
                    cap0 *= 2;
                    q->nb0 = realloc(q->nb0, (size_t)cap0 * sizeof(int));
                }
                q->nb0[c0++] = hl.h[z].x;
            } else {
                if (c1 == cap1) {
                    cap1 *= 2;
                    q->nb1 = realloc(q->nb1, (size_t)cap1 * sizeof(int));
                }
                q->nb1[c1++] = hl.h[z].x;
            }
        }
        q->o0[x + 1] = (int)c0;
        q->o1[x + 2] = (int)c1;
    }
    if (N >= 1)
        q->o0[N] = (int)c0;
    free(hl.h);
}
static void seq_make(Seq *q, Ev *ev, int N) {
    seq_make0(q, ev, N);
    seq_neighbours(q);
}

/* One new port and two joins (the exchange of three arcs, one of them a cut): the cut w of event hp, the tail x of
   one join (E_x -> S_w) and the head y of another (E_w -> S_y).  y <= x, hp outside y .. x: the block y .. x is hung
   on the port (A.close).  x < hp < y: the block x+1 .. y-1 is rotated in place around its member hp (B.pq).
   Both change the length by d1 + (3 - g) + d2 + r - J(x) - J(y-1), d1 = d(E_x, S_w), d2 = d(E_w, S_y), and the third
   join r = d(E_y-1, S_x+1) (0 at an end of the sequence).  Blocks of any length.
   Found: every such move with d1 <= K or d2 <= K.  The partner of a hit is looked for in three places: among the
   hits of the same cut (the other distance <= K too); among the nodes whose third join costs <= K (nb0 / nb1, known
   per join); and, when both are above K, only behind joins that are expensive enough to pay 2K + 2 (byJ). */
static inline void port_pair(const Seq *q, int hp, int x, int y, int d1, int d2, int D, ML *ml, const Move *proto) {
    int N = q->N;
    if (d1 + D + d2 + MINW - Jc(q, x) - Jc(q, y - 1) > thr)
        return; /* the third join costs MINW at least */
    if (y <= x) {
        if ((hp >= y && hp <= x) || WHOLE(y, x))
            return;
        int dl = d1 + D + d2 + rem_(q, y, x);
        if (dl <= thr)
            ADD(M_AC, y, x, x, -2, dl);
    } else if (x < hp && hp < y && y - x > 2 && !WHOLE(x + 1, y - 1)) {
        int dl = dist(q->E[y - 1], q->S[x + 1]) + d1 + D + d2 - Jc(q, x) - Jc(q, y - 1);
        if (dl <= thr)
            ADD(M_BN, x + 1, y - 1, -2, x, dl);
    }
}
/* Moves of kind P (A.close and B.pq) for one cut: pairs of hits, one that leads into the cut and one that
   leads out of it, give a block of any length; the third join of the exchange is looked up. */
static void scanP(const Seq *q, int hp, u64 Sw, u64 Ew, int D, const HL *l, ML *ml, const Move *proto) {
    int N = q->N;
    for (int z = 0; z < l->n; z++) {
        int x = l->h[z].x, lev = l->h[z].lev;
        if (l->h[z].kind == 0) { /* x = tail of the join into the port, d1 = lev */
            for (int z2 = 0; z2 < l->n; z2++)
                if (l->h[z2].kind == 1)
                    port_pair(q, hp, x, l->h[z2].x, lev, l->h[z2].lev, D, ml, proto);
            if (x + 1 < N) {
                for (int k = q->o0[x]; k < q->o0[x + 1]; k++) { /* third join <= K */
                    int y = q->nb0[k] + 1;
                    if (y >= N || lev + D + KL + 1 + MINW - Jc(q, x) - Jc(q, y - 1) > thr)
                        continue;
                    int d2 = dist(Ew, q->S[y]);
                    if (d2 > KL)
                        port_pair(q, hp, x, y, lev, d2, D, ml, proto);
                }
                if (lev + D + KL + 1 - Jc(q, x) <= thr) {
                    int d2 = dist(Ew, q->S[0]);
                    if (d2 > KL)
                        port_pair(q, hp, x, 0, lev, d2, D, ml, proto);
                } /* y = 0: no third join */
                int need = D + lev + 2 * KL + 2 - Jc(q, x) - thr;
                if (need < -2)
                    need = -2;
                if (need <= h)
                    for (int k = 0; k < q->nJ[need + 2]; k++) { /* both above K: only behind a join that pays for it */
                        int y = q->byJ[k] + 1;
                        if (y >= N || y == 0)
                            continue;
                        int d2 = dist(Ew, q->S[y]);
                        if (d2 <= KL)
                            continue;
                        if (dist(q->E[y - 1], q->S[x + 1]) <= KL)
                            continue;
                        port_pair(q, hp, x, y, lev, d2, D, ml, proto);
                    }
            } else { /* x is the last event: no third join */
                int need = D + lev + KL + 1 - thr;
                if (need < -2)
                    need = -2;
                if (need <= h)
                    for (int k = 0; k < q->nJ[need + 2]; k++) {
                        int y = q->byJ[k] + 1;
                        if (y >= N)
                            continue;
                        int d2 = dist(Ew, q->S[y]);
                        if (d2 > KL)
                            port_pair(q, hp, x, y, lev, d2, D, ml, proto);
                    }
            }
            if (x < hp && N - 1 - x >= 2) { /* no head: the block x+1 .. N-1 rotated at the end of the sequence */
                int dl = dist(q->E[N - 1], q->S[x + 1]) + lev + D - Jc(q, x);
                if (dl <= thr)
                    ADD(M_BN, x + 1, N - 1, -2, x, dl);
            }
        } else { /* x = head of the join out of the port, d2 = lev */
            if (x >= 1) {
                for (int k = q->o1[x]; k < q->o1[x + 1]; k++) { /* third join <= K */
                    int t = q->nb1[k] - 1;
                    if (t < 0 || lev + D + KL + 1 + MINW - Jc(q, t) - Jc(q, x - 1) > thr)
                        continue;
                    int d1 = dist(q->E[t], Sw);
                    if (d1 > KL)
                        port_pair(q, hp, t, x, d1, lev, D, ml, proto);
                }
                if (lev + D + KL + 1 - Jc(q, x - 1) <= thr) {
                    int d1 = dist(q->E[N - 1], Sw);
                    if (d1 > KL)
                        port_pair(q, hp, N - 1, x, d1, lev, D, ml, proto);
                } /* t = N-1: no third join */
                int need = D + lev + 2 * KL + 2 - Jc(q, x - 1) - thr;
                if (need < -2)
                    need = -2;
                if (need <= h)
                    for (int k = 0; k < q->nJ[need + 2]; k++) {
                        int t = q->byJ[k];
                        if (t < 0 || t == N - 1)
                            continue;
                        int d1 = dist(q->E[t], Sw);
                        if (d1 <= KL)
                            continue;
                        if (dist(q->E[x - 1], q->S[t + 1]) <= KL)
                            continue;
                        port_pair(q, hp, t, x, d1, lev, D, ml, proto);
                    }
            } else { /* x is the first event: no third join */
                int need = D + lev + KL + 1 - thr;
                if (need < -2)
                    need = -2;
                if (need <= h)
                    for (int k = 0; k < q->nJ[need + 2]; k++) {
                        int t = q->byJ[k];
                        if (t < 0)
                            continue;
                        int d1 = dist(q->E[t], Sw);
                        if (d1 > KL)
                            port_pair(q, hp, t, x, d1, lev, D, ml, proto);
                    }
            }
            if (hp < x && x >= 2) { /* no tail: the block 0 .. x-1 rotated at the start of the sequence */
                int dl = dist(q->E[x - 1], q->S[0]) + D + lev - Jc(q, x - 1);
                if (dl <= thr)
                    ADD(M_BN, 0, x - 1, -2, -1, dl);
            }
        }
    }
}
/* B / D: the cut (Sw, Ew, D) belongs to the loop, which must hold the events h0 .. h1 (exact: the block is ei .. ej);
   the hits are arcs of M.  mmin: smallest block; cu: what ADD records as the cut open arc of C (-3: the closing arc) */
static void scanB(const Seq *q, int h0, int h1, int exact, int ei, int ej, int mmin, int newarc, u64 Sw, u64 Ew, int D,
                  const HL *l, ML *ml, const Move *proto, int ty_ord, int ty_new, int cu) {
    int N = q->N;
    for (int z = 0; z < l->n; z++) {
        int x = l->h[z].x, lev = l->h[z].lev, kind = l->h[z].kind, tail, d1, d2, ord = 1;
        if (kind == 0) {
            tail = x;
            d1 = lev;
            d2 = x + 1 < N ? dist(Ew, q->S[x + 1]) : 0;
        } else {
            tail = x - 1;
            d2 = lev;
            d1 = tail >= 0 ? dist(q->E[tail], Sw) : 0;
            if (tail >= 0 && d1 <= KL)
                ord = 0;
        }
        if (ord) { /* the join tail -> tail+1, outside the block */
            int ins = d1 + D + d2 - Jc(q, tail);
            if (exact) {
                if (tail < ei - 1 || tail > ej) {
                    int dl = Fb(q, ei, ej) + ins;
                    if (dl <= thr)
                        ADD(ty_ord, ei, ej, cu == -3 ? ej : cu, tail, dl);
                }
            } else if (ins + (h0 == h1 ? q->mfn[h0] : q->mfa[h0]) <= thr)
                for (int i = h0; i >= 0 && h1 - i + 1 <= LMAX; i--) {
                    int j0 = h1 > i + mmin - 1 ? h1 : i + mmin - 1;
                    for (int j = j0; j < N && j - i + 1 <= LMAX; j++) {
                        if (!(tail < i - 1 || tail > j) || WHOLE(i, j))
                            continue;
                        int dl = Fb(q, i, j) + ins;
                        if (dl <= thr)
                            ADD(ty_ord, i, j, cu == -3 ? j : cu, tail, dl);
                    }
                }
            if (!exact && ins + q->LBmin <= thr)
                for (int b = 0; b < q->nLB; b++) {
                    int i = q->LB[b].i, j = q->LB[b].j;
                    if (i > h0 || j < h1 || !(tail < i - 1 || tail > j))
                        continue;
                    int dl = q->LB[b].f + ins;
                    if (dl <= thr)
                        ADD(ty_ord, i, j, cu, tail, dl);
                }
        }
        if (!newarc)
            continue;    /* the new join p -> q */
        if (kind == 0) { /* x = p */
            int i = x + 1;
            if (i > h0 || i >= N)
                continue;
            int j0 = h1 > i + mmin - 1 ? h1 : i + mmin - 1;
            for (int j = j0; j < N && j - i + 1 <= LMAX; j++) {
                if (WHOLE(i, j))
                    continue;
                int d2n = j + 1 < N ? dist(Ew, q->S[j + 1]) : 0;
                int dl = dist(q->E[j], q->S[i]) + lev + D + d2n - Jc(q, i - 1) - Jc(q, j);
                if (dl <= thr)
                    ADD(ty_new, i, j, cu, i - 1, dl);
            }
        } else { /* x = q */
            int j = x - 1;
            if (j < h1)
                continue;
            int i0 = h0 < j - mmin + 1 ? h0 : j - mmin + 1;
            for (int i = i0; i >= 0 && j - i + 1 <= LMAX; i--) {
                if (WHOLE(i, j))
                    continue;
                int d1n = i > 0 ? dist(q->E[i - 1], Sw) : 0;
                if (i > 0 && d1n <= KL)
                    continue;
                int dl = dist(q->E[j], q->S[i]) + d1n + D + lev - Jc(q, i - 1) - Jc(q, j);
                if (dl <= thr)
                    ADD(ty_new, i, j, cu, i - 1, dl);
            }
        }
    }
}
typedef struct {
    u64 w;
    int hp;
    i64 a;
} Vtx;
/* Order of the vertices: by h-word, then by hp, then by a. */
static int vtx_cmp(const void *x, const void *y) {
    const Vtx *a = x, *b = y;
    return a->w < b->w ? -1 : a->w > b->w ? 1 : a->hp < b->hp ? -1 : a->hp > b->hp ? 1 : a->a < b->a ? -1 : a->a > b->a;
}
typedef struct {
    i64 cuts[4], hostcuts[4], hits, vtx, vshared, vsame, skipcuts;
    double sec;
    int *zc;
} ScanStat;
/* zc[4 * x + g]: cuts of gap g (in events other than x, x+1) that lie on the shortest connector of the join x -> x+1 */
static i64 maxR;

/* One scan of the sequence: every cut of every event that could become a second cut (a port) is looked up in
   the index of the joins, and the moves of the kinds asked for with delta <= thr are listed, sorted. */
static void scan(const Seq *q, ML *out, ScanStat *st) {
    double t0 = wall();
    int N = q->N;
    memset(out, 0, sizeof *out);
    memset(st, 0, sizeof *st);
    st->zc = calloc((size_t)N * 4 + 4, sizeof(int));
    Vtx *VX = NULL;
    i64 nvx = 0, vxcap = 0;
    int wantP = !only[0] || strchr(only, 'P'), wantA = !only[0] || strchr(only, 'A'),
        wantB = !only[0] || strchr(only, 'B'), wantC = !only[0] || strchr(only, 'C'),
        wantD = useD && (!only[0] || strchr(only, 'D'));
#pragma omp parallel num_threads(NTHR)
    {
        HL hl;
        memset(&hl, 0, sizeof hl);
        ML ml;
        memset(&ml, 0, sizeof ml);
        Vtx *vx = NULL;
        i64 nv = 0, vcap = 0;
        ScanStat ls;
        memset(&ls, 0, sizeof ls);
        ls.zc = calloc((size_t)N * 4 + 4, sizeof(int));
        Move proto;
        memset(&proto, 0, sizeof proto);
        proto.hp = proto.hp2 = -1;
        proto.a = proto.a2 = -1;
#pragma omp for schedule(dynamic, 4)
        for (i64 t = 0; t < NT; t++) {
            const Trail *T = &TR[t];
            if (T->fixed || q->thead[t] < 0)
                continue;
            i64 R = T->R, first = -1, prev = -1;
            int wc[16] = {0}, distinct = 0;
            for (int k = 0; k < n - 1; k++)
                if (wc[T->c[k % R]]++ == 0)
                    distinct++;
            for (i64 p = 0; p <= R;
                 p++) { /* the windows in order (not stored); p == R: the pair that closes the trail */
                i64 b = p;
                if (p < R) {
                    i64 z = p + n - 1;
                    if (z >= R)
                        z -= R;
                    if (wc[T->c[z]]++ == 0)
                        distinct++;
                    int isw = distinct == n;
                    if (--wc[T->c[p]] == 0)
                        distinct--;
                    if (!isw)
                        continue;
                    if (first < 0) {
                        first = prev = p;
                        continue;
                    }
                } else {
                    if (first < 0 || first == prev)
                        break;
                    b = first;
                }
                i64 a = prev;
                int g = (int)((b - a + R) % R);
                prev = p;
                if (g < 1 || g > 3)
                    continue;
                ls.cuts[g]++;
                if (g == 1 && !use_gap1)
                    continue;
                int hp = -1;
                for (int pos = q->thead[t]; pos >= 0; pos = q->tnx[pos]) {
                    const Ev *x = &q->ev[pos];
                    i64 rel = ((a - x->st) % R + R) % R;
                    if (rel + g + n <= x->l) {
                        hp = pos;
                        break;
                    }
                }
                if (hp < 0)
                    continue;
                if (q->ev[hp].skip >= 0 && !skiphost) {
                    ls.skipcuts++;
                    continue;
                }
                ls.hostcuts[g]++;
                u64 Sw = win_cyc(T, b), Ew = win_cyc(T, a);
                if (g == 3 && wantC) {
                    if (nv == vcap) {
                        vcap = vcap ? vcap * 2 : 4096;
                        vx = realloc(vx, (size_t)vcap * sizeof(Vtx));
                    }
                    vx[nv].w = Sw >> 12;
                    vx[nv].hp = hp;
                    vx[nv].a = a;
                    nv++;
                }
                lookup(q, Sw, Ew, &hl);
                if (!hl.n)
                    continue;
                ls.hits += hl.n;
                proto.hp = hp;
                proto.a = a;
                proto.g = (unsigned char)g;
                for (int z = 0; z < hl.n; z++) { /* ports on the connectors of the joins as they are */
                    int x = hl.h[z].kind ? hl.h[z].x - 1 : hl.h[z].x, d1, d2;
                    if (x < 0 || x + 1 >= N || hp == x || hp == x + 1)
                        continue;
                    if (hl.h[z].kind) {
                        d2 = hl.h[z].lev;
                        d1 = dist(q->E[x], Sw);
                        if (d1 <= KL)
                            continue;
                    } else {
                        d1 = hl.h[z].lev;
                        d2 = dist(Ew, q->S[x + 1]);
                    }
                    if (d1 + 3 - g + d2 == q->J[x])
                        ls.zc[4 * x + g]++;
                }
                if (wantP)
                    scanP(q, hp, Sw, Ew, 3 - g, &hl, &ml, &proto);
                if (wantA)
                    scanA(q, hp, Sw, Ew, 3 - g, &hl, &ml, &proto);
                if (wantB)
                    scanB(q, hp, hp, 0, 0, 0, 2, 0, Sw, Ew, 3 - g, &hl, &ml, &proto, M_BO, M_BN, -2);
            }
        }
        proto.hp = -1;
        proto.a = -1;
        proto.g = 0;
        if (wantD) {
/* D: a join x -> x+1 of the loop is cut open (the block is rotated) */
#pragma omp for schedule(dynamic, 64)
            for (int x = 0; x < N - 1; x++) {
                lookup(q, q->S[x + 1], q->E[x], &hl);
                if (!hl.n)
                    continue;
                scanB(q, x, x + 1, 0, 0, 0, 2, 1, q->S[x + 1], q->E[x], -q->J[x], &hl, &ml, &proto, M_DI, M_DN, x);
            }
/* D: the closing arc is cut open: the plain block move */
#pragma omp for schedule(dynamic, 64)
            for (int i = 0; i < N; i++)
                for (int j = i; j < N && j - i + 1 <= LMAX; j++) {
                    if (WHOLE(i, j))
                        continue;
                    lookup(q, q->S[i], q->E[j], &hl);
                    if (!hl.n)
                        continue;
                    scanB(q, i, j, 1, i, j, 1, 0, q->S[i], q->E[j], -dist(q->E[j], q->S[i]), &hl, &ml, &proto, M_DC,
                          M_DC, -3);
                }
        }
#pragma omp critical
        {
            for (i64 z = 0; z < ml.n; z++) {
                if (out->n >= ML_MAX) {
                    out->over++;
                    continue;
                }
                if (out->n == out->cap) {
                    out->cap = out->cap ? out->cap * 2 : 4096;
                    out->m = realloc(out->m, (size_t)out->cap * sizeof(Move));
                }
                out->m[out->n++] = ml.m[z];
            }
            out->over += ml.over;
            for (int a = 0; a < M_NT; a++)
                for (int d = 0; d < 8; d++)
                    out->cnt[a][d] += ml.cnt[a][d];
            for (int g = 0; g < 4; g++) {
                st->cuts[g] += ls.cuts[g];
                st->hostcuts[g] += ls.hostcuts[g];
            }
            st->hits += ls.hits;
            st->skipcuts += ls.skipcuts;
            if (nvx + nv > vxcap) {
                vxcap = (nvx + nv) * 2 + 1024;
                VX = realloc(VX, (size_t)vxcap * sizeof(Vtx));
            }
            if (nv)
                memcpy(VX + nvx, vx, (size_t)nv * sizeof(Vtx));
            nvx += nv;
            for (int z = 0; z < 4 * N; z++)
                st->zc[z] += ls.zc[z];
        }
        free(hl.h);
        free(ml.m);
        free(vx);
        free(ls.zc);
    }
    /* C: two events with an inner gap-3 cut at the same h-word; any block that holds exactly one of them */
    if (wantC && nvx) {
        qsort(VX, (size_t)nvx, sizeof(Vtx), vtx_cmp);
        st->vtx = nvx;
        ML *ml = out;
        Move pr;
        memset(&pr, 0, sizeof pr);
        const Move *proto = &pr;
        for (i64 a = 0; a < nvx;) {
            i64 b = a;
            while (b < nvx && VX[b].w == VX[a].w)
                b++;
            for (i64 u = a; u < b; u++)
                for (i64 v = a; v < b; v++) {
                    if (u == v)
                        continue;
                    if (VX[u].hp == VX[v].hp) {
                        if (u < v)
                            st->vsame++;
                        continue;
                    }
                    if (u < v)
                        st->vshared++;
                    int hm = VX[u].hp, hc = VX[v].hp; /* hm stays in M, hc is in the loop */
                    pr.hp = hm;
                    pr.a = VX[u].a;
                    pr.g = 3;
                    pr.hp2 = hc;
                    pr.a2 = VX[v].a;
                    pr.g2 = 3;
                    for (int i = hc; i >= 0 && hc - i + 1 <= LMAX; i--)
                        for (int j = hc; j < N && j - i + 1 <= LMAX; j++) {
                            if ((hm >= i && hm <= j) || WHOLE(i, j))
                                continue;
                            int dl = Fb(q, i, j);
                            if (dl <= thr)
                                ADD(M_C, i, j, -2, -2, dl);
                        }
                    for (int b = 0; b < q->nLB; b++) {
                        int i = q->LB[b].i, j = q->LB[b].j;
                        if (hc < i || hc > j || (hm >= i && hm <= j))
                            continue;
                        ADD(M_C, i, j, -2, -2, q->LB[b].f);
                    }
                }
            a = b;
        }
    }
    free(VX);
    if (out->n)
        qsort(out->m, (size_t)out->n, sizeof(Move), mv_cmp);
    st->sec = wall() - t0;
}

/* ---------- --brute: the same set of moves by plain enumeration (for small words; checks the scan) */
static u64 mv_hash(const Move *m) {
    u64 x = hmix((u64)m->type * 1000003ULL + (u64)(m->delta + 100));
    x = hmix(x ^ ((u64)(u32)m->i << 32 | (u32)m->j));
    x = hmix(x ^ ((u64)(u32)m->hp << 32 | (u32)m->cu));
    x = hmix(x ^ ((u64)(u32)m->mx << 32 | (u32)m->g));
    x = hmix(x ^ (u64)m->a);
    return x;
}
/* Counts one move found by plain enumeration and adds it to the checksum. */
static void brute_add(i64 cnt[M_NT][8], u64 *sum, int ty, int i, int j, int hp, i64 a, int g, int cu, int mx, int dl) {
    Move m;
    memset(&m, 0, sizeof m);
    m.type = (unsigned char)ty;
    m.i = i;
    m.j = j;
    m.hp = hp;
    m.a = a;
    m.g = (unsigned char)g;
    m.cu = cu;
    m.mx = mx;
    m.delta = (short)dl;
    m.hp2 = -1;
    m.a2 = -1;
    int d = dl < -3 ? -3 : dl;
    if (d <= 4)
        cnt[ty][d + 3]++;
    *sum += mv_hash(&m);
}
/* The same moves by plain enumeration over all blocks, joins and cuts (--brute, small words only); prints the
   counts and the checksum to compare with those of the scan. */
static void brute(const Seq *q) {
    int N = q->N;
    i64 cnt[M_NT][8];
    memset(cnt, 0, sizeof cnt);
    u64 sum = 0;
    double t0 = wall();
    i64 *wp = malloc((size_t)(maxR + 8) * 8);
#define FOR_BLOCKS(...)                                            \
    {                                                              \
        for (int i = 0; i < N; i++)                                \
            for (int j = i; j < N && j - i + 1 <= LMAX; j++) {     \
                if (WHOLE(i, j))                                   \
                    continue;                                      \
                int f = Fb(q, i, j);                               \
                __VA_ARGS__                                        \
            }                                                      \
        for (int b_ = 0; b_ < q->nLB; b_++) {                      \
            int i = q->LB[b_].i, j = q->LB[b_].j, f = q->LB[b_].f; \
            __VA_ARGS__                                            \
        }                                                          \
    }
    for (i64 t = 0; t < NT; t++) {
        const Trail *T = &TR[t];
        if (T->fixed || q->thead[t] < 0)
            continue;
        i64 R = T->R, m = trail_windows(T, wp);
        if (m < 2)
            continue;
        for (i64 k = 0; k < m; k++) {
            i64 a = wp[k], b = wp[k + 1 == m ? 0 : k + 1];
            int g = (int)((b - a + R) % R);
            if (g < 1 || g > 3 || (g == 1 && !use_gap1))
                continue;
            int hp = -1;
            for (int pos = q->thead[t]; pos >= 0; pos = q->tnx[pos]) {
                const Ev *x = &q->ev[pos];
                i64 rel = ((a - x->st) % R + R) % R;
                if (rel + g + n <= x->l) {
                    hp = pos;
                    break;
                }
            }
            if (hp < 0 || (q->ev[hp].skip >= 0 && !skiphost))
                continue;
            u64 Sw = win_cyc(T, b), Ew = win_cyc(T, a);
            int D = 3 - g;
            /* A.close and B.pq: blocks of any length */
            for (int i = 0; i < N; i++)
                for (int j = i; j < N; j++) {
                    if (WHOLE(i, j))
                        continue;
                    if (hp < i || hp > j) {
                        int d1 = dist(q->E[j], Sw), d2 = dist(Ew, q->S[i]);
                        if (d1 > KL && d2 > KL)
                            continue;
                        int dl = d1 + D + d2 + rem_(q, i, j);
                        if (dl <= thr)
                            brute_add(cnt, &sum, M_AC, i, j, hp, a, g, j, -2, dl);
                    } else if (j > i) {
                        int d1 = i > 0 ? dist(q->E[i - 1], Sw) : 0, d2 = j + 1 < N ? dist(Ew, q->S[j + 1]) : 0;
                        if (!((i > 0 && d1 <= KL) || (j + 1 < N && d2 <= KL)))
                            continue;
                        int dl = dist(q->E[j], q->S[i]) + d1 + D + d2 - Jc(q, i - 1) - Jc(q, j);
                        if (dl <= thr)
                            brute_add(cnt, &sum, M_BN, i, j, hp, a, g, -2, i - 1, dl);
                    }
                }
            FOR_BLOCKS(
                if (hp < i || hp > j) { /* A.inner */
                                        for (int x = i; x < j; x++) {
                                            int d1 = dist(q->E[x], Sw), d2 = dist(Ew, q->S[x + 1]);
                                            if (d1 > KL && d2 > KL)
                                                continue;
                                            int dl = f + d1 + D + d2 - q->J[x];
                                            if (dl <= thr)
                                                brute_add(cnt, &sum, M_AI, i, j, hp, a, g, x, -2, dl);
                                        }
                } else if (j > i) { /* B.arc */
                                    for (int tl = -1; tl < N; tl++) {
                                        if (!(tl < i - 1 || tl > j))
                                            continue;
                                        int d1 = tl >= 0 ? dist(q->E[tl], Sw) : 0,
                                            d2 = tl + 1 < N ? dist(Ew, q->S[tl + 1]) : 0;
                                        if (!((tl >= 0 && d1 <= KL) || (tl + 1 < N && d2 <= KL)))
                                            continue;
                                        int dl = f + d1 + D + d2 - Jc(q, tl);
                                        if (dl <= thr)
                                            brute_add(cnt, &sum, M_BO, i, j, hp, a, g, -2, tl, dl);
                                    }
                })
        }
    }
    if (useD) {
        FOR_BLOCKS(
            if (j > i) for (int x = i; x < j; x++) {
                u64 Sw = q->S[x + 1], Ew = q->E[x];
                for (int tl = -1; tl < N; tl++) {
                    if (!(tl < i - 1 || tl > j))
                        continue;
                    int d1 = tl >= 0 ? dist(q->E[tl], Sw) : 0, d2 = tl + 1 < N ? dist(Ew, q->S[tl + 1]) : 0;
                    if (!((tl >= 0 && d1 <= KL) || (tl + 1 < N && d2 <= KL)))
                        continue;
                    int dl = f - q->J[x] + d1 + d2 - Jc(q, tl);
                    if (dl <= thr)
                        brute_add(cnt, &sum, M_DI, i, j, -1, -1, 0, x, tl, dl);
                }
                if (j - i + 1 <= LMAX) {
                    int d1 = i > 0 ? dist(q->E[i - 1], Sw) : 0, d2 = j + 1 < N ? dist(Ew, q->S[j + 1]) : 0;
                    if ((i > 0 && d1 <= KL) || (j + 1 < N && d2 <= KL)) {
                        int dl = dist(q->E[j], q->S[i]) + d1 + d2 - q->J[x] - Jc(q, i - 1) - Jc(q, j);
                        if (dl <= thr)
                            brute_add(cnt, &sum, M_DN, i, j, -1, -1, 0, x, i - 1, dl);
                    }
                }
            } if (j - i + 1 <= LMAX) for (int tl = -1; tl < N; tl++) {
                if (!(tl < i - 1 || tl > j))
                    continue;
                int d1 = tl >= 0 ? dist(q->E[tl], q->S[i]) : 0, d2 = tl + 1 < N ? dist(q->E[j], q->S[tl + 1]) : 0;
                if (!((tl >= 0 && d1 <= KL) || (tl + 1 < N && d2 <= KL)))
                    continue;
                int dl = rem_(q, i, j) + d1 + d2 - Jc(q, tl);
                if (dl <= thr)
                    brute_add(cnt, &sum, M_DC, i, j, -1, -1, 0, j, tl, dl);
            })
    }
    free(wp);
    printf("brute force (%.1fs): checksum %016llx\n", wall() - t0, (unsigned long long)sum);
    for (int a = 0; a < M_NT; a++) {
        printf("  %-9s", MNAME[a]);
        for (int d = 0; d < 7; d++)
            printf(" %8lld", cnt[a][d]);
        printf("\n");
    }
}

/* ---------- applying a move */
/* H[.. window at a], H[window at a + g ..] */
static void split_event(const Ev *H, i64 a, int g, Ev *H1, Ev *H2) {
    const Trail *T = &TR[H->t];
    i64 R = T->R, rel = ((a - H->st) % R + R) % R;
    if (rel + g + n > H->l || !is_win(T, a) || !is_win(T, a + g))
        DIE("internal error: cut outside its event");
    *H1 = seg_event(H->t, H->st, rel + n);
    *H2 = seg_event(H->t, H->st + rel + g, H->l - rel - g);
    H1->id = next_id++;
    H2->id = next_id++;
}
/* two neighbours that are consecutive stretches of one trail become one event again (a port that is no longer used);
   a stretch that is the whole trail from a plain cut becomes an O event.  Returns the new number of events. */
static int normalise(Ev *ev, int N) {
    int k = 0;
    for (int i = 0; i < N; i++) {
        Ev x = ev[i];
        if (k && ev[k - 1].t == x.t && !TR[x.t].fixed && ev[k - 1].skip < 0 && x.skip < 0) {
            const Ev *y = &ev[k - 1];
            const Trail *T = &TR[x.t];
            i64 R = T->R, a = y->st + y->l - n, g = ((x.st - a) % R + R) % R;
            if (g >= 1 && g <= 3 && y->l + x.l - (n - g) <= R + n - 1) {
                int clean = 1;
                for (i64 z = 1; z < g; z++)
                    if (is_win(T, a + z))
                        clean = 0;
                if (clean) {
                    x = seg_event(x.t, y->st, y->l + x.l - (n - g));
                    x.id = next_id++;
                    k--;
                }
            }
        }
        if (x.kind == EV_SEG && !TR[x.t].fixed) {
            const Trail *T = &TR[x.t];
            i64 g = T->R + n - x.l;
            if (g >= 2 && g <= 3 && is_win(T, x.st - g)) {
                int clean = 1;
                for (i64 z = 1; z < g; z++)
                    if (is_win(T, x.st - g + z))
                        clean = 0;
                if (clean) {
                    int id = x.id;
                    x = opt_event(x.t, x.st, (int)g, 0);
                    x.id = id;
                }
            }
        }
        ev[k++] = x;
    }
    return k;
}
/* the new sequence as it comes (not normalised) */
static Ev *apply_ev(const Ev *ev, int N, const Move *mv, int *Nout) {
    int i = mv->i, j = mv->j, k = 0;
    Ev *out = malloc(((size_t)N + 8) * sizeof(Ev)), H1, H2, G1, G2;
    Ev *loop = malloc(((size_t)(j - i + 1) + 8) * sizeof(Ev));
    int nl = 0;
    int ty = mv->type, hostM = ty == M_AC || ty == M_AI || ty == M_C, hostC = ty == M_BO || ty == M_BN;
    if (hostM)
        split_event(&ev[mv->hp], mv->a, mv->g, &H1, &H2);
    if (hostC) {
        split_event(&ev[mv->hp], mv->a, mv->g, &G1, &G2);
        loop[nl++] = G2;
        for (int x = mv->hp + 1; x <= j; x++)
            loop[nl++] = ev[x];
        for (int x = i; x < mv->hp; x++)
            loop[nl++] = ev[x];
        loop[nl++] = G1;
    } else if (ty == M_C) {
        split_event(&ev[mv->hp2], mv->a2, mv->g2, &G1, &G2);
        loop[nl++] = G2;
        for (int x = mv->hp2 + 1; x <= j; x++)
            loop[nl++] = ev[x];
        for (int x = i; x < mv->hp2; x++)
            loop[nl++] = ev[x];
        loop[nl++] = G1;
    } else {
        int v = mv->cu == j ? i : mv->cu + 1;
        for (int x = v; x <= j; x++)
            loop[nl++] = ev[x];
        for (int x = i; x < v; x++)
            loop[nl++] = ev[x];
    }
    if (!hostM && mv->mx == -1) {
        memcpy(out + k, loop, (size_t)nl * sizeof(Ev));
        k += nl;
    }
    for (int pos = 0; pos < N; pos++) {
        if (pos >= i && pos <= j)
            continue;
        if (hostM && pos == mv->hp) {
            out[k++] = H1;
            memcpy(out + k, loop, (size_t)nl * sizeof(Ev));
            k += nl;
            out[k++] = H2;
        } else
            out[k++] = ev[pos];
        if (!hostM && pos == mv->mx) {
            memcpy(out + k, loop, (size_t)nl * sizeof(Ev));
            k += nl;
        }
    }
    free(loop);
    *Nout = k;
    return out;
}
/* The sequence after move mv, normalised (two segments of one trail that meet are merged).  Stops if the
   length is not the one the move promised. */
static Ev *apply_move(const Seq *q, const Move *mv, int *Nout) {
    int k;
    Ev *out = apply_ev(q->ev, q->N, mv, &k);
    i64 nlen = seq_length(out, k);
    if (nlen != q->len + mv->delta)
        DIE("internal error: move %s block %d..%d predicted %d, real %lld", MNAME[mv->type], mv->i, mv->j, mv->delta,
            nlen - q->len);
    *Nout = normalise(out, k);
    return out;
}
/* ---------- many moves from one scan
   A scan lists moves by positions of the sequence it scanned.  To apply several of them the events get identities
   (Ev.id; the two parts of a split host and a merged event get new ones), a move is kept as identities (Cand), and
   before it is applied it is resolved against the sequence as it is now and its change of length is computed again
   from that sequence (live_delta: the formulas of the scan, by positions).  It is applied iff it is still a move
   (resolve) and still improves.  After every single move the length is checked against the model.

   When the scanned delta stays exact.  Let Z(m) be the positions a move uses: its block with both neighbours
   [i-1, j+1], its host(s) {hp}, and both ends of the join of M it opens {mx, mx+1} (the join p -> q, the cut open join
   of the loop and a host inside the block lie in [i-1, j+1] already).  A move cuts the sequence only inside its Z.
   If Z(m1) and Z(m2) are disjoint, every stretch of Z(m2) is still a stretch of consecutive events after m1, with
   the same events and the same joins, the host of m2 is unsplit and on the same side of its block: m2 is the same
   move with the same delta, and the deltas add.  Moves whose Z overlap an applied one (nested blocks, a host inside
   another block, ...) are not thrown away: they are re-evaluated and applied if they still pay. */
typedef struct {
    short delta;
    unsigned char type, g, g2, mxk;
    int bi, bj, pi, qi, host, host2, cu, cun, mx, mxn, blen, ord;
    i64 a, a2;
} Cand;
/* identities of events (-1: none).  bi, bj: first and last event of the block; pi, qi: its neighbours at the scan;
   cu -> cun: the join of the loop that is cut open (-1: the closing join);
   mxk: 0 no join of M, 1 the join p -> q, 2 the join mx -> mxn (mxn -1: the end of the sequence), 3 the start of the sequence */
static Cand cand_of(const Seq *q, const Move *m, int ord) {
    const Ev *ev = q->ev;
    int N = q->N, ty = m->type;
    Cand c;
    memset(&c, 0, sizeof c);
    c.delta = m->delta;
    c.type = m->type;
    c.g = m->g;
    c.g2 = m->g2;
    c.a = m->a;
    c.a2 = m->a2;
    c.ord = ord;
    c.blen = m->j - m->i + 1;
    c.bi = ev[m->i].id;
    c.bj = ev[m->j].id;
    c.pi = m->i > 0 ? ev[m->i - 1].id : -1;
    c.qi = m->j + 1 < N ? ev[m->j + 1].id : -1;
    c.host = (ty <= M_C && m->hp >= 0) ? ev[m->hp].id : -1;
    c.host2 = ty == M_C ? ev[m->hp2].id : -1;
    c.cu = c.cun = c.mx = c.mxn = -1;
    if (ty == M_AI || ty == M_DI || ty == M_DN) {
        c.cu = ev[m->cu].id;
        c.cun = ev[m->cu + 1].id;
    }
    if (ty == M_BN || ty == M_DN)
        c.mxk = 1;
    else if (ty == M_BO || ty == M_DI || ty == M_DC) {
        if (m->mx < 0) {
            c.mxk = 3;
            c.mxn = ev[0].id;
        } else {
            c.mxk = 2;
            c.mx = ev[m->mx].id;
            c.mxn = m->mx + 1 < N ? ev[m->mx + 1].id : -1;
        }
    }
    return c;
}
/* Order in which the moves of a round are tried: best delta first, then the shorter block. */
static int cand_cmp(const void *x, const void *y) {
    const Cand *a = x, *b = y;
    if (a->delta != b->delta)
        return a->delta < b->delta ? -1 : 1;
    if (a->blen != b->blen)
        return a->blen < b->blen ? -1 : 1;
    return a->ord < b->ord ? -1 : a->ord > b->ord;
}
typedef struct {
    Ev *ev;
    int N;
    int *pos;
    int pcap;
    i64 len;
} Live;
/* Position of every event in the sequence that is being changed, by its identity. */
static void live_index(Live *lv) {
    if (next_id + 16 > lv->pcap) {
        lv->pcap = next_id + next_id / 4 + 4096;
        lv->pos = realloc(lv->pos, (size_t)lv->pcap * sizeof(int));
        if (!lv->pos)
            DIE("out of memory");
    }
    memset(lv->pos, 0xff, (size_t)lv->pcap * sizeof(int));
    for (int i = 0; i < lv->N; i++)
        lv->pos[lv->ev[i].id] = i;
}
/* A working copy of the sequence for a round of moves. */
static void live_init(Live *lv, const Ev *ev, int N) {
    memset(lv, 0, sizeof *lv);
    lv->ev = malloc(((size_t)N + 8) * sizeof(Ev));
    if (!lv->ev)
        DIE("out of memory");
    memcpy(lv->ev, ev, (size_t)N * sizeof(Ev));
    lv->N = N;
    lv->len = seq_length(ev, N);
    live_index(lv);
}
/* 1 if the cut at offset a with gap g lies inside event H, between two whole windows of it. */
static int cut_inside(const Ev *H, i64 a, int g) {
    const Trail *T = &TR[H->t];
    if (T->fixed)
        return 0;
    i64 R = T->R, rel = ((a - H->st) % R + R) % R;
    return rel + g + n <= H->l && is_win(T, a) && is_win(T, a + g);
}
/* the move of c in the sequence as it is now (positions); 0: it is not a move any more */
static int resolve(const Live *lv, const Cand *c, Move *m) {
    const Ev *ev = lv->ev;
    int N = lv->N;
    const int *pos = lv->pos;
#define POS_(id) ((id) >= 0 && (id) < lv->pcap ? pos[id] : -1)
    int i = POS_(c->bi), j = POS_(c->bj);
    if (i < 0 || j < 0 || i > j || (i == 0 && j == N - 1))
        return 0;
    memset(m, 0, sizeof *m);
    m->type = c->type;
    m->i = i;
    m->j = j;
    m->g = c->g;
    m->g2 = c->g2;
    m->a = c->a;
    m->a2 = c->a2;
    m->hp = m->hp2 = -1;
    m->cu = j;
    m->mx = -2;
    int ty = c->type, hostM = ty == M_AC || ty == M_AI || ty == M_C, hostC = ty == M_BO || ty == M_BN;
    if (hostM || hostC) {
        int hp = POS_(c->host);
        if (hp < 0 || !cut_inside(&ev[hp], c->a, c->g))
            return 0;
        if (ev[hp].skip >= 0 && !skiphost)
            return 0;
        if ((hp >= i && hp <= j) != hostC)
            return 0;
        m->hp = hp;
    }
    if ((hostC || ty == M_DI || ty == M_DN) && j == i)
        return 0;
    if (ty == M_C) {
        int h2 = POS_(c->host2);
        if (h2 < i || h2 > j || !cut_inside(&ev[h2], c->a2, c->g2))
            return 0;
        if (c->g != 3 || c->g2 != 3 ||
            (win_cyc(&TR[ev[m->hp].t], c->a + 3) >> 12) != (win_cyc(&TR[ev[h2].t], c->a2 + 3) >> 12))
            return 0;
        m->hp2 = h2;
    }
    if (c->cu >= 0) {
        int cp = POS_(c->cu);
        if (cp < i || cp >= j || ev[cp + 1].id != c->cun)
            return 0;
        m->cu = cp;
    }
    if (c->mxk == 1)
        m->mx = i - 1;
    else if (c->mxk == 2) {
        int t = POS_(c->mx);
        if (t < 0 || !(t < i - 1 || t > j))
            return 0;
        if (c->mxn >= 0 ? (t + 1 >= N || ev[t + 1].id != c->mxn) : t != N - 1)
            return 0;
        m->mx = t;
    } else if (c->mxk == 3) {
        if (i < 1 || ev[0].id != c->mxn)
            return 0;
        m->mx = -1;
    }
#undef POS_
    return 1;
}
/* change of the length by the move m (positions of lv), from the sequence itself */
static int live_delta(const Live *lv, const Move *m) {
    const Ev *ev = lv->ev;
    int N = lv->N, i = m->i, j = m->j, D = 3 - m->g;
    u64 Sw = 0, Ew = 0;
#define LJ_(x) (((x) < 0 || (x) + 1 >= N) ? 0 : dist(ev[x].e, ev[(x) + 1].s))
#define DE_(x, s_) ((x) < 0 ? 0 : dist(ev[x].e, (s_)))
#define DS_(e_, y) ((y) >= N ? 0 : dist((e_), ev[y].s))
    int dpq_ = (i - 1 < 0 || j + 1 >= N) ? 0 : dist(ev[i - 1].e, ev[j + 1].s), rem = dpq_ - LJ_(i - 1) - LJ_(j),
        cl = dist(ev[j].e, ev[i].s), f = cl + rem;
    if (m->hp >= 0) {
        const Trail *T = &TR[ev[m->hp].t];
        Sw = win_cyc(T, m->a + m->g);
        Ew = win_cyc(T, m->a);
    }
    switch (m->type) {
    case M_AC:
        return dist(ev[j].e, Sw) + D + dist(Ew, ev[i].s) + rem;
    case M_AI:
        return f + dist(ev[m->cu].e, Sw) + D + dist(Ew, ev[m->cu + 1].s) - LJ_(m->cu);
    case M_BO:
        return f + DE_(m->mx, Sw) + D + DS_(Ew, m->mx + 1) - LJ_(m->mx);
    case M_BN:
        return cl + DE_(i - 1, Sw) + D + DS_(Ew, j + 1) - LJ_(i - 1) - LJ_(j);
    case M_C:
        return f;
    case M_DI:
        return f - LJ_(m->cu) + DE_(m->mx, ev[m->cu + 1].s) + DS_(ev[m->cu].e, m->mx + 1) - LJ_(m->mx);
    case M_DN:
        return cl + DE_(i - 1, ev[m->cu + 1].s) + DS_(ev[m->cu].e, j + 1) - LJ_(m->cu) - LJ_(i - 1) - LJ_(j);
    case M_DC:
        return rem + DE_(m->mx, ev[i].s) + DS_(ev[j].e, m->mx + 1) - LJ_(m->mx);
    }
#undef LJ_
#undef DE_
#undef DS_
    return BIG;
}
typedef struct {
    int listed, applied, exact, changed, invalid, notpay, mismatch;
    i64 gain;
    double sec;
} MStat;
/* applies the candidates c[0 .. nc-1] in this order to lv; a candidate must change the length by at most maxd
   (need0 = 0: it must improve; 1: change the length by exactly 0, the neutral moves; 2: by at most the threshold, a test).  done[k] = 1 for those applied (if not NULL);
   ids0 / ids1 (if not NULL): the range of new identities each applied move made */
static void multi_apply(Live *lv, const Cand *c, int nc, int need0, char *done, int *ids0, int *ids1, MStat *ms,
                        int verbose) {
    double t0 = wall();
    memset(ms, 0, sizeof *ms);
    ms->listed = nc;
    for (int k = 0; k < nc; k++) {
        Move m;
        if (done)
            done[k] = 0;
        if (!resolve(lv, &c[k], &m)) {
            ms->invalid++;
            continue;
        }
        int d = live_delta(lv, &m);
        if (need0 == 2 ? d > thr : need0 ? d != 0 : d >= 0) {
            ms->notpay++;
            continue;
        }
        int id0 = next_id, k1;
        m.delta = (short)d;
        Ev *out = apply_ev(lv->ev, lv->N, &m, &k1);
        i64 nlen = seq_length(out, k1);
        if (nlen != lv->len + d) {
            ms->mismatch++;
            free(out);
            next_id = id0;
            printf("multi: %s predicted %d, real %lld: not applied\n", MNAME[m.type], d, nlen - lv->len);
            continue;
        }
        int k2 = normalise(out, k1);
        if (k2 != k1)
            nlen = seq_length(out, k2);
        if (verbose)
            printf("  applied %-9s delta %d (scanned %d)  block %d..%d (%d events)%s\n", MNAME[m.type], d, c[k].delta,
                   m.i, m.j, m.j - m.i + 1, nlen != lv->len + d ? "  + a port closed again" : "");
        ms->applied++;
        if (d == c[k].delta)
            ms->exact++;
        else
            ms->changed++;
        ms->gain += lv->len - nlen;
        free(lv->ev);
        lv->ev = out;
        lv->N = k2;
        lv->len = nlen;
        live_index(lv);
        if (done)
            done[k] = 1;
        if (ids0) {
            ids0[k] = id0;
            ids1[k] = next_id;
        }
    }
    ms->sec = wall() - t0;
}
/* no copy of the word in memory */
static void write_word_stream(const Ev *ev, i64 N, const char *path) {
    FILE *f = fopen(path, "wb");
    if (!f)
        DIE("cannot write %s", path);
    size_t cap = 1 << 22, ob = 0;
    char *out = malloc(cap);
    i64 total = 0, expect = seq_length(ev, N);
    u64 tail = 0;
    for (i64 i = 0; i < N; i++) {
        const Ev *x = &ev[i];
        i64 skip = i ? h - dist(tail, x->s) : 0;
        if (x->kind == EV_PIECE) {
            for (i64 r = skip; r < x->l; r++) {
                out[ob++] = AL[W[PS[x->pk] + r]];
                if (ob == cap) {
                    fwrite(out, 1, ob, f);
                    ob = 0;
                }
            }
        } else {
            const Trail *t = &TR[x->t];
            i64 R = t->R, p = (x->st + skip) % R;
            for (i64 r = skip; r < x->l; r++) {
                out[ob++] = AL[t->c[p]];
                if (++p == R)
                    p = 0;
                if (ob == cap) {
                    fwrite(out, 1, ob, f);
                    ob = 0;
                }
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
/* the plan, written beside and moved into place */
static void checkpoint(const Ev *ev, int N, const char *path) {
    char tmp[4200];
    snprintf(tmp, sizeof tmp, "%s.partial", path);
    write_plan(ev, N, tmp);
    remove(path);
    if (rename(tmp, path))
        DIE("cannot rename %s to %s", tmp, path);
}
/* the positions a move uses, as up to four intervals; 1 if they meet one of the nz intervals in zl / zh */
static int zones_of(const Move *m, int N, int *lo, int *hi) {
    int k = 0;
    lo[k] = m->i - 1;
    hi[k] = m->j + 1;
    k++;
    if (m->hp >= 0) {
        lo[k] = hi[k] = m->hp;
        k++;
    }
    if (m->hp2 >= 0 && m->type == M_C) {
        lo[k] = hi[k] = m->hp2;
        k++;
    }
    if ((m->type == M_BO || m->type == M_DI || m->type == M_DC)) {
        lo[k] = m->mx;
        hi[k] = m->mx + 1;
        k++;
    }
    (void)N;
    return k;
}
/* Prints one move in words. */
static void print_move(const Seq *q, const Move *m, i64 idx) {
    const Ev *ev = q->ev;
    int N = q->N;
    printf("  #%lld %-9s delta %d  block %d..%d (%d events; joins in %d, out %d, p->q %d, close %d, f %d)", idx,
           MNAME[m->type], m->delta, m->i, m->j, m->j - m->i + 1, Jc(q, m->i - 1), Jc(q, m->j), dpq(q, m->i, m->j),
           dist(q->E[m->j], q->S[m->i]), dist(q->E[m->j], q->S[m->i]) + rem_(q, m->i, m->j));
    if (m->hp >= 0)
        printf("  host event %d (trail %u, R %lld) cut at %lld gap %d", m->hp, ev[m->hp].t, TR[ev[m->hp].t].R, m->a,
               m->g);
    if (m->type == M_C)
        printf("  second host event %d (trail %u) cut at %lld", m->hp2, ev[m->hp2].t, m->a2);
    if (m->type == M_AI || m->type == M_DI || m->type == M_DN)
        printf("  loop opened at join %d->%d (cost %d)", m->cu, m->cu + 1, q->J[m->cu]);
    if (m->type == M_BO || m->type == M_DI || m->type == M_DC)
        printf("  into join %d->%d (cost %d)", m->mx, m->mx + 1, Jc(q, m->mx));
    printf("\n");
    (void)N;
}
/* Prints the counts of the moves found, by kind and delta. */
static void print_summary(const Seq *q, const ML *ml, const ScanStat *st) {
    printf(
        "scan: cuts gap3 %lld gap2 %lld gap1 %lld; usable as ports (inside a host event) gap3 %lld gap2 %lld gap1 %lld; in skip events (not used) %lld; index hits %lld; %.1fs\n",
        st->cuts[3], st->cuts[2], st->cuts[1], st->hostcuts[3], st->hostcuts[2], st->hostcuts[1], st->skipcuts,
        st->hits, st->sec);
    printf("scan: inner gap-3 vertices %lld, pairs with equal h-word in two events %lld, in one event %lld\n", st->vtx,
           st->vshared, st->vsame);
    {
        i64 na[20] = {0}, nz[20] = {0}, ng[20][4];
        memset(ng, 0, sizeof ng);
        for (int x = 0; x + 1 < q->N; x++) {
            int c = q->J[x];
            if (c < 0)
                continue;
            na[c]++;
            const int *z = st->zc + 4 * x;
            if (z[1] + z[2] + z[3])
                nz[c]++;
            for (int g = 1; g <= 3; g++)
                if (z[g])
                    ng[c][g]++;
        }
        printf(
            "ports on the shortest connector of a join (cuts of other events), by cost of the join: cost:joins/with a port (gap3,gap2,gap1):");
        for (int c = 0; c <= h; c++)
            if (na[c])
                printf(" %d:%lld/%lld(%lld,%lld,%lld)", c, na[c], nz[c], ng[c][3], ng[c][2], ng[c][1]);
        printf("%c", 10);
        /* does the connector of a join hold h+1 / h+2 different letters in a row at all (a gap-2 / gap-1 cut can only sit there)? */
        i64 w0[20] = {0}, w1[20] = {0}, w2[20] = {0}, rot[20] = {0};
        for (int x = 0; x + 1 < q->N; x++) {
            int c = q->J[x];
            if (c <= 0)
                continue;
            int s[40], L2 = h + c, a0 = 0, a1 = 0, a2 = 0, pr = 1;
            for (int k = 0; k < h; k++)
                s[k] = (int)((q->E[x] >> (4 * (h - 1 - k))) & 15);
            for (int k = 0; k < c; k++)
                s[h + k] = (int)(((q->S[x + 1] >> 12) >> (4 * (c - 1 - k))) & 15);
            for (int o = 0; o + h + 1 <= L2; o++) {
                int u = 0, ok = 1;
                for (int k = 0; k < h + 1; k++) {
                    if (u >> s[o + k] & 1)
                        ok = 0;
                    u |= 1 << s[o + k];
                }
                a1 |= ok;
            }
            for (int o = 0; o + h + 2 <= L2; o++) {
                int u = 0, ok = 1;
                for (int k = 0; k < h + 2; k++) {
                    if (u >> s[o + k] & 1)
                        ok = 0;
                    u |= 1 << s[o + k];
                }
                a2 |= ok;
            }
            for (int o = 1; o < c; o++) {
                int u = 0, ok = 1;
                for (int k = 0; k < h; k++) {
                    if (u >> s[o + k] & 1)
                        ok = 0;
                    u |= 1 << s[o + k];
                }
                a0 |= ok;
            }
            for (int k = 0; k < c; k++)
                if (s[h + k] != s[k])
                    pr = 0;
            w0[c] += a0;
            w1[c] += a1;
            w2[c] += a2;
            rot[c] += pr;
        }
        printf(
            "joins whose connector has room for a port: an inner h-word of different letters (gap-3 cut) / h+1 different letters in a row (gap 2) / h+2 (gap 1); and joins that only rotate the h-word; by cost:");
        for (int c = 1; c <= h; c++)
            if (na[c])
                printf(" %d:%lld/%lld/%lld;rot %lld", c, w0[c], w1[c], w2[c], rot[c]);
        printf("%c", 10);
    }
    printf("moves with delta <= %d: %lld%s\n", thr, ml->n, ml->over ? " (list truncated)" : "");
    printf("  %-9s %8s %8s %8s %8s %8s %8s %8s   (delta)\n", "type", "<=-3", "-2", "-1", "0", "1", "2", "3");
    for (int a = 0; a < M_NT; a++) {
        printf("  %-9s", MNAME[a]);
        for (int d = 0; d < 7; d++)
            printf(" %8lld", ml->cnt[a][d]);
        printf("   %s\n", MDESC[a]);
    }
    (void)q;
}
/* --watch: every block that can be cut out and closed with a gain g = -f > 0 (the "detaching exchanges"), and the
   cheapest way found to join the loop to the rest again, by kind of move: cost = delta + g, to be compared with g */
static void watch_report(const Seq *q, const ML *ml) {
    int N = q->N;
    i64 nb = 0;
    printf(
        "detachable blocks (f < 0) and the cheapest re-attachment found with delta <= %d (cost = letters paid to join the loop again; the place it came from costs g):%c",
        thr, 10);
    for (int i = 0; i < N; i++)
        for (int j = i; j < N; j++) {
            if (i == 0 && j == N - 1)
                continue;
            int f = dist(q->E[j], q->S[i]) + rem_(q, i, j);
            if (f >= 0)
                continue;
            int best[M_NT];
            for (int a = 0; a < M_NT; a++)
                best[a] = BIG;
            for (i64 k = 0; k < ml->n; k++) {
                const Move *m = &ml->m[k];
                if (m->i == i && m->j == j && m->delta < best[m->type])
                    best[m->type] = m->delta;
            }
            printf(
                "  block %d..%d (%d events) joins in %d, out %d, p->q %d, close %d: gain g = %d; re-attachment cost:",
                i, j, j - i + 1, Jc(q, i - 1), Jc(q, j), dpq(q, i, j), dist(q->E[j], q->S[i]), -f);
            for (int a = 0; a < M_NT; a++) {
                if (best[a] < BIG)
                    printf(" %s %d", MNAME[a], best[a] - f);
                else
                    printf(" %s -", MNAME[a]);
            }
            printf("%c", 10);
            nb++;
        }
    printf("detachable blocks: %lld%c", nb, 10);
}
/* duplicated windows (a permutation that two places of the trails hold).  In the wide model two events that hold
   the two copies could be merged there at no cost (the analogue of a shared gap-3 vertex), so count where the copies lie */
typedef struct {
    u64 r;
    int hp;
    u32 t;
    i64 pos;
} DupW;
/* Order of the duplicated windows: by permutation, then by hp, then by position. */
static int dupw_cmp(const void *x, const void *y) {
    const DupW *a = x, *b = y;
    return a->r < b->r       ? -1
           : a->r > b->r     ? 1
           : a->hp < b->hp   ? -1
           : a->hp > b->hp   ? 1
           : a->pos < b->pos ? -1
                             : a->pos > b->pos;
}
/* Prints where the permutations that occur twice lie (--dups). */
static void dup_stats(const Seq *q) {
    if (n > 12)
        return;
    u64 NF = fact[n];
    u64 *seen = calloc((size_t)(NF >> 6) + 1, 8), *dup = calloc((size_t)(NF >> 6) + 1, 8);
    if (!seen || !dup)
        DIE("out of memory");
    i64 *wp = malloc((size_t)(maxR + 8) * 8);
    DupW *d = NULL;
    i64 nd = 0, cap = 0;
    for (int pass = 0; pass < 2; pass++)
        for (i64 t = 0; t < NT; t++) {
            const Trail *T = &TR[t];
            if (T->fixed)
                continue;
            i64 m = trail_windows(T, wp);
            for (i64 k = 0; k < m; k++) {
                u64 r = rank_cyc(T, wp[k]), bit = 1ULL << (r & 63);
                if (!pass) {
                    if (seen[r >> 6] & bit)
                        dup[r >> 6] |= bit;
                    seen[r >> 6] |= bit;
                    continue;
                }
                if (!(dup[r >> 6] & bit))
                    continue;
                int hp = -1;
                i64 R = T->R;
                for (int pos = q->thead[t]; pos >= 0; pos = q->tnx[pos]) {
                    const Ev *x = &q->ev[pos];
                    i64 rel = ((wp[k] - x->st) % R + R) % R;
                    if (rel + n <= x->l) {
                        hp = pos;
                        break;
                    }
                }
                if (nd == cap) {
                    cap = cap ? cap * 2 : 4096;
                    d = realloc(d, (size_t)cap * sizeof(DupW));
                }
                d[nd].r = r;
                d[nd].hp = hp;
                d[nd].t = (u32)t;
                d[nd].pos = wp[k];
                nd++;
            }
        }
    qsort(d, (size_t)nd, sizeof(DupW), dupw_cmp);
    i64 perms = 0, same = 0, two = 0, skipped = 0, sametrail = 0, near = 0, split = 0, neg = 0;
    for (i64 a = 0; a < nd;) {
        i64 b = a;
        while (b < nd && d[b].r == d[a].r)
            b++;
        perms++;
        if (b - a == 2) {
            const DupW *x = &d[a], *y = &d[a + 1];
            if (x->t == y->t) {
                sametrail++;
                i64 R = TR[x->t].R, dd = ((y->pos - x->pos) % R + R) % R;
                if (dd > R - dd)
                    dd = R - dd;
                if (dd <= 2 * n)
                    near++;
            }
            if (x->hp < 0 || y->hp < 0)
                skipped++;
            else if (x->hp == y->hp)
                same++;
            else {
                two++; /* does a detachable block separate them? */
                int N = q->N, lo = x->hp < y->hp ? x->hp : y->hp, hi = x->hp < y->hp ? y->hp : x->hp, any = 0,
                    anyneg = 0;
                for (int i = 0; i < N && !anyneg; i++)
                    for (int j = i; j < N; j++) {
                        if ((i == 0 && j == N - 1) || ((lo >= i && lo <= j) == (hi >= i && hi <= j)))
                            continue;
                        if (N > 20000 && j - i + 1 > LMAX)
                            break;
                        int f = dist(q->E[j], q->S[i]) + rem_(q, i, j);
                        if (f <= 0)
                            any = 1;
                        if (f < 0) {
                            anyneg = 1;
                            break;
                        }
                    }
                split += any;
                neg += anyneg;
            }
        }
        a = b;
    }
    printf(
        "duplicated windows: %lld permutations; both copies in one trail %lld (within %d letters of each other: %lld); in the sequence: both in one event %lld, in two events %lld, one copy not written (skip) %lld%c",
        perms, sametrail, 2 * n, near, same, two, skipped, 10);
    printf(
        "duplicated windows whose copies lie in two events: %lld are separated by a block with f <= 0, %lld by a block with f < 0%c",
        split, neg, 10);
    free(seen);
    free(dup);
    free(wp);
    free(d);
}
/* Prints how many blocks can be closed into a loop at which cost. */
static void block_stats(const Seq *q) {
    int N = q->N;
    i64 hist[64] = {0}, nb = 0, byc[20] = {0}, f0byc[20] = {0};
    int mn = BIG;
    for (int i = 0; i < N; i++)
        for (int m = 1; m <= LMAX; m++) {
            int f = q->F[(i64)i * LMAX + m - 1];
            if (f >= BIG)
                continue;
            nb++;
            if (f < mn)
                mn = f;
            hist[f + 20 < 0 ? 0 : f + 20 > 63 ? 63 : f + 20]++;
            int c = dist(q->E[i + m - 1], q->S[i]) + 2;
            byc[c]++;
            if (f <= 0)
                f0byc[c]++;
        }
    printf("blocks (1..%d events): %lld; f(Y) = close + d(p,q) - in - out: min %d; histogram", LMAX, nb, mn);
    for (int f = -20; f <= 43; f++)
        if (hist[f + 20])
            printf(" %d:%lld", f, hist[f + 20]);
    printf("\nblocks by cost of the closing connector (all / with f <= 0):");
    for (int c = MINW; c <= h; c++)
        printf(" %d:%lld/%lld", c, byc[c + 2], f0byc[c + 2]);
    printf("\n");
    {
        int cl = dist(q->E[N - 1], q->S[0]), mj = -9;
        for (int x = 0; x + 1 < N; x++)
            if (q->J[x] > mj)
                mj = q->J[x];
        printf(
            "the sequence as a cycle: joining its end to its start costs %d, its most expensive join %d (starting the word after that join would change the length by %d)%c",
            cl, mj, cl - mj, 10);
    }
    if (N <= 20000) { /* all lengths */
        i64 one0 = 0, oneneg = 0, s0 = 0, sneg = 0, l0 = 0, lneg = 0, tot = 0;
        int mnl = BIG;
        for (int i = 0; i < N; i++)
            for (int j = i; j < N; j++) {
                if (i == 0 && j == N - 1)
                    continue;
                int f = dist(q->E[j], q->S[i]) + rem_(q, i, j);
                tot++;
                if (j > i && f < mnl)
                    mnl = f;
                if (f > 0)
                    continue;
                if (j == i) {
                    one0++;
                    oneneg += f < 0;
                } else if (j - i + 1 <= LMAX) {
                    s0++;
                    sneg += f < 0;
                } else {
                    l0++;
                    lneg += f < 0;
                }
            }
        printf(
            "blocks of any length: %lld; with f <= 0 (of which f < 0): single events %lld (%lld), 2..%d events %lld (%lld), longer %lld (%lld); min f over blocks of 2+ events %d\n",
            tot, one0, oneneg, LMAX, s0, sneg, l0, lneg, mnl);
    }
}
/* Prints the make-up of a sequence: kinds of events, trails written in several events, joins by cost. */
static void seq_stats(const Ev *ev, i64 N) {
    i64 hist[20] = {0}, runs = 1, segs = 0, pieces = 0, opts = 0, skips = 0;
    int *cnt = calloc((size_t)NT + 1, sizeof(int));
    i64 multi = 0, multi3 = 0;
    for (i64 i = 0; i < N; i++) {
        if (ev[i].kind == EV_SEG)
            segs++;
        else if (ev[i].kind == EV_PIECE)
            pieces++;
        else
            opts++;
        if (ev[i].skip >= 0)
            skips++;
        cnt[ev[i].t]++;
        if (i + 1 < N) {
            int d = dist(ev[i].e, ev[i + 1].s);
            hist[d + 2]++;
            if (d >= 2)
                runs++;
        }
    }
    for (i64 t = 0; t < NT; t++) {
        if (cnt[t] >= 2)
            multi++;
        if (cnt[t] >= 3)
            multi3++;
    }
    printf(
        "sequence: %lld events (P %lld, O %lld, S %lld; skip openings %lld), trails in 2+ events %lld, in 3+ %lld, runs %lld, length %lld; joins by cost:",
        N, pieces, opts, segs, skips, multi, multi3, runs, seq_length(ev, N));
    for (int d = -2; d <= h; d++)
        if (hist[d + 2])
            printf(" %d:%lld", d, hist[d + 2]);
    printf("\n");
    free(cnt);
}

/* Reads the options, loads the base word and the plan as trailsearch.c does, then scans; with --greedy it
   makes the moves round by round, otherwise it prints, lists, verifies or applies single moves. */
int main(int argc, char **argv) {
    if (argc < 2)
        DIE("usage: loopscan BASE.txt --plan PLAN --only PABD --nogap1 --threads T --quiet --greedy [--neutral] --planout OUT.plan --out OUT.txt   (see the comment at the top of loopscan.c)");
    const char *plan_in = NULL, *list = NULL, *outw = NULL;
    i64 top = 20, verify = 0, apply_idx = -1, probe = 0;
    int greedy = 0, greedy_port = 0, do_brute = 0, walk = 0, single = 0, maxrounds = -1, neutral = 0, nbatch = 16,
        stress = 0;
    const char *planout = NULL;
    u64 wseed = 88172645463325252ULL;
    for (int a = 2; a < argc; a++) {
        if (!strcmp(argv[a], "--plan") && a + 1 < argc)
            plan_in = argv[++a];
        else if (!strcmp(argv[a], "--lmax") && a + 1 < argc)
            LMAX = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--klev") && a + 1 < argc)
            KL = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--thr") && a + 1 < argc)
            thr = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--threads") && a + 1 < argc)
            NTHR = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--top") && a + 1 < argc)
            top = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--list") && a + 1 < argc)
            list = argv[++a];
        else if (!strcmp(argv[a], "--verify") && a + 1 < argc)
            verify = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--apply") && a + 1 < argc)
            apply_idx = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--probe") && a + 1 < argc)
            probe = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--out") && a + 1 < argc)
            outw = argv[++a];
        else if (!strcmp(argv[a], "--only") && a + 1 < argc) {
            strncpy(only, argv[++a], 31);
        } else if (!strcmp(argv[a], "--maxlist") && a + 1 < argc)
            ML_MAX = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--nogap1"))
            use_gap1 = 0;
        else if (!strcmp(argv[a], "--skiphost"))
            skiphost = 1;
        else if (!strcmp(argv[a], "--noD"))
            useD = 0;
        else if (!strcmp(argv[a], "--nolong"))
            longblocks = 0;
        else if (!strcmp(argv[a], "--brute"))
            do_brute = 1;
        else if (!strcmp(argv[a], "--wide"))
            wide = 1;
        else if (!strcmp(argv[a], "--watch"))
            watch = 1;
        else if (!strcmp(argv[a], "--dups"))
            dupstat = 1;
        else if (!strcmp(argv[a], "--greedy"))
            greedy = 1;
        else if (!strcmp(argv[a], "--single"))
            greedy = single = 1;
        else if (!strcmp(argv[a], "--stress"))
            greedy = stress = 1;
        else if (!strcmp(argv[a], "--neutral"))
            greedy = neutral = 1;
        else if (!strcmp(argv[a], "--maxrounds") && a + 1 < argc)
            maxrounds = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--nbatch") && a + 1 < argc)
            nbatch = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--planout") && a + 1 < argc)
            planout = argv[++a];
        else if (!strcmp(argv[a], "--walk") && a + 1 < argc)
            walk = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--seed") && a + 1 < argc)
            wseed ^= hmix(strtoull(argv[++a], 0, 10) + 1);
        else if (!strcmp(argv[a], "--greedy-ports"))
            greedy = greedy_port = 1;
        else if (!strcmp(argv[a], "--quiet"))
            quiet = 1;
        else
            DIE("unknown option %s", argv[a]);
    }
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
    if (!LMAX)
        LMAX = 2 * h;
    if (LMAX > 64)
        LMAX = 64;
    if (KL > h - 2)
        KL = h - 2;
    OVMAX = wide ? n - 1 : h;
    NLEV = KL + 1 + OVMAX - h;
    MINW = h - OVMAX;
    for (int k = 0; k <= 16; k++)
        HMASK[k] = k >= 16 ? ~0ULL : ((1ULL << (4 * k)) - 1);
    fact[0] = 1;
    for (int i = 1; i < 17; i++)
        fact[i] = fact[i - 1] * i;
    /* permutation windows and pieces (split at gaps >= 4), exactly as trailsearch.c */
    {
        int cnt[16] = {0}, distinct = 0;
        i64 cap = 1 << 16, prev = -1, pstart = -1;
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
    }
    char *closed = calloc((size_t)NP, 1);
    trail_of_piece = malloc(NP * 8);
    POFF = calloc((size_t)NP, 8);
    for (i64 k = 0; k < NP; k++)
        trail_of_piece[k] = -1;
    TR = calloc((size_t)NP + 1, sizeof(Trail));
    NT = 0;
    for (i64 k = 0; k < NP; k++)
        if (closes(k, 0)) {
            closed[k] = 1;
            trail_of_piece[k] = NT;
            TR[NT].c = W + PS[k];
            TR[NT].R = PL[k] - h;
            NT++;
        }
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
                if (ex) {
                    closed[k] = 1;
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
                    POFF[chain[b]] = q;
                    q += PL[chain[b]] - h;
                    trail_of_piece[chain[b]] = NT;
                }
                TR[NT].c = c;
                TR[NT].R = R;
                if (tw != hwd) {
                    i64 lastp = chain[nc - 1];
                    memcpy(c + q, W + PS[lastp] + PL[lastp] - h, (size_t)h);
                    TR[NT].fixed = 1;
                }
                NT++;
            }
        free(op);
        free(used);
        free(haspred);
        free(chain);
    }
    i64 sumR = 0, nfixed = 0;
    maxR = 0;
    for (i64 t = 0; t < NT; t++) {
        sumR += TR[t].R;
        if (TR[t].R > maxR)
            maxR = TR[t].R;
        nfixed += TR[t].fixed;
    }
    printf("n=%d L=%lld pieces %lld trails %lld (open paths %lld) sum R %lld max R %lld (%.1fs)\n", n, L, NP, NT,
           nfixed, sumR, maxR, wall() - t00);
    /* the sequence */
    i64 cap = NP * 2 + 1024;
    Ev *ev = malloc(cap * sizeof(Ev));
    i64 N = 0;
    if (!plan_in) {
        for (i64 k = 0; k < NP; k++)
            ev[N++] = piece_event(k);
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
                x = piece_event(k);
            } else if (c[0] == 'O') {
                u32 t;
                i64 st;
                int g, g1;
                if (fscanf(f, "%u %lld %d %d", &t, &st, &g, &g1) != 4 || t >= NT)
                    DIE("bad plan");
                if (TR[t].fixed || !is_win(&TR[t], st) || !is_win(&TR[t], st - g) ||
                    (g1 && !is_win(&TR[t], st - g + g1)))
                    DIE("plan: O %u %lld %d %d is not an opening", t, st, g, g1);
                x = opt_event(t, st, g, g1);
            } else {
                u32 t;
                i64 st, l;
                if (fscanf(f, "%u %lld %lld", &t, &st, &l) != 3 || t >= NT)
                    DIE("bad plan");
                x = seg_event(t, st, l);
            }
            if (N + 2 >= cap) {
                cap *= 2;
                ev = realloc(ev, cap * sizeof(Ev));
            }
            ev[N++] = x;
        }
        fclose(f);
    }
    printf("model length of the sequence: %lld (%lld events)\n", seq_length(ev, N), N);
    seq_stats(ev, N);
    printf(
        "settings: %s, blocks up to %d events, joins of cost %d..%d indexed, gap-1 ports %s, threshold %d, %d threads\n",
        wide ? "WIDE model (overlaps up to n-1)" : "model of trailsearch (overlaps up to h)", LMAX, MINW, KL,
        use_gap1 ? "on" : "off", thr, NTHR);
    fflush(stdout);

    for (i64 i = 0; i < N; i++)
        ev[i].id = (int)i;
    next_id = (int)N;
    if (nbatch < 1)
        nbatch = 1;
    Seq q;
    ML ml;
    ScanStat st;
    int Ncur = (int)N;
    Ev *cur = ev;
    int round = 0;
    if (greedy) {
        /* rounds: scan; apply every improving move of the list that is still a move and still improves when its turn
           comes (best first); write the plan; scan again.  With --neutral, when nothing improves: batches of neutral
           port moves, each followed by a scan; a batch is kept only if improving moves appear after it */
        int round = 0;
        i64 len_start = seq_length(cur, Ncur);
        double tg = wall();
        for (;;) {
            if (maxrounds >= 0 && round >= maxrounds) {
                printf("stopped after %d rounds (--maxrounds)\n", round);
                break;
            }
            seq_make(&q, cur, Ncur);
            if (!round && !quiet)
                block_stats(&q);
            scan(&q, &ml, &st);
            round++;
            if (!quiet) {
                print_summary(&q, &ml, &st);
                for (i64 k = 0; k < ml.n && k < top; k++)
                    print_move(&q, &ml.m[k], k);
            }
            int nc = 0;
            Cand *cd = malloc(((size_t)ml.n + 1) * sizeof(Cand));
            if (stress) { /* test of the machinery: every listed move, whatever its sign, as long as it is still a move */
                for (i64 k = 0; k < ml.n; k++)
                    cd[nc++] = cand_of(&q, &ml.m[k], (int)k);
                Live lv;
                live_init(&lv, cur, Ncur);
                MStat ms;
                i64 l0 = lv.len;
                multi_apply(&lv, cd, nc, 2, NULL, NULL, NULL, &ms, 0);
                printf(
                    "stress: length %lld -> %lld  (moves listed %d, applied %d: %d with the scanned delta, %d re-evaluated; not applied: %d no longer moves, %d above the threshold, %d mismatches; apply %.1fs)%c",
                    l0, lv.len, nc, ms.applied, ms.exact, ms.changed, ms.invalid, ms.notpay, ms.mismatch, ms.sec, 10);
                cur = lv.ev;
                Ncur = lv.N;
                free(cd);
                break;
            }
            for (i64 k = 0; k < ml.n && ml.m[k].delta < 0; k++)
                if (!greedy_port || ml.m[k].type <= M_C)
                    cd[nc++] = cand_of(&q, &ml.m[k], (int)k);
            if (nc) {
                qsort(cd, (size_t)nc, sizeof(Cand), cand_cmp);
                Live lv;
                live_init(&lv, cur, Ncur);
                MStat ms;
                i64 l0 = lv.len;
                multi_apply(&lv, cd, single ? 1 : nc, 0, NULL, NULL, NULL, &ms, !quiet);
                printf(
                    "round %d: length %lld -> %lld  (improving moves listed %d, applied %d: %d with the scanned delta, %d re-evaluated; not applied: %d no longer moves, %d no longer improving, %d mismatches; scan %.1fs, apply %.1fs, total %.0fs)\n",
                    round, l0, lv.len, nc, ms.applied, ms.exact, ms.changed, ms.invalid, ms.notpay, ms.mismatch, st.sec,
                    ms.sec, wall() - t00);
                fflush(stdout);
                if (!ms.applied)
                    DIE("internal error: no listed move could be applied");
                if (cur != ev)
                    free(cur);
                cur = lv.ev;
                Ncur = lv.N;
                free(lv.pos);
                if (planout)
                    checkpoint(cur, Ncur, planout);
                seq_free(&q);
                free(ml.m);
                free(st.zc);
                free(cd);
                continue;
            }
            free(cd);
            if (!neutral) {
                printf("round %d: length %lld, no improving move (scan %.1fs, total %.0fs)\n", round, q.len, st.sec,
                       wall() - t00);
                seq_free(&q);
                free(ml.m);
                free(st.zc);
                break;
            }
            /* ---- neutral port moves */
            int nn = 0;
            Cand *ncd = malloc(((size_t)ml.n + 1) * sizeof(Cand));
            Move *nm = malloc(((size_t)ml.n + 1) * sizeof(Move));
            for (i64 k = 0; k < ml.n; k++)
                if (ml.m[k].delta == 0 && ml.m[k].type <= M_C) {
                    nm[nn] = ml.m[k];
                    ncd[nn] = cand_of(&q, &ml.m[k], (int)k);
                    nn++;
                }
            printf("round %d: length %lld, no improving move; %d neutral port moves listed (scan %.1fs, total %.0fs)\n",
                   round, q.len, nn, st.sec, wall() - t00);
            fflush(stdout);
            char *tried = calloc((size_t)nn + 1, 1);
            int found = 0, ntried = 0;
            int *zl = malloc(((size_t)nbatch * 4 + 4) * sizeof(int)),
                *zh = malloc(((size_t)nbatch * 4 + 4) * sizeof(int));
            Cand *bc = malloc(((size_t)nbatch + 1) * sizeof(Cand));
            char *done = malloc((size_t)nbatch + 1), *used = malloc((size_t)nbatch + 1);
            int *ids0 = malloc(((size_t)nbatch + 1) * sizeof(int)), *ids1 = malloc(((size_t)nbatch + 1) * sizeof(int));
            while (!found && ntried < nn) {
                if (maxrounds >= 0 && round >= maxrounds)
                    break;
                int nb = 0, nz = 0; /* a batch of untried moves on disjoint positions */
                for (int k = 0; k < nn && nb < nbatch; k++) {
                    if (tried[k])
                        continue;
                    int lo[4], hi[4], m4 = zones_of(&nm[k], q.N, lo, hi), clash = 0;
                    for (int a = 0; a < m4 && !clash; a++)
                        for (int b = 0; b < nz; b++)
                            if (lo[a] <= zh[b] && zl[b] <= hi[a]) {
                                clash = 1;
                                break;
                            }
                    if (clash)
                        continue;
                    for (int a = 0; a < m4; a++) {
                        zl[nz] = lo[a];
                        zh[nz] = hi[a];
                        nz++;
                    }
                    bc[nb++] = ncd[k];
                    tried[k] = 1;
                    ntried++;
                }
                if (!nb)
                    break;
                Live lv;
                live_init(&lv, cur, Ncur);
                MStat ms;
                multi_apply(&lv, bc, nb, 1, done, ids0, ids1, &ms, 0);
                Seq q1;
                ML ml1;
                ScanStat st1;
                seq_make(&q1, lv.ev, lv.N);
                scan(&q1, &ml1, &st1);
                round++;
                int ni = 0;
                for (i64 k = 0; k < ml1.n && ml1.m[k].delta < 0; k++)
                    if (!greedy_port || ml1.m[k].type <= M_C)
                        ni++;
                printf(
                    "round %d: %d neutral port moves applied on trial (%d of %d tried), improving moves after them: %d (scan %.1fs, total %.0fs)\n",
                    round, ms.applied, ntried, nn, ni, st1.sec, wall() - t00);
                fflush(stdout);
                if (!ni) {
                    seq_free(&q1);
                    free(ml1.m);
                    free(st1.zc);
                    free(lv.ev);
                    free(lv.pos);
                    continue;
                }
                /* which moves of the batch do the improving moves touch?  (identities at the changed joins and the new events) */
                int nused = 0;
                for (int b = 0; b < nb; b++) {
                    used[b] = 0;
                    if (!done[b])
                        continue;
                    int A[8] = {bc[b].pi, bc[b].bi, bc[b].bj, bc[b].qi, bc[b].cu, bc[b].cun, bc[b].mx, bc[b].mxn};
                    for (i64 k = 0; k < ml1.n && ml1.m[k].delta < 0 && !used[b]; k++) {
                        Cand c1 = cand_of(&q1, &ml1.m[k], 0);
                        int Rr[10] = {c1.pi, c1.bi, c1.bj, c1.qi, c1.host, c1.host2, c1.cu, c1.cun, c1.mx, c1.mxn};
                        for (int u = 0; u < 10 && !used[b]; u++) {
                            if (Rr[u] < 0)
                                continue;
                            if (Rr[u] >= ids0[b] && Rr[u] < ids1[b])
                                used[b] = 1;
                            for (int v = 0; v < 8; v++)
                                if (A[v] == Rr[u])
                                    used[b] = 1;
                        }
                    }
                    nused += used[b];
                }
                if (nused && nused < ms.applied) { /* again with the touched ones only */
                    Cand *uc = malloc(((size_t)nused + 1) * sizeof(Cand));
                    int nu = 0;
                    for (int b = 0; b < nb; b++)
                        if (used[b])
                            uc[nu++] = bc[b];
                    Live lv2;
                    live_init(&lv2, cur, Ncur);
                    MStat ms2;
                    multi_apply(&lv2, uc, nu, 1, NULL, NULL, NULL, &ms2, 0);
                    Seq q2;
                    ML ml2;
                    ScanStat st2;
                    seq_make(&q2, lv2.ev, lv2.N);
                    scan(&q2, &ml2, &st2);
                    round++;
                    int ni2 = 0;
                    for (i64 k = 0; k < ml2.n && ml2.m[k].delta < 0; k++)
                        if (!greedy_port || ml2.m[k].type <= M_C)
                            ni2++;
                    printf("round %d: with the %d neutral moves they touch only: improving moves %d (scan %.1fs)\n",
                           round, ms2.applied, ni2, st2.sec);
                    fflush(stdout);
                    if (ni2) {
                        seq_free(&q1);
                        free(ml1.m);
                        free(st1.zc);
                        free(lv.ev);
                        free(lv.pos);
                        q1 = q2;
                        ml1 = ml2;
                        st1 = st2;
                        lv = lv2;
                        ms = ms2;
                    } else {
                        seq_free(&q2);
                        free(ml2.m);
                        free(st2.zc);
                        free(lv2.ev);
                        free(lv2.pos);
                    }
                    free(uc);
                }
                int nc1 = 0;
                Cand *c1 = malloc(((size_t)ml1.n + 1) * sizeof(Cand));
                for (i64 k = 0; k < ml1.n && ml1.m[k].delta < 0; k++)
                    if (!greedy_port || ml1.m[k].type <= M_C)
                        c1[nc1++] = cand_of(&q1, &ml1.m[k], (int)k);
                qsort(c1, (size_t)nc1, sizeof(Cand), cand_cmp);
                MStat mi;
                i64 l0 = lv.len;
                multi_apply(&lv, c1, nc1, 0, NULL, NULL, NULL, &mi, !quiet);
                printf(
                    "round %d: %d neutral port moves kept, then length %lld -> %lld  (improving moves listed %d, applied %d: %d with the scanned delta, %d re-evaluated; not applied: %d no longer moves, %d no longer improving, %d mismatches; apply %.1fs, total %.0fs)\n",
                    round, ms.applied, l0, lv.len, nc1, mi.applied, mi.exact, mi.changed, mi.invalid, mi.notpay,
                    mi.mismatch, mi.sec, wall() - t00);
                fflush(stdout);
                free(c1);
                seq_free(&q1);
                free(ml1.m);
                free(st1.zc);
                if (lv.len < l0) {
                    if (cur != ev)
                        free(cur);
                    cur = lv.ev;
                    Ncur = lv.N;
                    free(lv.pos);
                    found = 1;
                    if (planout)
                        checkpoint(cur, Ncur, planout);
                } else {
                    free(lv.ev);
                    free(lv.pos);
                }
            }
            free(tried);
            free(zl);
            free(zh);
            free(bc);
            free(done);
            free(used);
            free(ids0);
            free(ids1);
            free(ncd);
            free(nm);
            seq_free(&q);
            free(ml.m);
            free(st.zc);
            if (!found) {
                printf("no neutral port move left that opens an improving move (%d tried)\n", ntried);
                break;
            }
        }
        printf("greedy: length %lld -> %lld in %d rounds (%.0fs)\n", len_start, seq_length(cur, Ncur), round,
               wall() - tg);
        fflush(stdout);
        if (planout)
            checkpoint(cur, Ncur, planout);
        goto output;
    }
    for (;;) {
        seq_make(&q, cur, Ncur);
        if (!round) {
            block_stats(&q);
            if (dupstat)
                dup_stats(&q);
        }
        scan(&q, &ml, &st);
        if (!quiet || !round) {
            print_summary(&q, &ml, &st);
            for (i64 k = 0; k < ml.n && k < top; k++)
                print_move(&q, &ml.m[k], k);
        }
        fflush(stdout);
        if (!greedy && round >= walk)
            break;
        i64 pick = -1;
        for (i64 k = 0; k < ml.n && ml.m[k].delta < 0; k++)
            if (!greedy_port || ml.m[k].type <= M_C) {
                pick = k;
                break;
            }
        if (pick < 0 && round < walk) { /* a random neutral move */
            i64 lo = 0, hi;
            while (lo < ml.n && ml.m[lo].delta < 0)
                lo++;
            hi = lo;
            while (hi < ml.n && ml.m[hi].delta == 0)
                hi++;
            if (hi > lo) {
                wseed ^= wseed << 13;
                wseed ^= wseed >> 7;
                wseed ^= wseed << 17;
                pick = lo + (i64)(wseed % (u64)(hi - lo));
            }
            printf("walk: %lld neutral moves here\n", hi - lo);
        }
        if (pick < 0)
            break;
        printf("greedy round %d: applying", ++round);
        print_move(&q, &ml.m[pick], pick);
        int N2;
        Ev *nx = apply_move(&q, &ml.m[pick], &N2);
        printf("greedy round %d: length %lld -> %lld\n", round, q.len, seq_length(nx, N2));
        fflush(stdout);
        seq_free(&q);
        free(ml.m);
        free(st.zc);
        if (cur != ev)
            free(cur);
        cur = nx;
        Ncur = N2;
    }
    if (watch && q.N <= 20000)
        watch_report(&q, &ml);
    if (do_brute) {
        u64 sum = 0;
        for (i64 k = 0; k < ml.n; k++)
            if (ml.m[k].type != M_C)
                sum += mv_hash(&ml.m[k]);
        printf("scan list checksum %016llx (%lld moves%s)\n", (unsigned long long)sum, ml.n,
               ml.over ? ", TRUNCATED" : "");
        brute(&q);
        fflush(stdout);
    }
    if (list) {
        FILE *f = fopen(list, "wb");
        if (!f)
            DIE("cannot write %s", list);
        fprintf(f, "# idx type delta i j hp a g hp2 a2 cu mx  (in %d out %d: joins around the block)\n", 0, 0);
        for (i64 k = 0; k < ml.n; k++) {
            const Move *m = &ml.m[k];
            fprintf(f, "%lld %s %d %d %d %d %lld %d %d %lld %d %d\n", k, MNAME[m->type], m->delta, m->i, m->j, m->hp,
                    m->a, m->g, m->hp2, m->a2, m->cu, m->mx);
        }
        fclose(f);
    }
    if (verify > 0 && ml.n) {
        i64 step = ml.n / verify;
        if (step < 1)
            step = 1;
        i64 done = 0, bad = 0, bytype[M_NT] = {0};
        for (i64 k = 0; k < ml.n; k += step) {
            int N2;
            Ev *nx = apply_move(&q, &ml.m[k], &N2); /* dies if the length differs from the prediction */
            i64 miss = missing_perms(nx, N2);
            if (miss) {
                bad++;
                printf("verify: move #%lld leaves %lld permutations out\n", k, miss);
                print_move(&q, &ml.m[k], k);
            }
            free(nx);
            done++;
            bytype[ml.m[k].type]++;
        }
        printf(
            "verify: %lld moves applied one at a time: lengths as predicted, %lld words with missing permutations; by type:",
            done, bad);
        for (int a = 0; a < M_NT; a++)
            if (bytype[a])
                printf(" %s %lld", MNAME[a], bytype[a]);
        printf("\n");
        fflush(stdout);
    }
    if (probe > 0 && ml.n) {
        /* neutral moves that create ports: apply one, scan again; report the improving moves that appear */
        i64 lo = 0, hi = 0;
        while (lo < ml.n && ml.m[lo].delta < 0)
            lo++;
        hi = lo;
        while (hi < ml.n && ml.m[hi].delta == 0)
            hi++;
        i64 cnt0 = hi - lo, step = cnt0 / probe;
        if (step < 1)
            step = 1;
        i64 tried = 0, opened = 0, bestd = 0;
        int thr0 = thr, q0 = quiet;
        thr = -1;
        quiet = 1;
        printf("probe: %lld neutral moves, trying every %lld-th\n", cnt0, step);
        fflush(stdout);
        for (i64 k = lo; k < hi; k += step) {
            int N2;
            Ev *nx = apply_move(&q, &ml.m[k], &N2);
            Seq q2;
            ML ml2;
            ScanStat st2;
            seq_make(&q2, nx, N2);
            scan(&q2, &ml2, &st2);
            tried++;
            if (ml2.n) {
                opened++;
                if (ml2.m[0].delta < bestd)
                    bestd = ml2.m[0].delta;
                printf("probe: after neutral move #%lld (%s, block %d..%d): %lld improving moves, best:\n", k,
                       MNAME[ml.m[k].type], ml.m[k].i, ml.m[k].j, ml2.n);
                print_move(&q2, &ml2.m[0], 0);
                fflush(stdout);
            }
            seq_free(&q2);
            free(ml2.m);
            free(st2.zc);
            free(nx);
        }
        thr = thr0;
        quiet = q0;
        printf("probe: %lld neutral moves tried, %lld open an improving move, best second step %lld\n", tried, opened,
               bestd);
        fflush(stdout);
    }
    if (apply_idx >= 0) {
        if (apply_idx >= ml.n)
            DIE("--apply: only %lld moves", ml.n);
        printf("applying");
        print_move(&q, &ml.m[apply_idx], apply_idx);
        int N2;
        Ev *nx = apply_move(&q, &ml.m[apply_idx], &N2);
        cur = nx;
        Ncur = N2;
    }
output:
    if (outw) {
        char pp[4096];
        snprintf(pp, sizeof pp, "%s.plan", outw);
        i64 len = seq_length(cur, Ncur), miss = n <= 11 ? missing_perms(cur, Ncur) : -1;
        write_plan(cur, Ncur, pp);
        write_word_stream(cur, Ncur, outw);
        seq_stats(cur, Ncur);
        printf("wrote %s length %lld (missing permutations %lld; -1: not checked here, run delcheck) and %s (%.0fs)\n",
               outw, len, miss, pp, wall() - t00);
    }
    return 0;
}
