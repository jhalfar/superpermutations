/* gen16.c - gen15h.c (opt/n15/gen15.c plus the fastcheck output hook) extended to L = 4 (n = 16): the last lift is made per walk when a unit needs it (see load_walk); for L <= 3 it is gen15. */
/* gen15.c - streaming generator for superpermutations on n = 12 + L symbols built from a selection on 11 symbols
   (K0 = 10 letters, rows F / S / D) by L transports (L = 0..3) and the completion.  The construction (slices,
   transport, completion, closed trails) is Jay Pantone's.  This is opt/n14/gen14.c (L = 2 only) made general in L;
   for L = 2 it writes the same words as gen14 for the same unit plans.  Nothing of the word is stored: it is spelled
   trail by trail into a 64 MiB buffer and written out, with SHA-256 and length computed on the way.

   usage:
     gen15 info   L SEL                         counts (walks, rows, units, sum R)
     gen15 trails L SEL [--out FILE]            one line per closed trail: R fp1 fp2 (rotation-invariant fingerprints
                                                of its cyclic word), to compare the trail set with other generators
     gen15 base   L SEL [options]               every closed trail once, natural order, cut at its start, largest
                                                overlap between neighbours (a valid, long word; for tests)
     gen15 plan   L SEL PLAN [options]          a unit plan (L >= 1, see below)
     gen15 dplan  L SEL OUT                     writes the default unit plan (units in natural order, first openings)
   options: --alpha A (default 0123456789ABCDE..), --limit LETTERS, --count (spell, do not write), --nosha,
            --events FILE, --to CMD (write the word into the standard input of CMD; repeatable; without --to and
            without --count the word goes to standard output)

   Letters at n = 12 + L: 0..9 the letters of SEL, 10 .. 9+L the transported letters, s = K = 10 + L the distinguished
   letter, z = K + 1 the completion letter; rows have K letters; h = n - 3 = K - 1; ports 0 .. K-2.

   Units (L >= 1; one unit per closed trail at n - 1; every unit has h closed trails):
     D d g1 .. g(L-1) j   small unit: detached loop d (index among the D rows of SEL, file order), y = x_d with
                letter 10 inserted before position g1, then letter 11 before position g2, ..; y has K - 1 letters;
                the h small trails "letter K-1 inserted in y at position a", a = j, j+1, .., j+h-1 (mod h), each
                written as a closed piece (R + h letters) from its vertex rot(y with K-1 at a, a + 1).
     W w i0 way walk unit: walk w of the L-lift (walks of SEL in file order, transport orbits by first port, L times
                nested), cut at its full row b = row i0; way 0: completion letter in the gaps 0 .. K-2 of b; way 1:
                gaps 1 .. K-1.  h trails, each cut at a weight-2 step, joins of cost 0 inside the unit.
   Consecutive units overlap in the largest overlap (<= h letters) of the last h letters written and the first h
   letters of the next unit; an optional last field "oK" caps that overlap at K.
   PLAN header: "N<n>-UNITPLAN 1"; "# expect length L sha256 H" is checked at the end; other '#' lines ignored.

   Prints to stderr a JSON line: length, trails, SHA-256 of the word as written (alphabet applied, no newline). */
#define _FILE_OFFSET_BITS 64
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#define popen _popen
#define pclose _pclose
#endif
#if defined(__SHA__) && defined(__SSE4_1__)
#include <immintrin.h>
#define HAVE_SHANI 1
#endif
typedef uint64_t u64; typedef uint32_t u32; typedef uint8_t u8; typedef long long i64;
#define DIE(...) do { fprintf(stderr, "gen15: " __VA_ARGS__); fprintf(stderr, "\n"); exit(1); } while (0)
static double wall(void) { struct timespec ts; timespec_get(&ts, TIME_UTC); return ts.tv_sec + ts.tv_nsec * 1e-9; }

static int L, NN, K, HH, SL, ZL;   /* lifts, n, row length, h, distinguished letter, completion letter */

/* ------------------------------------------------------------------ SHA-256 */
typedef struct { u32 h[8]; u8 buf[64]; u64 len; int n; } Sha;
static const u32 SK[64] = {
0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,
0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,
0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,
0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
#define ROR(x,n) (((x)>>(n))|((x)<<(32-(n))))
static void sha_block_c(u32 *h, const u8 *p) {
    u32 w[64];
    for (int i = 0; i < 16; i++) w[i] = (u32)p[4*i]<<24 | (u32)p[4*i+1]<<16 | (u32)p[4*i+2]<<8 | p[4*i+3];
    for (int i = 16; i < 64; i++) { u32 s0 = ROR(w[i-15],7)^ROR(w[i-15],18)^(w[i-15]>>3), s1 = ROR(w[i-2],17)^ROR(w[i-2],19)^(w[i-2]>>10); w[i] = w[i-16]+s0+w[i-7]+s1; }
    u32 a=h[0],b=h[1],c=h[2],d=h[3],e=h[4],f=h[5],g=h[6],hh=h[7];
    for (int i = 0; i < 64; i++) {
        u32 t1 = hh + (ROR(e,6)^ROR(e,11)^ROR(e,25)) + ((e&f)^(~e&g)) + SK[i] + w[i];
        u32 t2 = (ROR(a,2)^ROR(a,13)^ROR(a,22)) + ((a&b)^(a&c)^(b&c));
        hh=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2;
    }
    h[0]+=a; h[1]+=b; h[2]+=c; h[3]+=d; h[4]+=e; h[5]+=f; h[6]+=g; h[7]+=hh;
}
#ifdef HAVE_SHANI
static void sha_blocks_ni(u32 *state, const u8 *data, size_t nb) {
    const __m128i MASK = _mm_set_epi64x(0x0c0d0e0f08090a0bULL, 0x0405060700010203ULL);
    __m128i TMP = _mm_loadu_si128((const __m128i *)&state[0]), S1 = _mm_loadu_si128((const __m128i *)&state[4]), S0;
    TMP = _mm_shuffle_epi32(TMP, 0xB1); S1 = _mm_shuffle_epi32(S1, 0x1B);
    S0 = _mm_alignr_epi8(TMP, S1, 8); S1 = _mm_blend_epi16(S1, TMP, 0xF0);
    while (nb--) {
        __m128i A0 = S0, C0 = S1, W[4];
        for (int g = 0; g < 16; g++) {
            __m128i Wg;
            if (g < 4) { Wg = _mm_shuffle_epi8(_mm_loadu_si128((const __m128i *)(data + 16 * g)), MASK); W[g] = Wg; }
            else {
                __m128i t = _mm_sha256msg1_epu32(W[g & 3], W[(g + 1) & 3]);
                t = _mm_add_epi32(t, _mm_alignr_epi8(W[(g + 3) & 3], W[(g + 2) & 3], 4));
                t = _mm_sha256msg2_epu32(t, W[(g + 3) & 3]);
                W[g & 3] = Wg = t;
            }
            __m128i M = _mm_add_epi32(Wg, _mm_loadu_si128((const __m128i *)&SK[4 * g]));
            S1 = _mm_sha256rnds2_epu32(S1, S0, M);
            M = _mm_shuffle_epi32(M, 0x0E);
            S0 = _mm_sha256rnds2_epu32(S0, S1, M);
        }
        S0 = _mm_add_epi32(S0, A0); S1 = _mm_add_epi32(S1, C0);
        data += 64;
    }
    TMP = _mm_shuffle_epi32(S0, 0x1B); S1 = _mm_shuffle_epi32(S1, 0xB1);
    S0 = _mm_blend_epi16(TMP, S1, 0xF0); S1 = _mm_alignr_epi8(S1, TMP, 8);
    _mm_storeu_si128((__m128i *)&state[0], S0); _mm_storeu_si128((__m128i *)&state[4], S1);
}
static void sha_blocks(u32 *h, const u8 *p, size_t nb) { sha_blocks_ni(h, p, nb); }
#else
static void sha_blocks(u32 *h, const u8 *p, size_t nb) { while (nb--) { sha_block_c(h, p); p += 64; } }
#endif
static void sha_selftest(void) {
    static u8 d[64 * 1024]; u32 a[8] = {1,2,3,4,5,6,7,8}, b[8]; u64 x = 88172645463325252ULL;
    for (size_t i = 0; i < sizeof d; i++) { x ^= x << 13; x ^= x >> 7; x ^= x << 17; d[i] = (u8)x; }
    memcpy(b, a, 32); sha_blocks(a, d, sizeof d / 64);
    for (size_t i = 0; i < sizeof d / 64; i++) sha_block_c(b, d + 64 * i);
    if (memcmp(a, b, 32)) { fprintf(stderr, "gen15: SHA-256 self test failed\n"); exit(1); }
}
static void sha_init(Sha *s) { static const u32 iv[8] = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19}; memcpy(s->h, iv, 32); s->len = 0; s->n = 0; }
static void sha_update(Sha *s, const u8 *p, size_t L_) {
    s->len += L_;
    if (s->n) { while (L_ && s->n < 64) { s->buf[s->n++] = *p++; L_--; } if (s->n == 64) { sha_blocks(s->h, s->buf, 1); s->n = 0; } }
    if (L_ >= 64) { size_t nb = L_ / 64; sha_blocks(s->h, p, nb); p += 64 * nb; L_ -= 64 * nb; }
    while (L_) { s->buf[s->n++] = *p++; L_--; }
}
static void sha_final(Sha *s, char *hex) {
    u64 bits = s->len * 8; u8 pad = 0x80; sha_update(s, &pad, 1); pad = 0;
    while (s->n != 56) sha_update(s, &pad, 1);
    u8 lb[8]; for (int i = 0; i < 8; i++) lb[i] = (u8)(bits >> (56 - 8*i)); sha_update(s, lb, 8);
    for (int i = 0; i < 8; i++) sprintf(hex + 8*i, "%08x", s->h[i]);
}

/* ------------------------------------------------------------------ output */
#define OBUF (64u << 20)
#define MAXSINK 4
static u8 *obuf; static size_t on = 0; static u64 written = 0, limit = ~0ULL;
static u8 alpha[32]; static Sha sha; static int dosha = 1, dowrite = 1, limited = 0;
static FILE *sinks[MAXSINK]; static int nsink = 0;
static u8 tail[16]; static int ntail = 0;          /* last h letters written (letter values) */
static void (*check_hook)(const u8 *, size_t);   /* fastcheck: the letters (values) of every output block, before the alphabet */
static void flush_out(void) {
    if (!on) return;
    if (check_hook) check_hook(obuf, on);
    if (!dosha && !dowrite) { on = 0; return; }   /* fastcheck: nothing else needs the letters */
    for (size_t i = 0; i < on; i++) obuf[i] = alpha[obuf[i]];
    if (dosha) sha_update(&sha, obuf, on);
    if (dowrite) for (int s = 0; s < nsink; s++) if (fwrite(obuf, 1, on, sinks[s]) != on) DIE("write failed (sink %d)", s);
    on = 0;
}
static void emit(const u8 *p, size_t n) {
    if (limited) return;
    if (written + n >= limit) { n = (size_t)(limit - written); limited = 1; }
    while (n) {
        size_t c = OBUF - on; if (c > n) c = n;
        memcpy(obuf + on, p, c); on += c; written += c; p += c; n -= c;
        if (on == OBUF) flush_out();
    }
}

/* ------------------------------------------------------------------ selection and walks of SEL */
typedef struct { u8 x[16]; u8 L; u8 ty; u8 lp; } Row;   /* ty 0 = F, 1 = S, 2 = D */
static Row *sel; static int nsel; static int *det; static int ndet;
static int *walkrow, *walkstart, nwalk;            /* walks of SEL in file order of their first row */

static u64 key8(const u8 *x) { u64 k = 0; for (int i = 0; i < 8; i++) k = k << 4 | x[i]; return k; }
static void rot(u8 *dst, const u8 *b, int n, int j) { j %= n; if (j < 0) j += n; for (int i = 0; i < n; i++) dst[i] = b[(i + j) % n]; }
static void ins(u8 *dst, const u8 *b, int n, int z, int j) { int q = 0; for (int i = 0; i < n; i++) { if (i == j) dst[q++] = (u8)z; dst[q++] = b[i]; } if (j == n) dst[q++] = (u8)z; }

static void read_sel(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) DIE("cannot open %s", path);
    char line[256], xs[64], ts[64]; int cap = 400000;
    sel = malloc(sizeof(Row) * cap); det = malloc(sizeof(int) * cap); nsel = ndet = 0;
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#' || line[0] == '\n' || line[0] == '\r') continue;
        if (sscanf(line, "%63s %63s", xs, ts) != 2) continue;
        if (strlen(xs) != 10) DIE("row length");
        Row r; memset(&r, 0, sizeof r); r.L = 10; r.lp = 0;
        int seen = 0;
        for (int i = 0; i < 10; i++) { char c = xs[i]; if (c < '0' || c > '9') DIE("letter"); r.x[i] = (u8)(c - '0'); seen |= 1 << r.x[i]; }
        if (seen != 0x3ff) DIE("row is not a permutation of 0..9");
        if (ts[0] == 'F') r.ty = 0; else if (ts[0] == 'S') r.ty = 1; else if (ts[0] == 'D') r.ty = 2; else DIE("type");
        if (nsel == cap) DIE("too many rows");
        if (r.ty == 2) det[ndet++] = nsel;
        sel[nsel++] = r;
    }
    fclose(f);
    u64 hm = 1; while (hm < (u64)nsel * 4) hm <<= 1;
    u64 *hk = malloc(sizeof(u64) * hm); int *hv = malloc(sizeof(int) * hm); memset(hk, 0xff, sizeof(u64) * hm);
    for (int i = 0; i < nsel; i++) if (sel[i].ty != 2) {
        u64 k = key8(sel[i].x), p = (k * 0x9E3779B97F4A7C15ULL) & (hm - 1);
        while (hk[p] != ~0ULL) { if (hk[p] == k) DIE("repeated head"); p = (p + 1) & (hm - 1); }
        hk[p] = k; hv[p] = i;
    }
    char *seen = calloc(nsel, 1); walkrow = malloc(sizeof(int) * nsel); walkstart = malloc(sizeof(int) * (nsel + 1)); nwalk = 0; int nw = 0;
    for (int i = 0; i < nsel; i++) {
        if (sel[i].ty == 2 || seen[i]) continue;
        walkstart[nwalk++] = nw; int j = i;
        while (!seen[j]) {
            seen[j] = 1; walkrow[nw++] = j;
            u8 t[10]; rot(t, sel[j].x, 10, sel[j].ty == 0 ? 1 : -1);
            u64 k = key8(t), p = (k * 0x9E3779B97F4A7C15ULL) & (hm - 1);
            while (hk[p] != k) { if (hk[p] == ~0ULL) DIE("unbalanced walk"); p = (p + 1) & (hm - 1); }
            j = hv[p];
        }
        if (j != i) DIE("walk does not close at its first row");
    }
    walkstart[nwalk] = nw;
    free(hk); free(hv); free(seen);
}

/* transport one walk (rows of length n, letters 0..n-1) by inserting letter n; appends the orbit walks */
typedef struct { Row *r; size_t n, cap; } RowVec;
static void rv_push(RowVec *v, const Row *r) { if (v->n == v->cap) { v->cap = v->cap ? v->cap * 2 : 1024; v->r = realloc(v->r, sizeof(Row) * v->cap); if (!v->r) DIE("oom"); } v->r[v->n++] = *r; }
static int transport(const Row *w, size_t m, RowVec *out, size_t *ostart) {
    int n = w[0].L, H = n - 1, k = n; char done[16] = {0}; int no = 0;
    for (int p0 = 0; p0 < H; p0++) {
        if (done[p0]) continue;
        ostart[no++] = out->n; int p = p0; size_t i = 0;
        for (;;) {
            if (i == 0) { if (done[p]) DIE("repeated transport port"); done[p] = 1; }
            const Row *r = &w[i]; Row a; memset(&a, 0, sizeof a); a.L = (u8)(n + 1); a.ty = r->ty; a.lp = 0;
            if (r->ty == 0) {
                if (p == 0) { ins(a.x, r->x, n, k, 0); rv_push(out, &a); ins(a.x, r->x, n, k, n - 1); rv_push(out, &a); }
                else { ins(a.x, r->x, n, k, p); rv_push(out, &a); }
            } else {
                if (p < n - 2) { ins(a.x, r->x, n, k, p); rv_push(out, &a); }
                else { a.lp = 1; ins(a.x, r->x, n, k, n - 2); rv_push(out, &a); u8 y[16]; ins(y, r->x, n, k, n - 1); rot(a.x, y, n + 1, -1); rv_push(out, &a); }
            }
            p = (p + (r->ty == 0 ? -1 : 1) + H) % H;
            if (++i == m) { i = 0; if (p == p0) break; }
        }
    }
    ostart[no] = out->n;
    return no;
}

/* the walks of the L-lift: rows packed (K letters, 4 bits each; bit 60 = short, bit 61 = lp).
   gen16 (fastcheck): for L = 4 (n = 16) all lifted walks would need 6.1e9 rows (49 GB).  Only the walks of the
   3-lift are stored (KP = 13 letters per row, 471 million rows, 3.8 GB); a walk of the 4-lift is made when a unit
   needs it (load_walk): it is orbit a of the transport of its 3-lift walk v, in the order lift_rec would make it.
   The orbits of a transport are the cycles of p -> p + delta (mod H) on the H = 12 ports, delta = (short rows -
   full rows) of the walk, so walk v has gcd(delta, H) orbits; the 4-lift walk numbers follow from that.  For
   L = 4, wrow/wstart then describe the current walk only (wstart[w] = 0, wstart[w+1] = its rows). */
static u64 *wrow; static u64 *wstart; static int nwl; static u64 nrows;
static int *wbase;                                   /* walk of SEL for each lifted walk */
static int wcap = 0, KP, LB, LAZY;                   /* letters packed per stored row; levels stored; last level on demand */
static void wl_add_walk(const Row *r, size_t m, int wi) {
    if (nwl + 2 > wcap) { wcap = wcap ? wcap * 2 : 4096; wstart = realloc(wstart, 8 * (size_t)(wcap + 1)); wbase = realloc(wbase, 4 * (size_t)wcap); }
    wstart[nwl] = nrows; wbase[nwl] = wi; nwl++;
    for (size_t q = 0; q < m; q++) {
        u64 k = 0; for (int t = 0; t < KP; t++) k |= (u64)r[q].x[t] << (4 * t);
        if (r[q].ty) k |= 1ULL << 60;
        if (r[q].lp) k |= 1ULL << 61;
        wrow[nrows++] = k;
    }
    wstart[nwl] = nrows;
}
static RowVec lv[4]; static size_t los[4][20];
static void lift_rec(const Row *w, size_t m, int lev, int wi) {
    if (lev == LB) { wl_add_walk(w, m, wi); return; }
    RowVec *v = &lv[lev]; v->n = 0;
    int no = transport(w, m, v, los[lev]);
    size_t st[20]; memcpy(st, los[lev], sizeof st);
    for (int a = 0; a < no; a++) lift_rec(v->r + st[a], st[a + 1] - st[a], lev + 1, wi);
}
static u64 *w3row, *w3start; static int nw3; static int *w4pre;   /* L = 4: the 3-lift, first 4-lift walk of each */
static u64 *curbuf; static size_t curcap; static int curw = -1; static Row *curtmp; static size_t curtmpcap; static RowVec curv;
static int gcdi(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static void build_walks(void) {
    LAZY = L == 4 || (L >= 1 && getenv("GEN16_LAZY") != NULL);   /* GEN16_LAZY: the same for L = 1..3 (a test) */
    LB = LAZY ? L - 1 : L; KP = 10 + LB;
    u64 base = 0; for (int i = 0; i < nsel; i++) base += sel[i].ty != 2;
    u64 cap = base; for (int l = 0; l < LB; l++) cap *= (u64)(10 + l);
    wrow = malloc(8 * cap + 8); if (!wrow) DIE("cannot allocate %llu rows", (unsigned long long)cap);
    nrows = 0; nwl = 0;
    Row *tmp = malloc(sizeof(Row) * nsel);
    for (int wi = 0; wi < nwalk; wi++) {
        int m = walkstart[wi + 1] - walkstart[wi];
        for (int i = 0; i < m; i++) tmp[i] = sel[walkrow[walkstart[wi] + i]];
        lift_rec(tmp, m, 0, wi);
    }
    if (nrows != cap) DIE("rows %llu, expected %llu", (unsigned long long)nrows, (unsigned long long)cap);
    free(tmp); for (int l = 0; l < 4; l++) { free(lv[l].r); lv[l].r = NULL; lv[l].cap = 0; }
    if (!LAZY) return;
    /* L = 4: keep the 3-lift, number the 4-lift walks */
    w3row = wrow; w3start = wstart; nw3 = nwl;
    int H = KP - 1; w4pre = malloc(sizeof(int) * (nw3 + 1)); w4pre[0] = 0;
    for (int v = 0; v < nw3; v++) {
        int d = 0;
        for (u64 i = w3start[v]; i < w3start[v + 1]; i++) d += (w3row[i] >> 60 & 1) ? 1 : -1;
        d %= H; if (d < 0) d += H;
        w4pre[v + 1] = w4pre[v] + (d == 0 ? H : gcdi(d, H));
    }
    nwl = w4pre[nw3];
    nrows = cap * (u64)(10 + LB);                    /* rows of the 4-lift (each row of the 3-lift gives H + 1 rows over its orbits) */
    wstart = calloc((size_t)nwl + 2, 8); wrow = NULL;
}
/* L = 4: make walk w of the 4-lift the current one */
static void load_walk(int w) {
    if (!LAZY || w == curw) return;
    int lo = 0, hi = nw3;                             /* v with w4pre[v] <= w < w4pre[v+1] */
    while (hi - lo > 1) { int mid = (lo + hi) / 2; if (w4pre[mid] <= w) lo = mid; else hi = mid; }
    int v = lo, a = w - w4pre[v];
    static int curv_v = -1; static size_t ost[20];        /* the transport of v is kept for its other orbits */
    if (v != curv_v) {
    size_t m3 = w3start[v + 1] - w3start[v];
    if (m3 > curtmpcap) { curtmpcap = 2 * m3; curtmp = realloc(curtmp, sizeof(Row) * curtmpcap); if (!curtmp) DIE("oom"); }
    for (size_t i = 0; i < m3; i++) {
        u64 k = w3row[w3start[v] + i]; Row *r = &curtmp[i]; memset(r, 0, sizeof *r);
        for (int t = 0; t < KP; t++) r->x[t] = (k >> (4 * t)) & 15;
        r->L = (u8)KP; r->ty = (u8)(k >> 60 & 1); r->lp = (u8)(k >> 61 & 1);
    }
    curv.n = 0;
    int no = transport(curtmp, m3, &curv, ost);
    if (no != w4pre[v + 1] - w4pre[v]) DIE("walk %d: %d orbits, expected %d", v, no, w4pre[v + 1] - w4pre[v]);
    curv_v = v;
    }
    size_t m = ost[a + 1] - ost[a];
    if (m > curcap) { curcap = 2 * m; curbuf = realloc(curbuf, 8 * curcap); if (!curbuf) DIE("oom"); }
    for (size_t q = 0; q < m; q++) {
        const Row *r = &curv.r[ost[a] + q];
        u64 k = 0; for (int t = 0; t < K; t++) k |= (u64)r->x[t] << (4 * t);
        if (r->ty) k |= 1ULL << 60;
        if (r->lp) k |= 1ULL << 61;
        curbuf[q] = k;
    }
    if (curw >= 0) { wstart[curw] = 0; wstart[curw + 1] = 0; }
    wrow = curbuf; wstart[w] = 0; wstart[w + 1] = m; curw = w;
}
static inline void unpackK(u64 k, u8 *x) { for (int t = 0; t < K; t++) x[t] = (k >> (4 * t)) & 15; }
static inline int rty(u64 k) { return (int)((k >> 60) & 1); }

/* ------------------------------------------------------------------ spelling */
static u8 *tb; static size_t tcap = 0, tn = 0;       /* cyclic word of the current trail */
static inline void tneed(size_t add) { if (tn + add > tcap) { tcap = (tn + add) * 2 + 65536; tb = realloc(tb, tcap); if (!tb) DIE("oom"); } }
/* one slice: B (n-1 letters), satellite s, v classes: B s B (B[t] s rot(B,t+1))_{t<v-1} minus the last h letters */
static void slice(const u8 *B, int s, int v) {
    int n1 = NN - 1; size_t full = (size_t)2 * n1 + 1 + (size_t)(v - 1) * (n1 + 2);
    tneed(full);
    u8 *w = tb + tn; size_t q = 0;
    memcpy(w, B, n1); q += n1; w[q++] = (u8)s; memcpy(w + q, B, n1); q += n1;
    for (int t = 0; t < v - 1; t++) {
        w[q++] = B[t]; w[q++] = (u8)s;
        int r1 = n1 - (t + 1); memcpy(w + q, B + t + 1, r1); memcpy(w + q + r1, B, t + 1); q += n1;
    }
    tn += q - HH;
}
/* completion port path of a row b (K letters) with port p; records slice starts in st[] (returns count) */
static int portpath(const u8 *b, int ty, int p, size_t *st) {
    u8 B[16]; int ns = 0;
    if (ty == 0) {
        if (p == 0) { st[ns++] = tn; ins(B, b, K, ZL, 0); slice(B, SL, K + 1); st[ns++] = tn; ins(B, b, K, ZL, K - 1); slice(B, SL, K + 1); }
        else { st[ns++] = tn; ins(B, b, K, ZL, p); slice(B, SL, K + 1); }
    } else {
        if (p < K - 2) { st[ns++] = tn; ins(B, b, K, ZL, p); slice(B, SL, K - 1); }
        else {
            st[ns++] = tn; ins(B, b, K, ZL, K - 2); slice(B, SL, K - 2);
            st[ns++] = tn; rot(B, b, K, K - 2); B[K] = (u8)SL; slice(B, ZL, K + 1);
            st[ns++] = tn; rot(B, b, K, K - 1); B[K] = (u8)SL; slice(B, ZL, K + 1);
            st[ns++] = tn; ins(B, b, K, ZL, K - 1); slice(B, SL, K - 2);
        }
    }
    return ns;
}
static inline int nextport(int ty, int p) { return (p + (ty == 0 ? -1 : 1) + (K - 1)) % (K - 1); }
/* closed trail of lifted walk w from row i0 with port p (one pass for L >= 1; until (i0, p) again for L = 0) */
static int nst0; static size_t st0[4];
static u64 walk_trail(int w, u64 i0, int p) {
    u64 a = wstart[w], m = wstart[w + 1] - a; u8 b[16]; size_t st[4]; int p0 = p; u64 i = i0, steps = 0;
    tn = 0;
    do {
        u64 k = wrow[a + i]; unpackK(k, b);
        int ns = portpath(b, rty(k), p, st);
        if (steps == 0) { nst0 = ns; memcpy(st0, st, sizeof st); }
        p = nextport(rty(k), p); steps++;
        if (++i == m) i = 0;
        if (L >= 1 && steps == m && !(i == i0 && p == p0)) DIE("walk %d: trail of port %d is not one pass", w, p0);
    } while (!(i == i0 && p == p0));
    return steps;
}
static int walk_endport(int w, u64 i0, int p) {
    u64 a = wstart[w], m = wstart[w + 1] - a;
    for (u64 t = 0; t < m; t++) { u64 i = (i0 + t) % m; p = nextport(rty(wrow[a + i]), p); }
    return p;
}
/* small trail (L >= 1): y (K-1 letters), letter K-1 inserted at position at, written from vertex rot(loop, at+1).
   L = 0: y is the detached loop itself (K letters), written from rot(y, at). */
static void small_trail(const u8 *y, int at) {
    u8 loop[16], B[16]; tn = 0;
    if (L == 0) { memcpy(loop, y, K); for (int j = 0; j < K; j++) { rot(B, loop, K, at + j); B[K] = (u8)SL; slice(B, ZL, K + 1); } return; }
    ins(loop, y, K - 1, K - 1, at);
    for (int j = 0; j < K; j++) { rot(B, loop, K, at + 1 + j); B[K] = (u8)SL; slice(B, ZL, K + 1); }
}

/* ------------------------------------------------------------------ pieces */
static FILE *evf; static u64 nev = 0;
/* emit the cyclic word tb[0..tn) from offset c, len letters (len <= 2 tn), overlapping ov letters */
static void piece(size_t c, size_t len, int ov, const char *desc, int ti) {
    c %= tn;
    if (ov > ntail) DIE("overlap %d beyond what was written", ov);
    for (int i = 0; i < ov; i++) if (tail[ntail - ov + i] != tb[(c + i) % tn]) DIE("overlap mismatch at letter %llu", (unsigned long long)written);
    if (evf) fprintf(evf, "%llu %llu %llu %d %llu %s %d %llu\n", (unsigned long long)nev, (unsigned long long)(written - ov), (unsigned long long)len, ov, (unsigned long long)tn, desc, ti, (unsigned long long)c);
    nev++;
    if (len < (size_t)HH || len > 2 * tn) DIE("piece length");
    /* letters c+ov .. c+len-1 (cyclic) */
    size_t s = c + ov, e = c + len;             /* in the doubled word */
    if (s < tn) { size_t e1 = e < tn ? e : tn; emit(tb + s, e1 - s); s = e1; }
    if (s < e) emit(tb + (s - tn), e - s);
    for (int i = 0; i < HH; i++) tail[i] = tb[(c + len - HH + i) % tn];
    ntail = HH;
}
static int maxov(const u8 *S, int cap) {          /* largest q <= cap with tail suffix q == S prefix q */
    if (cap > ntail) cap = ntail;
    for (int q = cap; q > 0; q--) if (!memcmp(tail + ntail - q, S, q)) return q;
    return 0;
}

/* ------------------------------------------------------------------ units */
static u64 cnt_small = 0, cnt_walk = 0;
static void small_y(int d, const int *g, u8 *y) {      /* y = x_d with letters 10 .. 10+L-2 inserted */
    u8 t[16]; memcpy(y, sel[det[d]].x, 10); int n = 10;
    for (int l = 0; l < L - 1; l++) { ins(t, y, n, 10 + l, g[l]); n++; memcpy(y, t, n); }
}
static void unit_small(int d, const int *g, int j, int ovcap) {
    u8 y[16]; small_y(d, g, y);
    char desc[64]; int q = sprintf(desc, "D %d", d); for (int l = 0; l < L - 1; l++) q += sprintf(desc + q, " %d", g[l]); sprintf(desc + q, " %d", j);
    for (int i = 0; i < HH; i++) {
        int at = (j + i) % HH; small_trail(y, at);
        int ov = (i == 0) ? (written ? maxov(tb, ovcap) : 0) : HH - 1;
        piece(0, tn + HH, ov, desc, i);
        cnt_small++;
        if (limited) return;
    }
}
static void unit_walk(int w, u64 i0, int way, int ovcap) {
    load_walk(w);
    u64 a = wstart[w], m = wstart[w + 1] - a;
    if (i0 >= m || rty(wrow[a + i0]) != 0) DIE("walk unit %d: row %llu is not a full row", w, (unsigned long long)i0);
    char desc[64]; sprintf(desc, "W %d %llu %d", w, (unsigned long long)i0, way);
    for (int i = 0; i < HH; i++) {
        int q = way == 0 ? i : i + 1;               /* gap of the completion letter in row i0 */
        int port = q == K - 1 ? 0 : q;
        if (walk_endport(w, i0, port) != port) DIE("walk %d: trail of port %d is not one pass", w, port);
        walk_trail(w, i0, port);
        size_t s0 = (q == K - 1) ? st0[1] : st0[0];
        size_t cut = s0 + (size_t)(q + 1) * (NN + 1);
        int ov;
        if (i == 0) { u8 S[16]; for (int t = 0; t < HH; t++) S[t] = tb[(cut + t) % tn]; ov = written ? maxov(S, ovcap) : 0; }
        else ov = HH;
        piece(cut, tn + HH + 1, ov, desc, i);
        cnt_walk++;
        if (limited) return;
    }
}

static double t0g;
static unsigned long long expect_len = 0; static char expect_sha[65] = "";
static void plan(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) DIE("cannot open %s", path);
    char line[512], hdr[32]; int nl = 0; u64 nu = 0;
    sprintf(hdr, "N%d-UNITPLAN", NN);
    while (fgets(line, sizeof line, f)) {
        nl++;
        if (nl == 1) { if (strncmp(line, hdr, strlen(hdr))) DIE("not an n = %d unit plan (header %s)", NN, hdr); continue; }
        if (!strncmp(line, "# expect length ", 16)) { if (sscanf(line + 16, "%llu sha256 %64s", &expect_len, expect_sha) < 1) DIE("bad expect line"); continue; }
        if (line[0] == '#' || line[0] == '\n' || line[0] == '\r') continue;
        char *tok[16]; int nt = 0; char *sv = NULL;
        for (char *t = strtok_r(line, " \t\r\n", &sv); t && nt < 16; t = strtok_r(NULL, " \t\r\n", &sv)) tok[nt++] = t;
        int cap = HH;
        if (nt && tok[nt - 1][0] == 'o') { cap = atoi(tok[nt - 1] + 1); nt--; }
        if (cap < 0 || cap > HH) DIE("bad cap line %d", nl);
        if (nt >= 1 && tok[0][0] == 'D') {
            if (nt != 2 + L) DIE("D line %d needs %d numbers", nl, 1 + L);
            int d = atoi(tok[1]), g[4], j = atoi(tok[nt - 1]);
            if (d < 0 || d >= ndet || j < 0 || j >= HH) DIE("bad D line %d", nl);
            for (int l = 0; l < L - 1; l++) { g[l] = atoi(tok[2 + l]); if (g[l] < 0 || g[l] > 9 + l) DIE("bad D line %d", nl); }
            unit_small(d, g, j, cap);
        } else if (nt == 4 && tok[0][0] == 'W') {
            int w = atoi(tok[1]), way = atoi(tok[3]); u64 i0 = strtoull(tok[2], NULL, 10);
            if (w < 0 || w >= nwl || way < 0 || way > 1) DIE("bad W line %d", nl);
            unit_walk(w, i0, way, cap);
        } else DIE("bad plan line %d", nl);
        nu++;
        if (nu % 50000 == 0) fprintf(stderr, "  units %llu, letters %llu (%.0fs)\n", (unsigned long long)nu, (unsigned long long)written, wall() - t0g);
        if (limited) break;
    }
    fclose(f);
}

/* default plan: small units in order (d, g...), j = 0; walk units with the first full row, way 0 */
static void dplan(const char *path) {
    FILE *o = fopen(path, "w"); if (!o) DIE("cannot write %s", path);
    fprintf(o, "N%d-UNITPLAN 1\n# default plan of gen15 (natural order, first openings)\n", NN);
    int g[4] = {0, 0, 0, 0};
    for (int d = 0; d < ndet; d++) {
        for (;;) {
            fprintf(o, "D %d", d); for (int l = 0; l < L - 1; l++) fprintf(o, " %d", g[l]); fprintf(o, " 0\n");
            int l = L - 2; while (l >= 0) { if (++g[l] <= 9 + l) break; g[l] = 0; l--; }
            if (l < 0) break;
        }
    }
    for (int w = 0; w < nwl; w++) {
        load_walk(w);
        u64 a = wstart[w], m = wstart[w + 1] - a, i = 0;
        while (i < m && rty(wrow[a + i])) i++;
        if (i == m) DIE("walk %d without a full row", w);
        fprintf(o, "W %d %llu 0\n", w, (unsigned long long)i);
    }
    fclose(o);
}

/* fingerprint of the cyclic word tb[0..tn): sums over all cyclic windows of 16 letters of two mixes */
static u64 mix1(u64 x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
static u64 mix2(u64 x) { x += 0x9E3779B97F4A7C15ULL; x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL; x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL; return x ^ (x >> 31); }
static void fingerprint(u64 *f1, u64 *f2) {
    u64 a = 0, b = 0, win = 0;
    for (size_t i = 0; i < 16; i++) win = win << 4 | tb[i % tn];
    for (size_t i = 0; i < tn; i++) { a += mix1(win); b += mix2(win); win = win << 4 | tb[(i + 16) % tn]; }
    *f1 = a; *f2 = b;
}
static FILE *tro; static u64 ntr = 0, sumR = 0;
static void trail_out(void) { u64 a, b; fingerprint(&a, &b); fprintf(tro, "%llu %016llx %016llx\n", (unsigned long long)tn, (unsigned long long)a, (unsigned long long)b); ntr++; sumR += tn; }

/* every trail once: cb = 0 fingerprints, 1 base word */
static void all_trails(int base) {
    int g[4] = {0, 0, 0, 0};
    for (int d = 0; d < ndet; d++) {
        for (;;) {
            u8 y[16];
            if (L == 0) memcpy(y, sel[det[d]].x, 10); else small_y(d, g, y);
            int nt = L == 0 ? 1 : HH;
            for (int i = 0; i < nt; i++) {
                small_trail(y, i);
                if (base) { int ov = written ? maxov(tb, HH) : 0; piece(0, tn + HH, ov, "D", i); cnt_small++; }
                else trail_out();
            }
            int l = L - 2; while (l >= 0) { if (++g[l] <= 9 + l) break; g[l] = 0; l--; }
            if (l < 0) break;
        }
    }
    for (int w = 0; w < nwl; w++) {
        load_walk(w);
        u64 a = wstart[w], m = wstart[w + 1] - a;
        if (L >= 1) {
            for (int p = 0; p < K - 1; p++) {
                walk_trail(w, 0, p);
                if (base) { int ov = written ? maxov(tb, HH) : 0; piece(0, tn + HH, ov, "W", p); cnt_walk++; }
                else trail_out();
            }
        } else {
            /* port orbits: (row 0, port) pairs already used */
            char used[16] = {0};
            for (int p = 0; p < K - 1; p++) {
                if (used[p]) continue;
                u64 i = 0; int q = p;
                do { if (i == 0) used[q] = 1; q = nextport(rty(wrow[a + i]), q); if (++i == m) i = 0; } while (!(i == 0 && q == p));
                walk_trail(w, 0, p);
                if (base) { int ov = written ? maxov(tb, HH) : 0; piece(0, tn + HH, ov, "W", p); cnt_walk++; }
                else trail_out();
            }
        }
        if (limited) return;
    }
}

/* sinks: a command that reads the word on its standard input.  On Windows _popen's pipe has a tiny buffer, which
   made generator and checker run in lock step (each thread about half busy); there the pipe is made with _pipe and
   a large buffer (GEN15_PIPEBUF bytes, default 16 MiB) and the command is started by cmd.exe /c. */
#ifdef _WIN32
#include <process.h>
static intptr_t sink_pid[MAXSINK];
static FILE *open_sink(const char *cmd, int i) {
    int fds[2]; unsigned sz = 16u << 20; const char *e = getenv("GEN15_PIPEBUF"); if (e) sz = (unsigned)strtoul(e, NULL, 10);
    if (_pipe(fds, sz, _O_BINARY | _O_NOINHERIT)) DIE("pipe failed");
    int save = _dup(0); if (save < 0) DIE("dup failed");
    if (_dup2(fds[0], 0)) DIE("dup2 failed");                       /* the child inherits fd 0 = read end */
    const char *comspec = getenv("COMSPEC"); if (!comspec) comspec = "cmd.exe";
    sink_pid[i] = _spawnl(_P_NOWAIT, comspec, comspec, "/c", cmd, NULL);
    if (sink_pid[i] == -1) DIE("cannot start %s", cmd);
    _dup2(save, 0); _close(save); _close(fds[0]);
    FILE *f = _fdopen(fds[1], "wb"); if (!f) DIE("fdopen failed");
    setvbuf(f, NULL, _IOFBF, 1 << 20);
    return f;
}
static int close_sink(FILE *f, int i) { int st = 0; fclose(f); if (_cwait(&st, sink_pid[i], 0) == -1) return -1; return st; }
#else
static FILE *open_sink(const char *cmd, int i) { (void)i; FILE *p = popen(cmd, "w"); if (!p) DIE("cannot start %s", cmd); setvbuf(p, NULL, _IOFBF, 1 << 20); return p; }
static int close_sink(FILE *f, int i) { (void)i; return pclose(f); }
#endif

#ifndef GEN15_NO_MAIN
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: gen15 info|trails|base|plan|dplan L SEL [PLAN|OUT] [options]\n"); return 2; }
    double t0 = wall();
    t0g = t0;
    const char *mode = argv[1], *selp = argv[3], *planp = NULL, *alp = NULL, *evp = NULL, *outp = NULL;
    const char *tos[MAXSINK]; int nto = 0;
    L = atoi(argv[2]); if (L < 0 || L > 4) DIE("L must be 0..4");
    NN = 12 + L; K = 10 + L; HH = NN - 3; SL = K; ZL = K + 1;
    int ai = 4;
    if (!strcmp(mode, "plan") || !strcmp(mode, "dplan")) { if (argc < 5) DIE("%s needs a file", mode); planp = argv[4]; ai = 5; }
    for (; ai < argc; ai++) {
        if (!strcmp(argv[ai], "--limit") && ai + 1 < argc) limit = strtoull(argv[++ai], NULL, 10);
        else if (!strcmp(argv[ai], "--alpha") && ai + 1 < argc) alp = argv[++ai];
        else if (!strcmp(argv[ai], "--events") && ai + 1 < argc) evp = argv[++ai];
        else if (!strcmp(argv[ai], "--out") && ai + 1 < argc) outp = argv[++ai];
        else if (!strcmp(argv[ai], "--to") && ai + 1 < argc) { if (nto == MAXSINK) DIE("too many --to"); tos[nto++] = argv[++ai]; }
        else if (!strcmp(argv[ai], "--count")) dowrite = 0;
        else if (!strcmp(argv[ai], "--nosha")) dosha = 0;
        else DIE("unknown option %s", argv[ai]);
    }
    if (!alp) alp = "0123456789ABCDEFG";
    if ((int)strlen(alp) < NN) DIE("alphabet must have %d symbols", NN);
    for (int i = 0; i < NN; i++) alpha[i] = (u8)alp[i];
    for (int i = 0; i < NN; i++) for (int j = 0; j < i; j++) if (alpha[i] == alpha[j]) DIE("repeated alphabet symbol");
    sha_selftest();
    read_sel(selp);
    if (!strcmp(mode, "plan") && L == 0) DIE("unit plans need L >= 1");
    build_walks();
    u64 nshort = 0, nfull = 0; for (int i = 0; i < nsel; i++) { nshort += sel[i].ty == 1; nfull += sel[i].ty == 0; }
    u64 fact[20]; fact[0] = 1; for (int i = 1; i < 20; i++) fact[i] = fact[i - 1] * i;
    u64 mult = 1; for (int l = 0; l < L; l++) mult *= (u64)(10 + l);
    u64 F3 = fact[NN] + fact[NN - 1] + fact[NN - 2], Q = 2 * nshort * mult, sR = F3 + Q;
    u64 nsu = (u64)ndet; for (int l = 0; l < L - 1; l++) nsu *= (u64)(10 + l);
    fprintf(stderr, "n = %d (L = %d, K = %d, h = %d): selection %d loops, %d detached, %llu full, %llu short, %d walks; "
            "lifted walks %d with %llu rows (%.1fs)\n", NN, L, K, HH, nsel, ndet, (unsigned long long)nfull, (unsigned long long)nshort,
            nwalk, nwl, (unsigned long long)nrows, wall() - t0);
    fprintf(stderr, "F3(%d) %llu, Q %llu, sum R = %llu; units %llu small + %d walk, trails %llu\n", NN, (unsigned long long)F3,
            (unsigned long long)Q, (unsigned long long)sR, (unsigned long long)(L ? nsu : 0), L ? nwl : 0,
            (unsigned long long)(L ? (nsu + nwl) * HH : 0));
    if (!strcmp(mode, "info")) return 0;
    if (!strcmp(mode, "dplan")) { if (L == 0) DIE("dplan needs L >= 1"); dplan(planp); return 0; }
    if (!strcmp(mode, "trails")) {
        tro = outp ? fopen(outp, "w") : stdout; if (!tro) DIE("cannot write");
        all_trails(0); if (tro != stdout) fclose(tro);
        fprintf(stderr, "{\"mode\":\"trails\",\"n\":%d,\"trails\":%llu,\"sumR\":%llu,\"expected_sumR\":%llu,\"seconds\":%.0f}\n", NN,
                (unsigned long long)ntr, (unsigned long long)sumR, (unsigned long long)sR, wall() - t0);
        return sumR == sR ? 0 : 3;
    }
#ifdef _WIN32
    _setmode(_fileno(stdout), _O_BINARY);
#endif
    if (dowrite) {
        if (nto == 0) sinks[nsink++] = stdout;
        for (int i = 0; i < nto; i++) sinks[nsink++] = open_sink(tos[i], i);
    }
    obuf = malloc(OBUF); sha_init(&sha);
    if (evp) { evf = fopen(evp, "w"); if (!evf) DIE("cannot open %s", evp); }
    if (!strcmp(mode, "base")) all_trails(1); else if (!strcmp(mode, "plan")) plan(planp); else DIE("unknown mode");
    flush_out(); fflush(stdout);
    if (evf) fclose(evf);
    char hex[65] = ""; if (dosha) sha_final(&sha, hex);
    int rc = 0;
    for (int i = 0; i < nto; i++) { int r = close_sink(sinks[i], i); fprintf(stderr, "sink %d (%s) exit %d\n", i, tos[i], r); if (r) rc = 4; }
    fprintf(stderr, "{\"mode\":\"%s\",\"n\":%d,\"length\":%llu,\"small_trails\":%llu,\"walk_trails\":%llu,\"sha256\":\"%s\",\"alphabet\":\"%.*s\",\"sha_ni\":%d,\"seconds\":%.0f}\n",
            mode, NN, (unsigned long long)written, (unsigned long long)cnt_small, (unsigned long long)cnt_walk, hex, NN, alp,
#ifdef HAVE_SHANI
            1,
#else
            0,
#endif
            wall() - t0);
    if (expect_len) {
        int ok = written == expect_len && (!expect_sha[0] || !dosha || !strcmp(expect_sha, hex));
        fprintf(stderr, "expected length %llu%s%s: %s\n", expect_len, expect_sha[0] ? " sha256 " : "", expect_sha, ok ? "MATCH" : "MISMATCH");
        if (!ok) return 3;
    }
    return rc;
}
#endif
