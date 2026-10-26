/* genBt.c - opt/n17/gen17t.c with construction (B) of opt/const15 (agent constB, 2026-10-26; design: DESIGN.md).
   --block FILE (or env GENB_BLOCK): the (10,3) block relabelled onto every loop without a row of SEL becomes stored
   walks of level 3 (L = 4, 5); small units only for the block's loops without a row (dunit_ok); Q from the stored
   rows (Qall); mode rowcheck.  Everything else is gen17t. */
/* gen17t.c - opt/fastcheck/gen16t.c generalised to n = 12 + L, L = 1..5 (n = 13..17), for agent n17.  Changes:
   - L = 5: the stored level is the 3-lift (13 letters a row, 471 M rows, 3.8 GB, as gen16); the 4-lift and the
     5-lift are both made per walk when a unit needs it (load_walk: two transports of packed rows).  The number of
     walks of each lazy level comes from the orbit structure of the transport (see build_walks); load_walk dies if a
     transport gives another number of orbits, so a wrong count cannot pass silently.  GEN17_LAZY=k (k = 1, 2) makes
     k levels lazy for any L >= k (tests at n = 13..16).
   - slice descriptors: B holds the n - 1 letters other than the satellite s, each stored as c - (c > s), 4 bits a
     letter, so 16 letters (n = 17, letters 0..16) fit the 64-bit field; desc_slice dies if B is not a permutation of
     the letters other than s.  The card decodes the same way (gcheck17.cu: expand).
   - alphabet 0-9A-G; arrays sized for rows of up to 15 letters.
   - unit_trail_small / unit_trail_walk, tail_from, head_from: one trail of a unit and the h letters at either end of
     its piece.  gen17p starts a job with the last h letters of the unit before it (its last trail only), and
     --predict uses the first h letters of each unit against them (the length of a plan without spelling it).
   - "lazycheck L SEL": the counted walks of the lazy levels against real transports of every walk. */
/* gen16t.c - written by tlsify.py from gen16d.c (per-thread state for gen16p); gen16d.c is gen16.c with the descriptor mode of fastcheck v2 (DESC = 1: slices are handed on as spans, not spelled). */
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
typedef struct { u8 x[24]; u8 L; u8 ty; u8 lp; } Row;   /* ty 0 = F, 1 = S, 2 = D */
typedef struct { Row *r; size_t n, cap; } RowVec;
typedef struct { u64 B; u64 st; u32 q; u8 s, v; } SD;
/* gen16t/gen17t: per-thread state (see tlsify.py); lz1 / lz2: the cached transports of the lazy levels */
typedef struct {
    u64 written; int limited; u8 tail[24]; int ntail;
    u64 *wrow, *wstart; int curw; u64 curm;
    int lz1_v; u64 *lz1buf; size_t lz1cap; size_t lz1st[24]; int lz1no;
    int lz2_w; u64 *lz2buf; size_t lz2cap; size_t lz2st[24]; int lz2no;
    u8 *tb; size_t tcap, tn; SD *sd; size_t nsd, sdcap; int nst0; size_t st0[4]; u64 cnt_small, cnt_walk, nev;
} GS;
static __thread GS *gs_tls;
__attribute__((const, noinline)) static GS *GSP(void) { return gs_tls; }
static GS *gs_new(void) { GS *g = calloc(1, sizeof(GS)); if (!g) exit(2); g->curw = -1; g->lz1_v = -1; g->lz2_w = -1; gs_tls = g; return g; }
#define written (GSP()->written)
#define limited (GSP()->limited)
#define tail (GSP()->tail)
#define ntail (GSP()->ntail)
#define wrow (GSP()->wrow)
#define wstart (GSP()->wstart)
#define curw (GSP()->curw)
#define curm (GSP()->curm)
#define tb (GSP()->tb)
#define tcap (GSP()->tcap)
#define tn (GSP()->tn)
#define sd (GSP()->sd)
#define nsd (GSP()->nsd)
#define sdcap (GSP()->sdcap)
#define nst0 (GSP()->nst0)
#define st0 (GSP()->st0)
#define cnt_small (GSP()->cnt_small)
#define cnt_walk (GSP()->cnt_walk)
#define nev (GSP()->nev)

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
static u8 *obuf; static size_t on = 0; static u64 limit = ~0ULL;
static u8 alpha[32]; static Sha sha; static int dosha = 1, dowrite = 1;
static FILE *sinks[MAXSINK]; static int nsink = 0;
          /* last h letters written (letter values) */
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

/* ------------------------------------------------------------------ constB: construction (B)
   The (10,3) block of opt/const15 (BLOCK: 1,320 lines "x T", x = 13 letters 0-9 A B C, T = F / S / D) above every loop
   without a row d of SEL: block letter i < 10 -> x_d[i] (x_d as written in SEL), tokens A, B, C -> 10, 11, 12.  Its
   walks become stored walks of level 3 (after C's 3-lift: stored walk bst0 + d * nbw + k); its loops without a row
   are the triples R (g1, g2, g3) of y(d; g) = x_d with 10, 11, 12 inserted at g1, g2, g3, the same for every d.  Small
   units are allowed only for g in R (dunit_ok).  Checked at start: the 1,320 loops are exactly the cyclic orders above
   0123456789, each once; every row's step (rot(x, +1 full / -1 short), last two letters exchanged) is the written
   form of a row; the rows split into closed walks. */
static const char *blockp;                       /* --block FILE or env GENB_BLOCK */
static int nbw, nbrow, bws[64]; static u8 brow[1320][13], bty[1320];   /* block walks: rows in walk order, starts bws[] */
static u8 rowless[10][11][12]; static int nrowless; static int bst0 = -1; static u64 Qall;
static void bcanon(const u8 *x, u8 *c) { int i = 0; while (x[i]) i++; for (int t = 0; t < 13; t++) c[t] = x[(i + t) % 13]; }
static int blook(u64 (*keys)[2], int n, const u8 *x) { u8 c[13]; bcanon(x, c); u64 k = 0; for (int t = 0; t < 13; t++) k = k << 4 | c[t]; for (int i = 0; i < n; i++) if (keys[i][0] == k) return i; return -1; }
static void read_block(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) DIE("cannot open block %s", path);
    static u8 bx[1320][13], bt[1320]; static u64 keys[1320][2]; int n = 0; char line[256], xs[64], ts[64];
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#' || line[0] == '\n' || line[0] == '\r') continue;
        if (sscanf(line, "%63s %63s", xs, ts) != 2 || strlen(xs) != 13) DIE("block: bad line %s", line);
        if (n == 1320) DIE("block: more than 1320 loops");
        int seen = 0;
        for (int t = 0; t < 13; t++) { char c = xs[t]; int v = c >= '0' && c <= '9' ? c - '0' : c >= 'A' && c <= 'C' ? c - 'A' + 10 : -1; if (v < 0) DIE("block: letter %c", c); bx[n][t] = (u8)v; seen |= 1 << v; }
        if (seen != 0x1fff) DIE("block: row is not a permutation of 13 letters");
        bt[n] = ts[0] == 'F' ? 0 : ts[0] == 'S' ? 1 : ts[0] == 'D' ? 2 : 9; if (bt[n] == 9) DIE("block: type %s", ts);
        u8 c[13]; bcanon(bx[n], c); u64 k = 0; for (int t = 0; t < 13; t++) k = k << 4 | c[t];
        for (int i = 0; i < n; i++) if (keys[i][0] == k) DIE("block: loop twice");
        keys[n][0] = k; n++;
    }
    fclose(f);
    if (n != 1320) DIE("block: %d loops, expected 1320", n);
    /* the 1,320 triples give the 1,320 loops above 0123456789, each once */
    static char used[1320]; nrowless = 0;
    for (int g1 = 0; g1 < 10; g1++) for (int g2 = 0; g2 < 11; g2++) for (int g3 = 0; g3 < 12; g3++) {
        u8 y[16], t[16]; for (int i = 0; i < 10; i++) y[i] = (u8)i;
        ins(t, y, 10, 10, g1); ins(y, t, 11, 11, g2); ins(t, y, 12, 12, g3);
        int i = blook(keys, n, t); if (i < 0) DIE("block: loop of (%d,%d,%d) missing", g1, g2, g3);
        if (used[i]++) DIE("block: loop of (%d,%d,%d) twice", g1, g2, g3);
        rowless[g1][g2][g3] = bt[i] == 2; nrowless += bt[i] == 2;
    }
    /* walks */
    static char vis[1320]; nbw = 0; nbrow = 0; int nlive = 0;
    for (int i0 = 0; i0 < n; i0++) {
        if (bt[i0] == 2) continue;
        nlive++;
        if (vis[i0]) continue;
        if (nbw == 63) DIE("block: too many walks");
        bws[nbw++] = nbrow; int i = i0;
        while (!vis[i]) {
            vis[i] = 1; memcpy(brow[nbrow], bx[i], 13); bty[nbrow] = bt[i]; nbrow++;
            u8 y[13]; rot(y, bx[i], 13, bt[i] == 0 ? 1 : -1); u8 s = y[11]; y[11] = y[12]; y[12] = s;
            int j = blook(keys, n, y); if (j < 0 || bt[j] == 2) DIE("block: step leaves the rows");
            if (memcmp(bx[j], y, 13)) DIE("block: step lands on another rotation");
            i = j;
        }
        if (i != i0) DIE("block: walk does not close at its first row");
    }
    bws[nbw] = nbrow;
    if (nbrow != nlive) DIE("block: %d rows in walks, %d rows", nbrow, nlive);
    fprintf(stderr, "block %s: %d rows in %d walks, %d loops without a row\n", path, nbrow, nbw, nrowless);
}
static inline int dunit_ok(const int *g) { return !blockp || L < 4 || rowless[g[0]][g[1]][g[2]]; }
/* small units of the plan: ndet * (all g) without the block, ndet * |R| * (13 at L = 5) with it */
static u64 n_small_units(void) {
    u64 nsu = (u64)ndet;
    if (blockp && L >= 4) { nsu *= (u64)nrowless; for (int l = 3; l < L - 1; l++) nsu *= (u64)(10 + l); }
    else for (int l = 0; l < L - 1; l++) nsu *= (u64)(10 + l);
    return nsu;
}
/* id of a small unit (d, g): d * prod + mixed radix g; prod = 10 * 11 * .. (L - 1 factors) */
static u64 small_id_space(void) { u64 p = (u64)ndet; for (int l = 0; l < L - 1; l++) p *= (u64)(10 + l); return p; }
static u64 small_id(int d, const int *g) { u64 id = (u64)d; for (int l = 0; l < L - 1; l++) id = id * (u64)(10 + l) + (u64)g[l]; return id; }

/* transport one walk (rows of length n, letters 0..n-1) by inserting letter n; appends the orbit walks */
static void rv_push(RowVec *v, const Row *r) { if (v->n == v->cap) { v->cap = v->cap ? v->cap * 2 : 1024; v->r = realloc(v->r, sizeof(Row) * v->cap); if (!v->r) DIE("oom"); } v->r[v->n++] = *r; }
static int transport(const Row *w, size_t m, RowVec *out, size_t *ostart) {
    int n = w[0].L, H = n - 1, k = n; char done[24] = {0}; int no = 0;
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
                else { a.lp = 1; ins(a.x, r->x, n, k, n - 2); rv_push(out, &a); u8 y[24]; ins(y, r->x, n, k, n - 1); rot(a.x, y, n + 1, -1); rv_push(out, &a); }
            }
            p = (p + (r->ty == 0 ? -1 : 1) + H) % H;
            if (++i == m) { i = 0; if (p == p0) break; }
        }
    }
    ostart[no] = out->n;
    return no;
}

/* the walks of the L-lift: rows packed (K letters, 4 bits each; bit 60 = short, bit 61 = lp).
   Stored level LB = L - LAZY (built by lift_rec with Row structs, as gen15); the LAZY = 0, 1 or 2 levels above it are
   made per walk when a unit needs it (load_walk: ptransport on packed rows, the same rules as transport).
   Walk numbering of the lazy levels (the order lift_rec would give): the walks of a transport are its orbits, the
   cycles of the ports under p -> p + D (mod H), D = (short rows - full rows) of the walk, H = its row length - 1;
   there are g = gcd(D mod H, H) of them (H if D = 0 mod H), orbit a starts at port a and makes P = H / g passes.
   Level 1 (from a stored walk): g from D directly.  Level 2: needs D of every level-1 walk; for orbit a of a stored
   walk with prefix sums pre_i (sum of +1 short / -1 full over rows before i), every row i is visited at the ports
   a + pre_i + r D (r < P), which hit a port c exactly when c - a - pre_i = 0 (mod g).  A full row at port 0 gives
   two full rows, a short row at port H - 1 two short rows, every other visit one row of its type, so
     D(orbit a) = P (S - F) - #{full i : -a - pre_i = 0 (mod g)} + #{short i : H - 1 - a - pre_i = 0 (mod g)}.
   load_walk dies if a transport gives another number of orbits than counted here ("gen17t lazycheck" compares the
   formula with the transports for every walk). */
static int nwl; static u64 nrows; static u64 *wrow_sh, *wstart_sh;   /* the stored walks (shared) */
static int *wbase;                                   /* walk of SEL for each stored walk */
static int wcap = 0, KP, LB, LAZY;                   /* letters per stored row; stored level; lazy levels */
static int nst, nw1; static int *pre1, *pre2;         /* stored walks; level-1 walks; first walk numbers */
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
static RowVec lv[4]; static size_t los[4][24];
static void lift_rec(const Row *w, size_t m, int lev, int wi) {
    if (lev == LB) { wl_add_walk(w, m, wi); return; }
    RowVec *v = &lv[lev]; v->n = 0;
    int no = transport(w, m, v, los[lev]);
    size_t st[24]; memcpy(st, los[lev], sizeof st);
    for (int a = 0; a < no; a++) lift_rec(v->r + st[a], st[a + 1] - st[a], lev + 1, wi);
}
static int gcdi(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static inline int modp(i64 x, int g) { x %= g; return (int)(x < 0 ? x + g : x); }
/* x (n letters, no flags) with letter z inserted before position j (0 <= j <= n, n <= 14) */
static inline u64 pins(u64 x, int z, int j) { u64 lo = x & ((1ULL << (4 * j)) - 1), hi = x >> (4 * j); return lo | (u64)z << (4 * j) | hi << (4 * (j + 1)); }
/* transport of a packed walk w (m rows of n letters) by letter n: the rules of transport(), orbits by first port */
static int ptransport(const u64 *w, size_t m, int n, u64 **out, size_t *ocap, size_t *ost_) {
    int H = n - 1, k = n, no = 0; char done[24] = {0}; size_t on = 0; u64 LM = (1ULL << (4 * n)) - 1;
    if (n > 14) DIE("ptransport: rows of %d letters", n);
    for (int p0 = 0; p0 < H; p0++) {
        if (done[p0]) continue;
        ost_[no++] = on; int p = p0; size_t i = 0;
        for (;;) {
            if (i == 0) { if (done[p]) DIE("repeated transport port"); done[p] = 1; }
            u64 r = w[i], x = r & LM; int ty = (int)(r >> 60 & 1);
            if (on + 2 > *ocap) { *ocap = *ocap ? 2 * *ocap : 65536; *out = realloc(*out, 8 * *ocap); if (!*out) DIE("oom (ptransport)"); }
            u64 *o = *out;
            if (ty == 0) {
                if (p == 0) { o[on++] = pins(x, k, 0); o[on++] = pins(x, k, n - 1); }
                else o[on++] = pins(x, k, p);
            } else {
                u64 f = 1ULL << 60;
                if (p < n - 2) o[on++] = pins(x, k, p) | f;
                else { f |= 1ULL << 61; o[on++] = pins(x, k, n - 2) | f; u64 y = pins(x, k, n - 1); o[on++] = ((y >> (4 * n)) & 15) | (y & LM) << 4 | f; }
            }
            p = (p + (ty == 0 ? -1 : 1) + H) % H;
            if (++i == m) { i = 0; if (p == p0) break; }
        }
    }
    ost_[no] = on;
    return no;
}
/* orbits of the transport of packed walk w (m rows of n letters): returns their number g; dl[a] = D of orbit a */
static int orbits_of(const u64 *w, size_t m, int n, i64 *dl) {
    int H = n - 1; i64 S = 0, F = 0;
    for (size_t i = 0; i < m; i++) { if (w[i] >> 60 & 1) S++; else F++; }
    int d = modp(S - F, H), g = d == 0 ? H : gcdi(d, H);
    if (!dl) return g;
    int P = H / g; i64 *cf = calloc(g, sizeof(i64)), *cs = calloc(g, sizeof(i64)); i64 pre = 0;
    /* cs[c]: short rows with H-1-pre_i = c (mod g), hit at port H-1 by orbit c; cf[c]: full rows with -pre_i = c */
    for (size_t i = 0; i < m; i++) { int ty = (int)(w[i] >> 60 & 1); if (ty) cs[modp(H - 1 - pre, g)]++; else cf[modp(-pre, g)]++; pre += ty ? 1 : -1; }
    for (int a = 0; a < g; a++) dl[a] = (i64)P * (S - F) - cf[a] + cs[a];
    free(cf); free(cs);
    return g;
}
static void build_walks(void) {
    const char *e = getenv("GEN17_LAZY");
    if (!blockp) { const char *bp = getenv("GENB_BLOCK"); if (bp && *bp) blockp = bp; }
    if (blockp) read_block(blockp);
    LAZY = L >= 5 ? 2 : L == 4 ? 1 : 0;
    if (e) { LAZY = atoi(e); if (LAZY < 0 || LAZY > 2 || LAZY > L || L - LAZY > 3) DIE("bad GEN17_LAZY"); }
    LB = L - LAZY; KP = 10 + LB;
    u64 base = 0; for (int i = 0; i < nsel; i++) base += sel[i].ty != 2;
    u64 cap = base; for (int l = 0; l < LB; l++) cap *= (u64)(10 + l);
    if (blockp && LB != 3) DIE("the block needs the stored level 3 (L = 4 with 1 lazy level or L = 5 with 2)");
    u64 extra = blockp ? (u64)ndet * (u64)nbrow : 0;
    wrow = malloc(8 * (cap + extra) + 8); if (!wrow) DIE("cannot allocate %llu rows", (unsigned long long)(cap + extra));
    nrows = 0; nwl = 0;
    Row *tmp = malloc(sizeof(Row) * nsel);
    for (int wi = 0; wi < nwalk; wi++) {
        int m = walkstart[wi + 1] - walkstart[wi];
        for (int i = 0; i < m; i++) tmp[i] = sel[walkrow[walkstart[wi] + i]];
        lift_rec(tmp, m, 0, wi);
    }
    if (nrows != cap) DIE("rows %llu, expected %llu", (unsigned long long)nrows, (unsigned long long)cap);
    if (blockp) {                                    /* constB: the block relabelled onto every loop without a row */
        bst0 = nwl; Row br[1320];
        for (int d = 0; d < ndet; d++) {
            const u8 *xd = sel[det[d]].x;
            for (int k = 0; k < nbw; k++) {
                int m = bws[k + 1] - bws[k];
                for (int i = 0; i < m; i++) {
                    Row *r = &br[i]; memset(r, 0, sizeof *r); r->L = 13; r->ty = bty[bws[k] + i]; r->lp = 0;
                    for (int t = 0; t < 13; t++) { int c = brow[bws[k] + i][t]; r->x[t] = c < 10 ? xd[c] : (u8)c; }
                }
                wl_add_walk(br, m, -1 - d);
            }
        }
        cap += extra;
        if (nrows != cap) DIE("rows %llu with the blocks, expected %llu", (unsigned long long)nrows, (unsigned long long)cap);
    }
    { u64 ns = 0; for (u64 i = 0; i < nrows; i++) ns += wrow[i] >> 60 & 1; Qall = 2 * ns; for (int l = 0; l < LAZY; l++) Qall *= (u64)(KP + l); }
    free(tmp); for (int l = 0; l < 4; l++) { free(lv[l].r); lv[l].r = NULL; lv[l].cap = 0; }
    wrow_sh = wrow; wstart_sh = wstart; nst = nwl;
    if (!LAZY) return;
    pre1 = malloc(sizeof(int) * (nst + 1)); pre1[0] = 0;
    i64 dl[24];
    if (LAZY == 2) { u64 n1 = 0; for (int v = 0; v < nst; v++) n1 += orbits_of(wrow_sh + wstart_sh[v], wstart_sh[v + 1] - wstart_sh[v], KP, NULL); pre2 = malloc(sizeof(int) * (n1 + 1)); pre2[0] = 0; }
    for (int v = 0; v < nst; v++) {
        int g = orbits_of(wrow_sh + wstart_sh[v], wstart_sh[v + 1] - wstart_sh[v], KP, LAZY == 2 ? dl : NULL);
        if (LAZY == 2) for (int a = 0; a < g; a++) { int H2 = KP, d = modp(dl[a], H2), g2 = d == 0 ? H2 : gcdi(d, H2); pre2[pre1[v] + a + 1] = pre2[pre1[v] + a] + g2; }
        pre1[v + 1] = pre1[v] + g;
    }
    nw1 = pre1[nst]; nwl = LAZY == 2 ? pre2[nw1] : nw1;
    nrows = cap * (u64)KP; if (LAZY == 2) nrows *= (u64)(KP + 1);   /* every row gives H + 1 rows over the orbits of its transport */
    wrow = NULL; wstart = NULL;
}
static inline int pre_find(const int *pre, int cnt, int w) { int lo = 0, hi = cnt; while (hi - lo > 1) { int mid = (lo + hi) / 2; if (pre[mid] <= w) lo = mid; else hi = mid; } return lo; }
/* make walk w of the top level the current one (wrow = its rows, curm = their number) */
static void load_walk(int w) {
    if (!LAZY || w == curw) return;
    int w1 = w, a2 = 0;
    if (LAZY == 2) { w1 = pre_find(pre2, nw1, w); a2 = w - pre2[w1]; }
    int v = pre_find(pre1, nst, w1), a1 = w1 - pre1[v];
    GS *G = GSP();
    if (v != G->lz1_v) {
        int no = ptransport(wrow_sh + wstart_sh[v], wstart_sh[v + 1] - wstart_sh[v], KP, &G->lz1buf, &G->lz1cap, G->lz1st);
        if (no != pre1[v + 1] - pre1[v]) DIE("stored walk %d: %d orbits, expected %d", v, no, pre1[v + 1] - pre1[v]);
        G->lz1_v = v; G->lz1no = no; G->lz2_w = -1;
    }
    if (LAZY == 1) { wrow = G->lz1buf + G->lz1st[a1]; curm = G->lz1st[a1 + 1] - G->lz1st[a1]; curw = w; return; }
    if (w1 != G->lz2_w) {
        int no = ptransport(G->lz1buf + G->lz1st[a1], G->lz1st[a1 + 1] - G->lz1st[a1], KP + 1, &G->lz2buf, &G->lz2cap, G->lz2st);
        if (no != pre2[w1 + 1] - pre2[w1]) DIE("level-1 walk %d: %d orbits, expected %d", w1, no, pre2[w1 + 1] - pre2[w1]);
        G->lz2_w = w1; G->lz2no = no;
    }
    wrow = G->lz2buf + G->lz2st[a2]; curm = G->lz2st[a2 + 1] - G->lz2st[a2]; curw = w;
}
static inline u64 wbeg(int w) { return LAZY ? 0 : wstart_sh[w]; }
static inline u64 wlen(int w) { return LAZY ? curm : wstart_sh[w + 1] - wstart_sh[w]; }
/* lazycheck: the counted orbits and D values against real transports of every stored walk (and level-1 walk) */
static int lazycheck(void) {
    u64 *b1 = NULL, *b2 = NULL; size_t c1 = 0, c2 = 0, s1[24], s2[24]; i64 dl[24]; u64 bad = 0, chk1 = 0, chk2 = 0, rows2 = 0;
    for (int v = 0; v < nst; v++) {
        const u64 *w = wrow_sh + wstart_sh[v]; size_t m = wstart_sh[v + 1] - wstart_sh[v];
        int g = orbits_of(w, m, KP, dl), no = ptransport(w, m, KP, &b1, &c1, s1);
        if (no != g) bad++;
        for (int a = 0; a < no; a++) {
            i64 D = 0; for (size_t q = s1[a]; q < s1[a + 1]; q++) D += (b1[q] >> 60 & 1) ? 1 : -1;
            if (D != dl[a]) bad++;
            chk1++;
            if (KP + 1 <= 14) { int g2 = orbits_of(b1 + s1[a], s1[a + 1] - s1[a], KP + 1, NULL), n2 = ptransport(b1 + s1[a], s1[a + 1] - s1[a], KP + 1, &b2, &c2, s2); if (g2 != n2) bad++; chk2++; rows2 += s2[n2]; }
        }
    }
    fprintf(stderr, "{\"mode\":\"lazycheck\",\"stored_walks\":%d,\"level1_walks\":%llu,\"level2_transports\":%llu,\"level2_rows\":%llu,\"mismatches\":%llu}\n", nst, (unsigned long long)chk1, (unsigned long long)chk2, (unsigned long long)rows2, (unsigned long long)bad);
    return bad ? 3 : 0;
}
static inline void unpackK(u64 k, u8 *x) { for (int t = 0; t < K; t++) x[t] = (k >> (4 * t)) & 15; }
static inline int rty(u64 k) { return (int)((k >> 60) & 1); }

/* ------------------------------------------------------------------ spelling */
       /* cyclic word of the current trail */
static inline void tneed(size_t add) { if (tn + add > tcap) { tcap = (tn + add) * 2 + 65536; tb = realloc(tb, tcap); if (!tb) DIE("oom"); } }
/* fastcheck v2, descriptor mode (DESC = 1): a slice is not spelled; it is kept as (B packed 4 bits a letter,
   satellite s, classes v, start in the trail, full length q).  The trail's cyclic word is still the concatenation of
   the first q - h letters of its slices, so every letter can be read back (tbat), and a piece is handed on as spans
   (slice, from, length) through span_hook; the card spells them (gcheck.cu: expand). */
static int DESC = 0;

static void (*span_hook)(const SD *d, u32 from, u32 len);
static void desc_slice(const u8 *B, int s, int v) {
    int n1 = NN - 1; u32 full = (u32)(2 * n1 + 1 + (v - 1) * (n1 + 2));
    if (nsd == sdcap) { sdcap = sdcap ? 2 * sdcap : 4096; sd = realloc(sd, sdcap * sizeof(SD)); if (!sd) DIE("oom"); }
    u64 b = 0; u32 seen = 1u << s;
    for (int i = 0; i < n1; i++) { int c = B[i]; if (c >= NN || (seen >> c & 1)) DIE("slice: B is not a permutation of the letters other than %d", s); seen |= 1u << c; b |= (u64)(c - (c > s)) << (4 * i); }
    SD *z = &sd[nsd++]; z->B = b; z->st = tn; z->q = full; z->s = (u8)s; z->v = (u8)v;
    tn += full - HH;
}
static inline u8 sd_b(const SD *z, u32 i) { u32 c = (u32)(z->B >> (4 * i)) & 15; return (u8)(c + (c >= z->s)); }   /* letter i of B */
static inline u8 sd_letter(const SD *z, u32 p) {
    int n1 = NN - 1;
    if (p < (u32)n1) return sd_b(z, p);
    if (p == (u32)n1) return z->s;
    if (p < (u32)(2 * n1 + 1)) return sd_b(z, p - n1 - 1);
    u32 r0 = p - 2 * n1 - 1, t = r0 / (n1 + 2), r = r0 % (n1 + 2);
    if (r == 0) return sd_b(z, t);
    if (r == 1) return z->s;
    u32 k = t + 1 + r - 2; if (k >= (u32)n1) k -= n1;
    return sd_b(z, k);
}
static size_t sd_find(u64 pos) {                     /* the slice holding trail position pos (0 <= pos < tn) */
    size_t lo = 0, hi = nsd;
    while (hi - lo > 1) { size_t m = (lo + hi) / 2; if (sd[m].st <= pos) lo = m; else hi = m; }
    return lo;
}
static inline u8 tbat(u64 pos) { pos %= tn; size_t k = sd_find(pos); return sd_letter(&sd[k], (u32)(pos - sd[k].st)); }
static void emit_spans(u64 a, u64 b) {               /* trail positions [a, b), 0 <= a <= b <= tn + h */
    if (a >= b || limited) return;
    size_t k = sd_find(a);
    while (a < b) {
        if (k >= nsd) DIE("span beyond the trail");
        u64 end = sd[k].st + sd[k].q - (k + 1 == nsd ? 0 : HH);   /* the last slice also holds tb[tn .. tn+h), as gen15 reads it */
        u64 lim = b < end ? b : end; u64 len = lim - a;
        if (written + len >= limit) { len = limit - written; limited = 1; }
        if (len) span_hook(&sd[k], (u32)(a - sd[k].st), (u32)len);
        written += len;
        if (limited) return;
        a = lim; k++;
    }
}
static void piece_desc(size_t c, size_t len, int ov) {
    c %= tn;
    if (ov > ntail) DIE("overlap %d beyond what was written", ov);
    for (int i = 0; i < ov; i++) if (tail[ntail - ov + i] != tbat(c + i)) DIE("overlap mismatch at letter %llu", (unsigned long long)written);
    if (len < (size_t)HH || len > 2 * tn) DIE("piece length");
    size_t s = c + ov, e = c + len;
    if (s < tn) { size_t e1 = e < tn ? e : tn; emit_spans(s, e1); s = e1; }
    if (s < e) emit_spans(s - tn, e - tn);
    for (int i = 0; i < HH; i++) tail[i] = tbat(c + len - HH + i);
    ntail = HH;
}
/* one slice: B (n-1 letters), satellite s, v classes: B s B (B[t] s rot(B,t+1))_{t<v-1} minus the last h letters */
static void slice(const u8 *B, int s, int v) {
    if (DESC) { desc_slice(B, s, v); return; }
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
    u8 B[24]; int ns = 0;
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

static u64 walk_trail(int w, u64 i0, int p) {
    u64 a = wbeg(w), m = wlen(w); u8 b[24]; size_t st[4]; int p0 = p; u64 i = i0, steps = 0;
    tn = 0; nsd = 0;
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
    u64 a = wbeg(w), m = wlen(w);
    for (u64 t = 0; t < m; t++) { u64 i = (i0 + t) % m; p = nextport(rty(wrow[a + i]), p); }
    return p;
}
/* small trail (L >= 1): y (K-1 letters), letter K-1 inserted at position at, written from vertex rot(loop, at+1).
   L = 0: y is the detached loop itself (K letters), written from rot(y, at). */
static void small_trail(const u8 *y, int at) {
    u8 loop[24], B[24]; tn = 0; nsd = 0;
    if (L == 0) { memcpy(loop, y, K); for (int j = 0; j < K; j++) { rot(B, loop, K, at + j); B[K] = (u8)SL; slice(B, ZL, K + 1); } return; }
    ins(loop, y, K - 1, K - 1, at);
    for (int j = 0; j < K; j++) { rot(B, loop, K, at + 1 + j); B[K] = (u8)SL; slice(B, ZL, K + 1); }
}

/* ------------------------------------------------------------------ pieces */
static FILE *evf;
/* emit the cyclic word tb[0..tn) from offset c, len letters (len <= 2 tn), overlapping ov letters */
static void piece(size_t c, size_t len, int ov, const char *desc, int ti) {
    if (DESC) { (void)desc; (void)ti; piece_desc(c, len, ov); return; }
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

static void small_y(int d, const int *g, u8 *y) {      /* y = x_d with letters 10 .. 10+L-2 inserted */
    u8 t[24]; memcpy(y, sel[det[d]].x, 10); int n = 10;
    for (int l = 0; l < L - 1; l++) { ins(t, y, n, 10 + l, g[l]); n++; memcpy(y, t, n); }
}
static void unit_small(int d, const int *g, int j, int ovcap) {
    u8 y[24]; small_y(d, g, y);
    char desc[64]; int q = sprintf(desc, "D %d", d); for (int l = 0; l < L - 1; l++) q += sprintf(desc + q, " %d", g[l]); sprintf(desc + q, " %d", j);
    for (int i = 0; i < HH; i++) {
        int at = (j + i) % HH; small_trail(y, at);
        int ov; if (DESC && i == 0 && written) { u8 S0[24]; for (int t = 0; t < HH; t++) S0[t] = tbat(t); ov = maxov(S0, ovcap); } else ov = (i == 0) ? (written ? maxov(tb, ovcap) : 0) : HH - 1;
        piece(0, tn + HH, ov, desc, i);
        cnt_small++;
        if (limited) return;
    }
}
static void unit_walk(int w, u64 i0, int way, int ovcap) {
    load_walk(w);
    u64 a = wbeg(w), m = wlen(w);
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
        if (i == 0) { u8 S[24]; for (int t = 0; t < HH; t++) S[t] = DESC ? tbat(cut + t) : tb[(cut + t) % tn]; ov = written ? maxov(S, ovcap) : 0; }
        else ov = HH;
        piece(cut, tn + HH + 1, ov, desc, i);
        cnt_walk++;
        if (limited) return;
    }
}

/* gen17t: one trail of a unit, built in descriptors (DESC = 1) exactly as unit_small / unit_walk build it; *c and
   *len are its piece (from trail offset c, len letters).  Used for the last h letters of a unit (unit_tail: the tail
   before a job of gen17p) and for --predict (first h letters of the first piece, last h letters of the last). */
static void unit_trail_small(int d, const int *g, int j, int i, size_t *c, size_t *len) {
    u8 y[24]; small_y(d, g, y); small_trail(y, (j + i) % HH); *c = 0; *len = tn + HH;
}
static void unit_trail_walk(int w, u64 i0, int way, int i, size_t *c, size_t *len) {
    load_walk(w);
    u64 a = wbeg(w), m = wlen(w);
    if (i0 >= m || rty(wrow[a + i0]) != 0) DIE("walk unit %d: row %llu is not a full row", w, (unsigned long long)i0);
    int q = way == 0 ? i : i + 1, port = q == K - 1 ? 0 : q;
    if (walk_endport(w, i0, port) != port) DIE("walk %d: trail of port %d is not one pass", w, port);
    walk_trail(w, i0, port);
    size_t s0 = (q == K - 1) ? st0[1] : st0[0];
    *c = s0 + (size_t)(q + 1) * (NN + 1); *len = tn + HH + 1;
}
static void tail_from(size_t c, size_t len) { if (!DESC) DIE("tail_from needs DESC"); for (int t = 0; t < HH; t++) tail[t] = tbat(c + len - HH + t); ntail = HH; }
static void head_from(size_t c, u8 *hd) { if (!DESC) DIE("head_from needs DESC"); for (int t = 0; t < HH; t++) hd[t] = tbat(c + t); }

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
            int d = atoi(tok[1]), g[5], j = atoi(tok[nt - 1]);
            if (d < 0 || d >= ndet || j < 0 || j >= HH) DIE("bad D line %d", nl);
            for (int l = 0; l < L - 1; l++) { g[l] = atoi(tok[2 + l]); if (g[l] < 0 || g[l] > 9 + l) DIE("bad D line %d", nl); }
            if (!dunit_ok(g)) DIE("D line %d: its loop has a row of the block", nl);
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
    int g[5] = {0, 0, 0, 0, 0};
    for (int d = 0; d < ndet; d++) {
        for (;;) {
            if (dunit_ok(g)) { fprintf(o, "D %d", d); for (int l = 0; l < L - 1; l++) fprintf(o, " %d", g[l]); fprintf(o, " 0\n"); }
            int l = L - 2; while (l >= 0) { if (++g[l] <= 9 + l) break; g[l] = 0; l--; }
            if (l < 0) break;
        }
    }
    for (int w = 0; w < nwl; w++) {
        load_walk(w);
        u64 a = wbeg(w), m = wlen(w), i = 0;
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
    int g[5] = {0, 0, 0, 0, 0};
    for (int d = 0; d < ndet; d++) {
        for (;;) {
            u8 y[24];
            if (L == 0) memcpy(y, sel[det[d]].x, 10); else small_y(d, g, y);
            int nt = !dunit_ok(g) ? 0 : L == 0 ? 1 : HH;
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
        u64 a = wbeg(w), m = wlen(w);
        if (L >= 1) {
            for (int p = 0; p < K - 1; p++) {
                walk_trail(w, 0, p);
                if (base) { int ov = written ? maxov(tb, HH) : 0; piece(0, tn + HH, ov, "W", p); cnt_walk++; }
                else trail_out();
            }
        } else {
            /* port orbits: (row 0, port) pairs already used */
            char used[24] = {0};
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

/* constB rowcheck: every walk (stored, and the level-1 transports of the block walks) steps in SEL's convention:
   row i+1 = rot(row i, +1 full / -1 short) with the last two letters exchanged */
static u64 rc_walk(const u64 *w, size_t m, int n) {
    u64 bad = 0;
    for (size_t i = 0; i < m; i++) {
        u8 x[24], y[24], z[24]; for (int t = 0; t < n; t++) { x[t] = (w[i] >> (4 * t)) & 15; z[t] = (w[(i + 1) % m] >> (4 * t)) & 15; }
        rot(y, x, n, (w[i] >> 60 & 1) ? -1 : 1); u8 s = y[n - 2]; y[n - 2] = y[n - 1]; y[n - 1] = s;
        if (memcmp(y, z, n)) bad++;
    }
    return bad;
}
static int rowcheck(void) {
    u64 bad = 0, walks = 0, rows = 0, bad1 = 0, w1 = 0; u64 *b1 = NULL; size_t c1 = 0, s1[24];
    for (int v = 0; v < nst; v++) {
        size_t m = wstart_sh[v + 1] - wstart_sh[v]; bad += rc_walk(wrow_sh + wstart_sh[v], m, KP); walks++; rows += m;
        if (blockp && v >= bst0 && v < bst0 + nbw * 64 && KP < 14) {
            int no = ptransport(wrow_sh + wstart_sh[v], m, KP, &b1, &c1, s1);
            for (int a = 0; a < no; a++) { bad1 += rc_walk(b1 + s1[a], s1[a + 1] - s1[a], KP + 1); w1++; }
        }
    }
    fprintf(stderr, "{\"mode\":\"rowcheck\",\"stored_walks\":%llu,\"stored_rows\":%llu,\"bad_steps\":%llu,\"block_level1_walks\":%llu,\"block_level1_bad_steps\":%llu}\n",
            (unsigned long long)walks, (unsigned long long)rows, (unsigned long long)bad, (unsigned long long)w1, (unsigned long long)bad1);
    return bad || bad1 ? 3 : 0;
}

#ifndef GEN15_NO_MAIN
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: genBt info|lazycheck|rowcheck|trails|base|plan|dplan L SEL [PLAN|OUT] [--block FILE] [options]\n"); return 2; }
    double t0 = wall();
    t0g = t0; gs_new();
    const char *mode = argv[1], *selp = argv[3], *planp = NULL, *alp = NULL, *evp = NULL, *outp = NULL;
    const char *tos[MAXSINK]; int nto = 0;
    L = atoi(argv[2]); if (L < 0 || L > 5) DIE("L must be 0..5");
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
        else if (!strcmp(argv[ai], "--block") && ai + 1 < argc) blockp = argv[++ai];
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
    u64 F3 = fact[NN] + fact[NN - 1] + fact[NN - 2], Q = Qall, sR = F3 + Q; (void)mult;
    u64 nsu = n_small_units();
    fprintf(stderr, "n = %d (L = %d, K = %d, h = %d): selection %d loops, %d detached, %llu full, %llu short, %d walks; "
            "lifted walks %d with %llu rows (%.1fs)\n", NN, L, K, HH, nsel, ndet, (unsigned long long)nfull, (unsigned long long)nshort,
            nwalk, nwl, (unsigned long long)nrows, wall() - t0);
    fprintf(stderr, "F3(%d) %llu, Q %llu, sum R = %llu; units %llu small + %d walk, trails %llu\n", NN, (unsigned long long)F3,
            (unsigned long long)Q, (unsigned long long)sR, (unsigned long long)(L ? nsu : 0), L ? nwl : 0,
            (unsigned long long)(L ? (nsu + nwl) * HH : 0));
    if (!strcmp(mode, "info")) return 0;
    if (!strcmp(mode, "lazycheck")) return lazycheck();
    if (!strcmp(mode, "rowcheck")) return rowcheck();
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
