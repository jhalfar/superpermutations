/* pieces.c - split a component-structured superpermutation word into pieces and runs.

   A piece is a maximal stretch of the word in which consecutive permutation windows are at most 3 letters apart;
   joins between pieces are the steps of weight >= 4.  A closed piece is a closed trail written out once and
   opened at a weight-3 opening: piece = cyc + cyc[0..h), h = n - 3.  A run is a maximal sequence of pieces
   joined with the largest possible overlap h - 1.

   For every run the program lists the opening words (h letters) at which its first and last pieces may be
   re-opened without breaking the run ("S" / "E" lines), or all openings of a single-piece run ("O" lines).
   The piece table ("P" lines) is what assemble.c needs.

   Output format:
     N n h npieces nruns length
     P index start length closed
     R run first_piece last_piece
     S|E|O run offset word        (offset = opening position inside the piece's cyclic word; -1 = open piece)

   build: cc -O2 -o pieces pieces.c          usage: pieces word.txt pieces.txt
   Words of up to ~7e9 letters are fine (the word is held in memory, permutation windows in a bitset). */
#if !defined(_WIN32)
#define _FILE_OFFSET_BITS 64
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#if defined(_WIN32)
#define fseek64 _fseeki64
#define ftell64 _ftelli64
#else
#define fseek64 fseeko
#define ftell64 ftello
#endif

typedef long long i64;
static unsigned char *W; static i64 L; static int n, h;
static uint64_t *isp;
#define ISP(i) ((isp[(i) >> 6] >> ((i) & 63)) & 1)
static const char *AL = "0123456789ABCDEF";

static inline unsigned char cyc(i64 s, i64 R, i64 j) { j %= R; if (j < 0) j += R; return W[s + j]; }
static int isperm_cyc(i64 s, i64 R, i64 j) { int m = 0; for (int k = 0; k < n; k++) m |= 1 << cyc(s, R, j + k); return m == (1 << n) - 1; }
/* weight-3 opening at cyclic position j: permutation windows at j and j-3, none at j-1, j-2 */
static int opening(i64 s, i64 R, i64 j) {
    if (j >= 3 && j + n <= R) return ISP(s + j) && ISP(s + j - 3) && !ISP(s + j - 1) && !ISP(s + j - 2);
    return isperm_cyc(s, R, j) && isperm_cyc(s, R, j - 3) && !isperm_cyc(s, R, j - 1) && !isperm_cyc(s, R, j - 2);
}
static void word_at(i64 s, i64 R, i64 j, char *out) { for (int k = 0; k < h; k++) out[k] = AL[cyc(s, R, j + k)]; out[h] = 0; }
static void tail_word(i64 s, i64 len, char *out) { for (int k = 0; k < h; k++) out[k] = AL[W[s + len - h + k]]; out[h] = 0; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: pieces word.txt pieces.txt\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror(argv[1]); return 1; }
    fseek64(f, 0, SEEK_END); i64 sz = ftell64(f); fseek64(f, 0, SEEK_SET);
    W = malloc(sz + 16);
    i64 got = 0;
    while (got < sz) { size_t r = fread(W + got, 1, (size_t)((sz - got) > (1 << 30) ? (1 << 30) : (sz - got)), f); if (!r) break; got += r; }
    fclose(f); L = got; while (L > 0 && (W[L - 1] == '\n' || W[L - 1] == '\r')) L--;
    int map[256]; for (int c = 0; c < 256; c++) map[c] = -1;
    for (int c = 0; c < 16; c++) map[(unsigned char)AL[c]] = c;
    int mx = 0;
    for (i64 i = 0; i < L; i++) { int v = map[W[i]]; if (v < 0) { fprintf(stderr, "bad symbol\n"); return 1; } W[i] = (unsigned char)v; if (v > mx) mx = v; }
    n = mx + 1; h = n - 3;
    fprintf(stderr, "n=%d length=%lld\n", n, L);
    isp = calloc((size_t)(L >> 6) + 2, 8);
    int cnt[16] = {0}, distinct = 0;
    for (i64 i = 0; i < L; i++) {
        if (cnt[W[i]]++ == 0) distinct++;
        if (i >= n) { if (--cnt[W[i - n]] == 0) distinct--; }
        if (i >= n - 1 && distinct == n) { i64 p = i - n + 1; isp[p >> 6] |= 1ULL << (p & 63); }
    }
    /* pieces */
    i64 cap = 1 << 16, npc = 0; i64 *ps = malloc(cap * 8), *pl = malloc(cap * 8);
    i64 prev = -1, pstart = -1;
    for (i64 i = 0; i + n <= L; i++) {
        if (!ISP(i)) continue;
        if (prev < 0) pstart = i;
        else if (i - prev >= 4) {
            if (npc == cap) { cap *= 2; ps = realloc(ps, cap * 8); pl = realloc(pl, cap * 8); }
            ps[npc] = pstart; pl[npc] = prev + n - pstart; npc++; pstart = i;
        }
        prev = i;
    }
    if (npc == cap) { cap *= 2; ps = realloc(ps, cap * 8); pl = realloc(pl, cap * 8); }
    ps[npc] = pstart; pl[npc] = prev + n - pstart; npc++;
    char *closed = calloc((size_t)npc, 1);
    for (i64 k = 0; k < npc; k++) {
        i64 s = ps[k], len = pl[k], R = len - h;
        if (R > 2 * n && !memcmp(W + s + R, W + s, (size_t)(len - R))) closed[k] = 1;
    }
    int *ov = malloc((size_t)npc * sizeof(int));
    for (i64 k = 0; k + 1 < npc; k++) ov[k] = (int)(ps[k] + pl[k] - ps[k + 1]);
    i64 nruns = 1; for (i64 k = 0; k + 1 < npc; k++) if (ov[k] != h - 1) nruns++;
    FILE *fo = fopen(argv[2], "w"); if (!fo) { perror(argv[2]); return 1; }
    fprintf(fo, "N %d %d %lld %lld %lld\n", n, h, npc, nruns, L);
    for (i64 k = 0; k < npc; k++) fprintf(fo, "P %lld %lld %lld %d\n", k, ps[k], pl[k], closed[k]);
    i64 rid = 0, first = 0; char wb[32];
    for (i64 k = 0; k < npc; k++) {
        if (k + 1 < npc && ov[k] == h - 1) continue;
        i64 last = k;
        fprintf(fo, "R %lld %lld %lld\n", rid, first, last);
        if (first == last) {
            if (closed[first]) {
                i64 s = ps[first], R = pl[first] - h;
                for (i64 j = 0; j < R; j++) if (opening(s, R, j)) { word_at(s, R, j, wb); fprintf(fo, "O %lld %lld %s\n", rid, j, wb); }
            } else {
                word_at(ps[first], pl[first], 0, wb); fprintf(fo, "S %lld -1 %s\n", rid, wb);
                tail_word(ps[first], pl[first], wb); fprintf(fo, "E %lld -1 %s\n", rid, wb);
            }
        } else {
            if (closed[first]) {   /* b[1:] must equal the next piece's start word [0, h-1) */
                i64 s = ps[first], R = pl[first] - h; const unsigned char *nx = W + ps[first + 1];
                for (i64 j = 0; j < R; j++) {
                    int ok = 1; for (int t = 0; t < h - 1 && ok; t++) ok = cyc(s, R, j + 1 + t) == nx[t];
                    if (ok && opening(s, R, j)) { word_at(s, R, j, wb); fprintf(fo, "S %lld %lld %s\n", rid, j, wb); }
                }
            } else { word_at(ps[first], pl[first], 0, wb); fprintf(fo, "S %lld -1 %s\n", rid, wb); }
            if (closed[last]) {    /* e[0, h-1) must equal the previous piece's end word [1, h) */
                i64 s = ps[last], R = pl[last] - h; const unsigned char *pe = W + ps[last - 1] + pl[last - 1] - h;
                for (i64 j = 0; j < R; j++) {
                    int ok = 1; for (int t = 0; t < h - 1 && ok; t++) ok = cyc(s, R, j + t) == pe[t + 1];
                    if (ok && opening(s, R, j)) { word_at(s, R, j, wb); fprintf(fo, "E %lld %lld %s\n", rid, j, wb); }
                }
            } else { tail_word(ps[last], pl[last], wb); fprintf(fo, "E %lld -1 %s\n", rid, wb); }
        }
        rid++; first = k + 1;
    }
    fclose(fo);
    fprintf(stderr, "pieces %lld, runs %lld\n", npc, rid);
    return 0;
}
