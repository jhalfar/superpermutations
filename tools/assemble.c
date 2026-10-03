/* assemble.c - write a superpermutation from an existing word, its piece table and a plan.

   Each plan line is "piece offset".  A closed piece (offset >= 0) is written as cyc[offset..] + cyc[..offset] +
   cyc[offset..offset+h) where cyc = piece[0, length-h); an open piece (offset -1) is written as it is.
   Consecutive pieces are overlapped as much as possible (at most n-1 letters).

   build: cc -O2 -o assemble assemble.c      usage: assemble word.txt pieces.txt plan.txt out.txt */
#if !defined(_WIN32)
#define _FILE_OFFSET_BITS 64
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if defined(_WIN32)
#define fseek64 _fseeki64
#define ftell64 _ftelli64
#else
#define fseek64 fseeko
#define ftell64 ftello
#endif
typedef long long i64;

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: assemble word.txt pieces.txt plan.txt out.txt\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror(argv[1]); return 1; }
    fseek64(f, 0, SEEK_END); i64 sz = ftell64(f); fseek64(f, 0, SEEK_SET);
    unsigned char *W = malloc(sz + 16); i64 got = 0;
    while (got < sz) { size_t r = fread(W + got, 1, (size_t)((sz - got) > (1 << 30) ? (1 << 30) : (sz - got)), f); if (!r) break; got += r; }
    fclose(f);
    FILE *fp = fopen(argv[2], "r"); if (!fp) { perror(argv[2]); return 1; }
    char tag[4]; int n = 0, h = 0; i64 np = 0, nr = 0, L = 0;
    if (fscanf(fp, "%3s %d %d %lld %lld %lld", tag, &n, &h, &np, &nr, &L) != 6) { fprintf(stderr, "bad pieces file\n"); return 1; }
    i64 *ps = malloc(np * 8), *pl = malloc(np * 8); int *cl = malloc(np * sizeof(int));
    for (i64 k = 0; k < np; k++) { i64 idx; if (fscanf(fp, "%3s %lld %lld %lld %d", tag, &idx, &ps[k], &pl[k], &cl[k]) != 5) { fprintf(stderr, "bad P line\n"); return 1; } }
    fclose(fp);
    FILE *fq = fopen(argv[3], "r"), *fo = fopen(argv[4], "wb");
    if (!fq || !fo) { fprintf(stderr, "cannot open plan or output\n"); return 1; }
    i64 maxlen = 0; for (i64 k = 0; k < np; k++) if (pl[k] > maxlen) maxlen = pl[k];
    char *buf = malloc(maxlen + 64), *outb = malloc(1 << 24); size_t ob = 0;
    unsigned char tail[16]; int tl = 0; i64 total = 0, cnt = 0, piece, off;
    while (fscanf(fq, "%lld %lld", &piece, &off) == 2) {
        i64 s = ps[piece], len = pl[piece], m = 0;
        if (off < 0) { memcpy(buf, W + s, len); m = len; }
        else {
            i64 R = len - h;
            memcpy(buf, W + s + off, R - off); m = R - off;
            memcpy(buf + m, W + s, off); m += off;
            for (int t = 0; t < h; t++) buf[m++] = W[s + (off + t) % R];
        }
        int k = 0;
        if (cnt > 0) for (int kk = tl; kk > 0; kk--) if (kk <= m && !memcmp(tail + tl - kk, buf, kk)) { k = kk; break; }
        for (i64 i = k; i < m; i++) { outb[ob++] = buf[i]; if (ob == (1 << 24)) { fwrite(outb, 1, ob, fo); ob = 0; } }
        total += m - k; cnt++;
        memcpy(tail, buf + m - (n - 1), n - 1); tl = n - 1;
    }
    outb[ob++] = '\n'; fwrite(outb, 1, ob, fo); fclose(fo); fclose(fq);
    fprintf(stderr, "pieces %lld, length %lld (input word %lld)\n", cnt, total, L);
    return 0;
}
