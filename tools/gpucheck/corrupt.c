/* corrupt.c - copy a word from standard input to standard output with one change (a final newline is dropped):
     corrupt sub POS      letter at POS replaced by the next letter of the word's alphabet (cyclically: the letter
                          found at POS+1 if it differs, else the one at POS+2 ...)
     corrupt del POS      letter at POS deleted
     corrupt swap POS     letters POS and POS+1 exchanged
     corrupt first        first letter deleted
     corrupt last         last letter deleted
   POS counts letters from 0; a negative POS counts from the end (-1 = last).  The total length is needed for
   negative POS and for "last": give it with --len L.  Reports the change on standard error.
   build: gcc -O2 -o corrupt corrupt.c */
#define _FILE_OFFSET_BITS 64
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif
typedef long long i64;
#define BLK (1 << 24)
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: corrupt sub|del|swap POS | first | last [--len L]\n"); return 2; }
    const char *op = argv[1]; i64 pos = 0, L = -1; int ai = 2;
    if (!strcmp(op, "sub") || !strcmp(op, "del") || !strcmp(op, "swap")) { if (argc < 3) return 2; pos = atoll(argv[2]); ai = 3; }
    for (int i = ai; i < argc; i++) if (!strcmp(argv[i], "--len") && i + 1 < argc) L = atoll(argv[++i]);
    if (!strcmp(op, "first")) { op = "del"; pos = 0; }
    if (!strcmp(op, "last")) { if (L < 0) { fprintf(stderr, "last needs --len\n"); return 2; } op = "del"; pos = L - 1; }
    if (pos < 0) { if (L < 0) { fprintf(stderr, "negative POS needs --len\n"); return 2; } pos += L; }
#ifdef _WIN32
    _setmode(_fileno(stdin), _O_BINARY); _setmode(_fileno(stdout), _O_BINARY);
#endif
    static unsigned char in[BLK + 8], out[BLK + 8];
    i64 at = 0; size_t got; int pend = -1;   /* swap: letter held back */
    int sub_wait = 0; unsigned char sub_old = 0; i64 sub_out_idx = -1;  /* sub: replacement decided by the next letters */
    unsigned char *sbuf = NULL; size_t snb = 0;
    while ((got = fread(in, 1, BLK, stdin)) > 0) {
        size_t no = 0;
        for (size_t i = 0; i < got; i++) {
            unsigned char c = in[i];
            if (c == '\n' || c == '\r') continue;
            i64 k = at++;
            if (!strcmp(op, "del") && k == pos) { fprintf(stderr, "deleted letter %c at %lld\n", c, k); continue; }
            if (!strcmp(op, "swap") && k == pos) { pend = c; continue; }
            if (!strcmp(op, "swap") && k == pos + 1 && pend >= 0) { out[no++] = c; out[no++] = (unsigned char)pend; fprintf(stderr, "swapped %c%c at %lld\n", pend, c, pos); pend = -1; continue; }
            if (!strcmp(op, "sub") && k == pos) { sub_wait = 1; sub_old = c; sbuf = malloc(64); snb = 0; continue; }
            if (sub_wait) {              /* hold letters until one differs from the old letter */
                sbuf[snb++] = c;
                if (c != sub_old || snb == 64) {
                    out[no++] = c != sub_old ? c : (unsigned char)(sub_old ^ 1);
                    fprintf(stderr, "replaced %c by %c at %lld\n", sub_old, out[no - 1], pos);
                    for (size_t q = 0; q < snb; q++) out[no++] = sbuf[q];
                    sub_wait = 0; sub_out_idx = pos;
                }
                if (no > BLK - 80) { fwrite(out, 1, no, stdout); no = 0; }
                continue;
            }
            out[no++] = c;
        }
        fwrite(out, 1, no, stdout);
    }
    if (pend >= 0) { putchar(pend); fprintf(stderr, "swap at the last letter: nothing changed\n"); }
    if (sub_wait) { fprintf(stderr, "sub at the end: letter dropped instead\n"); fwrite(sbuf, 1, snb, stdout); }
    (void)sub_out_idx;
    fprintf(stderr, "letters in %lld\n", at);
    return 0;
}
