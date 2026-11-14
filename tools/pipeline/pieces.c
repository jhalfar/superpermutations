/* pieces.c WORD N OUT.tsv - cut a word into pieces as trailsearch.c does (maximal runs of permutation windows whose
   starts are at most 3 apart) and write one line per piece: index, start, length (letters from the first window's
   start to the last window's end), number of windows, FNV-1a 64 hash of the piece's letters, gap to the next piece.
   Streams the word in blocks; memory is a few MB. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define BLK (1 << 24)

static int val(int c) { return c <= '9' ? c - '0' : c - 'A' + 10; }

int main(int argc, char **argv) {
    /* WORD "-" reads standard input; a 4th argument "canon" hashes every piece after renaming its letters in the
       order of its first window, so that two words that differ by a relabelling give the same hashes */
    if (argc != 4 && argc != 5) { fprintf(stderr, "usage: pieces WORD|- N OUT.tsv [canon]\n"); return 2; }
    int canon = argc == 5 && !strcmp(argv[4], "canon");
    int map[16];
    for (int k = 0; k < 16; k++) map[k] = k;
    FILE *f = strcmp(argv[1], "-") ? fopen(argv[1], "rb") : stdin; int n = atoi(argv[2]); FILE *o = fopen(argv[3], "w");
    if (!f || !o || n < 2 || n > 16) { fprintf(stderr, "bad arguments\n"); return 2; }
    static unsigned char buf[BLK];
    unsigned char *win = malloc(n);          /* last n letters, ring */
    int cnt[16] = {0}, distinct = 0;
    long long pos = 0;                       /* letters read */
    long long pst = -1, plast = -1, pwin = 0, idx = 0;   /* current piece: first window start, last window start */
    uint64_t h = 0;                          /* hash of letters from pst to the current letter */
    const uint64_t P = 1099511628211ULL, H0 = 1469598103934665603ULL;
    /* letters between plast+n and the next window are hashed tentatively; keep the hash at the piece end */
    uint64_t hend = 0;
    size_t r;
    while ((r = fread(buf, 1, BLK, f)) > 0) {
        for (size_t i = 0; i < r; i++) {
            int c = buf[i];
            if (c == '\r' || c == '\n') continue;
            int v = val(c);
            if (pos >= n) { int u = win[pos % n]; if (--cnt[u] == 0) distinct--; }
            win[pos % n] = (unsigned char)v; if (cnt[v]++ == 0) distinct++;
            pos++;
            if (pst >= 0) h = (h ^ (uint64_t)"0123456789ABCDEF"[map[v]]) * P;
            if (pos >= n && distinct == n) {
                long long s = pos - n;       /* window start */
                if (pst >= 0 && s - plast >= 4) {
                    fprintf(o, "%lld\t%lld\t%lld\t%lld\t%016llx\t%lld\n", idx++, pst, plast + n - pst, pwin,
                            (unsigned long long)hend, s - plast);
                    pst = -1;
                }
                if (pst < 0) {               /* new piece: hash its first n letters */
                    pst = s; pwin = 0; h = H0;
                    if (canon) for (int k = 0; k < n; k++) map[win[(s + k) % n]] = k;
                    for (int k = 0; k < n; k++) h = (h ^ (uint64_t)"0123456789ABCDEF"[map[win[(s + k) % n]]]) * P;
                }
                plast = s; pwin++; hend = h;
            }
        }
    }
    if (pst >= 0) fprintf(o, "%lld\t%lld\t%lld\t%lld\t%016llx\t0\n", idx++, pst, plast + n - pst, pwin,
                          (unsigned long long)hend);
    fprintf(stderr, "letters %lld pieces %lld\n", pos, idx);
    fclose(o); return 0;
}
