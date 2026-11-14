/* gcheck.c - coverage check of a word on the card: the same numbers and the same output line as recipes/n14/vfast.c
   (src/verify_stream.c), with the full n! bit table in VRAM (n <= 14: 10.9 GB at n = 14).  A fast first check: the
   processor checkers (check_min.py, delcheck, literal_check) still give the verdict.  On a busy machine a .xz word is
   read faster as  xz -dc WORD.xz | gcheck N -  (the xz that gcheck starts inherits the idle priority of guard.py).

   usage: gcheck N WORD [--alpha AL] [--skip P] [--chunk MB] [--nbuf K] [--readers R] [--io direct|buffered] [--xz EXE]
                        [--S S] [--bt T]
     WORD     a file of letters (CR and LF ignored as vfast ignores them), WORD.xz (streamed through "xz -dc"), or "-"
              (standard input).  A plain file is read by R threads (default 2), unbuffered on Windows by default.
     --skip P the word without its letter P (0-based; a check of a deletion that gdelcheck found, with no copy)
     --alpha  the N letters (as vfast's ALPHABET).  Default: the first N of 0123456789ABCDEF; if the first chunk has
              exactly N different letters and one of them is outside that prefix, those letters (sorted) are used.
   Output: one JSON line with vfast's fields in vfast's order (n, length, windows, expected_windows,
   permutation_windows, first_occurrences, repeats, distinct_seen, missing, foreign_bytes, trailing_newlines), then
   alphabet, seconds, card_seconds, read_seconds, GB_per_s, filtered_chunks (and left_out_letter with --skip).  Exit
   code as vfast: 0 only if nothing is missing, no
   byte is foreign and the window count is right; 1 otherwise; 2 on an error.

   How: chunks of the file go to the card as bytes; a kernel maps them to symbols and counts bytes that are not
   letters.  A chunk with only letters (and line ends at its very end) is ranked as is; any other chunk is first
   filtered on the host exactly as vfast filters (a CR/LF followed by more bytes counts as foreign, foreign bytes
   are dropped and the letters on both sides join).  The last n-1 letters of a chunk are put in front of the next.
   Every window of n letters that is a permutation sets the bit of its rank with atomicOr; the bit was clear for
   exactly one window per permutation (first_occurrences).  distinct_seen = set bits counted on the card.

   build: gcc -O2 -o gcheck gcheck.c (-pthread); PTX: nvcc -arch=sm_120 -O3 -ptx -o gpuprep.ptx gpuprep.cu */
#include "gp_cuda.h"
#include "gp_reader.h"

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: gcheck N WORD [--alpha AL] [--chunk MB] [--nbuf K] [--readers R] [--io direct|buffered] [--xz EXE]\n"); return 2; }
    int n = atoi(argv[1]); const char *word = argv[2], *alpha = NULL, *io = "direct", *xz = NULL;
    size_t chunk = 256ULL << 20; int nbuf = 6, nrd = 2, S = 32, bt = 256;
    u64 skip_at = ~0ULL; int skipped = 0, skipchunk = 0;   /* --skip POS: check the word without its letter POS (0-based) */
    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i], "--alpha") && i + 1 < argc) alpha = argv[++i];
        else if (!strcmp(argv[i], "--chunk") && i + 1 < argc) chunk = (size_t)atoll(argv[++i]) << 20;
        else if (!strcmp(argv[i], "--nbuf") && i + 1 < argc) nbuf = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--readers") && i + 1 < argc) nrd = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--io") && i + 1 < argc) io = argv[++i];
        else if (!strcmp(argv[i], "--xz") && i + 1 < argc) xz = argv[++i];
        else if (!strcmp(argv[i], "--S") && i + 1 < argc) S = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--bt") && i + 1 < argc) bt = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--skip") && i + 1 < argc) skip_at = (u64)atoll(argv[++i]);
        else { fprintf(stderr, "gcheck: unknown option %s\n", argv[i]); return 2; }
    }
    if (n < 2 || n > 14 || chunk < (1 << 20) || nbuf < 2) { fprintf(stderr, "gcheck: bad arguments (2 <= N <= 14)\n"); return 2; }
    if (alpha && (int)strlen(alpha) != n) { fprintf(stderr, "gcheck: the alphabet must have N letters\n"); return 2; }
    double t0 = gp_wall();
    gp_init(argv[0]);
    void *fmap = gp_fn("mapsym"), *frank = gp_fn("rankmark");
    u64 nf = 1; for (int i = 2; i <= n; i++) nf *= i;
    u64 nw = nf / 32 + 1;
    size_t fr, tot; CK(cMemGetInfo(&fr, &tot));
    if (nw * 4 + 2 * chunk + (256ULL << 20) > fr) { fprintf(stderr, "gcheck: the bit table (%.1f GB) does not fit (%.1f GB free)\n", nw * 4 / 1e9, fr / 1e9); return 2; }
    DP dbits = gp_alloc(nw * 4, 1), draw = gp_alloc(chunk + 64, 0), dsym = gp_alloc(chunk + 64, 0), dlut = gp_alloc(256, 0), dst = gp_alloc(32, 1);
    Reader R; rd_open(&R, word, chunk, nbuf, nrd, io, xz);
    u8 lut[256]; char al[17] = {0};
    u64 total = 0, trailing = 0, foreign = 0, windows = 0, slow = 0; double tcard = 0;
    u8 car[16]; int nc = 0; int first = 1;
    for (;;) {
        RBuf *b = rd_next(&R); if (!b) { fprintf(stderr, "gcheck: read failed\n"); return 2; }
        u8 *d = b->data; size_t len = b->len;
        if (first) {      /* the alphabet */
            first = 0;
            if (alpha) memcpy(al, alpha, n);
            else {
                memcpy(al, "0123456789ABCDEF", n);
                int has[256] = {0}, k = 0, out = 0;
                for (size_t i = 0; i < len && i < (64u << 20); i++) has[d[i]] = 1;
                has['\n'] = has['\r'] = 0;
                for (int c = 0; c < 256; c++) if (has[c]) { k++; if (!memchr(al, c, n)) out = 1; }
                if (out && k == n) { int j = 0; for (int c = 0; c < 256; c++) if (has[c]) al[j++] = (char)c; }
            }
            memset(lut, 0xFF, sizeof lut); for (int i = 0; i < n; i++) lut[(u8)al[i]] = (u8)i;
            CK(cHtoD(dlut, lut, 256));
        }
        double a = gp_wall();
        size_t t = 0; while (t < len && (d[len - 1 - t] == '\n' || d[len - 1 - t] == '\r')) t++;
        size_t m = len - t;
        memcpy(d - nc, car, nc);
        u64 nb = 0, z = 0, have = nc + m, nwin = 0; DP pb = dst + 16;
        /* map and rank in one go with one wait; the ranker skips itself on the card if a byte is not a letter */
#define MAPRANK() do { CK(cMemsetD8(pb, 0, 8)); CK(cHtoD(draw, d - nc, have)); \
            void *ma[] = { &draw, &have, &dsym, &dlut, &pb }; gp_launch(fmap, 2048, 256, 0, ma); \
            nwin = have >= (u64)n ? have - n + 1 : 0; \
            if (nwin) { unsigned blocks = (unsigned)((nwin + (u64)bt * S - 1) / ((u64)bt * S)); \
                void *ra[] = { &dsym, &nwin, &n, &z, &nf, &dbits, &z, &dst, &S, &pb }; gp_launch(frank, blocks, bt, bt * S + n + 16, ra); } \
            CK(cDtoH(&nb, pb, 8)); } while (0)
        skipchunk = 0;
        if (skip_at != ~0ULL && !skipped && skip_at >= total && skip_at < total + m) {   /* --skip: leave the letter out */
            size_t k = (size_t)(skip_at - total); memmove(d + k, d + k + 1, m - k - 1 + t); m--; len--; have--; skipped = 1; skipchunk = 1;
        }
        if (m) MAPRANK();
        if (nb == 0) {    /* only letters, line ends at the end */
            if (m) { foreign += trailing; trailing = t; total += m; windows += nwin; } else trailing += t;
        } else {          /* filter as vfast */
            slow++;
            if (skipchunk) { fprintf(stderr, "gcheck: --skip needs a word of letters only around the letter left out\n"); return 2; }
            size_t k = 0;
            for (size_t i = 0; i < len; i++) {
                u8 c = d[i];
                if (c == '\n' || c == '\r') { trailing++; continue; }
                if (trailing) { foreign += trailing; trailing = 0; }
                if (lut[c] == 0xFF) { foreign++; continue; }
                d[k++] = c; total++;
            }
            m = k; have = nc + m; nwin = 0;
            memcpy(d - nc, car, nc);
            if (have) MAPRANK();
            if (nb) { fprintf(stderr, "gcheck: internal error (filtered chunk not clean)\n"); return 2; }
            windows += nwin;
        }
        int nc2 = have < (u64)(n - 1) ? (int)have : n - 1;
        memcpy(car, d - nc + have - nc2, nc2);
        int eof = b->eof;
        rd_release(&R, b);
        nc = nc2;
        tcard += gp_wall() - a;
        if (eof) break;
    }
    int xzbad = rd_close(&R);
    double a = gp_wall();
    u64 st[2]; CK(cDtoH(st, dst, 16));
    u64 seen = gp_popcount(dbits, nw);
    tcard += gp_wall() - a;
    double tt = gp_wall() - t0;
    u64 expect = total >= (u64)n ? total - n + 1 : 0;
    printf("{\"n\":%d,\"length\":%llu,\"windows\":%llu,\"expected_windows\":%llu,\"permutation_windows\":%llu,"
           "\"first_occurrences\":%llu,\"repeats\":%llu,\"distinct_seen\":%llu,\"missing\":%llu,\"foreign_bytes\":%llu,"
           "\"trailing_newlines\":%llu,\"alphabet\":\"%s\",\"seconds\":%.2f,\"card_seconds\":%.2f,\"read_seconds\":%.2f,\"GB_per_s\":%.2f,"
           "\"filtered_chunks\":%llu%s}\n",
           n, (unsigned long long)total, (unsigned long long)windows, (unsigned long long)expect, (unsigned long long)st[0],
           (unsigned long long)st[1], (unsigned long long)(st[0] - st[1]), (unsigned long long)seen, (unsigned long long)(nf - seen),
           (unsigned long long)foreign, (unsigned long long)trailing, al, tt, tcard, rd_busy(&R), R.bytes / tt / 1e9, (unsigned long long)slow, skipped ? ",\"left_out_letter\":1" : "");
    if (xzbad) { fprintf(stderr, "gcheck: xz reported an error\n"); return 2; }
    return (seen == nf && foreign == 0 && windows == expect) ? 0 : 1;
}
