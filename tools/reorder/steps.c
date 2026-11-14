/* steps.c WORD N GMIN OUT.bin - list every step of weight >= GMIN between consecutive permutation windows of WORD.
   OUT.bin: one int64 per step, (v << 4) | w, where v = start of the window after the step and w its weight (so the
   window before it starts at v - w).  Prints one JSON line: length, first and last permutation window start, number
   of permutation windows, steps by weight.  Streams the word; memory a few MB. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define BLK (1 << 24)
static int val(int c) { return c <= '9' ? c - '0' : c - 'A' + 10; }
int main(int argc, char **argv) {
    if (argc != 5) { fprintf(stderr, "usage: steps WORD N GMIN OUT.bin\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int n = atoi(argv[2]), g = atoi(argv[3]); FILE *o = fopen(argv[4], "wb");
    if (!f || !o || n < 2 || n > 16) { fprintf(stderr, "bad arguments\n"); return 2; }
    static unsigned char buf[BLK]; static int64_t ob[1 << 16]; int on = 0;
    unsigned char win[16]; int cnt[16] = {0}, distinct = 0;
    long long pos = 0, last = -1, first = -1, nwin = 0, byw[17] = {0};
    size_t r;
    while ((r = fread(buf, 1, BLK, f)) > 0) {
        for (size_t i = 0; i < r; i++) {
            int c = buf[i];
            if (c == '\r' || c == '\n') continue;
            int v = val(c);
            if (pos >= n) { int u = win[pos % n]; if (--cnt[u] == 0) distinct--; }
            win[pos % n] = (unsigned char)v; if (cnt[v]++ == 0) distinct++;
            pos++;
            if (pos >= n && distinct == n) {
                long long s = pos - n;
                if (last >= 0) {
                    long long w = s - last; byw[w < 16 ? w : 16]++;
                    if (w >= g) { ob[on++] = (int64_t)((s << 4) | (w < 15 ? w : 15)); if (on == (1 << 16)) { fwrite(ob, 8, on, o); on = 0; } }
                } else first = s;
                last = s; nwin++;
            }
        }
    }
    if (on) fwrite(ob, 8, on, o);
    fclose(o);
    printf("{\"length\":%lld,\"first\":%lld,\"last\":%lld,\"windows\":%lld,\"steps_by_weight\":[", pos, first, last, nwin);
    for (int w = 1; w <= 16; w++) printf("%lld%s", byw[w], w < 16 ? "," : "]}\n");
    return 0;
}
