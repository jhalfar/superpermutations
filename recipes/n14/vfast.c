/* vfast.c - src/verify_stream.c with one worker thread and no atomic operations: the ranks of a batch of windows
   are computed and their words of the bit table prefetched before the bits are set, so many cache misses are in
   flight at once.  Same input, same output line, same exit code as verify_stream.

   usage: vfast N ALPHABET          (stdin; 2 threads: reader + worker; memory N!/8 bytes, 10.9 GB for N = 14) */
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif

#define BLOCK (64u << 20)
#define NBUF 8
#define BATCH 64

static int N;
static unsigned char map[256];
static uint64_t fact[17];
static uint64_t *bits;
static uint64_t nbits;

typedef struct { unsigned char *data; size_t len; } Buf;
static Buf bufs[NBUF];
static int qhead, qtail, qcount, done_reading;
static int freelist[NBUF], nfree;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t cv_full = PTHREAD_COND_INITIALIZER, cv_free = PTHREAD_COND_INITIALIZER;
static int queue[NBUF];
static uint64_t windows, perms, firsts;

static uint64_t rk[2][BATCH]; static int nb[2] = {0, 0}, cur = 0;
static void flush_batches(void) {
  for (int o = 0; o < 2; o++) { for (int k = 0; k < nb[o]; k++) { uint64_t rr = rk[o][k], m = 1ull << (rr & 63); if (!(bits[rr >> 6] & m)) { bits[rr >> 6] |= m; firsts++; } } nb[o] = 0; }
}
static void process_block(const unsigned char *d, size_t len) {
    int cnt[16] = {0}, dup = 0;
    for (size_t i = 0; i < len; i++) {
      int s = d[i];
      if (cnt[s]++ == 1) dup++;
      if (i >= (size_t)N) { int t = d[i - N]; if (--cnt[t] == 1) dup--; }
      if (i + 1 < (size_t)N) continue;
      windows++;
      if (dup) continue;
      perms++;
      uint64_t r = 0; unsigned left = (1u << N) - 1;
      const unsigned char *x = d + i + 1 - N;
      for (int j = 0; j < N - 1; j++) {
        r += (uint64_t)__builtin_popcount(left & ((1u << x[j]) - 1)) * fact[N - 1 - j];
        left &= ~(1u << x[j]);
      }
      __builtin_prefetch(&bits[r >> 6], 1, 0);
      rk[cur][nb[cur]++] = r;
      if (nb[cur] == BATCH) {
        int o = cur ^ 1;
        for (int k = 0; k < nb[o]; k++) { uint64_t rr = rk[o][k], m = 1ull << (rr & 63); if (!(bits[rr >> 6] & m)) { bits[rr >> 6] |= m; firsts++; } }
        nb[o] = 0; cur = o;
      }
    }
}
static void *worker(void *arg) {
  (void)arg;
  for (;;) {
    pthread_mutex_lock(&mu);
    while (qcount == 0 && !done_reading) pthread_cond_wait(&cv_full, &mu);
    if (qcount == 0 && done_reading) { pthread_mutex_unlock(&mu); break; }
    int b = queue[qhead]; qhead = (qhead + 1) % NBUF; qcount--;
    pthread_mutex_unlock(&mu);
    process_block(bufs[b].data, bufs[b].len);
    pthread_mutex_lock(&mu);
    freelist[nfree++] = b;
    pthread_cond_signal(&cv_free);
    pthread_mutex_unlock(&mu);
  }
  flush_batches();
  return NULL;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: vfast N ALPHABET\n"); return 2; }
  N = atoi(argv[1]);
  if (N < 2 || N > 16 || (int)strlen(argv[2]) != N) { fprintf(stderr, "bad arguments\n"); return 2; }
  memset(map, 0xFF, sizeof map);
  for (int i = 0; i < N; i++) {
    if (map[(unsigned char)argv[2][i]] != 0xFF) { fprintf(stderr, "repeated symbol in alphabet\n"); return 2; }
    map[(unsigned char)argv[2][i]] = (unsigned char)i;
  }
  fact[0] = 1; for (int i = 1; i <= 16; i++) fact[i] = fact[i - 1] * i;
  nbits = fact[N];
  bits = calloc(nbits / 64 + 1, sizeof(uint64_t));
  if (!bits) { fprintf(stderr, "cannot allocate %llu bytes\n", (unsigned long long)(nbits / 8)); return 2; }
#ifdef _WIN32
  _setmode(_fileno(stdin), _O_BINARY);
#endif
  for (int i = 0; i < NBUF; i++) { bufs[i].data = malloc(BLOCK + 16); if (!bufs[i].data) return 2; freelist[nfree++] = i; }
  int single = argc > 3 && atoi(argv[3]) == 1;     /* vfast N ALPHABET 1: everything in one thread */
  pthread_t th; if (!single) pthread_create(&th, NULL, worker, NULL);
  unsigned char carry[16]; size_t ncarry = 0, total = 0, trailing_nl = 0, foreign = 0;
  unsigned char *raw = malloc(BLOCK);
  for (;;) {
    size_t got = fread(raw, 1, BLOCK - 16, stdin);
    if (got == 0) break;
    pthread_mutex_lock(&mu);
    while (nfree == 0) pthread_cond_wait(&cv_free, &mu);
    int b = freelist[--nfree];
    pthread_mutex_unlock(&mu);
    unsigned char *d = bufs[b].data;
    memcpy(d, carry, ncarry);
    size_t len = ncarry;
    for (size_t i = 0; i < got; i++) {
      unsigned char c = raw[i];
      if (c == '\n' || c == '\r') { trailing_nl++; continue; }
      if (trailing_nl) { foreign += trailing_nl; trailing_nl = 0; }
      unsigned char s = map[c];
      if (s == 0xFF) { foreign++; continue; }
      d[len++] = s; total++;
    }
    bufs[b].len = len;
    ncarry = len < (size_t)(N - 1) ? len : (size_t)(N - 1);
    memcpy(carry, d + len - ncarry, ncarry);
    pthread_mutex_lock(&mu);
    if (single) { pthread_mutex_unlock(&mu); process_block(d, len); pthread_mutex_lock(&mu); freelist[nfree++] = b; pthread_mutex_unlock(&mu); continue; }
    queue[qtail] = b; qtail = (qtail + 1) % NBUF; qcount++;
    pthread_cond_signal(&cv_full);
    pthread_mutex_unlock(&mu);
  }
  pthread_mutex_lock(&mu); done_reading = 1; pthread_cond_broadcast(&cv_full); pthread_mutex_unlock(&mu);
  if (!single) pthread_join(th, NULL); else flush_batches();
  /* windows counted per block include the N-1 carried letters: each block re-counts no window twice because a
     window is counted at its last letter and the carry holds only N-1 letters */
  uint64_t seen = 0;
  for (uint64_t i = 0; i < nbits / 64 + 1; i++) seen += (uint64_t)__builtin_popcountll(bits[i]);
  uint64_t expect_windows = total >= (size_t)N ? total - N + 1 : 0;
  printf("{\"n\":%d,\"length\":%llu,\"windows\":%llu,\"expected_windows\":%llu,\"permutation_windows\":%llu,"
         "\"first_occurrences\":%llu,\"repeats\":%llu,\"distinct_seen\":%llu,\"missing\":%llu,\"foreign_bytes\":%llu,"
         "\"trailing_newlines\":%llu}\n",
         N, (unsigned long long)total, (unsigned long long)windows, (unsigned long long)expect_windows,
         (unsigned long long)perms, (unsigned long long)firsts, (unsigned long long)(perms - firsts),
         (unsigned long long)seen, (unsigned long long)(nbits - seen), (unsigned long long)foreign,
         (unsigned long long)trailing_nl);
  return (seen == nbits && foreign == 0 && windows == expect_windows) ? 0 : 1;
}
