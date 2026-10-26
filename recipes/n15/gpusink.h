/* gpusink.h - route C inside gen16c: an independent check of one shard of the permutation ranks on the card, fed
   with the same letter blocks as the group check, in the same pass.  The kernel is rankmark of gpua.cu (gpua.ptx
   next to the program): every window is ranked by its Lehmer code (a different method from gcore.h) and the bit of
   its rank is set if the rank lies in the shard [I*span, (I+1)*span), span = ceil(n!/K).  At the end the bits are
   counted on the card: the shard is complete iff seen = span.
   The generator thread copies each block into a ring of pinned buffers; a feeder thread copies them to the card
   and launches the kernel; the last n-1 letters of a block start the next one.  If the file STOP_GPU appears next
   to the program, the card is given up at once and the result is reported as partial. */
#ifdef _WIN32
#define GAPI __stdcall
__declspec(dllimport) void *__stdcall LoadLibraryA(const char *);
__declspec(dllimport) void *__stdcall GetProcAddress(void *, const char *);
static void *glib_open(void) { return LoadLibraryA("nvcuda.dll"); }
static void *glib_sym(void *l, const char *s) { return GetProcAddress(l, s); }
#else
#include <dlfcn.h>
#define GAPI
static void *glib_open(void) { return dlopen("libcuda.so.1", RTLD_NOW); }
static void *glib_sym(void *l, const char *s) { return dlsym(l, s); }
#endif
typedef u64 GDP;
static int (GAPI *xInit)(unsigned), (GAPI *xDeviceGet)(int *, int), (GAPI *xCtxCreate)(void **, unsigned, int), (GAPI *xCtxSetCurrent)(void *);
static int (GAPI *xModuleLoadData)(void **, const void *), (GAPI *xModuleGetFunction)(void **, void *, const char *);
static int (GAPI *xMemAlloc)(GDP *, size_t), (GAPI *xMemsetD8)(GDP, unsigned char, size_t), (GAPI *xMemGetInfo)(size_t *, size_t *);
static int (GAPI *xHtoD)(GDP, const void *, size_t), (GAPI *xDtoH)(void *, GDP, size_t), (GAPI *xCtxSync)(void);
static int (GAPI *xLaunch)(void *, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned, void *, void **, void **);
static int (GAPI *xMemHostAlloc)(void **, size_t, unsigned);
#define GCK(x) do { int e_ = (x); if (e_) { fprintf(stderr, "gpusink: CUDA error %d at line %d\n", e_, __LINE__); exit(2); } } while (0)
#define GSB (64u << 20)
#define NGS 4
static struct {
    int on, stopped, n; u64 I, K, lo, span, nw; void *ctx, *fk, *fp; GDP dbits, dw, dst;
    u8 *ring[NGS]; size_t len[NGS]; u64 in, out; int done; u8 carry[16]; size_t ncarry;
    double tk; u64 fed; char stopf[4096];
    pthread_mutex_t mu; pthread_cond_t cv; pthread_t th;
} gs = { .mu = PTHREAD_MUTEX_INITIALIZER, .cv = PTHREAD_COND_INITIALIZER };
static void gs_init(const char *argv0, int n, u64 I, u64 K) {
    gs.n = n; gs.I = I; gs.K = K;
    u64 nf = 1; for (int i = 2; i <= n; i++) nf *= i;
    gs.span = (nf + K - 1) / K; gs.lo = I * gs.span; if (gs.lo + gs.span > nf) gs.span = nf - gs.lo;
    gs.nw = (gs.span + 31) / 32;
    void *lib = glib_open(); if (!lib) { fprintf(stderr, "gpusink: no CUDA driver\n"); exit(2); }
#define XSYM(v, s) do { *(void **)&v = glib_sym(lib, s); if (!v) { fprintf(stderr, "gpusink: missing %s\n", s); exit(2); } } while (0)
    XSYM(xInit, "cuInit"); XSYM(xDeviceGet, "cuDeviceGet"); XSYM(xCtxCreate, "cuCtxCreate_v2"); XSYM(xCtxSetCurrent, "cuCtxSetCurrent");
    XSYM(xModuleLoadData, "cuModuleLoadData"); XSYM(xModuleGetFunction, "cuModuleGetFunction"); XSYM(xMemAlloc, "cuMemAlloc_v2");
    XSYM(xMemsetD8, "cuMemsetD8_v2"); XSYM(xMemGetInfo, "cuMemGetInfo_v2"); XSYM(xHtoD, "cuMemcpyHtoD_v2"); XSYM(xDtoH, "cuMemcpyDtoH_v2");
    XSYM(xCtxSync, "cuCtxSynchronize"); XSYM(xLaunch, "cuLaunchKernel"); XSYM(xMemHostAlloc, "cuMemHostAlloc");
    char path[4096]; const char *sl = strrchr(argv0, '/'), *bs = strrchr(argv0, '\\'); if (bs > sl) sl = bs;
    if (sl) { snprintf(path, sizeof path, "%.*s/gpua.ptx", (int)(sl - argv0), argv0); snprintf(gs.stopf, sizeof gs.stopf, "%.*s/STOP_GPU", (int)(sl - argv0), argv0); }
    else { snprintf(path, sizeof path, "gpua.ptx"); snprintf(gs.stopf, sizeof gs.stopf, "STOP_GPU"); }
    FILE *pf = fopen(path, "rb"); if (!pf) { fprintf(stderr, "gpusink: %s not found\n", path); exit(2); }
    fseek(pf, 0, SEEK_END); long psz = ftell(pf); fseek(pf, 0, SEEK_SET); char *ptx = calloc(psz + 1, 1);
    if (fread(ptx, 1, psz, pf) != (size_t)psz) exit(2); fclose(pf);
    int dev; void *mod;
    GCK(xInit(0)); GCK(xDeviceGet(&dev, 0)); GCK(xCtxCreate(&gs.ctx, 4, dev));
    GCK(xModuleLoadData(&mod, ptx)); GCK(xModuleGetFunction(&gs.fk, mod, "rankmark")); GCK(xModuleGetFunction(&gs.fp, mod, "popcnt"));
    size_t fr, tot; GCK(xMemGetInfo(&fr, &tot));
    if (gs.nw * 4 + GSB + (768ULL << 20) > fr) { fprintf(stderr, "gpusink: shard of %.1f GB does not fit (%.1f GB free)\n", gs.nw * 4 / 1e9, fr / 1e9); exit(2); }
    GCK(xMemAlloc(&gs.dbits, gs.nw * 4)); GCK(xMemsetD8(gs.dbits, 0, gs.nw * 4));
    GCK(xMemAlloc(&gs.dw, GSB + 64)); GCK(xMemAlloc(&gs.dst, 16)); GCK(xMemsetD8(gs.dst, 0, 16));
    for (int i = 0; i < NGS; i++) if (xMemHostAlloc((void **)&gs.ring[i], GSB + 64, 0)) { gs.ring[i] = malloc(GSB + 64); if (!gs.ring[i]) exit(2); }
    GCK(xCtxSync());
    gs.on = 1;
}
static void *gs_thread(void *arg) {
    (void)arg; GCK(xCtxSetCurrent(gs.ctx));
    const int S = 32, bt = 256, raw = 1; int n = gs.n;
    for (;;) {
        pthread_mutex_lock(&gs.mu);
        while (gs.out == gs.in && !gs.done) pthread_cond_wait(&gs.cv, &gs.mu);
        if (gs.out == gs.in) { pthread_mutex_unlock(&gs.mu); break; }
        int r = (int)(gs.out % NGS); size_t len = gs.len[r];
        pthread_mutex_unlock(&gs.mu);
        if (!gs.stopped) {
            FILE *sf = fopen(gs.stopf, "r"); if (sf) { fclose(sf); gs.stopped = 1; fprintf(stderr, "gpusink: STOP_GPU seen, card given up\n"); }
        }
        if (!gs.stopped && len >= (size_t)n) {
            double a = wall();
            GCK(xHtoD(gs.dw, gs.ring[r], len));
            u64 nwin = len - n + 1;
            unsigned blocks = (unsigned)((nwin + (u64)bt * S - 1) / ((u64)bt * S));
            void *args[] = { &gs.dw, &nwin, &n, &gs.lo, &gs.span, &gs.dbits, &gs.dst, (void *)&S, (void *)&raw };
            GCK(xLaunch(gs.fk, blocks, 1, 1, bt, 1, 1, bt * S + n + 16, NULL, args, NULL)); GCK(xCtxSync());
            gs.tk += wall() - a;
        }
        pthread_mutex_lock(&gs.mu); gs.out++; pthread_cond_broadcast(&gs.cv); pthread_mutex_unlock(&gs.mu);
    }
    return NULL;
}
static void gs_start(void) { pthread_create(&gs.th, NULL, gs_thread, NULL); }
/* from the generator thread: a block of letter values */
static void gs_push(const u8 *p, size_t k) {
    while (k) {
        pthread_mutex_lock(&gs.mu);
        while (gs.in - gs.out >= NGS) pthread_cond_wait(&gs.cv, &gs.mu);
        int r = (int)(gs.in % NGS);
        pthread_mutex_unlock(&gs.mu);
        size_t c = k < GSB - gs.ncarry ? k : GSB - gs.ncarry;
        memcpy(gs.ring[r], gs.carry, gs.ncarry); memcpy(gs.ring[r] + gs.ncarry, p, c);
        size_t len = gs.ncarry + c;
        gs.ncarry = len < (size_t)(gs.n - 1) ? len : (size_t)(gs.n - 1);
        memcpy(gs.carry, gs.ring[r] + len - gs.ncarry, gs.ncarry);
        gs.fed += c;
        pthread_mutex_lock(&gs.mu); gs.len[r] = len; gs.in++; pthread_cond_broadcast(&gs.cv); pthread_mutex_unlock(&gs.mu);
        p += c; k -= c;
    }
}
static void gs_finish(u64 *seen, u64 *pw, u64 *marked) {
    pthread_mutex_lock(&gs.mu); gs.done = 1; pthread_cond_broadcast(&gs.cv); pthread_mutex_unlock(&gs.mu);
    pthread_join(gs.th, NULL);
    GCK(xCtxSetCurrent(gs.ctx));
    u64 st[2]; GCK(xDtoH(st, gs.dst, 16));
    GDP dc; GCK(xMemAlloc(&dc, 8)); GCK(xMemsetD8(dc, 0, 8));
    void *pa[] = { &gs.dbits, &gs.nw, &dc }; GCK(xLaunch(gs.fp, 4096, 1, 1, 256, 1, 1, 0, NULL, pa, NULL)); GCK(xCtxSync());
    GCK(xDtoH(seen, dc, 8)); *pw = st[0]; *marked = st[1];
}
