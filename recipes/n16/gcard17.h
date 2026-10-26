/* gcard17.h - opt/fastcheck/gcard.h for n <= 17 with group shards (agent n17): 9 mask words (n(n-1) <= 272 bits),
   group shard gI/gK (only groups g = gI mod gK are recorded; bit table of ceil((n-2)!/gK) bits, bit g / gK), the
   kernels in gcheck17.ptx.  "missing_permutations" counts the permutations of the shard's groups only.
   Original description: */
/* gcard.h - host side of v2 (gcheck.cu on the card, through the CUDA driver library; everything static).
   A segment = the last n-1 letters of the previous segment + SEG new letters (SEG a multiple of the 64 KiB leaf).
   Per segment: (expand the spans | upload the letters), scan, harvest, reinsert the survivors, leaf hashes, and
   optionally the route-A ranker on one shard and a copy of the letters back to the host (for the plain SHA-256).
   Leaf digests are hashed on the host: tree hash = SHA-256 of the concatenated leaf digests (32 bytes each, in
   order), leaf = 65,536 letters of the word spelled with 0-9A-F (the last leaf may be shorter).
   Needs from the includer: u8/u32/u64, wall(), Sha/sha_init/sha_update/sha_final, pthread. */
#ifdef _WIN32
#define CAPI __stdcall
__declspec(dllimport) void *__stdcall LoadLibraryA(const char *);
__declspec(dllimport) void *__stdcall GetProcAddress(void *, const char *);
static void *clib_open(void) { return LoadLibraryA("nvcuda.dll"); }
static void *clib_sym(void *l, const char *s) { return GetProcAddress(l, s); }
#else
#include <dlfcn.h>
#define CAPI
static void *clib_open(void) { return dlopen("libcuda.so.1", RTLD_NOW); }
static void *clib_sym(void *l, const char *s) { return dlsym(l, s); }
#endif
typedef u64 CDP;
static int (CAPI *cuInit_)(unsigned), (CAPI *cuDeviceGet_)(int *, int), (CAPI *cuCtxCreate_)(void **, unsigned, int), (CAPI *cuCtxSetCurrent_)(void *);
static int (CAPI *cuModuleLoadData_)(void **, const void *), (CAPI *cuModuleGetFunction_)(void **, void *, const char *), (CAPI *cuModuleGetGlobal_)(CDP *, size_t *, void *, const char *);
static int (CAPI *cuMemAlloc_)(CDP *, size_t), (CAPI *cuMemsetD8_)(CDP, unsigned char, size_t), (CAPI *cuMemGetInfo_)(size_t *, size_t *);
static int (CAPI *cuHtoD_)(CDP, const void *, size_t), (CAPI *cuDtoH_)(void *, CDP, size_t), (CAPI *cuDtoD_)(CDP, CDP, size_t), (CAPI *cuCtxSync_)(void);
static int (CAPI *cuLaunch_)(void *, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned, void *, void **, void **);
static int (CAPI *cuMemHostAlloc_)(void **, size_t, unsigned);
static int (CAPI *cuHtoDA_)(CDP, const void *, size_t, void *), (CAPI *cuEventCreate_)(void **, unsigned), (CAPI *cuEventRecord_)(void *, void *), (CAPI *cuEventSynchronize_)(void *);
#define NSTG 3                                     /* pinned staging slots for the spans (asynchronous copies) */
#define CCK(x) do { int e_ = (x); if (e_) { fprintf(stderr, "gcard: CUDA error %d at %s:%d\n", e_, __FILE__, __LINE__); exit(2); } } while (0)

#define LEAF 65536u
typedef struct { u64 g; u32 m[9]; u32 age; } CRec;                       /* = Rec in gcheck.cu */
typedef struct { u64 B; u64 off; unsigned short from, len; u8 s, v, pad0, pad1; } CSpan;   /* = Span */
typedef struct { int n, S, M, pad; u64 fact[21]; u64 gK, gI; u32 full[9]; u32 pad2; } CParam;            /* = GParam */

static struct {
    int n, S, M, MW, scan1; u64 NG, nw2, gK, gI, NGloc; u64 SEG; int CH; u64 tabcap;
    void *ctx, *fscan, *fharv, *freins, *fpop, *fexp, *fleaf, *frank;
    CDP B2, keys, masks, touched, ages, surv[2], nsurv, res, nres, seg, dig, stats, ovf, spans, rbits;
    u32 survcap, rescap; int sp; u32 ns;           /* survivors: buffer index, count */
    u64 spancap;
    u64 total, segs; int haveprev;
    CRec *hres; size_t nhres, caphres;             /* residues on the host */
    u32 *hdig; Sha tree; u64 nleaves;
    u8 *hcopy; int copyback; Sha plain;            /* plain SHA-256 of the copied letters */
    u64 rI, rK, rlo, rspan, rnw;                   /* route-A shard */
    double tk; u64 st[4]; u32 ovf_h;
    u64 flip_at, cut_at;                          /* tests: change the letter at this word position (+1 mod n); end the word here */
    CSpan *stg[NSTG]; void *stgev[NSTG]; int stgi, stgused[NSTG];   /* spans go card-wards from pinned slots, in stream order */
} G2;

static void *c_fn(void *mod, const char *name) { void *f; CCK(cuModuleGetFunction_(&f, mod, name)); return f; }
static void c_launch(void *f, u64 nthreads, unsigned bt, void **args) {
    u64 nb = (nthreads + bt - 1) / bt; if (nb < 1) nb = 1;
    CCK(cuLaunch_(f, (unsigned)nb, 1, 1, bt, 1, 1, 0, NULL, args, NULL));
}
/* n symbols, satellite S, table of 2^tbits entries, segments of seg letters; route-A shard rI/rK (rK = 0: none) */
static void g2_init(const char *argv0, int n, int S, int tbits, u64 seg, int copyback, u64 rI, u64 rK, u64 gI, u64 gK) {
    memset(&G2, 0, sizeof G2); G2.flip_at = ~0ULL;
    G2.n = n; G2.S = S < 0 ? n - 2 : S; G2.M = G2.S == 0 ? 1 : 0; G2.MW = n * (n - 1); G2.SEG = seg; G2.CH = 256; G2.copyback = copyback;
    u64 f[21]; f[0] = 1; for (int i = 1; i < 21; i++) f[i] = f[i - 1] * i;
    G2.NG = f[n - 2]; if (gK < 1 || gI >= gK) { fprintf(stderr, "gcard: bad group shard %llu/%llu\n", (unsigned long long)gI, (unsigned long long)gK); exit(2); }
    G2.gK = gK; G2.gI = gI; G2.NGloc = (G2.NG - gI + gK - 1) / gK;      /* groups g < NG with g = gI (mod gK) */
    G2.nw2 = G2.NGloc / 64 + 1;
    void *lib = clib_open(); if (!lib) { fprintf(stderr, "gcard: no CUDA driver\n"); exit(2); }
#define CSYM(v, s) do { *(void **)&v = clib_sym(lib, s); if (!v) { fprintf(stderr, "gcard: missing %s\n", s); exit(2); } } while (0)
    CSYM(cuInit_, "cuInit"); CSYM(cuDeviceGet_, "cuDeviceGet"); CSYM(cuCtxCreate_, "cuCtxCreate_v2"); CSYM(cuCtxSetCurrent_, "cuCtxSetCurrent");
    CSYM(cuModuleLoadData_, "cuModuleLoadData"); CSYM(cuModuleGetFunction_, "cuModuleGetFunction"); CSYM(cuModuleGetGlobal_, "cuModuleGetGlobal_v2");
    CSYM(cuMemAlloc_, "cuMemAlloc_v2"); CSYM(cuMemsetD8_, "cuMemsetD8_v2"); CSYM(cuMemGetInfo_, "cuMemGetInfo_v2");
    CSYM(cuHtoD_, "cuMemcpyHtoD_v2"); CSYM(cuDtoH_, "cuMemcpyDtoH_v2"); CSYM(cuDtoD_, "cuMemcpyDtoD_v2"); CSYM(cuCtxSync_, "cuCtxSynchronize");
    CSYM(cuLaunch_, "cuLaunchKernel"); CSYM(cuMemHostAlloc_, "cuMemHostAlloc");
    CSYM(cuHtoDA_, "cuMemcpyHtoDAsync_v2"); CSYM(cuEventCreate_, "cuEventCreate"); CSYM(cuEventRecord_, "cuEventRecord"); CSYM(cuEventSynchronize_, "cuEventSynchronize");
    char path[4096]; const char *sl = strrchr(argv0, '/'), *bs = strrchr(argv0, '\\'); if (bs > sl) sl = bs;
    if (sl) snprintf(path, sizeof path, "%.*s/gcheck17.ptx", (int)(sl - argv0), argv0); else snprintf(path, sizeof path, "gcheck17.ptx");
    FILE *pf = fopen(path, "rb"); if (!pf) pf = fopen("gcheck17.ptx", "rb"); if (!pf) { fprintf(stderr, "gcard: gcheck17.ptx not found\n"); exit(2); }
    fseek(pf, 0, SEEK_END); long psz = ftell(pf); fseek(pf, 0, SEEK_SET); char *ptx = calloc(psz + 1, 1);
    if (fread(ptx, 1, psz, pf) != (size_t)psz) exit(2); fclose(pf);
    int dev; void *mod;
    CCK(cuInit_(0)); CCK(cuDeviceGet_(&dev, 0)); CCK(cuCtxCreate_(&G2.ctx, 4, dev)); CCK(cuModuleLoadData_(&mod, ptx)); free(ptx);
    G2.scan1 = getenv("GEN17_SCAN2") == NULL; G2.fscan = c_fn(mod, G2.scan1 ? "scan" : "scan2");   /* scan (default) or scan2 (GEN17_SCAN2: letters staged in shared memory; same results, no faster here) */ G2.fharv = c_fn(mod, "harvest"); G2.freins = c_fn(mod, "reinsert"); G2.fpop = c_fn(mod, "popcnt64");
    G2.fexp = c_fn(mod, "expand"); G2.fleaf = c_fn(mod, "leafsha"); G2.frank = c_fn(mod, "rankmark");
    CParam cp; memset(&cp, 0, sizeof cp); cp.n = n; cp.S = G2.S; cp.M = G2.M; memcpy(cp.fact, f, sizeof f); cp.gK = gK; cp.gI = gI;
    for (int b = 0; b < G2.MW; b++) cp.full[b >> 5] |= 1u << (b & 31);
    CDP pp; size_t psz2; CCK(cuModuleGetGlobal_(&pp, &psz2, mod, "P")); if (psz2 != sizeof cp) { fprintf(stderr, "gcard: parameter block size %zu != %zu\n", psz2, sizeof cp); exit(2); }
    CCK(cuHtoD_(pp, &cp, sizeof cp));
    G2.tabcap = 1ULL << tbits; G2.survcap = 1u << 21; G2.rescap = 1u << 21; G2.spancap = seg / 64 + 65536;
    size_t fr, tot; CCK(cuMemGetInfo_(&fr, &tot));
    u64 need = G2.nw2 * 8 + G2.tabcap * 46 + 2ULL * G2.survcap * sizeof(CRec) + (u64)G2.rescap * sizeof(CRec) + seg + 64 + (seg / LEAF + 1) * 32 + G2.spancap * sizeof(CSpan);
    if (rK) { u64 nf = f[n]; G2.rI = rI; G2.rK = rK; G2.rspan = (nf + rK - 1) / rK; G2.rlo = rI * G2.rspan; if (G2.rlo + G2.rspan > nf) G2.rspan = nf - G2.rlo; G2.rnw = (G2.rspan + 31) / 32; need += G2.rnw * 4; }
    if (need + (512ULL << 20) > fr) { fprintf(stderr, "gcard: %.1f GB needed on the card, %.1f GB free\n", need / 1e9, fr / 1e9); exit(2); }
    CCK(cuMemAlloc_(&G2.B2, G2.nw2 * 8)); CCK(cuMemsetD8_(G2.B2, 0, G2.nw2 * 8));
    CCK(cuMemAlloc_(&G2.keys, G2.tabcap * 8)); CCK(cuMemsetD8_(G2.keys, 0xFF, G2.tabcap * 8));
    CCK(cuMemAlloc_(&G2.masks, G2.tabcap * 36)); CCK(cuMemsetD8_(G2.masks, 0, G2.tabcap * 36));
    CCK(cuMemAlloc_(&G2.touched, G2.tabcap)); CCK(cuMemsetD8_(G2.touched, 0, G2.tabcap));
    CCK(cuMemAlloc_(&G2.ages, G2.tabcap)); CCK(cuMemsetD8_(G2.ages, 0, G2.tabcap));
    for (int i = 0; i < 2; i++) CCK(cuMemAlloc_(&G2.surv[i], G2.survcap * sizeof(CRec)));
    CCK(cuMemAlloc_(&G2.res, G2.rescap * sizeof(CRec)));
    CCK(cuMemAlloc_(&G2.nsurv, 8)); CCK(cuMemAlloc_(&G2.nres, 8)); CCK(cuMemAlloc_(&G2.stats, 64)); CCK(cuMemsetD8_(G2.stats, 0, 64));
    CCK(cuMemAlloc_(&G2.ovf, 8)); CCK(cuMemsetD8_(G2.ovf, 0, 8));
    CCK(cuMemAlloc_(&G2.seg, seg + 64)); CCK(cuMemsetD8_(G2.seg, 0, seg + 64));
    CCK(cuMemAlloc_(&G2.dig, (seg / LEAF + 1) * 32));
    CCK(cuMemAlloc_(&G2.spans, G2.spancap * sizeof(CSpan)));
    if (rK) { CCK(cuMemAlloc_(&G2.rbits, G2.rnw * 4)); CCK(cuMemsetD8_(G2.rbits, 0, G2.rnw * 4)); }
    G2.hdig = malloc((seg / LEAF + 1) * 32); sha_init(&G2.tree); sha_init(&G2.plain);
    if (copyback && cuMemHostAlloc_((void **)&G2.hcopy, seg + 64, 0)) G2.hcopy = malloc(seg + 64);
    for (int i = 0; i < NSTG; i++) { CCK(cuMemHostAlloc_((void **)&G2.stg[i], G2.spancap * sizeof(CSpan), 0)); CCK(cuEventCreate_(&G2.stgev[i], 2)); }
    CCK(cuCtxSync_());
}
/* The card's letter buffer (G2.seg, SEG letters) holds the word from some position on: windows from offset wst on
   are not scanned yet, leaves from offset lst on (16-byte aligned; lst is a multiple of LEAF in word positions) are
   not hashed yet, letters up to fill are there.  g2_flush scans all windows that fit, hashes every complete leaf
   (and the last partial one when final), and keeps only the letters still needed at the front. */
static u64 g_fill, g_wst, g_lst; static CDP g_scratch;
/* GEN17_PROF: synchronise after every step of a flush and add up the times (queued copies and expands, reinsert,
   scan, harvest, leaf hashes, the rest); printed by g2_finish.  Timing only (slower). */
static int g_prof = -1; static double g_pt[6], g_tp;
#define PSYNC(k) do { if (g_prof) { CCK(cuCtxSync_()); double t_ = wall(); g_pt[k] += t_ - g_tp; g_tp = t_; } } while (0)
static void g2_flush(int final) {
    if (!g_scratch) CCK(cuMemAlloc_(&g_scratch, 2 * LEAF + 256));
    const int n = G2.n; double t0 = wall();
    if (g_prof < 0) g_prof = getenv("GEN17_PROF") != NULL;
    g_tp = t0; PSYNC(0);
    u64 tmask = G2.tabcap - 1;
    if (G2.ns) {                                        /* survivors of the last flush back into the table */
        void *a[] = { &G2.surv[G2.sp], &G2.ns, &G2.keys, &G2.masks, &G2.touched, &G2.ages, &tmask, &G2.ovf };
        c_launch(G2.freins, G2.ns, 256, a); G2.ns = 0;
    }
    PSYNC(1);
    u64 wend = g_fill >= (u64)n - 1 ? g_fill - (n - 1) : 0;    /* windows start at wst .. wend-1 */
    if (wend > g_wst) {
        CDP d = G2.seg + g_wst; u64 nwin = wend - g_wst;
        void *a1[] = { &d, &nwin, &G2.CH, &G2.keys, &G2.masks, &G2.touched, &tmask, &G2.stats, &G2.ovf };
        c_launch(G2.fscan, (nwin + G2.CH - 1) / G2.CH, 128, a1);
        if (G2.rK) { void *a3[] = { &d, &nwin, &G2.rlo, &G2.rspan, &G2.rbits, &G2.stats }; CCK(cuLaunch_(G2.frank, 4096, 1, 1, 256, 1, 1, 0, NULL, a3, NULL)); }
    } else wend = g_wst;
    PSYNC(2);
    int so = G2.sp ^ 1; CCK(cuMemsetD8_(G2.nsurv, 0, 8)); CCK(cuMemsetD8_(G2.nres, 0, 8));
    void *a2[] = { &G2.keys, &G2.masks, &G2.touched, &G2.tabcap, &G2.B2, &G2.surv[so], &G2.nsurv, &G2.survcap, &G2.res, &G2.nres, &G2.rescap, &G2.ages, &G2.stats, &G2.ovf };
    CCK(cuLaunch_(G2.fharv, 4096, 1, 1, 256, 1, 1, 0, NULL, a2, NULL));
    PSYNC(3);
    u64 hl = g_fill - g_lst, nleaf = final ? (hl + LEAF - 1) / LEAF : hl / LEAF, hlen = final ? hl : nleaf * LEAF;
    CDP nl = G2.seg + g_lst; u32 lf = LEAF;
    if (nleaf) { void *a4[] = { &nl, &hlen, &lf, &G2.dig }; c_launch(G2.fleaf, nleaf, 64, a4); }
    PSYNC(4);
    CCK(cuCtxSync_());
    u32 cnt[2]; CCK(cuDtoH_(&cnt[0], G2.nsurv, 4)); CCK(cuDtoH_(&cnt[1], G2.nres, 4)); CCK(cuDtoH_(&G2.ovf_h, G2.ovf, 4));
    if (G2.ovf_h) fprintf(stderr, "gcard: table or list overflow (flag %u) at flush %llu; the run is not valid\n", G2.ovf_h, (unsigned long long)G2.segs);
    G2.ns = cnt[0] < G2.survcap ? cnt[0] : G2.survcap; G2.sp = so;
    u32 nr = cnt[1] < G2.rescap ? cnt[1] : G2.rescap;
    if (nr) {
        if (G2.nhres + nr > G2.caphres) { G2.caphres = (G2.nhres + nr) * 2; G2.hres = realloc(G2.hres, G2.caphres * sizeof(CRec)); if (!G2.hres) { fprintf(stderr, "gcard: out of memory (residues)\n"); exit(2); } }
        CCK(cuDtoH_(G2.hres + G2.nhres, G2.res, (size_t)nr * sizeof(CRec))); G2.nhres += nr;
    }
    if (nleaf) {
        CCK(cuDtoH_(G2.hdig, G2.dig, nleaf * 32));
        for (u64 i = 0; i < nleaf; i++) { u8 b[32]; for (int j = 0; j < 8; j++) { u32 v = G2.hdig[i * 8 + j]; b[4*j] = v >> 24; b[4*j+1] = v >> 16; b[4*j+2] = v >> 8; b[4*j+3] = v; } sha_update(&G2.tree, b, 32); }
        G2.nleaves += nleaf;
        if (G2.copyback) {
            CCK(cuDtoH_(G2.hcopy, nl, hlen));
            static const char A[] = "0123456789ABCDEF"; for (u64 i = 0; i < hlen; i++) G2.hcopy[i] = A[G2.hcopy[i]];
            sha_update(&G2.plain, G2.hcopy, hlen);
        }
    }
    /* keep [r, fill): the unscanned windows' letters and the unhashed leaf; leaf start 16-byte aligned again */
    u64 lnext = g_lst + hlen, r = wend < lnext ? wend : lnext;
    u64 keep = g_fill - r, pad = (16 - ((lnext - r) & 15)) & 15;
    if (keep) { CCK(cuDtoD_(g_scratch, G2.seg + r, keep)); CCK(cuDtoD_(G2.seg + pad, g_scratch, keep)); }
    g_wst = wend - r + pad; g_lst = lnext - r + pad; g_fill = keep + pad;
    CCK(cuCtxSync_());
    PSYNC(5);
    G2.segs++; G2.tk += wall() - t0;
}
static void g2_reserve(u64 k) {
    if (k + LEAF + 64 > G2.SEG) { fprintf(stderr, "gcard: block of %llu letters larger than the buffer\n", (unsigned long long)k); exit(2); }
    if (g_fill + k > G2.SEG) g2_flush(0);
}
static void g2_placed(u64 k) {                     /* k letters were put at g_fill: apply the test hooks, take them */
    if (G2.cut_at && G2.total + k > G2.cut_at) k = G2.total < G2.cut_at ? G2.cut_at - G2.total : 0;
    if (G2.flip_at != ~0ULL && G2.flip_at >= G2.total && G2.flip_at < G2.total + k) {
        u8 b; CDP a = G2.seg + g_fill + (G2.flip_at - G2.total); CCK(cuCtxSync_()); CCK(cuDtoH_(&b, a, 1)); b = (u8)((b + 1) % G2.n); CCK(cuHtoD_(a, &b, 1));
        fprintf(stderr, "gcard: letter %llu changed (test)\n", (unsigned long long)G2.flip_at);
    }
    g_fill += k; G2.total += k;
}
static void g2_letters(const u8 *p, u64 k) { g2_reserve(k); CCK(cuHtoD_(G2.seg + g_fill, p, k)); g2_placed(k); }
/* spans from the host, offsets relative to their own first letter; k letters in all */
static void g2_spans(const CSpan *sp, u32 nsp, u64 k, int pinned) {   /* pinned: sp is pinned and stays untouched until its copy is done */
    g2_reserve(k);
    if (nsp) {
        /* copy through a pinned slot, asynchronously in the default stream: the copy runs after the kernels before it
           (so G2.spans is not overwritten while an expand still reads it) and the slot is reused only after its copy */
        if (pinned) CCK(cuHtoDA_(G2.spans, sp, (size_t)nsp * sizeof(CSpan), NULL));
        else {
            int si = G2.stgi; G2.stgi = (si + 1) % NSTG;
            if (G2.stgused[si]) CCK(cuEventSynchronize_(G2.stgev[si]));
            memcpy(G2.stg[si], sp, (size_t)nsp * sizeof(CSpan));
            CCK(cuHtoDA_(G2.spans, G2.stg[si], (size_t)nsp * sizeof(CSpan), NULL));
            CCK(cuEventRecord_(G2.stgev[si], NULL)); G2.stgused[si] = 1;
        }
        CDP out = G2.seg + g_fill;
        void *a[] = { &G2.spans, &nsp, &out };
        c_launch(G2.fexp, (u64)nsp * 32, 256, a);
    }
    g2_placed(k);
}
static int g2_cmp(const void *a, const void *b) { u64 x = ((const CRec *)a)->g, y = ((const CRec *)b)->g; return x < y ? -1 : x > y; }
typedef struct { u64 total, pw, runs, complete_on_card, residues, residue_groups, residue_complete, bits, missing, rseen, rmarked; int overflow; char tree[65], plain[65]; } G2Res;
static void g2_finish(G2Res *o) {
    g2_flush(1);
    if (g_prof > 0) fprintf(stderr, "gcard profile (s): queued copies+expands %.2f, reinsert %.2f, scan %.2f, harvest %.2f, leaf hashes %.2f, rest %.2f\n", g_pt[0], g_pt[1], g_pt[2], g_pt[3], g_pt[4], g_pt[5]);
    memset(o, 0, sizeof *o);
    /* the survivors left after the last segment are residues too */
    if (G2.ns) {
        size_t nr = G2.ns;
        if (G2.nhres + nr > G2.caphres) { G2.caphres = G2.nhres + nr; G2.hres = realloc(G2.hres, G2.caphres * sizeof(CRec)); }
        CCK(cuDtoH_(G2.hres + G2.nhres, G2.surv[G2.sp], nr * sizeof(CRec))); G2.nhres += nr;
    }
    CCK(cuDtoH_(G2.st, G2.stats, 32));
    o->total = G2.total; o->pw = G2.st[0]; o->runs = G2.st[1]; o->complete_on_card = G2.st[2]; o->rmarked = G2.st[3]; o->residues = G2.nhres;
    o->overflow = G2.ovf_h != 0;
    /* residues: OR per group; complete groups set their bit on the host copy of the affected words */
    qsort(G2.hres, G2.nhres, sizeof(CRec), g2_cmp);
    u32 full[9] = {0}; for (int b = 0; b < G2.MW; b++) full[b >> 5] |= 1u << (b & 31);
    size_t w = 0;
    for (size_t a = 0; a < G2.nhres;) {
        size_t b = a; u32 m[9] = {0};
        while (b < G2.nhres && G2.hres[b].g == G2.hres[a].g) { for (int q = 0; q < 9; q++) m[q] |= G2.hres[b].m[q]; b++; }
        o->residue_groups++;
        if (G2.hres[a].g % G2.gK != G2.gI) { fprintf(stderr, "gcard: residue of group %llu outside the shard\n", (unsigned long long)G2.hres[a].g); exit(2); }
        G2.hres[w].g = G2.hres[a].g; memcpy(G2.hres[w].m, m, 36); w++;
        a = b;
    }
    /* set the bits of complete residue groups: read-modify-write of their 64-bit words */
    u64 missing_parts = 0;
    for (size_t a = 0; a < w; a++) {
        int isfull = 1; for (int q = 0; q < 9; q++) if (G2.hres[a].m[q] != full[q]) isfull = 0;
        u64 g = G2.hres[a].g / G2.gK, word; CDP addr = G2.B2 + (g >> 6) * 8;      /* local bit of the group */
        CCK(cuDtoH_(&word, addr, 8));
        if (isfull) { if (!(word >> (g & 63) & 1)) { word |= 1ULL << (g & 63); CCK(cuHtoD_(addr, &word, 8)); o->residue_complete++; } }
        else if (!(word >> (g & 63) & 1)) { u32 c = 0; for (int q = 0; q < 9; q++) c += __builtin_popcount(G2.hres[a].m[q]); missing_parts += (u64)G2.MW - c; G2.hres[a].age = 0xFFFFFFFFu; }
    }
    CDP dc; CCK(cuMemAlloc_(&dc, 8)); CCK(cuMemsetD8_(dc, 0, 8));
    void *pa[] = { &G2.B2, &G2.nw2, &dc }; CCK(cuLaunch_(G2.fpop, 4096, 1, 1, 256, 1, 1, 0, NULL, pa, NULL)); CCK(cuCtxSync_());
    CCK(cuDtoH_(&o->bits, dc, 8));
    /* missing permutations: groups without bit and without residue count n(n-1); partial residue groups their gap */
    u64 nbit_parts = 0; for (size_t a = 0; a < w; a++) if (G2.hres[a].age == 0xFFFFFFFFu) nbit_parts++;
    o->missing = (G2.NGloc - o->bits - nbit_parts) * (u64)G2.MW + missing_parts;   /* bits outside the shard are never set */
    if (G2.rK) { CDP dc2; CCK(cuMemAlloc_(&dc2, 8)); CCK(cuMemsetD8_(dc2, 0, 8)); u64 nw32 = G2.rnw / 2 + 1; (void)nw32;
        /* rbits are u32 words: count them as u64 words over the rounded-up buffer (allocated rnw*4 bytes) */
        u64 nw64 = G2.rnw / 2; void *pr[] = { &G2.rbits, &nw64, &dc2 }; CCK(cuLaunch_(G2.fpop, 4096, 1, 1, 256, 1, 1, 0, NULL, pr, NULL)); CCK(cuCtxSync_());
        CCK(cuDtoH_(&o->rseen, dc2, 8));
        if (G2.rnw & 1) { u32 last; CCK(cuDtoH_(&last, G2.rbits + (G2.rnw - 1) * 4, 4)); o->rseen += __builtin_popcount(last); } }
    sha_final(&G2.tree, o->tree); if (G2.copyback) sha_final(&G2.plain, o->plain); else strcpy(o->plain, "none");
}
static void g2_json(FILE *f, const G2Res *o) {
    fprintf(f, "\"satellite\":%d,\"segment_letters\":%llu,\"segments\":%llu,\"permutation_windows\":%llu,\"rotation_runs\":%llu,\"groups\":%llu,\"groups_complete_on_card\":%llu,"
            "\"residues\":%llu,\"residue_groups\":%llu,\"residue_groups_complete\":%llu,\"group_bits\":%llu,\"missing_permutations\":%llu,\"overflow\":%d,"
            "\"tree_sha256\":\"%s\",\"leaves\":%llu,\"plain_sha256_card_letters\":\"%s\",\"card_seconds\":%.1f",
            G2.S, (unsigned long long)G2.SEG, (unsigned long long)G2.segs, (unsigned long long)o->pw, (unsigned long long)o->runs, (unsigned long long)G2.NG,
            (unsigned long long)o->complete_on_card, (unsigned long long)o->residues, (unsigned long long)o->residue_groups, (unsigned long long)o->residue_complete,
            (unsigned long long)o->bits, (unsigned long long)o->missing, o->overflow, o->tree, (unsigned long long)G2.nleaves, o->plain, G2.tk);
    fprintf(f, ",\"group_shard\":\"%llu/%llu\",\"shard_groups\":%llu,\"scan_kernel\":\"%s\"", (unsigned long long)G2.gI, (unsigned long long)G2.gK, (unsigned long long)G2.NGloc, G2.scan1 ? "scan" : "scan2");
    if (G2.rK) fprintf(f, ",\"card_shard\":\"%llu/%llu\",\"card_shard_span\":%llu,\"card_shard_seen\":%llu,\"card_shard_missing\":%llu",
                       (unsigned long long)G2.rI, (unsigned long long)G2.rK, (unsigned long long)G2.rspan, (unsigned long long)o->rseen, (unsigned long long)(G2.rspan - o->rseen));
}
