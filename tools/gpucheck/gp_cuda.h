/* gp_cuda.h - the CUDA driver library loaded at run time (nvcuda.dll / libcuda.so.1),
   plus loading of the PTX module gpuprep.ptx that sits next to the program.  Everything static (one include). */
#ifndef GP_CUDA_H
#define GP_CUDA_H
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#ifdef _WIN32
#define CAPI __stdcall
#else
#include <dlfcn.h>
#define CAPI
#endif
typedef uint64_t u64; typedef uint32_t u32; typedef uint8_t u8; typedef u64 DP;
static int (CAPI *cInit)(unsigned), (CAPI *cDeviceGet)(int *, int), (CAPI *cCtxCreate)(void **, unsigned, int);
static int (CAPI *cModuleLoadData)(void **, const void *), (CAPI *cModuleGetFunction)(void **, void *, const char *);
static int (CAPI *cModuleGetGlobal)(DP *, size_t *, void *, const char *);
static int (CAPI *cMemAlloc)(DP *, size_t), (CAPI *cMemFree)(DP), (CAPI *cMemsetD8)(DP, unsigned char, size_t), (CAPI *cMemGetInfo)(size_t *, size_t *);
static int (CAPI *cHtoD)(DP, const void *, size_t), (CAPI *cDtoH)(void *, DP, size_t), (CAPI *cCtxSync)(void);
static int (CAPI *cLaunch)(void *, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned, void *, void **, void **);
static int (CAPI *cMemHostAlloc)(void **, size_t, unsigned), (CAPI *cMemFreeHost)(void *);
#define CK(x) do { int e_ = (x); if (e_) { fprintf(stderr, "gpuprep: CUDA error %d at %s:%d\n", e_, __FILE__, __LINE__); exit(2); } } while (0)

#ifdef _WIN32
#ifndef NOMINMAX
#define NOMINMAX
#endif
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
static void *gp_lib_open(void) { return (void *)LoadLibraryA("nvcuda.dll"); }
static void *gp_lib_sym(void *l, const char *s) { return (void *)GetProcAddress((HMODULE)l, s); }
#else
static void *gp_lib_open(void) { return dlopen("libcuda.so.1", RTLD_NOW); }
static void *gp_lib_sym(void *l, const char *s) { return dlsym(l, s); }
#endif

static void *gp_mod;
/* create a context on device 0 and load gpuprep.ptx from the program's directory (or the current one) */
static void gp_init_ptx(const char *argv0, const char *ptxname) {
    void *lib = gp_lib_open(); if (!lib) { fprintf(stderr, "gpuprep: no CUDA driver\n"); exit(2); }
#define SYM(v, s) do { *(void **)&v = gp_lib_sym(lib, s); if (!v) { fprintf(stderr, "gpuprep: missing %s\n", s); exit(2); } } while (0)
    SYM(cInit, "cuInit"); SYM(cDeviceGet, "cuDeviceGet"); SYM(cCtxCreate, "cuCtxCreate_v2"); SYM(cModuleLoadData, "cuModuleLoadData");
    SYM(cModuleGetFunction, "cuModuleGetFunction"); SYM(cModuleGetGlobal, "cuModuleGetGlobal_v2");
    SYM(cMemAlloc, "cuMemAlloc_v2"); SYM(cMemFree, "cuMemFree_v2"); SYM(cMemsetD8, "cuMemsetD8_v2"); SYM(cMemGetInfo, "cuMemGetInfo_v2");
    SYM(cHtoD, "cuMemcpyHtoD_v2"); SYM(cDtoH, "cuMemcpyDtoH_v2"); SYM(cCtxSync, "cuCtxSynchronize"); SYM(cLaunch, "cuLaunchKernel");
    SYM(cMemHostAlloc, "cuMemHostAlloc"); SYM(cMemFreeHost, "cuMemFreeHost");
#undef SYM
    char path[4096]; const char *sl = strrchr(argv0, '/'), *bs = strrchr(argv0, '\\'); if (bs > sl) sl = bs;
    if (sl) snprintf(path, sizeof path, "%.*s/%s", (int)(sl - argv0), argv0, ptxname); else snprintf(path, sizeof path, "%s", ptxname);
    FILE *pf = fopen(path, "rb"); if (!pf) pf = fopen(ptxname, "rb");
    if (!pf) { fprintf(stderr, "gpuprep: gpuprep.ptx not found\n"); exit(2); }
    fseek(pf, 0, SEEK_END); long psz = ftell(pf); fseek(pf, 0, SEEK_SET);
    char *ptx = calloc(psz + 1, 1); if (fread(ptx, 1, psz, pf) != (size_t)psz) { fprintf(stderr, "gpuprep: cannot read %s\n", path); exit(2); }
    fclose(pf);
    int dev; void *ctx;
    CK(cInit(0)); CK(cDeviceGet(&dev, 0)); CK(cCtxCreate(&ctx, 4 /* blocking sync */, dev));
    CK(cModuleLoadData(&gp_mod, ptx)); free(ptx);
}
static void gp_init(const char *argv0) { gp_init_ptx(argv0, "gpuprep.ptx"); }
static void *gp_fn(const char *name) { void *f; CK(cModuleGetFunction(&f, gp_mod, name)); return f; }
static void gp_launch(void *f, unsigned blocks, unsigned bt, unsigned shmem, void **args) {
    if (blocks < 1) blocks = 1;
    CK(cLaunch(f, blocks, 1, 1, bt, 1, 1, shmem, NULL, args, NULL));
}
static DP gp_alloc(size_t bytes, int zero) { DP p; CK(cMemAlloc(&p, bytes)); if (zero) CK(cMemsetD8(p, 0, bytes)); return p; }
static u64 gp_popcount(DP bits32, u64 nwords) {
    static void *fp; if (!fp) fp = gp_fn("popcnt");
    DP dc = gp_alloc(8, 1);
    void *a[] = { &bits32, &nwords, &dc }; gp_launch(fp, 4096, 256, 0, a); CK(cCtxSync());
    u64 c; CK(cDtoH(&c, dc, 8)); CK(cMemFree(dc)); return c;
}
#endif
