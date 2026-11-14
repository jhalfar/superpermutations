/* gp_reader.h - streams a word in order, chunk by chunk, into page-locked host buffers (include after gp_cuda.h).
   Sources: a plain file (read by R threads at once, each its own chunks; on Windows unbuffered by default, which
   reads the disk at full speed and leaves the file cache alone), a .xz file (through "xz -dc", one reader thread),
   or "-" (standard input, one reader thread).  Chunks come back strictly in file order.  Every buffer has HEAD
   free bytes before the data, so the caller can put the carried letters of the previous chunk in front of it.
   The reader never changes the file. */
#ifndef GP_READER_H
#define GP_READER_H
#include <pthread.h>
#include <time.h>
#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#define popen _popen
#define pclose _pclose
#endif
#define RD_HEAD 4096
typedef struct { u8 *base, *data; size_t len; int eof, ready, pinned; u64 idx, want; } RBuf;
typedef struct {
    int mode;                      /* 0 file direct (Windows), 1 file buffered, 2 pipe (xz or stdin) */
    const char *path; FILE *pipe; int is_popen;
    size_t chunk; int nbuf, nth; RBuf *b; u64 next, nchunks, size;
    pthread_t th[8]; pthread_mutex_t mu; pthread_cond_t cv; int err; double busy[8]; u64 bytes;
} Reader;
static double gp_wall(void) { struct timespec ts; timespec_get(&ts, TIME_UTC); return ts.tv_sec + ts.tv_nsec * 1e-9; }

static int rd_ends(const char *s, const char *suf) { size_t a = strlen(s), b = strlen(suf); return a >= b && !strcmp(s + a - b, suf); }
static RBuf *rd_slot_for_write(Reader *r, u64 idx) {
    RBuf *s = &r->b[idx % r->nbuf];
    pthread_mutex_lock(&r->mu); while (s->want != idx && !r->err) pthread_cond_wait(&r->cv, &r->mu); pthread_mutex_unlock(&r->mu);
    return r->err ? NULL : s;
}
static void rd_publish(Reader *r, RBuf *s, u64 idx, size_t len, int eof) {
    pthread_mutex_lock(&r->mu); s->idx = idx; s->len = len; s->eof = eof; s->ready = 1; s->want = ~0ULL;
    r->bytes += len; pthread_cond_broadcast(&r->cv); pthread_mutex_unlock(&r->mu);
}
static void rd_fail(Reader *r, const char *what) {
    fprintf(stderr, "gpuprep: read error: %s\n", what);
    pthread_mutex_lock(&r->mu); r->err = 1; pthread_cond_broadcast(&r->cv); pthread_mutex_unlock(&r->mu);
}
typedef struct { Reader *r; int t; } RArg;
static void *rd_file_thread(void *arg) {
    Reader *r = ((RArg *)arg)->r; int t = ((RArg *)arg)->t; free(arg);
#ifdef _WIN32
    HANDLE h = INVALID_HANDLE_VALUE; FILE *f = NULL;
    if (r->mode == 0) {
        h = CreateFileA(r->path, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, OPEN_EXISTING, FILE_FLAG_NO_BUFFERING | FILE_FLAG_SEQUENTIAL_SCAN, NULL);
        if (h == INVALID_HANDLE_VALUE) { rd_fail(r, "CreateFile"); return NULL; }
    } else { f = fopen(r->path, "rb"); if (!f) { rd_fail(r, r->path); return NULL; } }
#else
    FILE *f = fopen(r->path, "rb"); if (!f) { rd_fail(r, r->path); return NULL; }
#endif
    for (u64 idx = t; idx < r->nchunks; idx += r->nth) {
        RBuf *s = rd_slot_for_write(r, idx); if (!s) break;
        u64 off = idx * r->chunk; size_t want = (size_t)(r->size - off < r->chunk ? r->size - off : r->chunk), got = 0;
        double a = gp_wall();
#ifdef _WIN32
        if (r->mode == 0) {
            size_t req = (want + 4095) & ~(size_t)4095;
            while (got < want) {
                OVERLAPPED ov; memset(&ov, 0, sizeof ov); u64 o = off + got; ov.Offset = (DWORD)o; ov.OffsetHigh = (DWORD)(o >> 32);
                DWORD g = 0; if (!ReadFile(h, s->data + got, (DWORD)(req - got), &g, &ov) || g == 0) break;
                got += g;
            }
            if (got > want) got = want;
        } else {
            if (_fseeki64(f, (long long)off, SEEK_SET)) { rd_fail(r, "seek"); break; }
            got = fread(s->data, 1, want, f);
        }
#else
        if (fseeko(f, (off_t)off, SEEK_SET)) { rd_fail(r, "seek"); break; }
        got = fread(s->data, 1, want, f);
#endif
        r->busy[t] += gp_wall() - a;
        if (got != want) { rd_fail(r, "short read"); break; }
        rd_publish(r, s, idx, got, idx + 1 == r->nchunks);
    }
#ifdef _WIN32
    if (h != INVALID_HANDLE_VALUE) CloseHandle(h);
#endif
    if (f) fclose(f);
    return NULL;
}
static void *rd_pipe_thread(void *arg) {
    Reader *r = ((RArg *)arg)->r; free(arg);
    for (u64 idx = 0;; idx++) {
        RBuf *s = rd_slot_for_write(r, idx); if (!s) break;
        size_t got = 0; double a = gp_wall();
        while (got < r->chunk) { size_t g = fread(s->data + got, 1, r->chunk - got, r->pipe); if (!g) break; got += g; }
        r->busy[0] += gp_wall() - a;
        int eof = got < r->chunk;
        if (eof && ferror(r->pipe)) { rd_fail(r, "pipe"); break; }
        rd_publish(r, s, idx, got, eof);
        if (eof) break;
    }
    return NULL;
}
/* io: "direct" (default for files on Windows) or "buffered"; nth reader threads for files (1..8) */
static void rd_open(Reader *r, const char *path, size_t chunk, int nbuf, int nth, const char *io, const char *xz) {
    memset(r, 0, sizeof *r); r->path = path; r->chunk = chunk; r->nbuf = nbuf; r->nth = nth < 1 ? 1 : nth > 8 ? 8 : nth;
    pthread_mutex_init(&r->mu, NULL); pthread_cond_init(&r->cv, NULL);
    if (!strcmp(path, "-")) { r->mode = 2; r->pipe = stdin;
#ifdef _WIN32
        _setmode(_fileno(stdin), _O_BINARY);
#endif
    } else if (rd_ends(path, ".xz")) {
        char cmd[8192]; snprintf(cmd, sizeof cmd, "\"%s\" -dc \"%s\"", xz ? xz : "xz", path);
#ifdef _WIN32
        { char c2[8300]; snprintf(c2, sizeof c2, "\"%s\"", cmd); r->pipe = popen(c2, "rb"); }   /* cmd.exe strips one pair of quotes */
#else
        r->pipe = popen(cmd, "r");
#endif
        if (!r->pipe) { fprintf(stderr, "gpuprep: cannot start %s\n", cmd); exit(2); }
        r->mode = 2; r->is_popen = 1;
    } else {
        FILE *f = fopen(path, "rb"); if (!f) { perror(path); exit(2); }
#ifdef _WIN32
        _fseeki64(f, 0, SEEK_END); r->size = (u64)_ftelli64(f);
#else
        fseeko(f, 0, SEEK_END); r->size = (u64)ftello(f);
#endif
        fclose(f);
        r->nchunks = r->size ? (r->size + chunk - 1) / chunk : 1;
#ifdef _WIN32
        r->mode = (io && !strcmp(io, "buffered")) ? 1 : 0;
#else
        r->mode = 1;
#endif
    }
    if (r->mode == 2) r->nth = 1;
    r->b = calloc(nbuf, sizeof(RBuf));
    for (int i = 0; i < nbuf; i++) {
        size_t sz = RD_HEAD + chunk + 8192;
        r->b[i].pinned = 1;
        if (cMemHostAlloc((void **)&r->b[i].base, sz, 0)) {
            r->b[i].pinned = 0;
#ifdef _WIN32
            r->b[i].base = _aligned_malloc(sz, 4096);
#else
            if (posix_memalign((void **)&r->b[i].base, 4096, sz)) r->b[i].base = NULL;
#endif
            if (!r->b[i].base) { fprintf(stderr, "gpuprep: out of host memory\n"); exit(2); }
        }
        r->b[i].data = r->b[i].base + RD_HEAD; r->b[i].want = i;
    }
    for (int t = 0; t < r->nth; t++) {
        RArg *a = malloc(sizeof *a); a->r = r; a->t = t;
        pthread_create(&r->th[t], NULL, r->mode == 2 ? rd_pipe_thread : rd_file_thread, a);
    }
}
/* the next chunk in order (blocks); NULL on a read error */
static RBuf *rd_next(Reader *r) {
    RBuf *s = &r->b[r->next % r->nbuf];
    pthread_mutex_lock(&r->mu); while (!(s->ready && s->idx == r->next) && !r->err) pthread_cond_wait(&r->cv, &r->mu); pthread_mutex_unlock(&r->mu);
    if (r->err) return NULL;
    r->next++; return s;
}
static void rd_release(Reader *r, RBuf *s) {
    pthread_mutex_lock(&r->mu); s->ready = 0; s->want = s->idx + r->nbuf; pthread_cond_broadcast(&r->cv); pthread_mutex_unlock(&r->mu);
}
/* after the last chunk was released: join the threads, close the pipe; returns 0, or 1 if xz failed */
static int rd_close(Reader *r) {
    pthread_mutex_lock(&r->mu); r->err |= 2; pthread_cond_broadcast(&r->cv); pthread_mutex_unlock(&r->mu);   /* wake any waiting reader */
    for (int t = 0; t < r->nth; t++) pthread_join(r->th[t], NULL);
    int rc = 0; if (r->is_popen) rc = pclose(r->pipe) != 0;
    for (int i = 0; i < r->nbuf; i++) {   /* the buffers go back (a program may read the word several times) */
        if (r->b[i].pinned) cMemFreeHost(r->b[i].base);
        else {
#ifdef _WIN32
            _aligned_free(r->b[i].base);
#else
            free(r->b[i].base);
#endif
        }
    }
    free(r->b); r->b = NULL;
    return rc;
}
static double rd_busy(Reader *r) { double m = 0; for (int t = 0; t < r->nth; t++) if (r->busy[t] > m) m = r->busy[t]; return m; }
#endif
