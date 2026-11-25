/* Equal-length derepeating for adjacent pairs. Build with GCC and OpenMP. */
#define _FILE_OFFSET_BITS 64
#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <limits.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

#ifdef _WIN32
#include <io.h>
#include <windows.h>
#else
#include <sys/mman.h>
#include <unistd.h>
#endif

enum { MAX_N = 14, CHUNK = 1 << 26 };
typedef uint64_t u64;
typedef int64_t i64;

typedef struct {
    const unsigned char *bytes;
    i64 size;
    i64 length;
} Word;

typedef struct {
    u64 windows, distinct, repeated;
} Counts;

typedef struct {
    i64 first, last, donor, copies, anchors;
} Repeat;

typedef struct {
    i64 at;
    /* An insertion stores a source permutation's start. A deletion stores -1. */
    i64 source;
} Event;

static int n;
static unsigned char symbol[256];
static u64 factorial[MAX_N + 1];

static void *array(u64 elements, size_t width) {
    if (elements > SIZE_MAX / width)
        return NULL;
    return calloc((size_t)(elements ? elements : 1), width);
}

static int map_word(const char *path, Word *word) {
#ifdef _WIN32
    HANDLE file = CreateFileA(path, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING,
                              FILE_ATTRIBUTE_NORMAL, NULL);
    if (file == INVALID_HANDLE_VALUE)
        return 0;
    LARGE_INTEGER size;
    if (GetFileType(file) != FILE_TYPE_DISK || !GetFileSizeEx(file, &size) ||
        size.QuadPart <= 0 || (u64)size.QuadPart > SIZE_MAX ||
        size.QuadPart > INT64_MAX - CHUNK - MAX_N) {
        CloseHandle(file);
        return 0;
    }
    word->size = size.QuadPart;
    HANDLE mapping = CreateFileMappingA(file, NULL, PAGE_READONLY, 0, 0, NULL);
    CloseHandle(file);
    if (!mapping)
        return 0;
    word->bytes = MapViewOfFile(mapping, FILE_MAP_READ, 0, 0, 0);
    CloseHandle(mapping);
    if (!word->bytes)
        return 0;
#else
    int fd = open(path, O_RDONLY | O_NONBLOCK);
    if (fd < 0)
        return 0;
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) || st.st_size <= 0 ||
        (u64)st.st_size > SIZE_MAX || st.st_size > INT64_MAX - CHUNK - MAX_N) {
        close(fd);
        return 0;
    }
    word->size = st.st_size;
    void *mapping = mmap(NULL, (size_t)word->size, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd);
    if (mapping == MAP_FAILED)
        return 0;
    word->bytes = mapping;
#endif
    word->length = word->size;
    while (word->length > 0 &&
           (word->bytes[word->length - 1] == '\n' || word->bytes[word->length - 1] == '\r'))
        --word->length;
    return 1;
}

static void unmap_word(Word *word) {
    if (!word->bytes)
        return;
#ifdef _WIN32
    UnmapViewOfFile(word->bytes);
#else
    munmap((void *)word->bytes, (size_t)word->size);
#endif
    word->bytes = NULL;
}

static inline u64 rank_of(const unsigned char *letters) {
    unsigned used = 0;
    u64 rank = 0;
    for (int i = 0; i < n; ++i) {
        unsigned c = letters[i];
        rank += (c - __builtin_popcount(used & ((1u << c) - 1))) * factorial[n - 1 - i];
        used |= 1u << c;
    }
    return rank;
}

static void unrank(u64 rank, unsigned char *letters) {
    unsigned used = 0;
    for (int i = 0; i < n; ++i) {
        unsigned index = (unsigned)(rank / factorial[n - 1 - i]);
        rank %= factorial[n - 1 - i];
        for (unsigned c = 0; c < (unsigned)n; ++c) {
            if (used & (1u << c))
                continue;
            if (index == 0) {
                letters[i] = (unsigned char)c;
                used |= 1u << c;
                break;
            }
            --index;
        }
    }
}

static inline int bit(const u64 *bits, u64 rank) {
    return (bits[rank >> 6] >> (rank & 63)) & 1;
}

static inline int set_bit(u64 *bits, u64 rank) {
    u64 mask = UINT64_C(1) << (rank & 63);
    return (__atomic_fetch_or(&bits[rank >> 6], mask, __ATOMIC_RELAXED) & mask) != 0;
}

/* Rolling distinct-letter test, then exact permutation ranking. */
static int scan(Word word, u64 words, u64 *seen, u64 *repeated, Counts *counts) {
    u64 windows = 0;
    int invalid = 0;
    i64 starts = word.length >= n ? word.length - n + 1 : 1;
    i64 chunks = (starts + CHUNK - 1) / CHUNK;

    #pragma omp parallel for schedule(dynamic, 1) reduction(+:windows) reduction(|:invalid)
    for (i64 chunk = 0; chunk < chunks; ++chunk) {
        i64 first = chunk * CHUNK;
        i64 last = first + CHUNK;
        if (last > starts)
            last = starts;
        int freq[MAX_N + 1] = {0};
        int distinct = 0;
        for (i64 i = first; i < last + n - 1 && i < word.length; ++i) {
            unsigned c = symbol[word.bytes[i]];
            invalid |= c == (unsigned)n;
            if (i - first >= n) {
                unsigned old = symbol[word.bytes[i - n]];
                if (--freq[old] == 0 && old != (unsigned)n)
                    --distinct;
            }
            if (freq[c]++ == 0 && c != (unsigned)n)
                ++distinct;
            if (i - first < n - 1 || distinct != n)
                continue;

            unsigned char letters[MAX_N];
            for (int k = 0; k < n; ++k)
                letters[k] = symbol[word.bytes[i - n + 1 + k]];
            u64 rank = rank_of(letters);
            if (set_bit(seen, rank))
                set_bit(repeated, rank);
            ++windows;
        }
    }

    if (invalid) {
        fputs("derepeat: word contains a byte outside the alphabet\n", stderr);
        return 0;
    }
    u64 distinct = 0;
    u64 repeat_types = 0;
    #pragma omp parallel for reduction(+:distinct,repeat_types)
    for (u64 k = 0; k < words; ++k) {
        distinct += __builtin_popcountll(seen[k]);
        repeat_types += __builtin_popcountll(repeated[k]);
    }
    *counts = (Counts){windows, distinct, repeat_types};
    return 1;
}

static u64 repeated_index(const u64 *bits, const u64 *prefix, u64 rank) {
    u64 word = rank >> 6;
    u64 index = prefix[word >> 3];
    for (u64 k = (word >> 3) << 3; k < word; ++k)
        index += __builtin_popcountll(bits[k]);
    return index + __builtin_popcountll(bits[word] & ((UINT64_C(1) << (rank & 63)) - 1));
}

static void keep_min(i64 *where, i64 at) {
    i64 old = __atomic_load_n(where, __ATOMIC_RELAXED);
    while (at < old && !__atomic_compare_exchange_n(where, &old, at, 0,
                                                   __ATOMIC_RELAXED, __ATOMIC_RELAXED)) {}
}

static void keep_max(i64 *where, i64 at) {
    i64 old = __atomic_load_n(where, __ATOMIC_RELAXED);
    while (at > old && !__atomic_compare_exchange_n(where, &old, at, 0,
                                                   __ATOMIC_RELAXED, __ATOMIC_RELAXED)) {}
}

static inline int padded_letter(Word word, i64 at) {
    return at <= 0 || at > word.length ? n : symbol[word.bytes[at - 1]];
}

static int gather_repeats(Word word, u64 words, u64 *middles, const u64 *repeated,
                          Repeat *repeats) {
    u64 blocks = (words + 7) / 8;
    u64 *prefix = array(blocks, sizeof(*prefix));
    if (!prefix)
        return 0;
    u64 rank_count = 0;
    for (u64 block = 0; block < blocks; ++block) {
        prefix[block] = rank_count;
        for (u64 k = block * 8; k < block * 8 + 8 && k < words; ++k)
            rank_count += __builtin_popcountll(repeated[k]);
    }

    memset(middles, 0, (size_t)words * sizeof(*middles));
    #pragma omp parallel for schedule(dynamic, 4096)
    for (u64 k = 0; k < words; ++k) {
        u64 bits = repeated[k];
        while (bits) {
            u64 rank = (k << 6) + __builtin_ctzll(bits);
            bits &= bits - 1;
            Repeat *r = &repeats[repeated_index(repeated, prefix, rank)];
            *r = (Repeat){INT64_MAX, -1, INT64_MAX, 0, 0};

            unsigned char letters[MAX_N] = {0};
            unrank(rank, letters);
            if (letters[0] > letters[n - 1]) {
                unsigned char swap = letters[0];
                letters[0] = letters[n - 1];
                letters[n - 1] = swap;
            }
            set_bit(middles, rank_of(letters));
        }
    }

    /* Only middles of repeated ranks need their two flank orientations counted. */
    i64 starts = word.length - n + 3;
    i64 chunks = (starts + CHUNK - 1) / CHUNK;
    #pragma omp parallel for schedule(dynamic, 1)
    for (i64 chunk = 0; chunk < chunks; ++chunk) {
        i64 end = (chunk + 1) * CHUNK;
        if (end > starts)
            end = starts;
        for (i64 at = chunk * CHUNK; at < end; ++at) {
            unsigned char letters[MAX_N];
            unsigned used = 0;
            for (int i = 1; i < n - 1; ++i) {
                int c = padded_letter(word, at + i);
                if (c == n || (used & (1u << c)))
                    break;
                used |= 1u << c;
                letters[i] = (unsigned char)c;
            }
            if (__builtin_popcount(used) != n - 2)
                continue;

            unsigned complement = ((1u << n) - 1) & ~used;
            int a = __builtin_ctz(complement);
            int b = __builtin_ctz(complement & (complement - 1));
            letters[0] = (unsigned char)a;
            letters[n - 1] = (unsigned char)b;
            if (!bit(middles, rank_of(letters)))
                continue;
            int left = padded_letter(word, at);
            int right = padded_letter(word, at + n - 1);
            for (int orientation = 0; orientation < 2; ++orientation) {
                letters[0] = (unsigned char)a;
                letters[n - 1] = (unsigned char)b;
                u64 rank = rank_of(letters);
                if (bit(repeated, rank)) {
                    Repeat *r = &repeats[repeated_index(repeated, prefix, rank)];
                    if (left == a && right == b) {
                        __atomic_fetch_add(&r->copies, 1, __ATOMIC_RELAXED);
                        keep_min(&r->first, at - 1);
                        keep_max(&r->last, at - 1);
                    } else if (left != a && right != b) {
                        __atomic_fetch_add(&r->anchors, 1, __ATOMIC_RELAXED);
                        /* Keep a reverse permutation and skip the leading sentinel. */
                        if (at > 0 && !(left == b && right == a))
                            keep_min(&r->donor, at - 1);
                    }
                }
                int swap = a;
                a = b;
                b = swap;
            }
        }
    }
    free(prefix);
    return 1;
}

static int compare_events(const void *left, const void *right) {
    i64 a = ((const Event *)left)->at;
    i64 b = ((const Event *)right)->at;
    return (a > b) - (a < b);
}

static int check_events(const Event *events, u64 count, i64 length) {
    i64 position = 0;
    for (u64 k = 0; k < count; ++k) {
        Event e = events[k];
        if (e.at < position || e.at > length || (k > 0 && e.at == events[k - 1].at) ||
            (e.source < 0 && e.at > length - n) || e.source > length - n)
            return 0;
        position = e.at + (e.source < 0 ? n : 0);
    }
    return 1;
}

static int write_word(FILE *file, Word word, const Event *events, u64 count) {
    i64 position = 0;
    for (u64 k = 0; k < count; ++k) {
        Event e = events[k];
        size_t span = (size_t)(e.at - position);
        if (fwrite(word.bytes + position, 1, span, file) != span)
            return 0;
        position = e.at;
        if (e.source < 0) {
            position += n;
        } else if (fputc(word.bytes[e.source + n - 1], file) == EOF ||
                   fwrite(word.bytes + e.source, 1, (size_t)n - 1, file) != (size_t)n - 1) {
            return 0;
        }
    }
    size_t tail = (size_t)(word.length - position);
    return fwrite(word.bytes + position, 1, tail, file) == tail;
}

static int output_exists(const char *path) {
#ifdef _WIN32
    return GetFileAttributesA(path) != INVALID_FILE_ATTRIBUTES;
#else
    struct stat st;
    return lstat(path, &st) == 0;
#endif
}

static FILE *make_temporary(const char *destination, char **name) {
    const char suffix[] = ".derepeat-XXXXXX";
    size_t length = strlen(destination);
    if (length > SIZE_MAX - sizeof(suffix))
        return NULL;
    char *path = malloc(length + sizeof(suffix));
    if (!path)
        return NULL;
    memcpy(path, destination, length);
    memcpy(path + length, suffix, sizeof(suffix));

#ifdef _WIN32
    int fd = -1;
    for (int attempt = 0; attempt < 64; ++attempt) {
        memcpy(path + length, suffix, sizeof(suffix));
        if (_mktemp_s(path, length + sizeof(suffix)) != 0)
            break;
        fd = _open(path, _O_CREAT | _O_EXCL | _O_WRONLY | _O_BINARY, _S_IREAD | _S_IWRITE);
        if (fd >= 0 || errno != EEXIST)
            break;
    }
    FILE *file = fd < 0 ? NULL : _fdopen(fd, "wb");
#else
    int fd = mkstemp(path);
    FILE *file = fd < 0 ? NULL : fdopen(fd, "wb");
#endif
    if (file) {
        *name = path;
    } else {
        if (fd >= 0) {
#ifdef _WIN32
            _close(fd);
#else
            close(fd);
#endif
            remove(path);
        }
        free(path);
    }
    return file;
}

static int publish(const char *temporary, const char *destination) {
#ifdef _WIN32
    return MoveFileExA(temporary, destination, 0) != 0;
#else
    /* link() publishes atomically and refuses any existing destination. */
    return link(temporary, destination) == 0;
#endif
}

static long number(const char *value, long minimum, long maximum) {
    if (!value[0] || strspn(value, "0123456789") != strlen(value))
        return -1;
    char *end;
    errno = 0;
    long result = strtol(value, &end, 10);
    return errno || *end || result < minimum || result > maximum ? -1 : result;
}

static void usage(FILE *out) {
    fputs("usage: derepeat N ALPHABET INPUT.txt OUTPUT.txt [--threads T]\n"
          "       derepeat N ALPHABET INPUT.txt --check [--threads T]\n"
          "N is 3..14, T is 1..256 (default 4).\n", out);
}

int main(int argc, char **argv) {
    if (argc == 2 && strcmp(argv[1], "--help") == 0) {
        usage(stdout);
        return 0;
    }
    int threads = 4;
    if ((argc != 5 && argc != 7) ||
        (argc == 7 && (strcmp(argv[5], "--threads") != 0 ||
                       (threads = (int)number(argv[6], 1, 256)) < 0))) {
        usage(stderr);
        return 2;
    }
    n = (int)number(argv[1], 3, MAX_N);
    if (n < 0 || strlen(argv[2]) != (size_t)n) {
        fputs("derepeat: expected N distinct alphabet bytes\n", stderr);
        return 2;
    }
    memset(symbol, n, sizeof(symbol));
    for (int i = 0; i < n; ++i) {
        unsigned char c = (unsigned char)argv[2][i];
        if (symbol[c] != n || c == '\r' || c == '\n') {
            fputs("derepeat: alphabet bytes must be distinct and cannot be CR or LF\n", stderr);
            return 2;
        }
        symbol[c] = (unsigned char)i;
    }

    const char *input = argv[3];
    const char *destination = argv[4];
    int check = strcmp(destination, "--check") == 0;
    if (!check && strcmp(destination, "--threads") == 0) {
        usage(stderr);
        return 2;
    }
    if (!check && (strcmp(input, destination) == 0 || output_exists(destination))) {
        fputs("derepeat: output path already exists\n", stderr);
        return 1;
    }

    omp_set_num_threads(threads);
    factorial[0] = 1;
    for (int i = 1; i <= n; ++i)
        factorial[i] = factorial[i - 1] * (unsigned)i;
    u64 words = (factorial[n] + 63) / 64;
    Word source = {0}, output = {0};
    u64 *seen = NULL, *repeated = NULL;
    Repeat *repeats = NULL;
    Event *events = NULL;
    char *temporary = NULL;
    int result = 1;

    if (!map_word(input, &source)) {
        fprintf(stderr, "derepeat: cannot map a nonempty regular file at %s\n", input);
        goto cleanup;
    }
    seen = array(words, sizeof(*seen));
    repeated = array(words, sizeof(*repeated));
    if (!seen || !repeated) {
        fputs("derepeat: cannot allocate permutation bitsets\n", stderr);
        goto cleanup;
    }
    Counts before;
    if (!scan(source, words, seen, repeated, &before))
        goto cleanup;
    u64 missing = factorial[n] - before.distinct;
    u64 initial_extra = before.windows - before.distinct;
    if (check) {
        printf("{\"n\":%d,\"length\":%" PRId64 ",\"distinct\":%" PRIu64
               ",\"missing\":%" PRIu64 ",\"repeated_types\":%" PRIu64
               ",\"extra_copies\":%" PRIu64 "}\n",
               n, source.length, before.distinct, missing, before.repeated, initial_extra);
        result = missing != 0;
        goto cleanup;
    }
    if (missing != 0) {
        fprintf(stderr, "derepeat: input is missing %" PRIu64 " permutations\n", missing);
        goto cleanup;
    }

    u64 moves = 0, criterion_fail = 0;
    if (before.repeated) {
        repeats = array(before.repeated, sizeof(*repeats));
        events = array(2 * before.repeated, sizeof(*events));
        if (!repeats || !events || !gather_repeats(source, words, seen, repeated, repeats)) {
            fputs("derepeat: cannot allocate repeat index\n", stderr);
            goto cleanup;
        }

        u64 counted_extra = 0;
        for (u64 i = 0; i < before.repeated; ++i) {
            Repeat r = repeats[i];
            if (r.copies < 2 || r.first < 0 || r.last > source.length - n || r.last < r.first) {
                fputs("derepeat: inconsistent repeat index\n", stderr);
                goto cleanup;
            }
            counted_extra += (u64)(r.copies - 1);
            if (r.anchors < r.copies)
                ++criterion_fail;
            if (r.copies != 2 || r.last - r.first != n || r.donor == INT64_MAX ||
                r.anchors < r.copies)
                continue;

            events[2 * moves] = (Event){r.last, -1};
            events[2 * moves + 1] = (Event){r.donor + n - 1, r.first};
            ++moves;
        }
        if (counted_extra != initial_extra) {
            fputs("derepeat: repeat index disagrees with coverage scan\n", stderr);
            goto cleanup;
        }
        qsort(events, (size_t)(2 * moves), sizeof(*events), compare_events);
        if (!check_events(events, 2 * moves, source.length)) {
            fputs("derepeat: conflicting edit locations; output was not created\n", stderr);
            goto cleanup;
        }
        free(repeats);
        repeats = NULL;
    }

    FILE *file = make_temporary(destination, &temporary);
    if (!file) {
        fprintf(stderr, "derepeat: cannot create a temporary file beside %s\n", destination);
        goto cleanup;
    }
    int written = write_word(file, source, events, 2 * moves);
    if (fclose(file) != 0 || !written) {
        fputs("derepeat: failed to write output\n", stderr);
        goto cleanup;
    }
    unmap_word(&source);
    if (!map_word(temporary, &output) || output.length != source.length ||
        output.length != output.size) {
        fputs("derepeat: output length check failed\n", stderr);
        goto cleanup;
    }
    memset(seen, 0, (size_t)words * sizeof(*seen));
    memset(repeated, 0, (size_t)words * sizeof(*repeated));
    Counts after;
    if (!scan(output, words, seen, repeated, &after) || after.distinct != factorial[n] ||
        after.windows - after.distinct != initial_extra - moves) {
        fputs("derepeat: output coverage or repeat count check failed; output was not created\n",
              stderr);
        goto cleanup;
    }
    unmap_word(&output);
    if (!publish(temporary, destination)) {
        fprintf(stderr, "derepeat: could not publish without overwriting %s\n", destination);
        goto cleanup;
    }
    printf("{\"n\":%d,\"length\":%" PRId64 ",\"distinct\":%" PRIu64
           ",\"missing\":0,\"moves\":%" PRIu64 ",\"initial_extra_copies\":%" PRIu64
           ",\"extra_copies\":%" PRIu64 ",\"repeated_types\":%" PRIu64
           ",\"criterion_fail_input\":%" PRIu64 ",\"skipped_input_types\":%" PRIu64 "}\n",
           n, output.length, after.distinct, moves, initial_extra, after.windows - after.distinct,
           after.repeated, criterion_fail, before.repeated - moves);
    result = 0;

cleanup:
    unmap_word(&source);
    unmap_word(&output);
    if (temporary) {
        remove(temporary);
        free(temporary);
    }
    free(seen);
    free(repeated);
    free(repeats);
    free(events);
    return result;
}
