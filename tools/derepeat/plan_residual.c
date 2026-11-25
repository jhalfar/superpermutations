/* Plan safe equal-length swaps from a sparse, independently counted context scan. */
#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { MAX_N = 16, MAX_MIDDLE = MAX_N - 2 };
typedef long long Offset;

typedef struct {
    Offset at;
    char middle[MAX_MIDDLE + 1], left, right;
} Hit;

typedef struct {
    size_t begin, end, copies[2];
    char permutation[2][MAX_N + 1];
} Group;

typedef struct { Offset start, size; } Piece;
typedef struct { Piece *rows; size_t count, capacity; } Pieces;

typedef struct {
    Offset position[3];
    char permutation[MAX_N + 1], opposite[MAX_N + 1];
} Step;

typedef struct {
    size_t group, mark[3];
    int direction, removes_opposite;
} Choice;

static void fail(const char *message) {
    fprintf(stderr, "plan_residual: %s\n", message);
    exit(EXIT_FAILURE);
}

static void *grow(void *rows, size_t count, size_t *capacity, size_t size) {
    if (count < *capacity)
        return rows;
    if (*capacity > SIZE_MAX / 2 / size || count > SIZE_MAX / 2 / size)
        fail("too many rows");
    size_t next = *capacity ? 2 * *capacity : 16;
    void *larger = realloc(rows, next * size);
    if (!larger)
        fail("out of memory");
    *capacity = next;
    return larger;
}

static Offset number(const char *text) {
    char *end;
    errno = 0;
    Offset value = strtoll(text, &end, 10);
    if (errno || end == text || *end || value < 0)
        fail("expected a nonnegative 64-bit integer");
    return value;
}

static int read_line(FILE *file, char **line, size_t *capacity) {
    int c;
    size_t len = 0;
    while ((c = fgetc(file)) != EOF && c != '\n') {
        if (c == 0)
            fail("NUL byte in context input");
        *line = grow(*line, len, capacity, 1);
        (*line)[len++] = (char)c;
    }
    if (ferror(file))
        fail("context input read failed");
    if (c == EOF && !len)
        return 0;
    *line = grow(*line, len, capacity, 1);
    (*line)[len] = '\0';
    return 1;
}

static Hit *read_hits(const char *path, const char *alphabet, Offset length, size_t width,
                      size_t *count) {
    FILE *file = fopen(path, "rb");
    if (!file)
        fail("cannot open contexts");
    Hit *hits = NULL;
    char *line = NULL;
    size_t capacity = 0, line_capacity = 0;
    Offset previous = -1;
    while (read_line(file, &line, &line_capacity)) {
        char *middle = strtok(line, " \t\r\v\f");
        char *position = strtok(NULL, " \t\r\v\f");
        char *left = strtok(NULL, " \t\r\v\f");
        char *right = strtok(NULL, " \t\r\v\f");
        if (!right || strtok(NULL, " \t\r\v\f") || strlen(middle) != width ||
            strlen(left) != 1 || strlen(right) != 1)
            fail("expected middle, offset, left flank, right flank");
        Offset at = number(position);
        if (at <= previous || at > length - (Offset)width ||
            (at == 0 ? *left != '-' : !strchr(alphabet, *left)) ||
            (at == length - (Offset)width ? *right != '-' : !strchr(alphabet, *right)))
            fail("expected ordered middle offsets and valid neighboring letters");
        for (size_t i = 0; i < width; ++i)
            if (!strchr(alphabet, middle[i]) || strchr(middle + i + 1, middle[i]))
                fail("expected a middle with distinct alphabet letters");
        hits = grow(hits, *count, &capacity, sizeof(*hits));
        Hit *hit = &hits[(*count)++];
        *hit = (Hit){.at = at, .left = *left, .right = *right};
        memcpy(hit->middle, middle, width);
        previous = at;
    }
    free(line);
    fclose(file);
    return hits;
}

static int compare_offsets(Offset a, Offset b) {
    return (a > b) - (a < b);
}

static int compare_hits(const void *left, const void *right) {
    const Hit *a = left, *b = right;
    int order = strcmp(a->middle, b->middle);
    return order ? order : compare_offsets(a->at, b->at);
}

static void tally(const Hit *hits, const Group *group, size_t width, size_t counts[2]) {
    char a = group->permutation[0][0], b = group->permutation[0][width + 1];
    counts[0] = counts[1] = 0;
    for (size_t i = group->begin; i < group->end; ++i) {
        counts[0] += hits[i].left == a && hits[i].right == b;
        counts[1] += hits[i].left == b && hits[i].right == a;
    }
}

static Group *group_hits(Hit *hits, size_t count, const char *alphabet, size_t width,
                        size_t *group_count) {
    if (count)
        qsort(hits, count, sizeof(*hits), compare_hits);
    Group *groups = NULL;
    size_t capacity = 0;
    for (size_t start = 0; start < count;) {
        size_t end = start + 1;
        while (end < count && !strcmp(hits[start].middle, hits[end].middle))
            ++end;
        groups = grow(groups, *group_count, &capacity, sizeof(*groups));
        Group *group = &groups[(*group_count)++];
        *group = (Group){.begin = start, .end = end};
        char missing[2];
        size_t absent = 0;
        for (const char *a = alphabet; *a; ++a)
            if (!strchr(hits[start].middle, *a))
                missing[absent++] = *a;
        for (int d = 0; d < 2; ++d) {
            char *p = group->permutation[d];
            p[0] = missing[d];
            memcpy(p + 1, hits[start].middle, width);
            p[width + 1] = missing[1 - d];
        }
        tally(hits, group, width, group->copies);
        start = end;
    }
    return groups;
}

static size_t extra_copies(const Group *groups, size_t count) {
    size_t extras = 0;
    for (size_t i = 0; i < count; ++i)
        for (int d = 0; d < 2; ++d)
            if (groups[i].copies[d] > 1)
                extras += groups[i].copies[d] - 1;
    return extras;
}

static Choice next_swap(const Hit *hits, const Group *groups, size_t count, size_t width) {
    Choice best = {.group = SIZE_MAX};
    Offset best_width = LLONG_MAX, best_start = LLONG_MAX;
    const char *best_permutation = "";
    for (size_t g = 0; g < count; ++g) {
        const Group *group = &groups[g];
        for (int d = 0; d < 2; ++d) {
            if (group->copies[d] < 2)
                continue;
            const char *p = group->permutation[d];
            char a = p[0], b = p[width + 1];
            size_t first = SIZE_MAX;
            for (size_t second = group->begin; second < group->end; ++second) {
                if (hits[second].left != a || hits[second].right != b)
                    continue;
                if (first != SIZE_MAX) {
                    for (size_t donor = group->begin; donor < group->end; ++donor) {
                        const Hit *hit = &hits[donor];
                        int opposite = hit->left == b && hit->right == a;
                        if (hit->left == a || hit->right == b ||
                            (opposite && group->copies[1 - d] < 2))
                            continue;
                        size_t lo = donor < first ? donor : first;
                        size_t hi = donor > second ? donor : second;
                        size_t mid = donor < first ? first : (donor > second ? second : donor);
                        Offset start = hits[lo].at, span = hits[hi].at - start;
                        if (span < best_width || (span == best_width &&
                            (start < best_start || (start == best_start &&
                             strcmp(p, best_permutation) < 0)))) {
                            best = (Choice){g, {lo, mid, hi}, d, opposite};
                            best_width = span;
                            best_start = start;
                            best_permutation = p;
                        }
                    }
                }
                first = second;
            }
        }
    }
    return best;
}

static void refringe(Hit *hits, size_t count, Choice choice, Offset width, Offset length) {
    Hit one = hits[choice.mark[0]], two = hits[choice.mark[1]], three = hits[choice.mark[2]];
    Offset i = one.at, j = two.at, k = three.at;
    if (j - i <= width || k - j <= width)
        fail("chosen middle occurrences overlap or touch");
    /* Between the three identical middles, exchange the two gaps. */
    const Offset outside[4][3] = {{0, i, 0}, {i + width, j, k - j},
                                 {j + width, k, i - j}, {k + width, length, 0}};
    for (size_t h = 0; h < count; ++h) {
        if (h == choice.mark[0] || h == choice.mark[1] || h == choice.mark[2])
            continue;
        Offset at = hits[h].at, shift = 0;
        int matches = 0;
        /* Outside the three marked rows, the full context follows one gap. */
        for (size_t gap = 0; gap < 4; ++gap) {
            Offset lo = outside[gap][0], hi = outside[gap][1];
            if (lo < hi && at - 1 < hi && at + width >= lo) {
                shift = outside[gap][2];
                ++matches;
            }
        }
        if (matches != 1)
            fail("context cannot be shifted unambiguously");
        hits[h].at += shift;
    }
    hits[choice.mark[0]].right = two.right;
    hits[choice.mark[1]].at = i + (k - j);
    hits[choice.mark[1]].left = three.left;
    hits[choice.mark[1]].right = one.right;
    hits[choice.mark[2]].left = two.left;
    qsort(hits, count, sizeof(*hits), compare_hits);
}

static void append_span(Pieces *output, const Pieces *input, Offset start, Offset end) {
    Offset at = 0;
    for (size_t i = 0; i < input->count && at < end; ++i) {
        Piece p = input->rows[i];
        Offset lo = start > at ? start : at;
        Offset hi = end < at + p.size ? end : at + p.size;
        if (lo < hi) {
            output->rows = grow(output->rows, output->count, &output->capacity, sizeof(Piece));
            output->rows[output->count++] = (Piece){p.start + (lo - at), hi - lo};
        }
        at += p.size;
    }
}

static int compare_pieces(const void *left, const void *right) {
    const Piece *a = left, *b = right;
    return compare_offsets(a->start, b->start);
}

static void check_partition(const Pieces *pieces, Offset length) {
    Piece *source_order = malloc(pieces->count * sizeof(*source_order));
    if (!source_order)
        fail("out of memory checking splice partition");
    memcpy(source_order, pieces->rows, pieces->count * sizeof(*source_order));
    qsort(source_order, pieces->count, sizeof(*source_order), compare_pieces);
    Offset at = 0;
    for (size_t p = 0; p < pieces->count; ++p) {
        if (source_order[p].start != at || source_order[p].size > length - at)
            fail("splice does not partition the source word");
        at += source_order[p].size;
    }
    free(source_order);
    if (at != length)
        fail("splice does not cover the source word");
}

static void remap(const Pieces *input, Pieces *output, const Step *step, Offset width,
                  Offset length) {
    Offset i = step->position[0], j = step->position[1], k = step->position[2];
    output->count = 0;
    append_span(output, input, 0, i + width);
    append_span(output, input, j + width, k);
    append_span(output, input, j, j + width);
    append_span(output, input, i + width, j);
    append_span(output, input, k, length);
    check_partition(output, length);
}

static void json_word(FILE *file, const char *word) {
    fputc('"', file);
    for (; *word; ++word) {
        if (*word == '"' || *word == '\\')
            fputc('\\', file);
        fputc(*word, file);
    }
    fputc('"', file);
}

static int is_json_suffix(const char *suffix) {
    const char *json = ".json";
    while (*suffix && tolower((unsigned char)*suffix) == *json) {
        ++suffix;
        ++json;
    }
    return *suffix == *json;
}

static char *receipt_path(const char *output) {
    size_t prefix = strlen(output);
    const char *name = strrchr(output, '/');
#ifdef _WIN32
    const char *backslash = strrchr(output, '\\');
    if (backslash && (!name || backslash > name))
        name = backslash;
#endif
    name = name ? name + 1 : output;
    const char *dot = strrchr(name, '.');
    if (dot && dot > name && dot[1]) {
        if (is_json_suffix(dot))
            fail("splice output cannot use the JSON receipt suffix");
        prefix = (size_t)(dot - output);
    }
    if (prefix > SIZE_MAX - 6)
        fail("output path is too long");
    char *path = malloc(prefix + 6);
    if (!path)
        fail("out of memory constructing receipt path");
    memcpy(path, output, prefix);
    memcpy(path + prefix, ".json", 6);
    return path;
}

static void write_result(const char *output, Offset length, size_t hit_count, const Pieces *pieces,
                         const Step *steps, size_t step_count, const Group *groups, size_t group_count) {
    char *path = receipt_path(output);
    FILE *plan = fopen(output, "wx");
    if (!plan)
        fail("cannot create new splice output");
    FILE *file = fopen(path, "wx");
    if (!file) {
        fclose(plan);
        if (remove(output) != 0)
            fail("cannot create JSON receipt or remove empty splice output");
        fail("cannot create new JSON receipt");
    }
    fprintf(plan, "SPLICE %lld %lld\n", length, length);
    for (size_t i = 0; i < pieces->count; ++i)
        fprintf(plan, "C %lld %lld\n", pieces->rows[i].start, pieces->rows[i].size);
    fprintf(file, "{\n  \"scanned_contexts\": %zu,\n  \"moves\": [", hit_count);
    for (size_t i = 0; i < step_count; ++i) {
        const Step *step = &steps[i];
        fprintf(file, "%s\n    {\"permutation\": ", i ? "," : "");
        json_word(file, step->permutation);
        fprintf(file, ", \"positions\": [%lld, %lld, %lld], \"removed\": [",
                step->position[0], step->position[1], step->position[2]);
        json_word(file, step->permutation);
        if (*step->opposite) {
            fputs(", ", file);
            json_word(file, step->opposite);
        }
        fputs("]}", file);
    }
    fprintf(file, "%s],\n  \"remaining\": {", step_count ? "\n  " : "");
    int comma = 0;
    for (size_t i = 0; i < group_count; ++i) {
        for (int d = 0; d < 2; ++d) {
            if (groups[i].copies[d] > 1) {
                fprintf(file, "%s\n    ", comma ? "," : "");
                json_word(file, groups[i].permutation[d]);
                fprintf(file, ": %zu", groups[i].copies[d]);
                comma = 1;
            }
        }
    }
    fprintf(file, "%s},\n  \"copy_pieces\": %zu\n}\n", comma ? "\n  " : "", pieces->count);
    int failed = ferror(plan) || ferror(file);
    if (fclose(plan) != 0)
        failed = 1;
    if (fclose(file) != 0)
        failed = 1;
    if (failed) {
        int remove_plan = remove(output);
        int remove_receipt = remove(path);
        if (remove_plan != 0 || remove_receipt != 0)
            fail("output write failed and a partial output could not be removed");
        fail("output write failed");
    }
    free(path);
}

static void parse_alphabet(const char *input, char *alphabet, size_t length) {
    size_t next = 0;
    if (length < 3 || length > MAX_N)
        fail("alphabet must contain 3 to 16 distinct visible ASCII letters excluding '-'");
    for (int c = 33; c <= 126; ++c)
        if (c != '-' && strchr(input, c))
            alphabet[next++] = (char)c;
    if (next != length)
        fail("alphabet must contain 3 to 16 distinct visible ASCII letters excluding '-'");
    alphabet[next] = '\0';
}

int main(int argc, char **argv) {
    if (argc != 6) {
        fprintf(stderr, "usage: %s WINDOWS LENGTH REPEATS ALPHABET OUTPUT\n", argv[0]);
        return 2;
    }
    size_t n = strlen(argv[4]);
    char alphabet[MAX_N + 1];
    parse_alphabet(argv[4], alphabet, n);
    Offset length = number(argv[2]), repeats = number(argv[3]);
    if (length < (Offset)n)
        fail("word length is shorter than the alphabet");
    size_t width = n - 2, hit_count = 0, group_count = 0;
    Hit *hits = read_hits(argv[1], alphabet, length, width, &hit_count);
    Group *groups = group_hits(hits, hit_count, alphabet, width, &group_count);
    if (extra_copies(groups, group_count) != (uintmax_t)repeats)
        fail("context counts disagree with the independent repeat count");

    Pieces pieces = {0}, next = {0};
    pieces.rows = grow(NULL, 0, &pieces.capacity, sizeof(Piece));
    pieces.rows[pieces.count++] = (Piece){0, length};
    Step *steps = NULL;
    size_t step_count = 0, step_capacity = 0;
    Choice choice;
    while ((choice = next_swap(hits, groups, group_count, width)).group != SIZE_MAX) {
        Group *group = &groups[choice.group];
        steps = grow(steps, step_count, &step_capacity, sizeof(*steps));
        Step *step = &steps[step_count++];
        *step = (Step){.position = {hits[choice.mark[0]].at, hits[choice.mark[1]].at,
                                   hits[choice.mark[2]].at}};
        strcpy(step->permutation, group->permutation[choice.direction]);
        --group->copies[choice.direction];
        if (choice.removes_opposite) {
            strcpy(step->opposite, group->permutation[1 - choice.direction]);
            --group->copies[1 - choice.direction];
        }
        refringe(hits, hit_count, choice, (Offset)width, length);
        for (size_t g = 0; g < group_count; ++g) {
            size_t actual[2];
            tally(hits, &groups[g], width, actual);
            if (actual[0] != groups[g].copies[0] || actual[1] != groups[g].copies[1])
                fail("swap changes unexpected permutation counts");
        }
        remap(&pieces, &next, step, (Offset)width, length);
        Pieces old = pieces;
        pieces = next;
        next = old;
    }

    write_result(argv[5], length, hit_count, &pieces, steps, step_count, groups, group_count);
    printf("moves=%zu copy_pieces=%zu repeats_left=%zu\n", step_count, pieces.count,
           extra_copies(groups, group_count));
    free(steps);
    free(next.rows);
    free(pieces.rows);
    free(groups);
    free(hits);
    return 0;
}
