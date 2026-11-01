/* blake3.h - BLAKE3 (default hash mode, no key, 32-byte output: the value b3sum prints) in portable C, written from
   the BLAKE3 specification (O'Connor, Aumasson, Neves, Wilcox-O'Hearn, 2020).  Header only, everything static, all
   names start with b3_ / B3_.

   Two independent ways to the same value (tested against each other in b3ref.c --selftest):
     b3_hash_tree     the whole input in memory, the tree built recursively as the specification defines it: a node of
                      more than one chunk splits into a left subtree of the largest power-of-two number of chunks that
                      leaves at least one byte for the right subtree;
     b3_hasher        streaming (b3_init / b3_update / b3_final): the chunk state and the stack of chaining values,
                      merged lazily as in the reference implementation (merge when the number of chunks so far says
                      so; the last chunk and the last subtree are never merged before the end, so the ROOT flag goes
                      on the right node).
   b3_push_subtree(h, cv, nchunks): add the chaining value of a complete subtree of nchunks = 2^k chunks that starts
   at the hasher's chunk counter (a multiple of nchunks), computed elsewhere (the card).  The subtree must not be the
   whole input (it would need the ROOT flag): callers push the two halves of each subtree, as the reference
   implementation does, so the stack always holds at least two values when the input ends on a subtree. */
#ifndef B3_H
#define B3_H
#include <stdint.h>
#include <string.h>

#define B3_CHUNK_LEN 1024
#define B3_BLOCK_LEN 64
#define B3_CHUNK_START 1u
#define B3_CHUNK_END 2u
#define B3_PARENT 4u
#define B3_ROOT 8u

static const uint32_t B3_IV[8] = { 0x6A09E667u, 0xBB67AE85u, 0x3C6EF372u, 0xA54FF53Au, 0x510E527Fu, 0x9B05688Cu, 0x1F83D9ABu, 0x5BE0CD19u };

static inline uint32_t b3_rotr(uint32_t x, int r) { return (x >> r) | (x << (32 - r)); }
#define B3_G(s, a, b, c, d, x, y) do { \
    s[a] = s[a] + s[b] + (x); s[d] = b3_rotr(s[d] ^ s[a], 16); s[c] = s[c] + s[d]; s[b] = b3_rotr(s[b] ^ s[c], 12); \
    s[a] = s[a] + s[b] + (y); s[d] = b3_rotr(s[d] ^ s[a], 8);  s[c] = s[c] + s[d]; s[b] = b3_rotr(s[b] ^ s[c], 7); } while (0)
static void b3_round(uint32_t s[16], const uint32_t m[16]) {
    B3_G(s, 0, 4, 8, 12, m[0], m[1]);  B3_G(s, 1, 5, 9, 13, m[2], m[3]);  B3_G(s, 2, 6, 10, 14, m[4], m[5]);  B3_G(s, 3, 7, 11, 15, m[6], m[7]);
    B3_G(s, 0, 5, 10, 15, m[8], m[9]); B3_G(s, 1, 6, 11, 12, m[10], m[11]); B3_G(s, 2, 7, 8, 13, m[12], m[13]); B3_G(s, 3, 4, 9, 14, m[14], m[15]);
}
static const int B3_PERM[16] = { 2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8 };
/* the compression function: 16 output words */
static void b3_compress(const uint32_t cv[8], const uint32_t block[16], uint64_t counter, uint32_t blen, uint32_t flags, uint32_t out[16]) {
    uint32_t s[16] = { cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7], B3_IV[0], B3_IV[1], B3_IV[2], B3_IV[3],
                       (uint32_t)counter, (uint32_t)(counter >> 32), blen, flags };
    uint32_t m[16], t[16]; memcpy(m, block, 64);
    for (int r = 0; r < 7; r++) {
        b3_round(s, m);
        if (r < 6) { for (int i = 0; i < 16; i++) t[i] = m[B3_PERM[i]]; memcpy(m, t, 64); }
    }
    for (int i = 0; i < 8; i++) { out[i] = s[i] ^ s[i + 8]; out[i + 8] = s[i + 8] ^ cv[i]; }
}
static void b3_words(const uint8_t *p, uint32_t w[16]) {         /* 64 bytes, little endian */
    for (int i = 0; i < 16; i++) w[i] = (uint32_t)p[4*i] | (uint32_t)p[4*i+1] << 8 | (uint32_t)p[4*i+2] << 16 | (uint32_t)p[4*i+3] << 24;
}
static void b3_bytes(const uint32_t w[8], uint8_t out[32]) {
    for (int i = 0; i < 8; i++) { out[4*i] = (uint8_t)w[i]; out[4*i+1] = (uint8_t)(w[i] >> 8); out[4*i+2] = (uint8_t)(w[i] >> 16); out[4*i+3] = (uint8_t)(w[i] >> 24); }
}
static void b3_hex(const uint8_t h[32], char out[65]) {
    static const char X[] = "0123456789abcdef";
    for (int i = 0; i < 32; i++) { out[2*i] = X[h[i] >> 4]; out[2*i+1] = X[h[i] & 15]; } out[64] = 0;
}
/* the inputs of a node's last compression: its chaining value is the first 8 output words; as the root it is
   compressed again with ROOT (output block counter 0) */
typedef struct { uint32_t cv[8], block[16]; uint64_t counter; uint32_t blen, flags; } b3_out;
static void b3_out_cv(const b3_out *o, uint32_t cv[8]) { uint32_t w[16]; b3_compress(o->cv, o->block, o->counter, o->blen, o->flags, w); memcpy(cv, w, 32); }
static void b3_out_root(const b3_out *o, uint8_t h[32]) { uint32_t w[16]; b3_compress(o->cv, o->block, 0, o->blen, o->flags | B3_ROOT, w); b3_bytes(w, h); }
static b3_out b3_parent_out(const uint32_t l[8], const uint32_t r[8]) {
    b3_out o; memcpy(o.cv, B3_IV, 32); memcpy(o.block, l, 32); memcpy(o.block + 8, r, 32); o.counter = 0; o.blen = 64; o.flags = B3_PARENT; return o;
}
static void b3_parent_cv(const uint32_t l[8], const uint32_t r[8], uint32_t cv[8]) { b3_out o = b3_parent_out(l, r); b3_out_cv(&o, cv); }

/* ---------------------------------------------------------------- path 1: recursive tree over a buffer */
static b3_out b3_chunk_out_buf(const uint8_t *p, size_t len, uint64_t counter) {   /* len <= 1024 */
    b3_out o; uint32_t cv[8]; memcpy(cv, B3_IV, 32);
    size_t nb = len == 0 ? 1 : (len + 63) / 64;
    for (size_t b = 0; b < nb; b++) {
        uint8_t blk[64] = {0}; size_t bl = len - b * 64 < 64 ? len - b * 64 : 64; if (len == 0) bl = 0;
        memcpy(blk, p + b * 64, bl);
        uint32_t w[16]; b3_words(blk, w);
        uint32_t fl = (b == 0 ? B3_CHUNK_START : 0) | (b == nb - 1 ? B3_CHUNK_END : 0);
        if (b == nb - 1) { memcpy(o.cv, cv, 32); memcpy(o.block, w, 64); o.counter = counter; o.blen = (uint32_t)bl; o.flags = fl; }
        else { uint32_t r[16]; b3_compress(cv, w, counter, 64, fl, r); memcpy(cv, r, 32); }
    }
    return o;
}
static b3_out b3_node_out(const uint8_t *p, size_t len, uint64_t counter) {
    if (len <= B3_CHUNK_LEN) return b3_chunk_out_buf(p, len, counter);
    size_t lc = 1; while (2 * lc * B3_CHUNK_LEN < len) lc *= 2;       /* left: largest power of 2 chunks < len */
    b3_out L = b3_node_out(p, lc * B3_CHUNK_LEN, counter), R = b3_node_out(p + lc * B3_CHUNK_LEN, len - lc * B3_CHUNK_LEN, counter + lc);
    uint32_t l[8], r[8]; b3_out_cv(&L, l); b3_out_cv(&R, r); return b3_parent_out(l, r);
}
static void b3_hash_tree(const uint8_t *p, size_t len, uint8_t h[32]) { b3_out o = b3_node_out(p, len, 0); b3_out_root(&o, h); }
/* chaining value of a complete (non-root) subtree of len bytes starting at chunk `counter` (tests of the card) */
static void b3_subtree_cv(const uint8_t *p, size_t len, uint64_t counter, uint32_t cv[8]) { b3_out o = b3_node_out(p, len, counter); b3_out_cv(&o, cv); }

/* ---------------------------------------------------------------- path 2: streaming hasher */
typedef struct { uint32_t cv[8]; uint64_t counter; uint8_t buf[64]; uint32_t buflen, blocks; } b3_chunk;
typedef struct { b3_chunk c; uint32_t stack[64][8]; int sl; } b3_hasher;
static void b3_chunk_init(b3_chunk *c, uint64_t counter) { memcpy(c->cv, B3_IV, 32); c->counter = counter; c->buflen = 0; c->blocks = 0; memset(c->buf, 0, 64); }
static size_t b3_chunk_len(const b3_chunk *c) { return (size_t)c->blocks * 64 + c->buflen; }
static void b3_chunk_update(b3_chunk *c, const uint8_t *p, size_t len) {
    while (len) {
        if (c->buflen == 64) {           /* a full block and more input: it is not the chunk's last block */
            uint32_t w[16], r[16]; b3_words(c->buf, w);
            b3_compress(c->cv, w, c->counter, 64, c->blocks == 0 ? B3_CHUNK_START : 0, r); memcpy(c->cv, r, 32);
            c->blocks++; c->buflen = 0; memset(c->buf, 0, 64);
        }
        size_t take = 64 - c->buflen; if (take > len) take = len;
        memcpy(c->buf + c->buflen, p, take); c->buflen += (uint32_t)take; p += take; len -= take;
    }
}
static b3_out b3_chunk_output(const b3_chunk *c) {
    b3_out o; memcpy(o.cv, c->cv, 32); b3_words(c->buf, o.block); o.counter = c->counter; o.blen = c->buflen;
    o.flags = (c->blocks == 0 ? B3_CHUNK_START : 0) | B3_CHUNK_END; return o;
}
static void b3_init(b3_hasher *h) { b3_chunk_init(&h->c, 0); h->sl = 0; }
static void b3_merge(b3_hasher *h, uint64_t total_chunks) {
    int post = __builtin_popcountll(total_chunks);
    while (h->sl > post) { uint32_t cv[8]; b3_parent_cv(h->stack[h->sl - 2], h->stack[h->sl - 1], cv); h->sl--; memcpy(h->stack[h->sl - 1], cv, 32); }
}
static void b3_push_cv(b3_hasher *h, const uint32_t cv[8], uint64_t counter) { b3_merge(h, counter); memcpy(h->stack[h->sl++], cv, 32); }
static void b3_update(b3_hasher *h, const void *data, size_t len) {
    const uint8_t *p = (const uint8_t *)data;
    if (b3_chunk_len(&h->c) > 0) {
        size_t take = B3_CHUNK_LEN - b3_chunk_len(&h->c); if (take > len) take = len;
        b3_chunk_update(&h->c, p, take); p += take; len -= take;
        if (!len) return;
        b3_out o = b3_chunk_output(&h->c); uint32_t cv[8]; b3_out_cv(&o, cv);
        b3_push_cv(h, cv, h->c.counter); b3_chunk_init(&h->c, h->c.counter + 1);
    }
    while (len > B3_CHUNK_LEN) {          /* a whole chunk with more input after it */
        b3_chunk_update(&h->c, p, B3_CHUNK_LEN);
        b3_out o = b3_chunk_output(&h->c); uint32_t cv[8]; b3_out_cv(&o, cv);
        b3_push_cv(h, cv, h->c.counter); b3_chunk_init(&h->c, h->c.counter + 1);
        p += B3_CHUNK_LEN; len -= B3_CHUNK_LEN;
    }
    if (len) { b3_chunk_update(&h->c, p, len); b3_merge(h, h->c.counter); }
}
/* a complete subtree of nchunks (a power of 2) chunks at the current chunk counter, from its chaining value */
static int b3_push_subtree(b3_hasher *h, const uint32_t cv[8], uint64_t nchunks) {
    if (b3_chunk_len(&h->c) != 0 || nchunks == 0 || (nchunks & (nchunks - 1)) || h->c.counter % nchunks) return -1;
    b3_push_cv(h, cv, h->c.counter); b3_chunk_init(&h->c, h->c.counter + nchunks); return 0;
}
static void b3_final(const b3_hasher *h, uint8_t out[32]) {
    if (h->sl == 0) { b3_out o = b3_chunk_output(&h->c); b3_out_root(&o, out); return; }
    b3_out o; int rem = h->sl;
    if (b3_chunk_len(&h->c) > 0) o = b3_chunk_output(&h->c);
    else if (rem >= 2) { o = b3_parent_out(h->stack[rem - 2], h->stack[rem - 1]); rem -= 2; }   /* sl >= 2 here (see the header) */
    else { memset(out, 0, 32); return; }   /* one subtree pushed as the whole input: not allowed (all-zero result marks the misuse) */
    while (rem > 0) { uint32_t cv[8]; b3_out_cv(&o, cv); o = b3_parent_out(h->stack[rem - 1], cv); rem--; }
    b3_out_root(&o, out);
}
#endif
