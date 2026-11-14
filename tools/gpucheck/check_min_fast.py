#!/usr/bin/env python
"""check_min_fast.py - check_min.py (reproduce/tools) with the same method and output,
in less time.

usage: check_min_fast.py N WORD.txt [--chunk WINDOWS] [--procs P]

Same check: the file is mapped read-only; for every window of N letters that are all different, its rank among the
N! permutations (Lehmer code) sets one bit; at the end all N! bits must be set.  Same output lines and exit status
as check_min.py (0 valid, 1 not valid).  It shares no code with delcheck, literal_check or trailsearch.

What is faster: --procs P (default 1 = check_min.py): P processes over P ranges of the windows, each with its own
bitmap in shared memory, running the loop body of check_min.py unchanged; the bitmaps are OR-ed at the end.
Memory about P x (N!/8 + 1.5 GB) with the default --chunk (measured: N = 12, P = 3: 5.1 GB peak, 52 s against
138 s for check_min.py; N = 13, P = 4: about 9 GB, GUESS); --chunk 4194304 cuts the 1.5 GB to about 0.4.  (A Lehmer code by bit masks and
np.bitwise_count, and np.bitwise_or.at for the bits, were tried: no faster than the original body at N = 11.)
"""
import sys
import time
from math import factorial
from multiprocessing import Process, shared_memory

import numpy as np

ALPHABET = b"0123456789ABCDEF"


def scan(n, path, w0, w1, chunk, seen, stats):
    """Marks the permutation windows that begin at w0 .. w1 - 1; stats[0] += windows, stats[1] += occurrences."""
    word = np.memmap(path, dtype=np.uint8, mode="r")
    code = np.full(256, 255, np.uint8)
    for i, c in enumerate(ALPHABET[:n]):
        code[c] = i
    weight = [factorial(n - 1 - i) for i in range(n)]
    full = (1 << n) - 1
    windows = occurrences = 0
    for start in range(w0, w1, chunk):
        m = min(chunk, w1 - start)
        block = code[word[start:start + m + n - 1]]
        if block.max() >= n:
            bad = start + int(np.argmax(block >= n))
            return f"position {bad}: byte {int(word[bad])} is not one of the {n} letters"
        # from here to the end of the loop: the code of check_min.py, line for line
        col = [block[i:i + m] for i in range(n)]    # col[i][s] = letter i of the window that begins at start + s
        letters = np.zeros(m, np.uint16)            # the set of letters of every window, as a bit mask
        for c in col:
            letters |= np.left_shift(np.uint16(1), c.astype(np.uint16))
        perm = np.flatnonzero(letters == full)      # the windows that are permutations
        windows += m
        occurrences += len(perm)
        sel = [c[perm] for c in col]
        rank = np.zeros(len(perm), np.int64)
        for i in range(n - 1):                      # Lehmer code: how many later letters are smaller than letter i
            smaller = np.zeros(len(perm), np.int64)
            for j in range(i + 1, n):
                smaller += sel[j] < sel[i]
            rank += smaller * weight[i]
        for bit in range(8):                        # all writes of one pass set the same bit, so duplicates are harmless
            byte = rank[(rank & 7) == bit] >> 3
            seen[byte] |= np.uint8(1 << bit)
    stats[0] += windows
    stats[1] += occurrences
    return None


def worker(n, path, w0, w1, chunk, shm_name, nbytes, res_name, k):
    shm = shared_memory.SharedMemory(name=shm_name)
    res = shared_memory.SharedMemory(name=res_name)
    seen = np.ndarray((nbytes,), np.uint8, buffer=shm.buf)
    out = np.ndarray((3 * 64,), np.int64, buffer=res.buf)
    st = [0, 0]
    err = scan(n, path, w0, w1, chunk, seen, st)
    out[3 * k], out[3 * k + 1], out[3 * k + 2] = st[0], st[1], 1 if err else 0
    if err:
        print(err, file=sys.stderr)
    del seen, out
    shm.close()
    res.close()


def main():
    n = int(sys.argv[1])
    path = sys.argv[2]
    chunk = int(sys.argv[sys.argv.index("--chunk") + 1]) if "--chunk" in sys.argv else 1 << 24
    procs = int(sys.argv[sys.argv.index("--procs") + 1]) if "--procs" in sys.argv else 1
    t0 = time.time()
    word = np.memmap(path, dtype=np.uint8, mode="r")
    length = len(word) - 1 if word[-1] == 10 else len(word)
    del word
    nfact = factorial(n)
    nbytes = (nfact + 7) // 8
    nwin = length - n + 1
    if procs <= 1:
        seen = np.zeros(nbytes, np.uint8)
        st = [0, 0]
        err = scan(n, path, 0, nwin, chunk, seen, st)
        if err:
            sys.exit(err)
        windows, occurrences = st
    else:
        res = shared_memory.SharedMemory(create=True, size=3 * 64 * 8)
        out = np.ndarray((3 * 64,), np.int64, buffer=res.buf)
        out[:] = 0
        shms, ps = [], []
        for k in range(procs):
            shm = shared_memory.SharedMemory(create=True, size=nbytes)
            np.ndarray((nbytes,), np.uint8, buffer=shm.buf)[:] = 0
            shms.append(shm)
            w0, w1 = nwin * k // procs, nwin * (k + 1) // procs
            p = Process(target=worker, args=(n, path, w0, w1, chunk, shm.name, nbytes, res.name, k))
            p.start()
            ps.append(p)
        for p in ps:
            p.join()
        if any(p.exitcode != 0 for p in ps) or out[2:3 * procs:3].any():
            sys.exit("a worker failed (see above)")
        windows, occurrences = int(out[0:3 * procs:3].sum()), int(out[1:3 * procs:3].sum())
        seen = np.ndarray((nbytes,), np.uint8, buffer=shms[0].buf).copy()
        for shm in shms[1:]:
            seen |= np.ndarray((nbytes,), np.uint8, buffer=shm.buf)
        for shm in shms:
            shm.close()
            shm.unlink()
        del out
        res.close()
        res.unlink()
    distinct = sum(int(np.bitwise_count(seen[i:i + (1 << 24)]).sum(dtype=np.int64)) for i in range(0, len(seen), 1 << 24))
    print(f"n = {n}, length {length}, windows {windows}, windows that are permutations {occurrences}")
    print(f"distinct permutations {distinct} of {nfact}, missing {nfact - distinct}, "
          f"repeated occurrences {occurrences - distinct}  ({time.time() - t0:.0f} s)")
    print("VALID: every permutation occurs" if distinct == nfact else "NOT VALID")
    sys.exit(0 if distinct == nfact else 1)


if __name__ == "__main__":
    main()
