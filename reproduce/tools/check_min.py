#!/usr/bin/env python
"""check_min.py - a minimal, independent check that a word contains every permutation of N symbols.

usage: check_min.py N WORD.txt [--chunk WINDOWS]

Input   WORD.txt: the word on one line, letters 0-9 then A-F (one optional final line feed is ignored).
Output  stdout: length, number of windows that are permutations, distinct permutations, missing, repeated;
        last line "VALID: every permutation occurs" or "NOT VALID".  Exit status 0 if valid, 1 if not.

It shares no code with delcheck or with Pantone's literal_check; it is short enough to read in one sitting.

Method: the file is mapped read-only.  For every window of N letters: if its N letters are all different, its rank
among the N! permutations is computed from the Lehmer code and one bit is set.  At the end all N! bits must be set.
Memory: N!/8 bytes for the bits (0.06 GB at N = 12, 0.78 GB at N = 13) plus a few arrays of WINDOWS elements
(default 2^24).  It does not test whether a letter can be deleted.

Measured (one thread, OPENBLAS_NUM_THREADS=1; without that setting numpy reserves about 0.7 GB more on a machine
with 32 threads):       N = 10: 2 s, 0.19 GB.   N = 11: 16 s, 0.75 GB.   N = 12: 3 minutes, 0.84 GB.
                        N = 13: 33 minutes, 1.56 GB.
"""
import sys
import time
from math import factorial

import numpy as np

ALPHABET = b"0123456789ABCDEF"


def main():
    n = int(sys.argv[1])
    path = sys.argv[2]
    chunk = int(sys.argv[sys.argv.index("--chunk") + 1]) if "--chunk" in sys.argv else 1 << 24
    t0 = time.time()

    word = np.memmap(path, dtype=np.uint8, mode="r")
    length = len(word) - 1 if word[-1] == 10 else len(word)

    code = np.full(256, 255, np.uint8)              # byte of the file -> letter 0..n-1, 255 = not a letter
    for i, c in enumerate(ALPHABET[:n]):
        code[c] = i

    nfact = factorial(n)
    weight = [factorial(n - 1 - i) for i in range(n)]
    seen = np.zeros((nfact + 7) // 8, np.uint8)     # bit r = the permutation of rank r has been seen
    full = (1 << n) - 1
    windows = occurrences = 0

    for start in range(0, length - n + 1, chunk):
        m = min(chunk, length - n + 1 - start)      # windows that begin in this chunk
        block = code[word[start:start + m + n - 1]]
        if block.max() >= n:
            bad = start + int(np.argmax(block >= n))
            sys.exit(f"position {bad}: byte {int(word[bad])} is not one of the {n} letters")
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

    ones = np.array([bin(i).count("1") for i in range(256)], np.int64)
    distinct = sum(int(ones[seen[i:i + (1 << 24)]].sum()) for i in range(0, len(seen), 1 << 24))
    print(f"n = {n}, length {length}, windows {windows}, windows that are permutations {occurrences}")
    print(f"distinct permutations {distinct} of {nfact}, missing {nfact - distinct}, "
          f"repeated occurrences {occurrences - distinct}  ({time.time() - t0:.0f} s)")
    print("VALID: every permutation occurs" if distinct == nfact else "NOT VALID")
    sys.exit(0 if distinct == nfact else 1)


if __name__ == "__main__":
    main()
