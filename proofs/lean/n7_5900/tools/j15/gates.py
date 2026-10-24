# The gates of the six statements (piece, rows, classes) and the number of modules; read by gen_native.py and by the
# sampling benchmarks.  Chosen from the measured tree above every gate (STATE_5900E.md).
# The numbers of classes of the gates of one piece are pairwise coprime where the piece is not the last one: a
# piece that is complete before a gate goes to the class of the key of its end at every gate it has not reached,
# and with coprime numbers these classes are spread over all combinations of digits.
GATES = {
    'S5':   ([(0, 20, 5), (0, 28, 4), (0, 36, 3)], 1),
    'S4':   ([(0, 16, 5), (0, 24, 4), (0, 32, 3)], 1),
    'S3':   ([(0, 8, 11), (0, 12, 7), (0, 20, 5), (0, 30, 3), (0, 40, 2), (1, 6, 4)], 1),
    'S2a1': ([(0, 20, 13), (0, 32, 5), (0, 44, 3), (0, 56, 7), (0, 60, 2)], 3),
    'S1':   ([(0, 16, 32), (0, 22, 5), (0, 28, 3), (0, 32, 7)], 12),
    'S2a2': ([(1, 2, 16), (1, 8, 8), (1, 14, 4), (1, 20, 4), (1, 26, 4), (1, 32, 2)], 18),
}
def nparts(gs):
    n = 1
    for g in gs:
        n *= g[2]
    return n
def digits(gs, tp):
    out = []
    for (gi, gr, n) in gs:
        out.append((gi, gr, n, tp % n)); tp //= n
    return out
