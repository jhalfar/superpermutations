"""drand_keys.py BEACON_RANDOMNESS_HEX PLAN_SHA256_HEX - the four hash keys r_1..r_4 of the n = 18 card check.

For k = 1..4 and j = 0, 1, 2, ...: x = SHA-256(beacon || plan || k || j), where beacon is the 32 bytes of the drand
round's "randomness", plan the 32 bytes of the plan's SHA-256, and k and j one byte each. r = (x read as a big-endian
integer, mod 2^64) & (2^61 - 1); the first j with 2 <= r <= p - 2 (p = 2^61 - 1) gives r_k. Prints MHR=r1,r2,r3,r4.
"""
import hashlib
import sys

P = (1 << 61) - 1


def keys(beacon, plan):
    out = []
    for k in range(1, 5):
        for j in range(256):
            x = hashlib.sha256(beacon + plan + bytes([k, j])).digest()
            r = (int.from_bytes(x, "big") % (1 << 64)) & P
            if 2 <= r <= P - 2:
                out.append(r)
                break
        else:
            raise SystemExit("no key for k = %d" % k)
    return out


if __name__ == "__main__":
    b, p = bytes.fromhex(sys.argv[1]), bytes.fromhex(sys.argv[2])
    if len(b) != 32 or len(p) != 32:
        raise SystemExit("both arguments must be 32 bytes in hex")
    print("MHR=" + ",".join(str(r) for r in keys(b, p)))
