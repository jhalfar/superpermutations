"""Test both derepeat tools on two small superpermutations."""

import argparse
from collections import Counter
from itertools import permutations
import json
from pathlib import Path
import subprocess
import tempfile


FIXTURES = Path(__file__).resolve().with_name("fixtures")


def run(program, *args):
    result = subprocess.run([program, *map(str, args)], check=True, capture_output=True, text=True)
    return result.stdout


def counts(word, width):
    return Counter(word[i:i + width] for i in range(len(word) - width + 1))


def check(before, after, expected):
    assert after == expected and len(before) == len(after)
    assert counts(before, 1) == counts(after, 1)
    assert counts(before, 2) == counts(after, 2)
    windows = counts(after, 3)
    assert all(windows[bytes(p)] == 1 for p in permutations(b"012"))


def replay(word, plan):
    header, *rows = plan.read_text(encoding="ascii").splitlines()
    assert header == f"SPLICE {len(word)} {len(word)}"
    ranges = []
    for row in rows:
        kind, offset, length = row.split()
        assert kind == "C"
        start, size = int(offset), int(length)
        assert 0 <= start < start + size <= len(word)
        ranges.append((start, size))
    next_start = 0
    for start, size in sorted(ranges):
        assert start == next_start
        next_start += size
    assert next_start == len(word)
    return b"".join(word[start:start + size] for start, size in ranges)


def reject(program, tsv, repeats, output):
    result = subprocess.run([program, tsv, "12", str(repeats), "012", output], capture_output=True)
    assert result.returncode != 0
    assert not output.exists() and not output.with_suffix(".json").exists()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("derepeat", type=Path)
    parser.add_argument("plan_residual", type=Path)
    args = parser.parse_args()
    derepeat, planner = args.derepeat.resolve(), args.plan_residual.resolve()
    with tempfile.TemporaryDirectory(prefix="derepeat-") as directory:
        work = Path(directory)
        adjacent = FIXTURES / "adjacent.txt"
        output = work / "adjacent.out"
        report = json.loads(run(derepeat, 3, "012", adjacent, output, "--threads", 1))
        assert report["moves"] == 1 and report["extra_copies"] == 0
        check(adjacent.read_bytes().rstrip(b"\r\n"), output.read_bytes(), b"0121021201")

        tsv = FIXTURES / "distant.contexts.tsv"
        word = (FIXTURES / "distant.txt").read_bytes().rstrip(b"\r\n")
        plan = work / "distant.ops"
        assert run(planner, tsv, 12, 1, "012", plan).strip() == "moves=1 copy_pieces=5 repeats_left=0"
        receipt = json.loads(plan.with_suffix(".json").read_text(encoding="ascii"))
        assert len(receipt["moves"]) == 1 and not receipt["remaining"]
        check(word, replay(word, plan), b"012102120101")

        reject(planner, tsv, 2, work / "wrong-count.ops")
        reject(planner, tsv, 1, work / "receipt.JSON")
    print("PASS adjacent and distant derepeat, replay, wrong count and reserved suffix")


if __name__ == "__main__":
    main()
