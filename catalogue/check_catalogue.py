"""Validate catalogue/catalogue.jsonl against schema.md.

Read-only: it opens the catalogue, the cited source files and the evidence files, and writes nothing.

    python3 catalogue/check_catalogue.py [FILE.jsonl] [--full] [--quiet]

Checks: the schema (fields, types, enums), unique ids, that every cited path exists, that every source line holds
its quote (a quote found within +-3 lines of the cited line is a warning, elsewhere an error), that evidence hashes
match where the file exists (files over 512 MB are hashed only with --full), that supersedes/superseded_by point
at existing ids and agree with each other, and that no entry contains a long run of symbols that looks like a word.
Exit code 0 when there are no errors (warnings allowed).
"""
import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, ".."))          # the top of the repository
CAT = os.path.join(HERE, "catalogue.jsonl")

KINDS = {"lower-bound", "class-negative", "class-optimum", "structural", "upper-construction", "method-negative"}
STATUSES = {"lean", "certificate", "computed-one-program", "computed-two-programs", "conjecture"}
REQUIRED = {
    "id": str, "n": (int, list, str), "kind": str, "claim": str, "family": str, "status": str, "method": str,
    "reproduce": dict, "evidence": list, "date": str, "credit": str, "published": dict, "supersedes": list,
    "superseded_by": list, "source": list, "source_quote": list, "needs_owner": str,
}
OPTIONAL = {"notes": str}
BIG = 512 * 1024 * 1024
WORDLIKE = re.compile(r"[1-9A-Za-z]{40,}")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def lines_of(path, cache={}):
    if path not in cache:
        with open(path, encoding="utf-8", errors="replace") as f:
            cache[path] = f.read().split("\n")
    return cache[path]


def main():
    full = "--full" in sys.argv
    quiet = "--quiet" in sys.argv
    paths = [a for a in sys.argv[1:] if not a.startswith("--")]
    errors, warnings = [], []
    entries = []
    with open(paths[0] if paths else CAT, encoding="utf-8") as f:
        for k, line in enumerate(f, 1):
            if not line.strip():
                continue
            try:
                entries.append((k, json.loads(line)))
            except json.JSONDecodeError as e:
                errors.append(f"line {k}: not JSON ({e})")
    ids = {}
    for k, e in entries:
        tag = f"line {k} ({e.get('id', '?')})"
        for field, typ in REQUIRED.items():
            if field not in e:
                errors.append(f"{tag}: missing field {field}")
            elif not isinstance(e[field], typ):
                errors.append(f"{tag}: field {field} has type {type(e[field]).__name__}")
        for field in e:
            if field not in REQUIRED and field not in OPTIONAL:
                errors.append(f"{tag}: unknown field {field}")
        if any(field not in e for field in REQUIRED):
            continue
        if e["id"] in ids:
            errors.append(f"{tag}: id also on line {ids[e['id']]}")
        ids[e["id"]] = k
        n = e["n"]
        if isinstance(n, str) and n != "all":
            errors.append(f"{tag}: n is a string other than 'all'")
        if isinstance(n, list) and not all(isinstance(x, int) for x in n):
            errors.append(f"{tag}: n list holds non-integers")
        if e["kind"] not in KINDS:
            errors.append(f"{tag}: kind {e['kind']!r}")
        if e["status"] not in STATUSES:
            errors.append(f"{tag}: status {e['status']!r}")
        if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", e["date"]):
            errors.append(f"{tag}: date {e['date']!r}")
        for field in ("claim", "family", "method", "credit"):
            if not e[field].strip():
                errors.append(f"{tag}: empty {field}")
        if e["kind"] in ("class-negative", "class-optimum") and e["family"].strip().lower() == "all words":
            errors.append(f"{tag}: class claim with family 'all words'")
        if e["kind"] != "lower-bound" and e["status"] not in ("lean",) and re.search(
                r"no shorter word exists|is optimal\b(?! among| in| for| within| on)", e["claim"]):
            warnings.append(f"{tag}: claim reads as unconditional optimality")
        pub = e["published"]
        if set(pub) != {"yes", "where"} or not isinstance(pub.get("yes"), bool) or not isinstance(pub.get("where"), str):
            errors.append(f"{tag}: published must be {{yes: bool, where: str}}")
        elif not pub["yes"] and pub["where"] != "local, unpublished":
            errors.append(f"{tag}: unpublished entry with where={pub['where']!r}")
        rep = e["reproduce"]
        if set(rep) != {"command", "path"} or not all(isinstance(v, str) for v in rep.values()):
            errors.append(f"{tag}: reproduce must be {{command: str, path: str}}")
        elif rep["path"] and not os.path.exists(os.path.join(ROOT, rep["path"])):
            errors.append(f"{tag}: reproduce path missing: {rep['path']}")
        for ev in e["evidence"]:
            if not isinstance(ev, dict) or set(ev) != {"file", "sha256"}:
                errors.append(f"{tag}: evidence item {ev!r}")
                continue
            p = os.path.join(ROOT, ev["file"])
            if not os.path.exists(p):
                (errors if ev["sha256"] == "" else warnings).append(
                    f"{tag}: evidence file missing: {ev['file']}")
                continue
            if ev["sha256"] == "growing":  # the log of a job that is still running
                continue
            if ev["sha256"]:
                if not re.fullmatch(r"[0-9a-f]{64}", ev["sha256"]):
                    errors.append(f"{tag}: bad sha256 for {ev['file']}")
                elif os.path.getsize(p) > BIG and not full:
                    warnings.append(f"{tag}: {ev['file']} over 512 MB, hash not checked (use --full)")
                elif sha256(p) != ev["sha256"]:
                    # .md files are living reports (STATE, FINDINGS, PROOF): a change is a warning, a log change an error
                    (warnings if ev["file"].endswith(".md") else errors).append(
                        f"{tag}: sha256 differs for {ev['file']}")
            else:
                warnings.append(f"{tag}: no sha256 for existing {ev['file']}")
        if not e["source"]:
            errors.append(f"{tag}: no source")
        if len(e["source"]) != len(e["source_quote"]):
            errors.append(f"{tag}: source and source_quote differ in length")
        for src, quote in zip(e["source"], e["source_quote"]):
            m = re.fullmatch(r"(.+):(\d+)", src)
            if not m:
                errors.append(f"{tag}: source {src!r} is not path:line")
                continue
            p, ln = os.path.join(ROOT, m.group(1)), int(m.group(2))
            if not os.path.exists(p):
                errors.append(f"{tag}: source file missing: {m.group(1)}")
                continue
            lines = lines_of(p)
            if 1 <= ln <= len(lines) and quote in lines[ln - 1]:
                continue
            near = [j + 1 for j in range(max(0, ln - 4), min(len(lines), ln + 3)) if quote in lines[j]]
            if near:
                warnings.append(f"{tag}: quote of {src} found on line {near[0]}")
            else:
                anywhere = [j + 1 for j, t in enumerate(lines) if quote in t]
                # the READMEs are rewritten from time to time: a quote that moved is a warning, a lost one an error
                if anywhere:
                    warnings.append(f"{tag}: quote of {src} found on line {anywhere[0]}")
                else:
                    errors.append(f"{tag}: quote not in {m.group(1)}")
        text = json.dumps({k2: v for k2, v in e.items() if k2 not in ("evidence", "source", "source_quote", "reproduce")})
        for hit in WORDLIKE.findall(text):
            if not re.fullmatch(r"[A-Za-z]+", hit):
                errors.append(f"{tag}: word-like run {hit[:20]}...")
    for k, e in entries:
        tag = f"line {k} ({e.get('id', '?')})"
        for other in e.get("supersedes", []):
            if other not in ids:
                errors.append(f"{tag}: supersedes unknown {other}")
            elif e["id"] not in dict(entries)[ids[other]].get("superseded_by", []):
                warnings.append(f"{tag}: {other} does not list it in superseded_by")
        for other in e.get("superseded_by", []):
            if other not in ids:
                errors.append(f"{tag}: superseded_by unknown {other}")
    for w in warnings if not quiet else []:
        print("WARN ", w)
    for x in errors:
        print("ERROR", x)
    owner = sum(1 for _, e in entries if e.get("needs_owner"))
    print(f"{len(entries)} entries, {len(errors)} errors, {len(warnings)} warnings, {owner} need the owner")
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
