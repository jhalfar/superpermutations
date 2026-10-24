"""Narrow the imports of the generated parts: each part (and the head file) imports only the data files (D..) that
define the names it uses, instead of Defs (which imports all of them: 9.9 GB of .olean for 14 843 63334 16000,
more than one Lean process should hold).

    fix_imports.py SGEN_DIR NAME

The data files are not trusted (the kernel checks every lemma of the parts), so the change of imports changes nothing
about what is proved; a missing import makes Lean fail, it cannot make a false statement pass. The original import
lines are kept in SGEN_DIR/imports_original.txt; the script refuses to run twice.
"""
import os
import re
import sys


def main():
    sgen, name = sys.argv[1], sys.argv[2]
    d = os.path.join(sgen, "LowerBounds", "SGen")
    mark = os.path.join(sgen, "imports_original.txt")
    if os.path.exists(mark):
        sys.exit("imports already narrowed")
    defre = re.compile(r"^(?:noncomputable )?def (\S+)")
    where = {}
    dfiles = sorted(f[:-5] for f in os.listdir(d) if re.fullmatch(re.escape(name) + r"D\d+\.lean", f))
    for mod in dfiles:
        with open(os.path.join(d, mod + ".lean"), encoding="utf-8") as f:
            for line in f:
                m = defre.match(line)
                if m:
                    where[m.group(1)] = mod
    print(f"{len(dfiles)} data files, {len(where)} definitions")
    users = sorted(f[:-5] for f in os.listdir(d) if re.fullmatch(re.escape(name) + r"(P\d+)?\.lean", f))
    tok = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
    defs_import = f"import LowerBounds.SGen.{name}Defs"
    log = []
    total = 0
    for mod in users:
        path = os.path.join(d, mod + ".lean")
        with open(path, encoding="utf-8") as f:
            text = f.read()
        need = sorted({where[t] for t in tok.findall(text) if t in where})
        lines = text.split("\n")
        old = [l for l in lines if l.startswith("import ")]
        if defs_import not in lines and not need:
            continue
        new_imports = [f"import LowerBounds.SGen.{m}" for m in need]
        out, placed = [], False
        for l in lines:
            if l == defs_import:
                if not placed:
                    out.extend(new_imports); placed = True
                continue
            out.append(l)
        if not placed:   # the head file: add the data imports after its last import
            last = max(i for i, l in enumerate(out) if l.startswith("import "))
            existing = set(out)
            out[last + 1:last + 1] = [l for l in new_imports if l not in existing]
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            f.write("\n".join(out))
        log.append(f"{mod}\t{' '.join(o[7:] for o in old)}")
        total += len(need)
    with open(mark, "w", encoding="utf-8") as f:
        f.write("\n".join(log) + "\n")
    print(f"{len(log)} files changed, {total} data imports in all ({total / max(1, len(log)):.1f} per file)")


if __name__ == "__main__":
    main()
