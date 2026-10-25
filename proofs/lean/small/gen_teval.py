"""gen_teval.py: writes the evaluation files of the tight case, K6/TE/T<T>P<p0>Q<p1>.lean, one part each, and
K6/TightAll.lean, which collects them into one statement per number of trails T.

Parts (T: g0 n0 n1): T = 1: 6 8 1;  T = 2: 4 4 8;  T = 3: 30 1 32.  The part sizes were chosen with a copy of the
search in Python; nothing depends on them but the time of the parts."""
import os
import sys

# the directory to write into (K6/ below it): the first argument, or the directory of this script
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
PARTS = {1: (6, 8, 1), 2: (4, 4, 8), 3: (30, 1, 32)}
FUEL = 40


def main():
    d = os.path.join(OUT, "K6", "TE")
    os.makedirs(d, exist_ok=True)
    mods = []
    for T, (g0, n0, n1) in PARTS.items():
        for p0 in range(n0):
            for p1 in range(n1):
                name = f"T{T}P{p0}Q{p1}"
                mods.append(name)
                with open(os.path.join(d, name + ".lean"), "w", newline="\n", encoding="utf-8") as f:
                    f.write(f"""import K6.TightRules

/-! Evaluation by the kernel: the tight case with {T} trails, part ({p0}, {p1}) of {n0} x {n1}. -/

namespace K6

theorem te_{name} : part (famRules {T} {g0} {n0} {p0} {n1} {p1}) {FUEL} = false := by decide +kernel

end K6
""")
    L = ["import Mathlib.Tactic.IntervalCases", "\n".join(f"import K6.TE.{m}" for m in mods), "", "/-!",
         "# All parts of the search of the tight case",
         "", "`tightAll T`: for `T = 1, 2, 3` trails, every part of the search answers `false`.", "-/", "",
         "namespace K6", "",
         "/-- The parts of the search with `T` trails: `(g0, n0, n1)`. -/",
         "def tparts : Nat → Nat × Nat × Nat",
         "  | 1 => (6, 8, 1)", "  | 2 => (4, 4, 8)", "  | _ => (30, 1, 32)", ""]
    for T, (g0, n0, n1) in PARTS.items():
        L.append(f"theorem tightAll{T} : ∀ p0, p0 < {n0} → ∀ p1, p1 < {n1} →")
        L.append(f"    part (famRules {T} {g0} {n0} p0 {n1} p1) {FUEL} = false := by")
        L.append("  intro p0 h0 p1 h1")
        L.append("  interval_cases p0 <;> interval_cases p1")
        for p0 in range(n0):
            for p1 in range(n1):
                L.append(f"  · exact te_T{T}P{p0}Q{p1}")
        L.append("")
    L.append("end K6")
    with open(os.path.join(OUT, "K6", "TightAll.lean"), "w", newline="\n", encoding="utf-8") as f:
        f.write("\n".join(L) + "\n")
    print(len(mods), "parts")


if __name__ == "__main__":
    main()
