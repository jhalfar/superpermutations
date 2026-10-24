"""Write the final Lean file of one Theorem C certificate (in the form of the public SCertW, SCertificates and
SFinal files, which s_certs.py and s_final.py generate for the certificates of the public lists).

    make_final.py K CN BN Q HEADFILE OUTFILE

HEADFILE is the head file s_plan2.py wrote; its comment names the search `S.search K A q2 C1 C2 BN fuel`, whose
parameters are copied. The value of boundC is computed here and checked again by `decide` in Lean.
"""
import math
import re
import sys


def bound_c(k, cn, bn, q):
    hpv = math.factorial(k) + math.factorial(k - 1) + math.factorial(k - 2) + k - 3
    pi = q * (k * k - 4 * k + 1) - cn * (k - 1)
    return hpv + (2 * q * math.factorial(k - 2) - (2 * q * (k - 2) + bn) + pi - 1) // pi


def main():
    k, cn, bn, q = (int(x) for x in sys.argv[1:5])
    head, out = sys.argv[5], sys.argv[6]
    name = f"C{k}_{cn}_{bn}_{q}"
    tag = f"{k}_{cn}_{bn}_{q}"
    with open(head, encoding="utf-8") as f:
        text = f.read()
    m = re.search(r"S\.search (\d+) (\d+) (\d+) (\d+) (\d+) (\d+) (\d+) = false", text)
    if not m or int(m.group(1)) != k or int(m.group(6)) != bn:
        sys.exit(f"no `S.search {k} A q2 C1 C2 {bn} fuel = false` in {head}")
    a, q2, c1, c2, fuel = (m.group(i) for i in (2, 3, 4, 5, 7))
    b = bound_c(k, cn, bn, q)
    lean = f"""/-
Written by make_final.py for the certificate {name} (s_plan2.py of proofs/lean/lower).
-/
import LowerBounds.SSound
import LowerBounds.SRun
import LowerBounds.SModel
import LowerBounds.SBridgeTheoremC
import LowerBounds.SGen.{name}

-- bound {b:,} for k = {k} (c = {cn}/{q}, b = {bn}/{q})

namespace SuperpermLowerBounds

open Hunter PreimageChain SuperpermutationBounds

theorem wstatement_{tag} : S.WStatement {k} {cn} {bn} {q} :=
  S.wstatement_of_search (A := {a}) (q2 := {q2}) (C1 := {c1}) (C2 := {c2}) (fuel := {fuel})
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    S.runSearch_{k} SGen.search_{name}

theorem modelStatement_{tag} : ModelStatement {k} {cn} {bn} {q} :=
  modelStatement_of_wstatement wstatement_{tag}

theorem conditionsC_{tag} : ConditionsC {k} {cn} {bn} {q} := ⟨by decide, by decide, by decide, by decide⟩

theorem boundC_{tag} : boundC {k} {cn} {bn} {q} = {b} := by decide

/-- Every word over {k} symbols that contains every permutation of the symbols as a factor has at
least {b:,} letters. -/
theorem covers_length_ge_{b} : ∀ w : List (Fin {k}), Covers w → {b} ≤ w.length :=
  boundC_{tag} ▸ covers_length_ge_boundC_of_model (by decide) conditionsC_{tag} modelStatement_{tag}

/-- The shortest superpermutation on {k} symbols has at least {b:,} letters. -/
theorem ssuper_ge_{b} : {b} ≤ Ssuper {k} :=
  boundC_{tag} ▸ superperm_boundC_of_model (by decide) conditionsC_{tag} modelStatement_{tag}

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_length_ge_{b}
#print axioms SuperpermLowerBounds.ssuper_ge_{b}
"""
    with open(out, "w", encoding="utf-8", newline="\n") as f:
        f.write(lean)
    print(f"{out}: bound {b:,}")


if __name__ == "__main__":
    main()
