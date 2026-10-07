import LowerBounds.PSearch

/-!
# A small search on 6 symbols evaluated by the kernel

Chains on 6 symbols with no hole have at most 4 rows: the search with arithmetic tables
(`seqSearchA`), 4 kept prefixes, evaluated by `decide +kernel`.  The table of marks has
`6 ^ 5 = 7776` bytes and the list of words 720 codes.
-/

namespace SuperpermLowerBounds
namespace PS
namespace Small

/-- Chains on 6 symbols with no hole (4 kept prefixes). -/
theorem chain6 : seqSearchA 6 [[4]] 0 0 0 30 0 1 0 1 = false := by decide +kernel

end Small
end PS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.PS.Small.chain6
