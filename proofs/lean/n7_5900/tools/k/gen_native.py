# Generates the evaluation modules of part B of 5,900 (LowerBounds/K*Native.lean), KFinalNative.lean and the order
# file scratchK/native_order.txt.  Do not run it while evaluations run.
#   .venv/Scripts/python.exe scratchK/gen_native.py
# One entry of EVALS: (field, module, table, statement, fuel, ds, nt, ranges, kept prefixes of the reference run, text).
# statement = (s, lo, hi, a, b, h) for KS.seqSearch, or ('ring', G) for PS.ringSearch.
import os
here = os.path.dirname(os.path.abspath(__file__))
out = os.environ.get('OUT', os.path.join(here, '..', '..', 'LowerBounds'))

EVALS = [
    ('k8',  'KK87',   'Ttab', (8, 0, 42, 1, 0, 0),     400, 0, 1, 1,        '27,105; 32,407 on the reference table,', '8 links, all levels to 42 holes'),
    ('k7',  'KK87',   'Ttab', (7, 0, 48, 1, 0, 0),     400, 0, 1, 1,        '22,709,717; 29,066,365 on the reference table,', '7 links, all levels to 48 holes'),
    ('c59', 'KSmall', 'Ttab', (0, 59, 59, 2, 3, 5),    400, 8, 61, 1,       '321,229,855', 'chains, level 59'),
    ('c62', 'KSmall', 'Ttab', (0, 62, 75, 2, 3, 5),    400, 12, 499, 1,     '3,319,568,194', 'chains, levels 62 to 75'),
    ('ring', 'KSmall', 'Ttab', ('ring', 69),           400, 16, 1009, 1,    '3,156,668,409', 'rings to 69 holes'),
    ('k6',  'KSmall', 'Ttab', (6, 0, 54, 1, 0, 0),     400, 10, 251, 1,     'at most 4,551,813,305, the number on the reference table,', '6 links, all levels to 54 holes'),
    ('c76', 'KSmall', 'Ttab', (0, 76, 76, 2, 3, 5),    400, 12, 499, 1,     '6,065,162,755', 'chains, level 76'),
    ('k4',  'KK4',    'Dtab', (4, 48, 66, 10, 16, 25), 400, 12, 251, 1,     '45,080,993,091', '4 links, levels 48 to 66'),
    ('k5',  'KK5',    'Ttab', (5, 0, 60, 1, 0, 0),     400, 12, 1021, 1,    '159,884,470,908', '5 links, all levels to 60 holes'),
    ('k3',  'KK3',    'Dtab', (3, 55, 72, 10, 16, 30), 400, 13, 1021, 1,    '445,234,933,436', '3 links, levels 55 to 72'),
    ('k1',  'KK1',    'Dtab', (1, 62, 84, 10, 15, 30), 400, 17, 8191, 8,    '3,743,897,407,212', '1 link, levels 62 to 84'),
    ('k0',  'KK0',    'Dtab', (0, 77, 90, 2, 3, 5),    400, 18, 16381, 11,  '5,236,271,122,213', 'chains, levels 77 to 90'),
    ('k2',  'KK2',    'Dtab', (2, 61, 78, 10, 16, 25), 400, 14, 4093, 12,   '5,583,726,910,601', '2 links, levels 61 to 78'),
]

HEAD = '''import LowerBounds.KSearch
import LowerBounds.KTables

/-!
# %s, evaluated as compiled code

**Trusted here.**  Every theorem of this file is proved by `native_decide`: Lean does not check
the computation in its kernel but runs it as compiled code and records the result as an axiom
(`SuperpermLowerBounds.KS.<name>._native.native_decide.ax_1_1`, listed by `#print axioms`).  So
this file trusts, in addition to the kernel: the Lean compiler (from `PSearch.lean` and
`KSearch.lean` to C), the C compiler of the Lean toolchain (`leanc`, clang), the Lean runtime
(natural numbers, integers, arrays, byte arrays, tasks), and that the library loaded with
`--load-dynlib` (the library `KSearch` that `build.sh` makes) was compiled from these
two files as they are.  The search and the proof that its answer `false` means what is claimed
(`KSound.lean`, `KRev.lean`, `KPot.lean`, `KRules.lean`, `KFinal.lean`) are checked by the kernel
and do not depend on this file.

%s

This file imports `KSearch.lean` and the tables `KTables.lean` only.  No file of level 1 imports
it.
-/

namespace SuperpermLowerBounds
namespace KS

open T5900

'''

def call(e, pa, pb):
    field, mod, tab, st, fuel, ds, nt, ranges, kept, text = e
    if st[0] == 'ring':
        return 'PS.ringSearch 7 (%s.getD 0 []) TRtab %d %d %d %d %d %d' % (tab, st[1], fuel, ds, nt, pa, pb)
    return 'seqSearch 7 %s %d %d %d %d %d %d %d %d %d %d %d' % ((tab,) + st + (fuel, ds, nt, pa, pb))

def partial(e):
    field, mod, tab, st, fuel, ds, nt, ranges, kept, text = e
    if st[0] == 'ring':
        return 'PS.ringSearch 7 (%s.getD 0 []) TRtab %d %d %d %d' % (tab, st[1], fuel, ds, nt)
    return 'seqSearch 7 %s %d %d %d %d %d %d %d %d %d' % ((tab,) + st + (fuel, ds, nt))

def bounds(nt, ranges):
    return [nt * i // ranges for i in range(ranges)] + [nt]

mods = {}
order = []
for e in EVALS:
    field, mod, tab, st, fuel, ds, nt, ranges, kept, text = e
    bs = bounds(nt, ranges)
    for i in range(ranges):
        name = mod if ranges == 1 else '%s_%02d' % (mod, i)
        thm = field if ranges == 1 else '%s_%d' % (field, i)
        mods.setdefault(name, []).append((thm, e, bs[i], bs[i + 1]))
        if name not in order:
            order.append(name)

for name in order:
    items = mods[name]
    title = 'Statements of part B of 5,900' if len(items) > 1 else 'A statement of part B of 5,900'
    what = 'What is evaluated (the reference run of the first and the second program found no violation, with\nthe number of kept prefixes given):\n\n'
    for thm, e, pa, pb in items:
        rng = '' if e[7] == 1 else ', parts %d to %d of %d' % (pa, pb - 1, e[6])
        what += '* `%s`: %s%s (%s kept prefixes in all)\n' % (thm, e[9], rng, e[8])
    body = HEAD % (title, what.rstrip())
    for thm, e, pa, pb in items:
        body += 'theorem %s : %s = false := by\n  native_decide\n\n' % (thm, call(e, pa, pb))
    body += 'end KS\nend SuperpermLowerBounds\n\n'
    for thm, e, pa, pb in items:
        body += '#print axioms SuperpermLowerBounds.KS.%s\n' % thm
    open(os.path.join(out, name + 'Native.lean'), 'w', encoding='utf-8', newline='\n').write(body)

open(os.path.join(os.environ.get('OUT', here), 'native_order.txt'), 'w', newline='\n').write('\n'.join(n + 'Native' for n in order) + '\n')

# KFinalNative.lean
fin = '''import LowerBounds.KFinal
import LowerBounds.PFinalNative
''' + ''.join('import LowerBounds.%sNative\n' % n for n in order) + '''
/-!
# Table T' and Theorem K, with the searches evaluated as compiled code

**Trusted here.**  The theorems of this file depend on the equations of the files `K*Native.lean`
and on the equations of the proof of 5,899 (`P*Native.lean`), each proved by `native_decide`: one
axiom per equation, listed by `#print axioms` below.  Everything else is checked by the kernel.
No file of level 1 imports this file.  The names of the theorems end in `_native`.
-/

namespace SuperpermLowerBounds
namespace KS

open T5899 T5900

'''
for e in EVALS:
    field, mod, tab, st, fuel, ds, nt, ranges, kept, text = e
    bs = bounds(nt, ranges)
    kind = 'EvR (%s.getD 0 []) TRtab %d' % (tab, st[1]) if st[0] == 'ring' else 'Ev %s %d %d %d %d %d %d' % ((tab,) + st)
    fin += '/-- %s. -/\ntheorem %s_native : %s :=\n' % (text[0].upper() + text[1:], field, kind)
    if ranges == 1:
        fin += '  ⟨%d, %d, %d, by norm_num, PS.covered_one %s⟩\n\n' % (fuel, ds, nt, field)
    else:
        fin += '  ⟨%d, %d, %d, by norm_num, fun tp htp => by\n' % (fuel, ds, nt)
        for i in range(ranges - 1):
            fin += '    by_cases h%d : tp < %d\n    · exact ⟨%d, %d, by omega, h%d, %s_%d⟩\n' % (i, bs[i + 1], bs[i], bs[i + 1], i, field, i)
        fin += '    exact ⟨%d, %d, by omega, htp, %s_%d⟩⟩\n\n' % (bs[ranges - 1], bs[ranges], field, ranges - 1)
fin += '''/-- The evaluated statements behind table T'. -/
theorem evalsT_native : EvalsT :=
  ⟨c59_native, c62_native, c76_native, ring_native, k5_native, k6_native, k7_native, k8_native⟩

/-- The evaluated statements for 0 to 4 links. -/
theorem evalsK_native : EvalsK := ⟨k0_native, k1_native, k2_native, k3_native, k4_native⟩

/-- Set B on words, from the evaluated equations of the proof of 5,899. -/
theorem setB_native : SetB :=
  setB_of_search (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) f0_covered_native f1_covered_native (PS.covered_one PS.f2)
    (PS.covered_one PS.f3) (PS.covered_one PS.f4) (PS.covered_one PS.f5) (PS.covered_one PS.ring)

/-- Table T' is valid. -/
theorem tableT_native : TableT := tableT_of_search setB_native evalsT_native

/-- Theorem K. -/
theorem theoremK_native : TheoremK := theoremK_of_search setB_native evalsT_native evalsK_native

end KS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.KS.tableT_native
#print axioms SuperpermLowerBounds.KS.theoremK_native
'''
open(os.path.join(out, 'KFinalNative.lean'), 'w', encoding='utf-8', newline='\n').write(fin)
# scratchK/KFinalCheck.lean: KFinalNative with the equations assumed (sorry), to check the assembly of the ranges
# without evaluating anything:  ./k_run.sh -c KFinalCheck scratchK/KFinalCheck.lean KFinalCheck
chk = 'import LowerBounds.KFinal\nimport LowerBounds.PFinalNative\n\nnamespace SuperpermLowerBounds\nnamespace KS\nopen T5900\n'
for name in order:
    for thm, e, pa, pb in mods[name]:
        chk += 'theorem %s : %s = false := sorry\n' % (thm, call(e, pa, pb))
chk += 'end KS\nend SuperpermLowerBounds\n\n' + fin[fin.index('/-!'):]
open(os.path.join(os.environ.get('OUT', here), 'KFinalCheck.lean'), 'w', encoding='utf-8', newline='\n').write(chk)
print('modules:', len(order), ' '.join(order))
