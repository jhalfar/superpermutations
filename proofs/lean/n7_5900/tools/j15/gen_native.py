# Generates the evaluation modules of part C of 5,900 (LowerBounds/J15*Native.lean), J15FinalNative.lean, the order
# file scratchJ15/native_order.txt and the check file scratchJ15/J15FinalCheck.lean (the assembly of the ranges
# with the equations assumed).  Do not run it while evaluations run.
#   .venv/Scripts/python.exe scratchJ15/gen_native.py
# One entry of EVALS: (field, module, pieces, V, W, B, fuel, gates, modules, kept, tried, text).
# pieces: list of (c, lo, hi): c = 0 a ring with lo..hi holes, c = s + 1 a sequence with at most s links.
# gates: list of (piece, rows, classes).  A prefix with `rows` rows of `piece` is continued only in the parts whose
# digit at this gate is (last entry + 8192 holes) mod classes; the number of parts is the product of the classes,
# and the digits of a part are its digits in the mixed radix of the classes (first gate = lowest digit), so a range
# of consecutive parts takes a slice of every class of the first gates.
# The order of EVALS is the order in which the modules are started (scratchJ15/native_order.txt).
import os
here = os.path.dirname(os.path.abspath(__file__))
out = os.environ.get('OUT', os.path.join(here, '..', '..', 'LowerBounds'))

_g = {}
exec(open(os.path.join(here, 'gates.py'), encoding='utf-8').read(), _g)
G = _g['GATES']

EVALS = [
    ('s5',   'J15S5', [(1, 0, 0), (1, 0, 0), (0, 0, 70)], 62, 70, 2, 400, G['S5'][0], G['S5'][1],
     '43,171,554', '218,221,531', 'S5 = J(S0 S0 R; 62, 70; 2)'),
    ('s4',   'J15S4', [(2, 0, 0), (2, 0, 0), (0, 0, 71)], 61, 71, 1, 400, G['S4'][0], G['S4'][1],
     '1,002,039,640', '5,072,908,057', 'S4 = J(S1 S1 R; 61, 71; 1)'),
    ('s3',   'J15S3',  [(3, 0, 0), (0, 0, 76), (0, 0, 76)], 57, 76, 2, 400, G['S3'][0], G['S3'][1],
     '86,628,445,019', '438,813,979,430', 'S3 = J(S2 R R; 57, 76; 2)'),
    ('s2a1', 'J15S2A1', [(0, 16, 83), (6, 0, 0)], 51, 83, 1, 400, G['S2a1'][0], G['S2a1'][1],
     '379,470,653,297', '1,906,338,561,159', 'S2a1 = J(R S5; 51, 83; 1), rings with at least 16 holes'),
    ('s1',   'J15S1',  [(5, 0, 0), (5, 0, 0)], 55, 78, 1, 400, G['S1'][0], G['S1'][1],
     '2,104,901,227,440', '10,736,238,262,512', 'S1 = J(S4 S4; 55, 78; 1)'),
    ('s2a2', 'J15S2A2', [(0, 8, 15), (6, 0, 0)], 51, 83, 1, 400, G['S2a2'][0], G['S2a2'][1],
     '3,220,712,840,648', '16,152,522,797,959', 'S2a2 = J(R S5; 51, 83; 1), rings with 8 to 15 holes'),
]

HEAD = '''import LowerBounds.J15Search
import LowerBounds.KTables

/-!
# %s, evaluated as compiled code

**Trusted here.**  Every theorem of this file is proved by `native_decide`: Lean does not check
the computation in its kernel but runs it as compiled code and records the result as an axiom
(`SuperpermLowerBounds.J15.<name>._native.native_decide.ax_1_1`, listed by `#print axioms`).  So
this file trusts, in addition to the kernel: the Lean compiler (from `PSearch.lean`,
`KSearch.lean` and `J15Search.lean` to C), the C compiler of the Lean toolchain (`leanc`, clang),
the Lean runtime (natural numbers, integers, arrays, byte arrays, tasks), and that the library
loaded with `--load-dynlib` (the library `J15Search` that `build.sh` makes) was
compiled from these three files as they are.  The search and the proof that its answer `false`
means what is claimed (`J15Sound.lean`, `J15Rules.lean`, `J15Final.lean`) are checked by the
kernel and do not depend on this file.

%s

A piece is `(c, lo, hi)`: `c = 0` a ring with `lo` to `hi` holes, `c = s + 1` a sequence with at
most `s` links of weight 4.  The arguments after the pieces are `V W B`, the fuel, the gates
`(piece, rows, classes)` and the range of parts (the number of parts is the product of the
numbers of classes).

This file imports `J15Search.lean` and the tables `KTables.lean` only.  No file of level 1
imports it.
-/

namespace SuperpermLowerBounds
namespace J15

open T5900

'''

def lst(ps):
    return '[' + ', '.join('(%d, %d, %d)' % p for p in ps) + ']'

def nparts(gs):
    n = 1
    for g in gs:
        n *= g[2]
    return n

def call(e, pa, pb):
    field, mod, ps, V, W, B, fuel, gs, nmod, kept, tried, text = e
    return 'jSearch 7 Ttab TRtab %s %d %d %d %d %s %d %d' % (lst(ps), V, W, B, fuel, lst(gs), pa, pb)

def bounds(nt, ranges):
    return [nt * i // ranges for i in range(ranges)] + [nt]

mods = {}
order = []
for e in EVALS:
    field, mod, ps, V, W, B, fuel, gs, nmod, kept, tried, text = e
    nt = nparts(gs)
    bs = bounds(nt, nmod)
    width = len(str(nmod - 1)) if nmod > 1 else 1
    for i in range(nmod):
        name = mod if nmod == 1 else '%s_%0*d' % (mod, max(2, width), i)
        thm = field if nmod == 1 else '%s_%d' % (field, i)
        mods.setdefault(name, []).append((thm, e, bs[i], bs[i + 1]))
        if name not in order:
            order.append(name)

for name in order:
    items = mods[name]
    title = 'Statements of part C of 5,900' if len(items) > 1 else 'A statement of part C of 5,900'
    what = ('What is evaluated (the reference runs of the first and the second program found no object, with\n'
            'the numbers of kept prefixes and of start vertices tried given):\n\n')
    for thm, e, pa, pb in items:
        nt = nparts(e[7])
        rng = '' if e[8] == 1 else ', parts %d to %d of %d' % (pa, pb - 1, nt)
        what += '* `%s`: %s%s (%s kept, %s tried in all)\n' % (thm, e[11], rng, e[9], e[10])
    body = HEAD % (title, what.rstrip())
    for thm, e, pa, pb in items:
        body += 'theorem %s :\n    %s = false := by\n  native_decide\n\n' % (thm, call(e, pa, pb))
    body += 'end J15\nend SuperpermLowerBounds\n\n'
    for thm, e, pa, pb in items:
        body += '#print axioms SuperpermLowerBounds.J15.%s\n' % thm
    open(os.path.join(out, name + 'Native.lean'), 'w', encoding='utf-8', newline='\n').write(body)

open(os.path.join(os.environ.get('OUT', here), 'native_order.txt'), 'w', newline='\n').write('\n'.join(n + 'Native' for n in order) + '\n')

# J15FinalNative.lean
fin = '''import LowerBounds.J15Final
''' + ''.join('import LowerBounds.%sNative\n' % n for n in order) + '''
/-!
# The six evaluated statements of part C, with the searches evaluated as compiled code

**Trusted here.**  The theorems of this file depend on the equations of the files
`J15*Native.lean`, each proved by `native_decide`: one axiom per equation, listed by
`#print axioms` below.  Everything else is checked by the kernel.  No file of level 1 imports
this file.  The names of the theorems end in `_native`.
-/

namespace SuperpermLowerBounds
namespace J15

open T5900

'''
for e in EVALS:
    field, mod, ps, V, W, B, fuel, gs, nmod, kept, tried, text = e
    nt = nparts(gs)
    bs = bounds(nt, nmod)
    fin += '/-- %s. -/\ntheorem %s_native : Ev %s %d %d %d :=\n' % (text, field, lst(ps), V, W, B)
    fin += '  ⟨%d, %s, by decide, fun tp htp => by\n    have htp\' : tp < %d := htp\n' % (fuel, lst(gs), nt)
    if nmod == 1:
        fin += '    exact ⟨0, %d, Nat.zero_le _, htp\', %s⟩⟩\n\n' % (nt, field)
    else:
        for i in range(nmod - 1):
            fin += '    by_cases h%d : tp < %d\n    · exact ⟨%d, %d, by omega, h%d, %s_%d⟩\n' % (i, bs[i + 1], bs[i], bs[i + 1], i, field, i)
        fin += '    exact ⟨%d, %d, by omega, htp\', %s_%d⟩⟩\n\n' % (bs[nmod - 1], bs[nmod], field, nmod - 1)
fin += '''/-- The six evaluated statements. -/
theorem evals_native : Evals :=
  ⟨s1_native, s2a1_native, s2a2_native, s3_native, s4_native, s5_native⟩

end J15
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.J15.evals_native
'''
open(os.path.join(out, 'J15FinalNative.lean'), 'w', encoding='utf-8', newline='\n').write(fin)
# scratchJ15/J15FinalCheck.lean: J15FinalNative with the equations assumed (sorry), to check the assembly of the
# ranges without evaluating anything:  ./j15_run.sh -c J15FinalCheck scratchJ15/J15FinalCheck.lean J15FinalCheck
chk = 'import LowerBounds.J15Final\n\nnamespace SuperpermLowerBounds\nnamespace J15\nopen T5900\n'
for name in order:
    for thm, e, pa, pb in mods[name]:
        chk += 'theorem %s :\n    %s = false := sorry\n' % (thm, call(e, pa, pb))
chk += 'end J15\nend SuperpermLowerBounds\n\n' + fin[fin.index('/-!'):]
open(os.path.join(os.environ.get('OUT', here), 'J15FinalCheck.lean'), 'w', encoding='utf-8', newline='\n').write(chk)
print('modules:', len(order), ' '.join(order))
for e in EVALS:
    print(e[0], 'parts', nparts(e[7]), 'modules', e[8])
