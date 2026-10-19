"""gen_bounds.py - write GenericBounds / Main / Corollaries from the files of step (B) by text substitution.

    gen_bounds.py C      two block levels: 43586371/86486400 for n >= 19 (module Nested2)
    gen_bounds.py D      three block levels: 21751799/43243200 for n >= 22 (module Nested3)

step (B)'s GenericBoundsB.lean, MainB.lean and CorollariesB.lean (16 symbols on, 305989/604800) are pure
arithmetic around `Cert.word_ledgerB`; with the base moved by S = 3 (or 6) symbols and the constants replaced they
are the arithmetic around `word_ledgerC` (`word_ledgerD`) of Nested2.lean (Nested3.lean).  The substitutions are
listed below; the output is compiled by Lean like every other file, so a wrong substitution cannot go unnoticed.
"""
import os, re, sys
from fractions import Fraction as Fr

here = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(here, '..', 'constant305989', 'SuperpermutationUpperBound305989')
OUT = os.path.join(here, 'SuperpermutationUpperBound43586371')
if '--out' in sys.argv:
    i = sys.argv.index('--out'); OUT = sys.argv[i + 1]; del sys.argv[i:i + 2]
NS0, NS = 'SuperpermutationUpperBound305989', 'SuperpermutationUpperBound43586371'

CONF = {
    'C': dict(S=3, nested='Nested2', ledger='word_ledgerC', q=Fr(41281, 83160), c=Fr(654131, 86486400),
              words=[(17, 10, 128413786203964800, 'nineteen'), (18, 10, 2561130027702731520, 'twenty')]),
    'E': dict(S=3, nested='Nested2b', ledger='word_ledgerE', q=Fr(413173, 831600), c=Fr(121207, 17297280),
              bname='_3961457', heartbeats=20000000,
              words=[(17, 10, 128413777883852160, 'nineteen'), (18, 10, 2561129892078508800, 'twenty')]),
    'F': dict(S=3, nested='Nested2c', ledger='word_ledgerF', q=Fr(41281, 83160), c=Fr(124711, 17297280),
              bname='_8711159', heartbeats=20000000,
              words=[(17, 10, 128413775108545920, 'nineteen'), (18, 10, 2561129842779083520, 'twenty')]),
    'G': dict(S=6, nested='Nested3b', ledger='word_ledgerG', q=Fr(22921, 46200), c=Fr(56491, 8648640),
              bname='_21736511', heartbeats=20000000,
              words=[(20, 10, 1177586065108048296960, 'twentytwo'), (21, 10, 27028337991051598387200, 'twentythree')]),
    # no seed (opt/const_limit)
    'H': dict(S=6, nested='NestedN1', ledger='word_ledgerH', q=Fr(2239, 6930), c=Fr(32759, 288288),
              bname='_629507', heartbeats=20000000,
              words=[(20, 9, 1177582944431453414400, 'twentytwo'), (21, 9, 27028271385160615987200, 'twentythree')]),
    'I': dict(S=3, nested='NestedN2', ledger='word_ledgerI', q=Fr(465, 1232), c=Fr(6113, 96096),
              bname='_3853', heartbeats=20000000,
              words=[(17, 9, 128412985922988480, 'nineteen'), (18, 9, 2561115976208213760, 'twenty')]),
    'J': dict(S=6, nested='NestedN3', ledger='word_ledgerJ', q=Fr(51923, 166320), c=Fr(1769507, 19768320),
              bname='_11117297', heartbeats=20000000,
              words=[(20, 9, 1177577603255664374400, 'twentytwo'), (21, 9, 27028165642650064065600, 'twentythree')]),
    'D': dict(S=6, nested='Nested3', ledger='word_ledgerD', q=Fr(22921, 46200), c=Fr(297743, 43243200),
              words=[(20, 10, 1177586126221615488000, 'twentytwo'), (21, 10, 27028339195215218595840, 'twentythree')]),
}
Q0, C0 = Fr(11771, 23760), Fr(23333, 2217600)


def subst(text, X, cf):
    S = cf['S']
    q, c = cf['q'], cf['c']
    coef = q + c
    text = text.replace(NS0, NS)    # first: the old namespace contains the old numerator
    # constants (word boundaries; the source constants are distinct)
    for a, b in ((Q0.numerator, q.numerator), (Q0.denominator, q.denominator),
                 (C0.numerator, c.numerator), (C0.denominator, c.denominator),
                 ((Q0 + C0).numerator, coef.numerator), ((Q0 + C0).denominator, coef.denominator)):
        text = re.sub(r'(?<![0-9])%d(?![0-9])' % a, '@%d@' % b, text)
    text = re.sub(r'@(\d+)@', r'\1', text)
    # indices
    text = re.sub(r'k \+ (1[2-6])\b', lambda m: 'k + %d' % (int(m.group(1)) + S), text)
    text = text.replace('((k : ℚ) + 13)', '((k : ℚ) + %d)' % (13 + S))
    text = text.replace('14 ≤ m', '%d ≤ m' % (14 + S)).replace('hm : 14 ≤', 'hm : %d ≤' % (14 + S))
    text = text.replace('hm14 : 14 ≤ K - 2', 'hm14 : %d ≤ K - 2' % (14 + S))
    text = text.replace('16 ≤ N', '%d ≤ N' % (16 + S)).replace('⟨16 + 8 * r + M', '⟨%d + 8 * r + M' % (16 + S))
    text = text.replace('Nat.add_comm 14 k', 'Nat.add_comm %d k' % (14 + S))
    text = text.replace(NS0, NS)
    return text


def gen(X):
    cf = CONF[X]
    S = cf['S']
    coef = cf['q'] + cf['c']
    n0 = 16 + S
    cs = '%d/%d' % (coef.numerator, coef.denominator)
    # ---- GenericBounds
    t = open(os.path.join(SRC, 'GenericBoundsB.lean'), encoding='utf-8').read()
    t = t.replace('import SuperpermutationUpperBound305989.AllSizesB', 'import %s.%s' % (NS0, cf['nested']))
    t = t.replace('BoundsB', 'Bounds' + X)
    t = t.replace('''The arithmetic of `SuperpermutationUpperBound43/GenericBounds.lean` with the constants of the
selection of `Fifteen.lean` (step (A) with a (10,3) block above every loop without a row)''',
                  '''The arithmetic of step (B) `GenericBoundsB.lean` (generated by `gen_bounds.py %s`) with the constants of
the nested construction of `%s.lean`''' % (X, cf['nested']))
    t = t.replace('starting at 16 symbols', 'starting at %d symbols' % n0)
    t = t.replace('/-- The integer ledger of `Cert.word_ledgerB`. -/', '/-- The integer ledger of `%s`. -/' % cf['ledger'])
    t = t.replace('theorem finite_of_cert (C : Cert) (K : BlockCert) : FiniteStatement := by',
                  'theorem finite_of_cert : FiniteStatement := by')
    t = t.replace('C.word_ledgerB K k a ha hak', '%s k a ha hak' % cf['ledger'])
    t = t.replace('theorem asymptotic_of_cert (C : Cert) (K : BlockCert) : AsymptoticStatement :=\n  asymptotic_of_finite (finite_of_cert C K)',
                  'theorem asymptotic_of_cert : AsymptoticStatement :=\n  asymptotic_of_finite finite_of_cert')
    t = subst(t, X, cf)
    # omega needs minutes (C) or times out (D) on the principal numerator; a two-line calc instead
    D_, qd = coef.denominator, cf['q'].denominator
    hS = 13 + S
    src = '  have he := circle_count_scaled k c hc\n  omega\n'
    assert t.count(src) == 1
    cd = cf['c'].denominator
    if not (D_ % qd == 0 and cd == D_):
        # general form: multiply by qd * cd, then cancel
        L_ = qd * cd
        t = t.replace(src, '''  have he := circle_count_scaled k c hc
  apply Nat.eq_of_mul_eq_mul_left (show 0 < %d by norm_num)
  calc %d * (%d * (q + (k + %d) * c)) = %d * (%d * q) + %d * (%d * ((k + %d) * c)) := by ring
    _ = %d * (%d * (k + %d).factorial) + %d * (%d * (k + %d).factorial) := by rw [hq, he]
    _ = %d * (%d * (k + %d).factorial) := by ring
''' % (L_, L_, D_, hS, cd * D_, qd, qd * D_, cd, hS, cd * D_, cf['q'].numerator, hS, qd * D_, cf['c'].numerator, hS,
       L_, coef.numerator, hS))
    r = D_ // qd
    t = t.replace(src, '''  have he := circle_count_scaled k c hc
  calc %d * (q + (k + %d) * c) = %d * (%d * q) + %d * ((k + %d) * c) := by ring
    _ = %d * (%d * (k + %d).factorial) + %d * (k + %d).factorial := by rw [hq, he]
    _ = %d * (k + %d).factorial := by ring
''' % (D_, hS, r, qd, D_, hS, r, cf['q'].numerator, hS, cf['c'].numerator, hS, coef.numerator, hS))
    if 'heartbeats' in cf:   # E: ledger_eq_bound needs more than 2,000,000 with these constants
        t = t.replace('set_option maxHeartbeats 2000000\n', 'set_option maxHeartbeats %d\n' % cf['heartbeats'])
    assert 'BlockCert' not in t and 'word_ledgerB' not in t
    open(os.path.join(OUT, 'GenericBounds%s.lean' % X), 'w', encoding='utf-8', newline='\n').write(t)
    # ---- Main
    t = open(os.path.join(SRC, 'MainB.lean'), encoding='utf-8').read()
    t = t.replace('import SuperpermutationUpperBound305989.GenericBoundsB\nimport SuperpermutationUpperBound305989.Certificate.Cert\nimport SuperpermutationUpperBound305989.Certificate.BlockCert\n',
                  'import SuperpermutationUpperBound305989.GenericBounds%s\n' % X)
    i0 = t.index('/-!'); i1 = t.index('-/', i0) + 2
    t = t[:i0] + '''/-!
# The bounds for every size from %d symbols on, and the coefficient %s

The statements are in the vocabulary of `Challenge.lean` (`SuperpermutationBounds.Covers`,
`SuperpermutationBounds.F3`) and have the shape of `finite_bound` and `eventual_bound` of
`Solution.lean` (and of step (B)'s `finite_bound16`), with `%s = %s + %s` and
`%s` in place of `43/80`, `17/240`.  They start at %d symbols (`m ≥ %d`): the construction is the
selection of step (A) (`Certificate.cert`) with nested blocks above its loops without a row
(`%s.lean`), closed and completed.  Generated by `gen_bounds.py %s` from step (B)'s `MainB.lean`.
-/''' % (n0, cs, cs, '%d/%d' % (cf['q'].numerator, cf['q'].denominator), '%d/%d' % (cf['c'].numerator, cf['c'].denominator),
         '%d/%d' % (cf['c'].numerator, cf['c'].denominator), n0, 14 + S, cf['nested'], X) + t[i1:]
    t = t.replace('BoundsB.finite_of_cert Certificate.cert Certificate.blockCert', 'Bounds%s.finite_of_cert' % X)
    t = t.replace('BoundsB.asymptotic_of_cert Certificate.cert Certificate.blockCert', 'Bounds%s.asymptotic_of_cert' % X)
    t = t.replace('BoundsB.bound', 'Bounds%s.bound' % X)
    bn = cf.get('bname', '')
    t = t.replace('finite_bound16', 'finite_bound%d%s' % (n0, bn)).replace('eventual_bound16', 'eventual_bound%d%s' % (n0, bn))
    t = t.replace('`m + 2 ≥ 16`', '`m + 2 ≥ %d`' % n0)
    t = t.replace("step (B)'s `finite_bound%d%s`" % (n0, bn), "step (B)'s `finite_bound16`")
    t = subst(t, X, cf)
    open(os.path.join(OUT, 'Main%s.lean' % X), 'w', encoding='utf-8', newline='\n').write(t)
    # ---- Corollaries
    t = open(os.path.join(SRC, 'CorollariesB.lean'), encoding='utf-8').read()
    t = t.replace('import SuperpermutationUpperBound305989.MainB', 'import SuperpermutationUpperBound305989.Main%s' % X)
    bn = cf.get('bname', '')
    t = t.replace('finite_bound16', 'finite_bound%d%s' % (n0, bn))
    tag = str(coef.numerator)
    t = t.replace('Cost305989', 'Cost' + tag).replace('Finite305989', 'Finite' + tag)
    t = t.replace('FiniteInteger305989', 'FiniteInteger' + tag).replace('finite_305989', 'finite_' + tag)
    t = t.replace('finiteInteger_305989', 'finiteInteger_' + tag)
    t = t.replace('starting at `m = 14` (16 symbols)', 'starting at `m = %d` (%d symbols)' % (14 + S, n0))
    t = t.replace('symbols.\n', 'symbols.\n', 1)
    j0 = t.index('/-- 16 symbols'); j1 = t.index('end SuperpermutationUpperBound305989')
    words = ''
    for m, a, val, nm in cf['words']:
        words += '''/-- %d symbols: `m = %d`, `a = %d`. -/
theorem hasWord_%s_%s : HasWord %d %d := by
  obtain ⟨w, hw, hl⟩ := finite_bound%d%s %d (by norm_num) %d (by norm_num) (by norm_num)
  refine ⟨w, hw, ?_⟩
  norm_num [Nat.factorial] at hl
  exact_mod_cast hl

''' % (m + 2, m, a, nm, X, m + 2, val, n0, bn, m, a)
    t = t[:j0] + words + t[j1:]
    t = t.replace('The two `HasWord` statements are `finite_bound%d%s` at the best parameter `a` for 16 and 17\nsymbols.' % (n0, bn),
                  'The two `HasWord` statements are `finite_bound%d%s` at the best parameter `a` for %d and %d\nsymbols (`ledgerC.py`).' % (n0, bn, n0, n0 + 1))
    t = re.sub(r'#print axioms SuperpermutationUpperBound305989\.hasWord_\w+\n', '', t)
    t = subst(t, X, cf)
    for m, a, val, nm in cf['words']:
        t += '#print axioms %s.hasWord_%s_%s\n' % (NS, nm, X)
    open(os.path.join(OUT, 'Corollaries%s.lean' % X), 'w', encoding='utf-8', newline='\n').write(t)


if __name__ == '__main__':
    for X in sys.argv[1:]:
        gen(X)
