"""Audit of all part files of the counted computations of L(7) >= 5,901 (PROOF_5901.md 0.3, 6.3, 7.4).

Agent pub5901, 2026-10-20.  Run from anywhere:
    python -I audit/partaudit.py > audit/partaudit.txt   (in my research tree; it reads the part files there)

For every counted tag of Table C (and, marked "not counted", the ORDS runs) it checks:
  1. every part index 0..N-1 (kernel) or (i, j), 0 <= i < N, 0 <= j < N2 (joint) has a file, no file has an index
     outside that range, and N, N2 are those of params.txt / command.txt;
  2. every part file has a complete result (kernel: the counters of the first line; joint: a RESULT line);
  3. M5: the first line (statement line) is the same in all part files once the part numbers are masked; for the
     kernel tags the part count and the gate depth in it equal params.txt, and the counts above the gate are the
     same in every part;
  4. no part reports a violation (kernel: "violations 0" and no VIOLATION line; joint: "found 0" in the RESULT
     line and no FOUND line);
  5. the sums (kernel: above the gate + sum over the parts of (kept - above the gate), as ksumm.sh; joint: the sum of
     the RESULT lines, as gj2summ.sh) equal Table C;
  6. the statement line names the table, V, W, B, the kinds, the window and the switches of section 6.2; for the
     gkjs tags (K0, K1, K2), whose line carries a hash of the table as used, the hash is recomputed from
     caps/capD16_k.txt (in gkjs/ and in gpu2/k/).
The K0/K1/K2 part files are read from the packed archives K*js.tar.xz of my archive (not in this repository) without
unpacking them to disk; T1 is read from its part folder and compared file by file with its archive.
K8 and K9 were single runs without part files; their result lines (gk4 on the card, kfast2 on the CPU) are checked.
Writes nothing.  Exit status 0 iff every check passed.
"""
import os
import re
import sys
import tarfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', '..'))
D16 = os.path.join(ROOT, 'opt', 'n7', 'd16')
ARCH = os.path.join(ROOT, 'archive', 'opt', 'n7', 'd16')

problems = []


def bad(tag, msg):
    problems.append('%s: %s' % (tag, msg))
    print('  PROBLEM: ' + msg)


class DirSrc:
    def __init__(self, path):
        self.path = path
        self.names = sorted(os.listdir(path))

    def raw(self, name):
        with open(os.path.join(self.path, name), 'rb') as f:
            return f.read()

    def read(self, name):
        return self.raw(name).decode('utf-8', 'replace').replace('\r\n', '\n')

    def where(self):
        return os.path.relpath(self.path, ROOT).replace('\\', '/')


class TarSrc:
    def __init__(self, path):
        self.path = path
        self.tf = tarfile.open(path, 'r:xz')
        self.members = {os.path.basename(m.name): m for m in self.tf.getmembers() if m.isfile()}
        self.names = sorted(self.members)

    def raw(self, name):
        return self.tf.extractfile(self.members[name]).read()

    def read(self, name):
        return self.raw(name).decode('utf-8', 'replace').replace('\r\n', '\n')

    def where(self):
        return os.path.relpath(self.path, ROOT).replace('\\', '/') + ' (packed)'


# ---------------------------------------------------------------- kernel tags (gk4, gkjs)
KLINE = re.compile(r'^(?P<stm>(?:gpu )?run S=(?P<S>\d+) .*?) part (?P<i>\d+) of (?P<n>\d+) at depth (?P<dep>\d+): '
                   r'violations (?P<v>\d+)\s+rows placed (?P<pl>\d+)\s+kept (?P<k>\d+)\s+above the gate: rows placed '
                   r'(?P<apl>\d+) kept (?P<ak>\d+)')

# tag: (source, S, LO, NPARTS, DEPTH, caps, POT, JS, Table C kept)
KERNEL = [
    ('K0js', ('tar', 'gkjs/parts/K0js.tar.xz'), 0, 65, 4096, 16, 'caps/capD16_k.txt', '17,24,5', True, 497079750869693),
    ('K1js', ('tar', 'gkjs/parts/K1js.tar.xz'), 1, 55, 2048, 14, 'caps/capD16_k.txt', '20,29,60', True, 755070879353479),
    ('K2js', ('tar', 'gkjs/parts/K2js.tar.xz'), 2, 51, 512, 13, 'caps/capD16_k.txt', '20,29,60', True, 375408252302475),
    ('K3', ('dir', 'gpu2/k/parts/K3'), 3, 48, 256, 13, 'caps/capD16_k.txt', '10,15,30', False, 527651578348368),
    ('K4', ('dir', 'gpu2/k/parts/K4'), 4, 41, 64, 12, 'caps/capD16_k.txt', '10,15,25', False, 160141566085840),
    ('K5', ('dir', 'gpu2/k/parts/K5'), 5, 37, 64, 12, 'caps/capD16u_5_k.txt', '10,16,25', False, 23993915746406),
    ('K6', ('dir', 'gpu2/k/parts/K6'), 6, 37, 16, 10, 'caps/capD16u_6_k.txt', '10,16,25', False, 2569985903558),
    ('K7', ('dir', 'gpu2/k/parts/K7'), 7, 35, 1, 0, 'caps/capD16u_7_k.txt', '10,16,25', False, 320243136927),
    ('K10', ('dir', 'gpu2/k/parts/K10'), 10, 35, 1, 0, 'caps/capD16u_10_k.txt', '10,16,25', False, 172577),
]


def capsum(path, S, G):
    rows = {}
    for l in open(path, encoding='utf-8'):
        m = re.match(r'^(\d+):(.*)$', l.strip())
        if m:
            rows[int(m.group(1))] = [int(x) for x in m.group(2).split()]
    h = 2166136261
    for s in range(S + 1):
        for x in range(G + 1):
            h = ((h ^ (rows[s][x] & 0xffffffff)) * 16777619) & 0xffffffff
    return h


def kernel_tag(tag, src, S, LO, N, DEP, caps, pot, js, want):
    s = TarSrc(os.path.join(ARCH, src[1])) if src[0] == 'tar' else DirSrc(os.path.join(D16, src[1]))
    print('%s  [%s]' % (tag, s.where()))
    params = s.read('params.txt').strip() if 'params.txt' in s.names else None
    if params is None:
        bad(tag, 'no params.txt')
    else:
        print('  params: ' + params)
        pw = dict(x.split('=', 1) for x in params.split() if '=' in x)
        exp = {'S': str(S), 'LO': str(LO), 'NPARTS': str(N), 'DEPTH': str(DEP), 'CAPS': caps, 'GTOP': '96',
               'CUT': '12', 'POT': pot}
        for key, val in exp.items():
            if pw.get(key) != val:
                bad(tag, 'params.txt %s=%s, expected %s' % (key, pw.get(key), val))
        if (pw.get('JS') == '1') != js:
            bad(tag, 'params.txt JS=%s, expected %s' % (pw.get('JS'), '1' if js else 'absent'))
    pat = re.compile(r'^p(\d+)\.txt$')
    idx = {}
    for nm in s.names:
        m = pat.match(nm)
        if m:
            idx[int(m.group(1))] = nm
        elif nm not in ('params.txt', 'log.txt', 'err.txt', 'm5.txt'):
            bad(tag, 'unexpected file %s' % nm)
    missing = [i for i in range(N) if i not in idx]
    extra = [i for i in idx if i >= N]
    if missing:
        bad(tag, '%d missing parts, first %s' % (len(missing), missing[:10]))
    if extra:
        bad(tag, 'parts with index >= %d: %s' % (N, sorted(extra)[:10]))
    if 'err.txt' in s.names and s.read('err.txt').strip():
        bad(tag, 'err.txt is not empty')
    stms = {}
    above = set()
    kept = viol = 0
    for i in sorted(idx):
        txt = s.read(idx[i])
        first = txt.split('\n', 1)[0]
        m = KLINE.match(first)
        if not m:
            bad(tag, 'part %d: first line not complete: %r' % (i, first[:120]))
            continue
        if int(m.group('i')) != i or int(m.group('n')) != N or int(m.group('dep')) != DEP or int(m.group('S')) != S:
            bad(tag, 'part %d: line says part %s of %s at depth %s, S=%s' % (i, m.group('i'), m.group('n'),
                                                                          m.group('dep'), m.group('S')))
        v = int(m.group('v'))
        if v or 'VIOLATION' in txt:
            bad(tag, 'part %d reports a violation (%d)' % (i, v))
        viol += v
        line = m.group('stm') + ' of %s at depth %s' % (m.group('n'), m.group('dep'))
        stms[line] = stms.get(line, 0) + 1
        above.add((int(m.group('apl')), int(m.group('ak'))))
        kept += int(m.group('k')) - int(m.group('ak'))
        for need in ('S=%d ' % S, 'LO=%d ' % LO, 'CUT=12 ', 'POT=%s' % pot, 'GTOP=96 '):
            if need not in line:
                bad(tag, 'part %d: statement line lacks %r' % (i, need))
                break
        if js != ('JS=1' in line):
            bad(tag, 'part %d: JS switch in the statement line is not as expected' % i)
    akept = sorted(set(a[1] for a in above))
    if len(akept) == 1:
        kept += akept[0]
    else:
        bad(tag, 'the kept counts above the gate differ between parts: %s' % akept[:4])
    if len(above) > 1:
        print('  note: "rows placed" above the gate takes the values %s in different parts (not a count of Table C)'
              % sorted(set(a[0] for a in above)))
    print('  part files %d of %d; distinct statement lines %d' % (len(idx), N, len(stms)))
    for line, c in stms.items():
        print('    %5d x  %s' % (c, line))
        mc = re.search(r'caps=([0-9a-f]{8})', line)
        if mc:
            # gkjs.c: FNV-1a over the table as used, rows 0..S, holes 0..G (G from "holes <= G")
            G = int(re.search(r'holes <= (\d+)', line).group(1))
            for cdir in ('gkjs', 'gpu2/k'):
                h = capsum(os.path.join(D16, cdir, caps), S, G)
                ok = '%08x' % h == mc.group(1)
                print('  caps hash of %s/%s (rows 0..%d, holes 0..%d): %08x %s' % (cdir, caps, S, G, h,
                                                                                 'EQUAL' if ok else 'DIFFERENT'))
                if not ok:
                    bad(tag, 'caps hash of %s/%s differs from the statement line' % (cdir, caps))
    if len(stms) != 1:
        bad(tag, 'M5 fails: %d distinct statement lines' % len(stms))
    print('  kept %d (Table C %d) %s; violations %d' % (kept, want, 'EQUAL' if kept == want else 'DIFFERENT', viol))
    if kept != want:
        bad(tag, 'kept %d differs from Table C %d' % (kept, want))
    return s


def single_kernel(tag, files, S, want):
    print('%s  [single runs]' % tag)
    for rel in files:
        p = os.path.join(D16, rel)
        txt = open(p, encoding='utf-8', errors='replace').read()
        lines = [l for l in txt.split('\n') if KLINE.match(l)]
        if not lines:
            bad(tag, '%s: no result line' % rel)
            continue
        m = KLINE.match(lines[-1])
        k, v = int(m.group('k')), int(m.group('v'))
        print('  %s: %s' % (rel, lines[-1][:150]))
        if v or 'VIOLATION' in txt:
            bad(tag, '%s reports a violation' % rel)
        if int(m.group('S')) != S or k != want:
            bad(tag, '%s: S=%s kept %d, Table C %d' % (rel, m.group('S'), k, want))
        else:
            print('  kept %d (Table C %d) EQUAL; violations 0' % (k, want))


# ---------------------------------------------------------------- joint tags (gj, gj2, gj3)
RES = re.compile(r'^RESULT: found (\d+)\s+kept (\d+)\s+rows tried (\d+)', re.M)

# tag: (dir, NPARTS, NPARTS2, required substrings of the statement line, Table C kept, tried, counted)
CAPD = 'caps=../jrev/capD.txt '
JOINT = [
    ('T1', 'gpu2/parts/T1', 1024, 1, [CAPD, 'V=50 W=84 B=1 pieces S7 S7 ', 'REV=1 RP=0 potential 10,15,25 ORD=1 ORDS=0'],
     432156242209710, 2386049711507025, True),
    ('T2_08', 'gpu2/parts/T2_08', 1, 64, [CAPD, 'V=46 W=89 B=1 pieces R S7 ', 'RLO=8 RHI=15 REV=1 RP=1 potential 10,15,40 ORD=0 ORDS=0'],
     101123384635543, 591203509244515, True),
    ('T2_16', 'gpu2/parts/T2_16', 1, 64, [CAPD, 'V=46 W=89 B=1 pieces R S7 ', 'RLO=16 RHI=23 REV=1 RP=1 potential 10,15,40 ORD=0 ORDS=0'],
     129493336379997, 664376894711771, True),
    ('T2_24', 'gpu2/parts/T2_24', 64, 1, [CAPD, 'V=46 W=89 B=1 pieces R S7 ', 'RLO=24 RHI=31 REV=1 RP=1 potential 10,15,40 ORD=0 ORDS=0'],
     135483427600468, 687655387002664, True),
    ('T2_32_hi17', 'tune/gj3/parts/T2_32_hi17', 16, 1, ['caps=../../ringcap/capD_r.txt ', 'V=46 W=89 B=1 pieces R S7 ',
     'RLO=32 RHI=39 RVMIN=17 REV=1 RP=1 potential 10,15,40 ORD=0 ORDS=0'], 151457803584, 795609616646, True),
    ('T2_32_lo17', 'gpu2/parts/T2_32_lo17', 16, 1, ['caps=../tune/caps/lo_32_39_a17.txt ', 'V=46 W=89 B=1 pieces S7 R ',
     'RLO=32 RHI=39 REV=1 RP=0 potential 10,15,30 ORD=0 ORDS=0'], 817008248719, 4282237016933, True),
    ('T2_40_hi20', 'tune/gj3/parts/T2_40_hi20', 16, 1, ['caps=../../ringcap/capD_r.txt ', 'V=46 W=89 B=1 pieces R S7 ',
     'RLO=40 RHI=47 RVMIN=20 REV=1 RP=1 potential 10,15,40 ORD=0 ORDS=0'], 91979996005, 476425689572, True),
    ('T2_40_lo20', 'gpu2/parts/T2_40_lo20', 16, 1, ['caps=../tune/caps/lo_40_47_a20.txt ', 'V=46 W=89 B=1 pieces S7 R ',
     'RLO=40 RHI=47 REV=1 RP=0 potential 10,15,30 ORD=0 ORDS=0'], 284267038527, 1671708523584, True),
    ('T2_48_hi23', 'tune/gj3/parts/T2_48_hi23', 64, 1, ['caps=../../ringcap/capD_r.txt ', 'V=46 W=89 B=1 pieces R S7 ',
     'RLO=48 RHI=55 RVMIN=23 REV=1 RP=1 potential 10,15,40 ORD=0 ORDS=0'], 71260814984, 365649914334, True),
    ('T2_48_lo23', 'gpu2/parts/T2_48_lo23', 64, 1, ['caps=../ringcap/capD_r_rv22.txt ', 'V=46 W=89 B=1 pieces S7 R ',
     'RLO=48 RHI=55 REV=1 RP=0 potential 10,15,30 ORD=0 ORDS=0'], 174112070351, 957110796225, True),
    ('T2_56', 'gpu2/parts/T2_56', 64, 1, [CAPD, 'V=46 W=89 B=1 pieces R S7 ', 'RLO=56 RHI=89 REV=1 RP=1 potential 10,15,40 ORD=0 ORDS=0'],
     28953480015964, 152453459284641, True),
    ('T3r', 'gpu2/parts/T3r', 64, 1, [CAPD, 'V=52 W=82 B=2 pieces R S5 R ', 'RLO=8 RHI=128 REV=1 RP=1 potential 10,16,43 ORD=0 ORDS=0'],
     40196474735125, 213550167376609, True),
    ('T4r', 'gpu2/parts/T4r', 64, 1, [CAPD, 'V=56 W=77 B=2 pieces R S4 S4 ', 'RLO=8 RHI=128 REV=1 RP=1 potential 10,16,43 ORD=1 ORDS=0'],
     1479145818172, 7891206447132, True),
    ('T5', 'gpuj/parts/T5', 16, 1, [CAPD, 'V=60 W=72 B=2 pieces S3 S3 S3 ', 'REV=0 ', 'ORD=0 '],
     52379362069149, 268009289170899, True),
    ('T6rp', 'gpu2/parts/T6rp', 16, 1, [CAPD, 'V=58 W=75 B=3 pieces S2 R R R ', 'RLO=8 RHI=128 REV=1 RP=0 potential 10,16,25 ORD=0 ORDS=0'],
     112728682360, 592623181185, True),
    ('T7 (gj2 repeat)', 'gpu2/parts/T7', 1, 1, [CAPD, 'V=62 W=70 B=3 pieces S1 S1 R R ', 'REV=0 ', 'ORD=0 ORDS=0'],
     1432335917907, 7283065963552, True),
    ('T8 (gj2 repeat)', 'gpu2/parts/T8', 1, 1, [CAPD, 'V=66 W=65 B=2 pieces S0 S0 S0 R ', 'REV=0 ', 'ORD=0 ORDS=0'],
     7126584865, 36384111126, True),
    ('T9r', 'gpu2/parts/T9r', 1, 8, [CAPD, 'V=64 W=68 B=4 pieces S0 R R R R ', 'RLO=8 RHI=128 REV=0 ', 'ORD=0 ORDS=0'],
     11105597, 59706146, True),
    ('T6r', 'gpu2/parts/T6r', 16, 1, [CAPD, 'V=58 W=75 B=3 pieces S2 R R R ', 'ORDS=1'], 98752840534, 515328744583, False),
    ('T9rs', 'gpu2/parts/T9rs', 1, 8, [CAPD, 'V=64 W=68 B=4 pieces S0 R R R R ', 'RLO=8 ', 'ORDS=1'], 4287144, 22804444, False),
    ('T9s', 'gpu2/parts/T9s', 1, 8, [CAPD, 'V=64 W=68 B=4 pieces S0 R R R R ', 'RLO=0 ', 'ORDS=1'], 9560336846694, 50933661579615, False),
]


def joint_tag(tag, rel, N, N2, needs, wk, wt, counted):
    s = DirSrc(os.path.join(D16, rel))
    print('%s  [%s]%s' % (tag, s.where(), '' if counted else '  NOT COUNTED (ORDS run)'))
    cmd = s.read('command.txt').strip() if 'command.txt' in s.names else ''
    print('  command: ' + cmd)
    cw = dict(x.split('=', 1) for x in cmd.split() if '=' in x)
    if cw.get('NPARTS') != str(N) or cw.get('NPARTS2') != str(N2):
        bad(tag, 'command.txt NPARTS=%s NPARTS2=%s, expected %d, %d' % (cw.get('NPARTS'), cw.get('NPARTS2'), N, N2))
    pat = re.compile(r'^p(\d+)_(\d+)\.txt$')
    idx = {}
    for nm in s.names:
        m = pat.match(nm)
        if m:
            idx[(int(m.group(1)), int(m.group(2)))] = nm
        elif nm not in ('command.txt', 'log.txt', 'err.txt', 'm5.txt', 'sum.txt'):
            bad(tag, 'unexpected file %s' % nm)
    missing = [(i, j) for i in range(N) for j in range(N2) if (i, j) not in idx]
    extra = [ij for ij in idx if ij[0] >= N or ij[1] >= N2]
    if missing:
        bad(tag, '%d missing parts, first %s' % (len(missing), missing[:10]))
    if extra:
        bad(tag, 'parts outside the range: %s' % sorted(extra)[:10])
    if 'err.txt' in s.names and s.read('err.txt').strip():
        bad(tag, 'err.txt is not empty')
    stms = {}
    kept = tried = found = 0
    for (i, j) in sorted(idx):
        txt = s.read(idx[(i, j)])
        first = txt.split('\n', 1)[0]
        mp = re.search(r'PART=(\d+)/(\d+) ', first)
        mq = re.search(r'PART2=(\d+)/(\d+) ', first)
        if not mp or not mq or (int(mp.group(1)), int(mp.group(2)), int(mq.group(1)), int(mq.group(2))) != (i, N, j, N2):
            bad(tag, 'part %d_%d: part numbers in the statement line do not fit the file name' % (i, j))
        line = re.sub(r'PART=\d+/', 'PART=*/', first)
        line = re.sub(r'PART2=\d+/', 'PART2=*/', line)
        stms[line] = stms.get(line, 0) + 1
        for need in needs:
            if need not in line:
                bad(tag, 'part %d_%d: statement line lacks %r' % (i, j, need))
                break
        if counted and 'ORDS=1' in line:
            bad(tag, 'part %d_%d: a counted run with ORDS=1' % (i, j))
        rs = RES.findall(txt)
        if len(rs) != 1:
            bad(tag, 'part %d_%d: %d RESULT lines' % (i, j, len(rs)))
            continue
        f, k, t = map(int, rs[0])
        if f or re.search(r'^FOUND', txt, re.M):
            bad(tag, 'part %d_%d reports an object (found %d)' % (i, j, f))
        found += f
        kept += k
        tried += t
    print('  part files %d of %d; distinct statement lines %d' % (len(idx), N * N2, len(stms)))
    for line, c in stms.items():
        print('    %5d x  %s' % (c, line))
    if len(stms) != 1:
        bad(tag, 'M5 fails: %d distinct statement lines' % len(stms))
    ok = kept == wk and tried == wt
    print('  found %d   kept %d   tried %d   (Table C %d, %d) %s' % (found, kept, tried, wk, wt,
                                                                     'EQUAL' if ok else 'DIFFERENT'))
    if not ok:
        bad(tag, 'counts differ from Table C')
    return s


def compare_archive(tag, live, tarrel):
    t = TarSrc(os.path.join(ARCH, tarrel))
    same = diff = 0
    for nm in t.names:
        if nm in live.names and live.raw(nm) == t.raw(nm):
            same += 1
        else:
            diff += 1
    only_live = [nm for nm in live.names if nm not in t.members]
    print('  archive %s: %d files equal to the live directory, %d different or absent; %d live files not in it %s'
          % (t.where(), same, diff, len(only_live), only_live[:5]))
    if diff:
        bad(tag, 'archive and live directory differ')


def main():
    print('Part-file audit of the computations of L(7) >= 5,901 (PROOF_5901.md 0.3); root %s' % ROOT)
    print()
    print('== Kernel alone')
    for row in KERNEL:
        kernel_tag(*row)
        print()
    single_kernel('K8', ['gpu2/k/cpu_K8_k.txt'], 8, 22732567392)
    single_kernel('K9', ['gpu2/k/cpu_K9_k.txt'], 9, 384081983)
    print()
    print('== Joint')
    for row in JOINT:
        s = joint_tag(*row)
        if row[0] == 'T1':
            compare_archive('T1', s, 'gpu2/parts/T1.tar.xz')
        print()
    print('== Summary')
    if problems:
        print('%d problems:' % len(problems))
        for p in problems:
            print('  ' + p)
        return 1
    print('every counted tag: all parts present, one statement line, no violation / found 0, sums equal to Table C')
    return 0


if __name__ == '__main__':
    sys.exit(main())
