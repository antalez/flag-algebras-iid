"""Generate the modules that prove the finite facts of BeatAvg/K8/Main8K.lean by kernel evaluation.

  python3 gen/gen_k8.py        (run in formal/proof, after the data modules exist)

Reads data/k8_profile.txt (gen/run_prof.sh) and gen/k8_fit.txt (constants of the cost model).
Writes BeatAvg/K8/F/** (table and level facts), BeatAvg/K8/P8/** (the order-8 check, one module per
piece), BeatAvg/K8/Final.lean, and scratch/k8_jobs.txt (the modules in build order, with an
estimate of their cost in seconds and GB) for gen/run_k8.py. Deterministic; a few minutes.

Pieces of the order-8 check: a piece is one declaration in its own module (kernel memory is only
partly released between declarations). Memory model (measured): 0.9 GB + 1.3 GB per prefix
searched + 28 MB per leaf evaluated, kept below 14 GB.
"""
import os, re

ROOT = 'BeatAvg/K8'
HDR = 'set_option maxRecDepth 10000000\nset_option maxHeartbeats 0\n\n'
jobs = []          # (phase, module, estimated seconds, estimated GB)


def write(mod, text, phase, est, mem=10.0):
    path = mod.replace('.', '/') + '.lean'
    os.makedirs(os.path.dirname(path), exist_ok=True)
    if not (os.path.exists(path) and open(path).read() == text):     # keep the date of unchanged files
        with open(path, 'w') as f:
            f.write(text)
    jobs.append((phase, mod, est, mem))


def kfact(mod, name, stmt, imports, phase=1, est=60, mem=10.0):
    write(mod, ''.join(f'import {i}\n' for i in imports) + '\n' + HDR +
          'namespace BeatAvg.K8\n\n' + f'theorem {name} : {stmt} := by decide +kernel\n\nend BeatAvg.K8\n',
          phase, est, mem)


# ---------------------------------------------------------------- static facts
F = 'BeatAvg.K8.F'
SPEC = ['BeatAvg.K8.TbSpec', 'BeatAvg.K8.TbF', 'BeatAvg.K8.EvalFSound']
small = {
    # table checks (TbOk through tbOk_of)
    'tb_sub5': 'D.tb.sub5 = sub5Spec',
    'tb_sq': 'D.tb.sq = Fast.repsSq.map fun l => compSq (nl l)',
    'tb_deg': 'D.tb.deg = Fast.repsDeg.map fun l => compDeg (nl l)',
    'tb_thr': 'D.tb.thr = Fast.repsThr.map fun l => compThr (nl l)',
    'tb_obj': 'D.tb.obj = Fast.repsObj.map fun l => compObj (nl l)',
    'tb_flag': 'flagTabOk Fast.tabs8.ft D.tb.ftP = true',
    'tb_cls': 'clsTabOk Fast.tabs8.ct D.tb.ctP = true',
    'tb_dt': 'dtOk D.tb = true',
    'tb_tt': 'ttOk D.tb = true',
    'tb_misc': 'miscOk D.tb = true',
    # arrangement checks (RepsOk)
    'reps_sq': '∀ l ∈ Fast.repsSq, sqChk l = true',
    'reps_deg': '∀ l ∈ Fast.repsDeg, degChk l = true',
    'encl': 'Fast.enclosureOk D.tb.encLo D.tb.encHi D.tb.encM = true',
    # grouped tables (TfOk)
    'tf_sNew': 'D.tf.sNew = sNewSpec D.tb.sub5 0',
    'tf_psok': 'D.tb.sub5.all psOk = true',
    'tf_newOK': '∀ S, S < 56 → isNewS (8 * S) = Nat.ble 70 (D.tb.sub5.getD S (0, 0, 0, 0, 0)).2.1',
    'tf_sqG': 'D.tf.sqG = D.tf.sNew.map fun s => D.tb.sq.filter fun e => Nat.beq (sqKey e) s.1',
    'tf_sqR': 'D.tf.sqR = D.tb.sq.filter fun e => Nat.beq (sqKey e) 1000',
    'tf_sqK': '∀ e ∈ D.tb.sq, sqKey e ∈ D.tf.sNew.map (fun s : ℕ × ℕ × ℕ × ℕ × ℕ => s.1) ++ [1000]',
    'tf_sqSh': '∀ e ∈ D.tb.sq, e.1 % 8 = 0 ∧ e.1 / 8 < 56 ∧ e.2.2.1 % 8 = 0 ∧ e.2.2.1 / 8 < 56',
    'tf_sqNd': '(D.tf.sNew.map (fun s : ℕ × ℕ × ℕ × ℕ × ℕ => s.1) ++ [1000]).Nodup',
    'tf_degG': 'D.tf.degG = D.tf.sNew.map fun s => D.tb.deg.filter fun e => Nat.beq (degKey e) s.1',
    'tf_degQ': 'D.tf.degQ = D.quads.map fun k => (k - 70, D.tb.deg.filter fun e => Nat.beq (degKey e) (Nat.add 2000 k))',
    'tf_degK': '∀ e ∈ D.tb.deg, degKey e ∈ D.tf.sNew.map (fun s : ℕ × ℕ × ℕ × ℕ × ℕ => s.1) ++ D.quads.map (Nat.add 2000)',
    'tf_degNd': '(D.tf.sNew.map (fun s : ℕ × ℕ × ℕ × ℕ × ℕ => s.1) ++ D.quads.map (Nat.add 2000)).Nodup',
    'tf_degSh': '∀ e ∈ D.tb.deg, e.1 % 8 = 0 ∧ e.1 / 8 < 56 ∧ e.2.2.1 % 2 = 0',
    'tf_quadsOk': '∀ k ∈ D.quads, 70 ≤ k ∧ k % 2 = 0',
    'tf_kqLen': 'D.tf.kq.length = D.tf.sNew.length',
    'tf_kqOk': '∀ p ∈ D.tf.sNew.zip D.tf.kq, p.2 % 2 = 0 ∧ ∀ e ∈ D.tb.deg, degKey e = p.1.1 → e.2.2.1 < 70 ∨ e.2.2.1 = 70 + p.2',
    'tf_thrLen': '∀ e ∈ D.tb.thr, e.2.length = 8',
    'tf_thrIncl': '∀ e ∈ D.tb.thr, ∀ fq ∈ e.2, Nat.land fq.1 e.1 = e.1 ∧ Nat.land fq.2.1 e.1 = e.1 ∧ Nat.land fq.2.2 e.1 = e.1',
    'tf_thrG': 'D.tf.thrG = D.masks.map fun m => (m, ((thrFlat D.tb).filter fun it => Nat.beq (Nat.shiftRight it.1 105) m).length, ((thrFlat D.tb).filter fun it => Nat.beq (Nat.shiftRight it.1 105) m).map fun it => (Nat.land it.1 lowM, it.2))',
    'tf_thrK': '∀ it ∈ thrFlat D.tb, Nat.shiftRight it.1 105 ∈ D.masks',
    'tf_thrNd': 'D.masks.Nodup',
    'tf_objO': 'D.tf.objO = D.tb.obj.filter fun m => Nat.beq (Nat.shiftRight m 105) 0',
    'tf_objN': 'D.tf.objN = (D.tb.obj.filter fun m => !(Nat.beq (Nat.shiftRight m 105) 0)).map fun m => Nat.shiftRight m 105',
    'tf_objSh': '∀ m ∈ D.tb.obj, Nat.shiftRight m 105 = 0 ∨ Nat.land m lowM = 0',
}
for name, stmt in small.items():
    kfact(f'{F}.S.{name}', name, stmt, SPEC, est=300, mem=20.0)
LEV = ['BeatAvg.K8.Level7Sound']
levf = {
    'stat3': 'statOk 3 = true', 'stat4': 'statOk 4 = true', 'stat5': 'statOk 5 = true', 'stat6': 'statOk 6 = true',
    'base4': '∀ t, t ≤ 2 → t ∈ unpackE 2 (lookupG D.G4 0).1 (lookupG D.G4 0).2',
    'lev5': '(allCodes 0 2 D.G4).all chk5 = true', 'lev6': '(allCodes 2 8 D.G5).all chk6 = true',
}
for name, stmt in levf.items():
    kfact(f'{F}.S.{name}', name, stmt, LEV, est=60)

# rows of Dn · Q: one module each
for i in range(300):
    kfact(f'{F}.Row.r{i}', f'row{i}', f'qRowOk D.tb {i} = true', ['BeatAvg.K8.TbSpec', 'BeatAvg.K8.Tb'], est=40, mem=10.0)
lines = ['import BeatAvg.K8.Combine', 'import BeatAvg.K8.TbSpec'] + [f'import {F}.Row.r{i}' for i in range(300)]
proof = ['  have h0 : (List.range\' 0 (0 + 1 - 0)).all (qRowOk D.tb) = true := rall_one row0']
for i in range(1, 300):
    proof.append(f'  have h{i} : (List.range\' 0 ({i} + 1 - 0)).all (qRowOk D.tb) = true :=\n'
                 f'    rall_trans h{i - 1} (rall_one row{i}) (by decide) (by decide)')
write(f'{F}.Rows', '\n'.join(lines) + '\n\n' + HDR + 'namespace BeatAvg.K8\n\n'
      'theorem rows : ∀ i, i < 300 → qRowOk D.tb i = true := by\n' + '\n'.join(proof) +
      '\n  exact rall_forall h299\n\nend BeatAvg.K8\n', 2, 120)

# level 7: pieces of 5 patterns of six points (1290 of them)
N6, S7 = 1290, 5
cuts = list(range(0, N6, S7))
for k, lo in enumerate(cuts):
    if lo + S7 < N6:
        kfact(f'{F}.L7.p{k}', f'l7p{k}', f'lev7T {lo} {lo + S7} = true', ['BeatAvg.K8.Check7K'], est=50, mem=12.0)
    else:
        kfact(f'{F}.L7.p{k}', f'l7p{k}', f'lev7D {lo} = true', ['BeatAvg.K8.Check7K'], est=50, mem=12.0)
lines = ['import BeatAvg.K8.Level7Sound'] + [f'import {F}.L7.p{k}' for k in range(len(cuts))]
last = len(cuts) - 1
proof = [f'  have h{last} : lev7D {cuts[last]} = true := l7p{last}']
for k in range(last - 1, -1, -1):
    proof.append(f'  have h{k} : lev7D {cuts[k]} = true := lev7T_trans l7p{k} h{k + 1} (by decide)')
write(f'{F}.L7', '\n'.join(lines) + '\n\n' + HDR + 'namespace BeatAvg.K8\n\ntheorem lev7 : lev7D 0 = true := by\n'
      + '\n'.join(proof) + '\n  exact h0\n\nend BeatAvg.K8\n', 2, 60)

# all facts
imports = ['BeatAvg.K8.Main8K', 'BeatAvg.K8.Level7Sound', f'{F}.Rows', f'{F}.L7'] + \
    [f'{F}.S.{n}' for n in list(small) + list(levf)]
tf_fields = ['sNew', 'psok', 'newOK', 'sqG', 'sqR', 'sqK', 'sqSh', 'sqNd', 'degG', 'degQ', 'degK', 'degNd',
             'degSh', 'quadsOk', 'kqLen', 'kqOk', 'thrLen', 'thrIncl', 'thrG', 'thrK', 'thrNd', 'objO', 'objN', 'objSh']
body = ('theorem tbOk : TbOk D.tb :=\n  tbOk_of tb_sub5 tb_sq tb_deg tb_thr tb_obj tb_flag tb_cls rows tb_dt tb_tt tb_misc\n\n'
        'theorem tfOk : TfOk D.tb D.tf D.quads D.masks :=\n  ⟨' + ', '.join('tf_' + f for f in tf_fields) + '⟩\n\n'
        'theorem repsOk : RepsOk := ⟨reps_sq, reps_deg⟩\n\n'
        'theorem lev7Ok : LevelOk D.G7 40 6 := levels base4 stat3 stat4 stat5 lev5 lev6 lev7\n')
write(f'{F}.All', '\n'.join(f'import {i}' for i in imports) + '\n\n' + HDR + 'namespace BeatAvg.K8\n\n' + body +
      '\nend BeatAvg.K8\n', 3, 120)

# ---------------------------------------------------------------- order-8 pieces
# Cost model (gen/k8_fit.txt: times from a pilot run with 150 jobs in parallel, memory from single
# runs with the trie join): for a set of first-stage candidates with L leaves and S compatibility
# tests of the plain join (data/k8_profile.txt, a proxy for the work of the trie join),
#   seconds = START + TPRE + TT * S + TL * L,     GB = GBASE + GT * S + GL * L.
fit = dict(l.split() for l in open('gen/k8_fit.txt'))
START, TPRE, TT, TL = (float(fit[k]) for k in ('START', 'TPRE', 'TT', 'TL'))
GBASE, GT, GL = (float(fit[k]) for k in ('GBASE', 'GT', 'GL'))
MEM = float(fit.get('MEM', 14.0))
P8 = 'BeatAvg.K8.P8'
prof = {}
for line in open('data/k8_profile.txt'):
    f = line.split()
    g, j = int(f[0]), int(f[1])
    prof[g, j] = [tuple(map(int, x.split(':'))) for x in f[2:]]
s = open(f'{ROOT}/L7G.lean').read()
body7 = s[s.index('def G7'):s.index('def X8')]
G = [(int(a, 0), int(b), int(c, 0)) for a, b, c in
     re.findall(r'\((0x[0-9a-f]+|\d+), (\d+), (0x[0-9a-f]+|\d+)\)', body7)]
assert len(G) == 1290
npiece = 0
groups = []
big = 0


def piece(stmt, est, mem):
    global npiece
    mod = f'{P8}.D.d{npiece}'
    npiece += 1
    ns = mod.replace('BeatAvg.K8.P8.D.', '')
    write(mod, f'import BeatAvg.K8.Check8K\n\n{HDR}namespace BeatAvg.K8.P8.D.{ns}\n\nopen BeatAvg.K8\n\n'
          f'theorem d : {stmt} = true := by decide +kernel\n\nend BeatAvg.K8.P8.D.{ns}\n', 1, est, mem)
    return mod


for g, (key, cnt, packed) in enumerate(G):
    items = []
    j = 0
    while j < cnt:
        pr = prof[g, j]
        L, S = sum(x[0] for x in pr), sum(x[1] for x in pr)
        if GBASE + GT * S + GL * L > MEM:
            # split along the first-stage candidates
            parts = []
            lo = 0
            while lo < len(pr):
                hi, l_, s_ = lo, 0, 0
                while hi < len(pr) and (hi == lo or GBASE + GT * (s_ + pr[hi][1]) + GL * (l_ + pr[hi][0]) <= MEM):
                    l_ += pr[hi][0]
                    s_ += pr[hi][1]
                    hi += 1
                if GBASE + GT * s_ + GL * l_ > MEM:
                    big += 1
                est, mem = START + TPRE + TT * s_ + TL * l_, GBASE + GT * s_ + GL * l_
                if hi < len(pr):
                    parts.append((lo, piece(f'chkC {g} {j} {lo} {hi}', est, mem)))
                else:
                    parts.append((lo, piece(f'chkCD {g} {j} {lo}', est, mem)))
                lo = hi
            items.append(('S', j, parts))
            j += 1
        else:
            a, mem, est = j, GBASE, START
            while j < cnt and j - a < 6:
                pr = prof[g, j]
                L, S = sum(x[0] for x in pr), sum(x[1] for x in pr)
                if j > a and mem + GT * S + GL * L > MEM:
                    break
                mem += GT * S + GL * L
                est += TPRE + TT * S + TL * L
                j += 1
            items.append(('J', a, j, piece(f'chkJ {g} {a} {j}', est, mem)))
    # group module
    imps = ['BeatAvg.K8.Combine']
    proof = []
    first = True
    for it in items:
        if it[0] == 'J':
            _, a, bb, mod = it
            imps.append(mod)
            h = mod.replace('BeatAvg.K8.P8.', '') + '.d'
        else:
            _, jj, parts = it
            imps += [m for _, m in parts]
            names = [m.replace('BeatAvg.K8.P8.', '') + '.d' for _, m in parts]
            proof.append(f'  have s{jj} : chkCD {g} {jj} {parts[-1][0]} = true := {names[-1]}')
            for (lo, _), nm in reversed(list(zip(parts[:-1], names[:-1]))):
                proof.append(f'  have s{jj} : chkCD {g} {jj} {lo} = true := chkC_trans {nm} s{jj} (by decide)')
            h = f'(chkJ_one (chkCD_zero s{jj}))'
            bb = jj + 1
        if first:
            proof.append(f'  have c : chkJ {g} 0 {bb} = true := {h}')
            first = False
        else:
            proof.append(f'  have c : chkJ {g} 0 {bb} = true := chkJ_trans c {h} (by decide) (by decide)')
    gm = f'{P8}.G.g{g}'
    write(gm, '\n'.join(f'import {i}' for i in imps) + f'\n\n{HDR}namespace BeatAvg.K8.P8\n\n'
          f'theorem g{g} : chkG {g} = true := by\n' + '\n'.join(proof) +
          f'\n  exact chkG_of c (by decide +kernel)\n\nend BeatAvg.K8.P8\n', 2, 30)
    groups.append(gm)
print(f'{big} pieces over the memory cap (one first-stage candidate alone)')

# blocks of 30 groups, then the whole check
NB = 30
blocks = []
for bi, a in enumerate(range(0, 1290, NB)):
    bgs = list(range(a, min(1290, a + NB)))
    proof = [f'  have c : chkGs {a} ({a} + 1) = true := chkGs_one g{a}']
    for g in bgs[1:]:
        proof.append(f'  have c : chkGs {a} ({g} + 1) = true := chkGs_trans c (chkGs_one g{g}) (by decide) (by decide)')
    bm = f'{P8}.B.b{bi}'
    write(bm, 'import BeatAvg.K8.Combine\n' + '\n'.join(f'import {P8}.G.g{g}' for g in bgs) +
          f'\n\n{HDR}namespace BeatAvg.K8.P8\n\ntheorem b{bi} : chkGs {a} {bgs[-1] + 1} = true := by\n' +
          '\n'.join(proof) + '\n  exact c\n\nend BeatAvg.K8.P8\n', 3, 30)
    blocks.append((bi, a, bgs[-1] + 1))
proof = [f'  have c : chkGs 0 {blocks[0][2]} = true := b0']
for bi, a, b in blocks[1:]:
    proof.append(f'  have c : chkGs 0 {b} = true := chkGs_trans c b{bi} (by decide) (by decide)')
write(f'{P8}.All', 'import BeatAvg.K8.Combine\n' + '\n'.join(f'import {P8}.B.b{bi}' for bi, _, _ in blocks) +
      f'\n\n{HDR}namespace BeatAvg.K8.P8\n\n'
      'theorem all8 : ∀ T ∈ codes7, chk8 T = true := by\n' + '\n'.join(proof) +
      '\n  exact chk8_all c (by decide +kernel)\n\nend BeatAvg.K8.P8\n', 4, 60)

# ---------------------------------------------------------------- the final theorem
write('BeatAvg.K8.Final', 'import BeatAvg.K8.F.All\nimport BeatAvg.K8.P8.All\nimport BeatAvg.Lower.Main\n\n/-!\n'
      '# `C ≤ B*` with the finite part checked by the kernel\n\n'
      'No `native_decide`: every finite fact is proved by `decide +kernel` in the modules\n'
      '`BeatAvg.K8.F.*` and `BeatAvg.K8.P8.*` (generated by `gen/gen_k8.py`).\n-/\n\n'
      'namespace BeatAvg.K8\n\n'
      'theorem facts : Facts :=\n  ⟨lev7Ok, stat6, P8.all8, tbOk, tfOk, repsOk, encl⟩\n\n'
      '/-- **The Beat the Average constant is at most `B*`**, with standard axioms only. -/\n'
      'theorem C_le_Bstar_kernel : C ≤ Bstar := C_le_Bstar_of_facts facts\n\n'
      '/-- **`C = B*`**, with standard axioms only. -/\n'
      'theorem C_eq_Bstar_kernel : C = Bstar := le_antisymm C_le_Bstar_kernel Bstar_le_C\n\nend BeatAvg.K8\n', 5, 60)

os.makedirs('scratch', exist_ok=True)
with open('scratch/k8_jobs.txt', 'w') as f:
    for ph, mod, est, mem in jobs:
        f.write(f'{ph} {mod} {est:.0f} {mem:.1f}\n')
p1 = [e for ph, _, e, _ in jobs if ph == 1]
print(f'{len(jobs)} modules; {npiece} order-8 pieces; phase 1: {len(p1)} modules, {sum(p1) / 3600:.0f} CPU-h estimated')
