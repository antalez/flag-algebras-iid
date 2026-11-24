"""Compile the modules listed by gen/gen_k8.py (scratch/k8_jobs.txt) with bounded parallelism.

  setsid nohup python3 gen/run_k8.py [--jobs N] [--mem GB] [--phase P] [--only REGEX] > scratch/k8_run.log 2>&1 &

Each module is compiled by `lean -o`, with LEAN_PATH taken from `lake env`. Phases run in order
(a phase starts when the previous one is complete); within a phase the most expensive jobs go first.
A job starts only if the estimated memory of the running jobs stays below `--mem` and the system
has that much available. Modules whose .olean is newer than the source are skipped, so the run can
be restarted. One line per finished job in scratch/k8_status.txt: status, module, seconds, GB.
"""
import argparse, os, re, resource, subprocess, sys, time

ap = argparse.ArgumentParser()
ap.add_argument('--jobs', type=int, default=150)
ap.add_argument('--mem', type=float, default=1650.0)
ap.add_argument('--phase', type=int, default=0, help='run only this phase (0: all)')
ap.add_argument('--only', default=None, help='regular expression on module names')
ap.add_argument('--limit', type=int, default=0, help='at most this many jobs (testing)')
args = ap.parse_args()

env = dict(os.environ)
env['LEAN_PATH'] = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], capture_output=True,
                                  text=True, check=True).stdout.strip()
LEAN = subprocess.run(['lake', 'env', 'which', 'lean'], capture_output=True, text=True,
                      check=True).stdout.strip()
jobs = []
for line in open('scratch/k8_jobs.txt'):
    ph, mod, est, mem = line.split()
    jobs.append((int(ph), mod, float(est), float(mem)))
if args.phase:
    jobs = [j for j in jobs if j[0] == args.phase]
if args.only:
    jobs = [j for j in jobs if re.search(args.only, j[1])]
if args.limit:
    jobs = jobs[:args.limit]


def paths(mod):
    rel = mod.replace('.', '/')
    return rel + '.lean', '.lake/build/lib/lean/' + rel + '.olean'


def done(mod):
    src, out = paths(mod)
    return os.path.exists(out) and os.path.getmtime(out) >= os.path.getmtime(src)


def mem_available():
    for line in open('/proc/meminfo'):
        if line.startswith('MemAvailable:'):
            return int(line.split()[1]) / 1e6
    return 0.0


os.makedirs('scratch/k8_logs', exist_ok=True)   # scratch/ is created by gen_k8.py
status = open('scratch/k8_status.txt', 'a')
t0 = time.time()
failed = 0
for phase in sorted({j[0] for j in jobs}):
    todo = sorted((j for j in jobs if j[0] == phase and not done(j[1])), key=lambda j: -j[2])
    print(f'[{time.time() - t0:.0f}s] phase {phase}: {len(todo)} modules to build', flush=True)
    running = {}          # pid -> (mod, est mem, start, log file, olean, Popen)
    i = 0
    nok = 0
    while i < len(todo) or running:
        while i < len(todo) and len(running) < args.jobs:
            mod, mem = todo[i][1], todo[i][3]
            used = sum(r[1] for r in running.values())
            if running and (used + mem > args.mem or mem_available() < mem + 40):
                break
            src, out = paths(mod)
            os.makedirs(os.path.dirname(out), exist_ok=True)
            logf = open(f'scratch/k8_logs/{mod}.log', 'w')
            p = subprocess.Popen([LEAN, '-o', out, src], stdout=logf, stderr=subprocess.STDOUT, env=env)
            running[p.pid] = (mod, mem, time.time(), logf, out, p)   # keep p: no reaping by subprocess
            i += 1
        pid, st, ru = os.wait4(-1, 0)
        if pid not in running:
            continue
        mod, mem, start, logf, out, _ = running.pop(pid)
        logf.close()
        ok = os.WIFEXITED(st) and os.WEXITSTATUS(st) == 0
        log = f'scratch/k8_logs/{mod}.log'
        if ok:
            nok += 1
            text = open(log).read()
            if 'error' in text or 'sorry' in text:
                ok = False
        if ok:
            os.remove(log)
        else:
            failed += 1
            if os.path.exists(out):
                os.remove(out)
        status.write(f'{"ok" if ok else "FAIL"} {mod} {time.time() - start:.1f} {ru.ru_maxrss / 1e6:.2f}\n')
        status.flush()
        if nok % 1000 == 0 and ok:
            print(f'[{time.time() - t0:.0f}s] phase {phase}: {nok} done, {len(running)} running, {failed} failed', flush=True)
    print(f'[{time.time() - t0:.0f}s] phase {phase} finished: {nok} built, {failed} failed so far', flush=True)
    if failed:
        print('stopping: failures in this phase (see scratch/k8_logs)', flush=True)
        sys.exit(1)
print(f'[{time.time() - t0:.0f}s] all done', flush=True)
