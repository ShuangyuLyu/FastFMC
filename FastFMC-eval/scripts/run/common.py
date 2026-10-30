import csv
import os
import shutil
import signal
import subprocess
import time


def find_gtime():
    for c in (shutil.which('gtime'), '/usr/bin/time', '/usr/local/bin/time'):
        if c and os.path.isfile(c):
            try:
                subprocess.run([c, '--version'], stdout=subprocess.DEVNULL,
                               stderr=subprocess.DEVNULL)
                return c
            except Exception:
                continue
    return None


def log(msg):
    print(time.strftime('[%H:%M:%S] ') + msg, flush=True)


def load_queries(path):
    queries = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                queries.append(line)
    return queries


def load_cnf(path):
    nv = nc = 0
    body = []
    with open(path) as f:
        for line in f:
            s = line.strip()
            if not s or s.startswith('c'):
                continue
            if s.startswith('p'):
                parts = s.split()
                nv, nc = int(parts[2]), int(parts[3])
            else:
                body.append(s)
    return nv, nc, body


def run_cmd(cmd, timeout, stdout_file=None, memfile=None, gtime=None):
    if memfile and gtime:
        cmd = [gtime, '-v', '-o', memfile] + cmd
    t0 = time.time()
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE if not stdout_file else
                            open(stdout_file, 'w'), stderr=subprocess.DEVNULL,
                            preexec_fn=os.setsid)
    try:
        out = proc.communicate(timeout=timeout)[0]
        wall = time.time() - t0
        if stdout_file:
            out = open(stdout_file, 'rb').read()
        return wall, proc.returncode, out or b''
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except Exception:
            pass
        proc.communicate()
        return time.time() - t0, -9, b''


def load_fm_manifest(path):
    if path.endswith('.rar'):
        out = subprocess.check_output(['bsdtar', '-tf', path],
                                      stderr=subprocess.DEVNULL).decode()
        return {os.path.basename(l.strip())[:-4]
                for l in out.splitlines() if l.strip().endswith('.cnf')}
    with open(path) as f:
        return {l.strip()[:-4] if l.strip().endswith('.cnf') else l.strip()
                for l in f if l.strip() and not l.startswith('#')}


def fnum(v, default=-1.0):
    try:
        return float(str(v).strip())
    except Exception:
        return default


def parse_peak_kb(memfile):
    try:
        with open(memfile) as f:
            for line in f:
                if 'Maximum resident set size' in line:
                    return float(line.strip().split()[-1])
    except Exception:
        pass
    return None


def write_er_csv(path, rows):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', newline='') as f:
        f.write('file_name,build_time,count_time\n')
        for b in sorted(rows):
            bt, ct = rows[b]
            f.write('%s,%s,%s\n' % (b, fmt(bt), fmt(ct)))


def fmt(v):
    return '-1.0000000000' if v is None or v < 0 else '%.10f' % v
