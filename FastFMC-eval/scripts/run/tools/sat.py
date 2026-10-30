import os
import subprocess
import tempfile
import time

from common import load_cnf, load_queries


def run(r, bench, tool):
    bin_ = r.tools[tool]['bin']
    cnf = os.path.join(r.bench_dir, bench + '.cnf')
    nv, nc, body = load_cnf(cnf)
    body_str = '\n'.join(body)
    budget = r.cut
    elapsed = 0.0
    cmd_args = {'Ganak': ['--prob', '0'], 'sharpSAT': ['-q'],
                'countAntom': []}.get(tool, [])
    for line in load_queries(r.config_path(bench)):
        units = '\n'.join('%s 0' % lit for lit in line.split())
        with tempfile.NamedTemporaryFile('w', suffix='.cnf', delete=False) as tf:
            tf.write('p cnf %d %d\n%s\n%s\n' % (nv, nc + len(line.split()),
                                                body_str, units))
            tmp = tf.name
        remaining = budget - elapsed
        if remaining <= 0:
            os.unlink(tmp)
            return -1.0, -1.0
        t0 = time.time()
        try:
            subprocess.run([bin_] + cmd_args + [tmp], stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, timeout=remaining)
        except subprocess.TimeoutExpired:
            os.unlink(tmp)
            return -1.0, -1.0
        elapsed += time.time() - t0
        os.unlink(tmp)
    return -1.0, elapsed
