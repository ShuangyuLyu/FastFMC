import os
import re
import tempfile

from common import load_queries, run_cmd


def run(r, bench):
    d4v2 = r.tools['d4-query']['d4v2']
    cnf = os.path.join(r.bench_dir, bench + '.cnf')
    qfile = None
    with tempfile.NamedTemporaryFile('w', suffix='.q', delete=False) as tf:
        for line in load_queries(r.config_path(bench)):
            line = line.rstrip()
            tf.write(('m ' + line + (' 0' if not line.endswith(' 0') else '')) + '\n')
        qfile = tf.name
    wall, rc, out = run_cmd([d4v2, '-i', cnf, '-m', 'ddnnf-compiler', '-q', qfile],
                            r.cut)
    os.unlink(qfile)
    if rc != 0:
        return -1.0, -1.0
    m = re.findall(r'c Final time:\s*([\d.]+(?:[eE][-+]?\d+)?)',
                   out.decode(errors='ignore'))
    build = float(m[0]) if m else 0.0

    build = min(build, wall)
    count = max(wall - build, 0.0)
    if wall > r.cut:
        return -1.0, -1.0
    return build, count
