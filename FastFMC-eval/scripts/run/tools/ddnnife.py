import os
import tempfile

from common import load_cnf, run_cmd


def run(r, bench):
    d4v2 = r.tools['ddnnife']['d4v2']
    bin_ = r.tools['ddnnife']['ddnnife']
    cnf = os.path.join(r.bench_dir, bench + '.cnf')
    nv, _, _ = load_cnf(cnf)
    with tempfile.TemporaryDirectory() as wd:
        nnf = os.path.join(wd, 'model.nnf')
        wall, rc, _ = run_cmd([d4v2, '-i', cnf, '-m', 'ddnnf-compiler',
                             '--dump-ddnnf', nnf], r.cut)
        if rc != 0 or not os.path.isfile(nnf):
            return -1.0, -1.0
        build = wall
        wall2, rc2, _ = run_cmd([bin_, '-i', nnf, '-t', str(nv),
                                 'count-queries', r.config_path(bench)],
                                r.cut - build)
        if rc2 != 0 or build + wall2 > r.cut:
            return build, -1.0
        return build, wall2
