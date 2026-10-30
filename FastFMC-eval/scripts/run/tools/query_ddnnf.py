import os
import tempfile

from common import load_cnf, load_queries, run_cmd


def run(r, bench):
    c2d = r.tools.get('query-ddnnf', {}).get('c2d')
    if not c2d or not os.path.isfile(c2d):
        return None
    qd = r.tools['query-ddnnf']['querydnnf']
    cnf = os.path.join(r.bench_dir, bench + '.cnf')
    nv, _, _ = load_cnf(cnf)
    with tempfile.TemporaryDirectory() as wd:
        nnf = os.path.join(wd, 'model.nnf')
        wall, rc, _ = run_cmd([c2d, '-c', cnf, '-ddnnf', nnf], r.cut)
        if rc != 0 or not os.path.isfile(nnf):
            return -1.0, -1.0
        build = wall
        cmdfile = os.path.join(wd, 'cmd.txt')
        with open(cmdfile, 'w') as f:

            f.write('load %s\n' % nnf)
            for line in load_queries(r.config_path(bench)):
                f.write('cond %s\nmc\n' % line)
        wall2, rc2, _ = run_cmd([qd, '-cmd', cmdfile], r.cut - build,
                                stdout_file=os.path.join(wd, 'out.txt'))
        if rc2 != 0 or build + wall2 > r.cut:
            return build, -1.0
        return build, wall2
