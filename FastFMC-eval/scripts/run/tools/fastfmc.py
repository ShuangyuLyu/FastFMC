import os
import re
import tempfile

from common import load_cnf, run_cmd


def compile_nnf(r, bench, cnf, workdir, use_coprocessor=True):
    cur_cnf = cnf
    t_compile = 0.0
    sat = True
    if use_coprocessor and r.tools['FastFMC'].get('coprocessor'):
        red = os.path.join(workdir, 'reduced.cnf')
        wall, rc, _ = run_cmd([r.tools['FastFMC']['coprocessor'],
                               '-enabled_cp3', '-up', '-subsimp', '-no-bve',
                               '-no-bce', '-no-dense', '-dimacs=' + red, cur_cnf], r.cut)
        t_compile += wall
        if rc not in (0, 10, 20) or not os.path.isfile(red):
            return None, -1.0, False
        sat = (rc != 20)
        cur_cnf = red
    nnf = os.path.join(workdir, 'model.nnf')
    nv, nc = 0, 0
    with open(cur_cnf) as f:
        for line in f:
            if line.startswith('p'):
                _, _, nv, nc = line.split()
                nv, nc = int(nv), int(nc)
                break
    if nv == 0:
        with open(nnf, 'w') as f:
            f.write('p nnf 1 0\n' + ('a 0\n' if sat else 'o 0\n'))
        return nnf, t_compile, True
    wall, rc, _ = run_cmd([r.tools['FastFMC']['d4v2'], '-i', cur_cnf, '-m', 'ddnnf-compiler',
                           '--dump-ddnnf', nnf], max(r.cut - t_compile, 1))
    t_compile += wall
    if rc != 0 or not os.path.isfile(nnf):
        return None, -1.0, False
    return nnf, t_compile, False


def online_phase(r, ff_bin, nnf, bench, extra=(), budget=None):
    nv, _, _ = load_cnf(os.path.join(r.bench_dir, bench + '.cnf'))
    qout = os.path.join(tempfile.mkdtemp(), 'q.csv')
    cmd = [ff_bin, nnf] + list(extra) + ['-t', str(nv), 'count-queries',
           r.config_path(bench), qout]
    wall, rc, out = run_cmd(cmd, r.cut if budget is None else budget)
    if rc != 0:
        return None
    m = re.findall(r'It took\s+([\d.]+)\s*seconds', out.decode(errors='ignore'))
    online_s = float(m[-1]) if m else None
    return wall, online_s


def run(r, bench, variant=None):
    v = variant or {}
    ff_bin = v.get('fastfmc', r.tools['FastFMC']['fastfmc'])
    cnf = os.path.join(r.bench_dir, bench + '.cnf')
    with tempfile.TemporaryDirectory() as wd:
        nnf, t_compile, degenerate = compile_nnf(r, 
            bench, cnf, wd, v.get('use_coprocessor', True))
        if nnf is None:
            return -1.0, -1.0
        extra = list(v.get('fastfmc_flags', []))
        if v.get('mu'):
            extra += ['--n', str(v['mu'])]
        if degenerate:

            return t_compile, 0.0
        res = online_phase(r, ff_bin, nnf, bench, extra,
                                   budget=max(r.cut - t_compile, 1.0))
        if res is None:
            return t_compile, -1.0
        wall_ff, online_s = res
        count = online_s if (online_s is not None and 0 < online_s <= wall_ff) else wall_ff
        build = t_compile + max(wall_ff - count, 0.0)

        if build >= r.cut or build + count > r.cut:
            return -1.0, -1.0
        return build, count
