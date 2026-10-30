import os
import statistics
import subprocess
import tempfile
import time

from common import load_cnf, load_queries, log, parse_peak_kb, run_cmd
from tools import fastfmc


def run(r, runs, tools=None):
    benches = r.benches()
    peaks = {}
    for tool in (tools or ['FastFMC', 'ddnnife', 'd4-query', 'Ganak',
                                'sharpSAT', 'countAntom']):
        for run in range(runs):
            for i, b in enumerate(benches):
                mf = tempfile.mktemp(suffix='.mem')
                try:
                    if tool == 'FastFMC':
                        ok = fastfmc_mem(r, b, mf)
                    elif tool in ('Ganak', 'sharpSAT', 'countAntom'):
                        ok = sat_mem(r, b, tool, mf)
                    elif tool == 'ddnnife':
                        ok = ddnnife_mem(r, b, mf)
                    elif tool == 'd4-query':
                        ok = d4q_mem(r, b, mf)
                    else:
                        ok = None
                except Exception:
                    ok = None
                if ok:
                    pk = parse_peak_kb(mf)
                    if pk:
                        peaks.setdefault((tool, b), []).append(pk)
                if os.path.isfile(mf):
                    os.unlink(mf)
                if (i + 1) % 100 == 0:
                    log('  memory %s run %d: %d/%d' % (tool, run, i + 1, len(benches)))
    tools = sorted(set(t for t, _ in peaks))
    os.makedirs(os.path.join(r.out, 'memory'), exist_ok=True)
    p1 = os.path.join(r.out, 'memory', 'memory_per_benchmark.csv')
    with open(p1, 'w', newline='') as f:
        f.write('benchmark,is_fm,' + ','.join('%s_GB' % t for t in tools) + '\n')
        for b in benches:
            col = []
            for t in tools:
                v = peaks.get((t, b))
                col.append('%.4f' % (statistics.mean(v) / 1048576.0) if v else 'NA')
            f.write('%s,%d,%s\n' % (b, 1 if b in r.fm else 0, ','.join(col)))
    p2 = os.path.join(r.out, 'memory', 'memory_summary.csv')
    with open(p2, 'w', newline='') as f:
        f.write('tool,benchmark_set,mean_peak_rss_GB,std_peak_rss_GB,max_peak_rss_GB,n_runs\n')
        for t in tools:
            for cat in ('FM', 'Other'):
                vals = [statistics.mean(v) / 1048576.0
                        for (tt, b), v in peaks.items()
                        if tt == t and (cat == 'FM') == (b in r.fm)]
                if vals:
                    f.write('%s,%s,%.3f,%.3f,%.3f,%d\n' % (
                        t, cat, statistics.mean(vals), statistics.pstdev(vals),
                        max(vals), runs))
    log('memory -> %s, %s' % (p1, p2))


def fastfmc_mem(r, bench, mf):
    cnf = os.path.join(r.bench_dir, bench + '.cnf')
    nv, _, _ = load_cnf(cnf)
    with tempfile.TemporaryDirectory() as wd:
        nnf, t_compile, deg = fastfmc.compile_nnf(r, bench, cnf, wd)
        if nnf is None:
            return None
        qout = os.path.join(wd, 'q.csv')
        cmd = [r.tools['FastFMC']['fastfmc'], nnf, '-t', str(nv),
               'count-queries', r.config_path(bench), qout]
        wall, rc, _ = run_cmd(cmd, r.cut, memfile=mf, gtime=r.gtime)
        return rc == 0


def ddnnife_mem(r, bench, mf):
    d4v2 = r.tools['ddnnife']['d4v2']
    cnf = os.path.join(r.bench_dir, bench + '.cnf')
    nv, _, _ = load_cnf(cnf)
    with tempfile.TemporaryDirectory() as wd:
        nnf = os.path.join(wd, 'm.nnf')
        w1, rc1, _ = run_cmd([d4v2, '-i', cnf, '-m', 'ddnnf-compiler',
                              '--dump-ddnnf', nnf], r.cut, memfile=mf,
                             gtime=r.gtime)
        if rc1 != 0:
            return None
        p1 = parse_peak_kb(mf)
        w2, rc2, _ = run_cmd([r.tools['ddnnife']['ddnnife'], '-i', nnf,
                              '-t', str(nv), 'count-queries',
                              r.config_path(bench)],
                             r.cut, memfile=mf, gtime=r.gtime)
        p2 = parse_peak_kb(mf)
        ps = [x for x in (p1, p2) if x]
        return max(ps) if ps else None


def d4q_mem(r, bench, mf):
    d4v2 = r.tools['d4-query']['d4v2']
    cnf = os.path.join(r.bench_dir, bench + '.cnf')
    qfile = tempfile.mktemp(suffix='.q')
    with open(qfile, 'w') as tf:
        for line in load_queries(r.config_path(bench)):
            line = line.rstrip()
            tf.write('m ' + line + (' 0' if not line.endswith(' 0') else '') + '\n')
    wall, rc, _ = run_cmd([d4v2, '-i', cnf, '-m', 'ddnnf-compiler', '-q', qfile],
                          r.cut, memfile=mf, gtime=r.gtime)
    os.unlink(qfile)
    return rc == 0


def sat_mem(r, bench, tool, mf):
    bin_ = r.tools[tool]['bin']
    cnf = os.path.join(r.bench_dir, bench + '.cnf')
    nv, nc, body = load_cnf(cnf)
    body_str = '\n'.join(body)
    budget = r.cut
    elapsed = 0.0
    cmd_args = {'Ganak': ['--prob', '0'], 'sharpSAT': ['-q'],
                'countAntom': []}.get(tool, [])
    mx = None
    for line in load_queries(r.config_path(bench)):
        units = '\n'.join('%s 0' % lit for lit in line.split())
        with tempfile.NamedTemporaryFile('w', suffix='.cnf', delete=False) as tf:
            tf.write('p cnf %d %d\n%s\n%s\n' % (nv, nc + len(line.split()),
                                                  body_str, units))
            tmp = tf.name
        remaining = budget - elapsed
        if remaining <= 0:
            os.unlink(tmp)
            break
        wall, rc, _ = run_cmd([bin_] + cmd_args + [tmp], remaining,
                              memfile=mf, gtime=r.gtime)
        if rc == -9:
            os.unlink(tmp)
            return None
        elapsed += wall
        p = parse_peak_kb(mf)
        if p:
            mx = p if mx is None else max(mx, p)
        os.unlink(tmp)
    return mx
