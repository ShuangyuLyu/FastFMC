import csv
import os
import statistics

CUTOFF = 1800.0
PENALTY = 2 * CUTOFF
N_RUNS = 10
MISSING = 'family_grid_new_dispose_4_1_p_t2'
REUSE = ['FastFMC', 'ddnnife', 'd4-query', 'query-ddnnf']
SAT = ['Ganak', 'SharpSAT', 'countAntom']
ALT = [('FastFMC', None), ('LPE', 'LPE'), ('Simp', 'Simp'),
       ('BHM', 'BHM'), ('ZNP', 'ZNP')]
EFF = ['FastFMC', 'ddnnife', 'd4-query']
ALL_TOOLS = REUSE + SAT
TOOL_DIR_ALIASES = {
    'FastFMC': ['FastFMC', 'fastfmc'],
    'ddnnife': ['ddnnife'],
    'd4-query': ['d4-query', 'd4query'],
    'query-ddnnf': ['query-ddnnf', 'query-dnnf', 'query_dnnf'],
    'Ganak': ['Ganak', 'ganak'],
    'SharpSAT': ['SharpSAT', 'sharpSAT', 'sharpsat'],
    'countAntom': ['countAntom', 'countantom'],
}


def read_csv(path):
    with open(path, newline='') as f:
        return list(csv.DictReader(f))


def fnum(v):
    try:
        return float(str(v).strip())
    except (TypeError, ValueError):
        return -1.0


def load_timings(directory, prefix=''):
    runs = []
    for i in range(N_RUNS):
        path = os.path.join(directory, f'{prefix}{i}.csv')
        if not os.path.isfile(path):
            continue
        d = {}
        for r in read_csv(path):
            d[r['file_name'].strip()] = (fnum(r['build_time']), fnum(r['count_time']))
        runs.append(d)
    return runs


def tool_dir(root, tool):
    for name in TOOL_DIR_ALIASES.get(tool, [tool]):
        path = os.path.join(root, name)
        if os.path.isdir(path):
            return path
    return None


def mu_prefix(root, mu):
    for pre in (f'μ={mu}_', f'mu={mu}_'):
        if os.path.isfile(os.path.join(root, 'hyper_parameter', pre + '0.csv')):
            return pre
    return f'μ={mu}_'


def load_fm_from_archive(path):
    if not os.path.isfile(path):
        return set()
    try:
        out = subprocess.check_output(['bsdtar', '-tf', path],
                                      stderr=subprocess.DEVNULL).decode()
    except Exception:
        return set()
    return {os.path.basename(l.strip())[:-4]
            for l in out.splitlines() if l.strip().endswith('.cnf')}


def load_fm_names(rows):
    return {r['benchmark'].strip() for r in rows if r['is_fm'].strip() == '1'}


def offline_ok(bt, ct):
    return 0 <= bt < CUTOFF


def online_ok(method, bt, ct):
    if method in SAT:
        return 0 <= ct < CUTOFF
    return bt >= 0 and ct >= 0 and (bt + ct) < CUTOFF


def ok_of(method, phase, bt, ct):
    return offline_ok(bt, ct) if phase == 'off' else online_ok(method, bt, ct)


def par2(runs, method, bset, phase):
    sucs, p2ts = [], []
    for rd in runs:
        suc, tot, n = 0, 0.0, 0
        for b in sorted(bset):
            if b == MISSING:
                continue
            bt, ct = rd.get(b, (-1.0, -1.0))
            ok = ok_of(method, phase, bt, ct)
            tot += (bt if phase == 'off' else ct) if ok else PENALTY
            suc += ok
            n += 1
        sucs.append(suc)
        p2ts.append(tot / n if n else float('nan'))
    if not sucs:
        return float('nan'), float('nan'), float('nan')
    sd = statistics.stdev(sucs) if len(sucs) > 1 else 0.0
    return statistics.mean(sucs), sd, statistics.mean(p2ts)


def effective_set(data, methods, bset, phase):
    out = set()
    for b in sorted(bset):
        if b == MISSING:
            continue
        if all(all(ok_of(m, phase, *data[m][r].get(b, (-1.0, -1.0)))
                   for r in range(len(data[m]))) for m in methods):
            out.add(b)
    return out


def mean_time(runs, bset, phase):
    idx = 0 if phase == 'off' else 1
    vals = [statistics.mean([rd[b][idx] for rd in runs]) for b in sorted(bset) if b in runs[0]]
    return statistics.mean(vals) if vals else float('nan')


def r1(x):
    return f'{x:,.1f}'


def default_data_dir(script_file):
    """The released data directory, i.e. FastFMC-eval/experimental_results."""
    return os.path.abspath(os.path.join(
        os.path.dirname(os.path.abspath(script_file)), '..', '..', 'experimental_results'))


def load_experiment(data_dir):
    """Per-tool runs, the memory table, the FM names and the (FM, Other) split.

    A benchmark enters the universe when at least one method answered it in at
    least one run; every table is computed over that population.
    """
    data = {}
    for m in ALL_TOOLS:
        d = tool_dir(data_dir, m)
        data[m] = load_timings(d) if d else []
    mem_path = os.path.join(data_dir, 'memory', 'memory_per_benchmark.csv')
    mem = read_csv(mem_path) if os.path.isfile(mem_path) else []
    fm_names = (load_fm_names(mem) if mem
                else load_fm_from_archive(os.path.join(data_dir, 'results', 'cnf.rar')))
    avail = [m for m in ALL_TOOLS if data[m]]
    universe = set()
    for m in avail:
        universe.update(data[m][0])
    universe = {b for b in universe
                if any(online_ok(m, *data[m][r].get(b, (-1.0, -1.0)))
                       for r in range(len(data[m])) for m in avail)}
    fm = universe & fm_names
    return data, mem, fm_names, fm, universe - fm
