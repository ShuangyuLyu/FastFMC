import os
import statistics
import sys

from common import (ALL_TOOLS, EFF, default_data_dir, effective_set,
                    load_experiment, load_timings, mu_prefix)
from stats.correction import holm
from stats.paired import per_benchmark_mean, set_level
from stats.win import win_counts

COMPETITORS = ['ddnnife', 'd4-query', 'query-ddnnf', 'Ganak', 'SharpSAT', 'countAntom']


def main():
    argv = sys.argv[1:]
    data_dir = default_data_dir(__file__)
    if '--data-dir' in argv:
        i = argv.index('--data-dir')
        data_dir = os.path.abspath(argv[i + 1])
        del argv[i:i + 2]
        sys.argv = [sys.argv[0]] + argv
    D = data_dir
    print(f'data directory: {D}')
    data, mem, fm_names, FM, OTH = load_experiment(D)
    absent = [m for m in ALL_TOOLS if not data[m]]
    if absent:
        print('WARNING: no data for ' + ', '.join(absent) + ' (skipped)')
    hp = os.path.join(D, 'hyper_parameter')
    mu10 = load_timings(hp, prefix=mu_prefix(D, 10)) if os.path.isdir(hp) else []
    ab = os.path.join(D, 'ablation')
    alt = {k: load_timings(ab, prefix=f'{k}_') for k in ('LPE', 'Simp', 'BHM', 'ZNP')} \
        if os.path.isdir(ab) else {}

    print('=== Table IV : online phase, entire benchmark set ===')
    for cat, bset in (('FM', FM), ('Other', OTH)):
        rows = []
        for m in [c for c in COMPETITORS if data.get(c)]:
            x = per_benchmark_mean(data['FastFMC'], 'FastFMC', bset, 'on')
            y = per_benchmark_mean(data[m], m, bset, 'on')
            if not x or not y:
                continue
            p, nun, a = set_level(x, y)
            rows.append([m, statistics.mean(y) - statistics.mean(x), p, nun, a])
        if not rows:
            print(f'  [{cat}] no data, skipped')
            continue
        adj = holm([r[2] for r in rows])
        print(f'  [{cat}] n_set={len(bset)}')
        for r, pa in zip(rows, adj):
            print(f'      vs {r[0]:12s} diff +{r[1]:8.1f} s  raw p={r[2]:.3e}  '
                  f'n_pairs={r[3]:5d}  A12={r[4]:.3f}  Holm p={pa:.3e}')

    print('\n=== Table V : online phase, effective intersection set ===')
    for cat, bset in ((('FM', FM), ('Other', OTH)) if all(data.get(m) for m in EFF) else ()):
        common_set = effective_set(data, EFF, bset, 'on')
        rows = []
        for m in ('ddnnife', 'd4-query'):
            x = per_benchmark_mean(data['FastFMC'], 'FastFMC', common_set, 'on')
            y = per_benchmark_mean(data[m], m, common_set, 'on')
            if not x or not y:
                continue
            p, nun, a = set_level(x, y)
            rows.append([m, statistics.mean(y) - statistics.mean(x), p, nun, a])
        if not rows:
            print(f'  [{cat}] no data, skipped')
            continue
        adj = holm([r[2] for r in rows])
        for r, pa in zip(rows, adj):
            print(f'  [{cat}] n_eff={len(common_set)}  vs {r[0]:9s} diff +{r[1]:6.2f} s  '
                  f'raw p={r[2]:.3e}  n_pairs={r[3]:5d}  A12={r[4]:.3f}  Holm p={pa:.3e}')

    print('\n=== Table VI : ablation, online phase, entire benchmark set ===')
    for cat, bset in ((('FM', FM), ('Other', OTH)) if data['FastFMC'] and alt else ()):
        rows = []
        for k in ('LPE', 'Simp', 'BHM', 'ZNP'):
            x = per_benchmark_mean(data['FastFMC'], 'FastFMC', bset, 'on')
            y = per_benchmark_mean(alt.get(k, []), 'FastFMC', bset, 'on')
            if not x or not y:
                continue
            p, nun, a = set_level(x, y)
            rows.append([k, statistics.mean(y) - statistics.mean(x), p, nun, a])
        if not rows:
            print(f'  [{cat}] no data, skipped')
            continue
        adj = holm([r[2] for r in rows])
        for r, pa in zip(rows, adj):
            print(f'  [{cat}] vs {r[0]:5s} diff +{r[1]:7.2f} s  raw p={r[2]:.3e}  '
                  f'n_pairs={r[3]:5d}  Holm p={pa:.3e}')

    print('\n=== #win (per-benchmark, ten paired runs, no correction) ===')
    for phase, tag, comps in (('off', 'Table II  #win_off', COMPETITORS[:3]),
                              ('on', 'Table IV  #win_on', COMPETITORS)):
        comps = [c for c in comps if data.get(c)]
        for cat, bset in (('FM', FM), ('Other', OTH)):
            w = win_counts(data, data['FastFMC'], bset, phase, comps)
            print(f'  {tag} [{cat:5s}] ' +
                  '  '.join(f'{m}={v}' for m, v in w.items()))


if __name__ == '__main__':
    main()
