import os
import sys

from common import (ALL_TOOLS, ALT, EFF, REUSE, default_data_dir,
                    load_experiment, load_timings, mu_prefix, r1, read_csv)
from tables import ablation, effective, memory, mu, size, sota


def main():
    argv = sys.argv[1:]
    data_dir = default_data_dir(__file__)
    if '--data-dir' in argv:
        i = argv.index('--data-dir')
        data_dir = os.path.abspath(argv[i + 1])
        del argv[i:i + 2]
        sys.argv = [sys.argv[0]] + argv
    print(f'data directory: {data_dir}')
    data, mem_rows, fm_names, FM, OTH = load_experiment(data_dir)
    absent = [m for m in ALL_TOOLS if not data[m]]
    if absent:
        print('WARNING: no data for ' + ', '.join(absent) + ' (skipped)')
    avail = [m for m in ALL_TOOLS if data[m]]
    size_path = os.path.join(
        data_dir, 'size', 'Results_of_FastFMC_and_its_alternative_versions_d-DNNF_size_all.csv')
    size_rows = read_csv(size_path) if os.path.isfile(size_path) else []
    if not mem_rows:
        print('NOTE: memory/ absent, feature-model list taken from results/cnf.rar '
              f'({len(fm_names)} models)')

    universe = FM | OTH
    print(f'benchmarks: {len(universe)}  (feature model {len(FM)}, other {len(OTH)})')

    t24 = sota.compute(data, FM, OTH, avail)
    t35 = effective.compute(data, FM, OTH) if all(m in avail for m in EFF) else None
    hp = os.path.join(data_dir, 'hyper_parameter')
    mu10_runs = load_timings(hp, prefix=mu_prefix(data_dir, 10)) if os.path.isdir(hp) else []
    t6, alt_runs = (ablation.compute(data['FastFMC'], FM, OTH, data_dir) if data['FastFMC']
                    and os.path.isdir(os.path.join(data_dir, 'ablation')) else ({}, {}))
    t7 = (size.compute(mu10_runs,
                       load_timings(os.path.join(data_dir, 'ablation'), prefix='LPE_'),
                       load_timings(os.path.join(data_dir, 'ablation'), prefix='BHM_'),
                       size_rows, FM) if mu10_runs and size_rows else {})
    t8 = mu.compute(FM, OTH, data_dir) if os.path.isdir(hp) else {}
    t9 = memory.compute(mem_rows, universe)

    print('\n=== Table II : offline #suc + PAR-2 ===')
    for cat in ('FM', 'Other'):
        print(f'  [{cat}]')
        for m in [x for x in REUSE if ('II', cat, x) in t24]:
            s, sd, p = t24[('II', cat, m)]
            print(f'      {m:12s} #suc {r1(s)} +- {sd:.1f}   P2T {p:9.1f}')

    print('\n=== Table III : offline average time on the effective set ===')
    if not t35:
        print('  skipped (need FastFMC, ddnnife and d4-query)')
    for cat in (('FM', 'Other') if t35 else ()):
        n = t35[('III', cat, 'FastFMC')][0]
        print(f'  [{cat}] #suc_eff={n}')
        for m in EFF:
            print(f'      {m:12s} {t35[("III", cat, m)][1]:8.2f}')

    print('\n=== Table IV : online #suc + PAR-2 ===')
    for cat in ('FM', 'Other'):
        print(f'  [{cat}]')
        for m in [x for x in ALL_TOOLS if ('IV', cat, x) in t24]:
            s, sd, p = t24[('IV', cat, m)]
            print(f'      {m:12s} #suc {r1(s)} +- {sd:.1f}   P2T {p:9.1f}')

    print('\n=== Table V : online average time on the effective set ===')
    if not t35:
        print('  skipped')
    for cat in (('FM', 'Other') if t35 else ()):
        n = t35[('V', cat, 'FastFMC')][0]
        print(f'  [{cat}] #suc_eff={n}')
        for m in EFF:
            print(f'      {m:12s} {t35[("V", cat, m)][1]:8.2f}')

    print('\n=== Table VI : ablation ===')
    if not t6:
        print('  skipped (needs hyper_parameter/ and ablation/)')
    for cat in (('FM', 'Other') if t6 else ()):
        print(f'  [{cat}]')
        for name, _ in ALT:
            if (cat, name) not in t6:
                continue
            (so, sdo, po), (sn, sdn, pn) = t6[(cat, name)]
            print(f'      {name:8s} off {r1(so):>8s} +- {sdo:4.1f} / {po:7.1f}   '
                  f'on {r1(sn):>8s} +- {sdn:4.1f} / {pn:7.1f}')

    print('\n=== Table VII : d-DNNF size / smoothing time ===')
    if not t7:
        print('  skipped (needs size/ and hyper_parameter/)')
    for cat in (('FM', 'Other') if t7 else ()):
        print(f'  [{cat}] #suc_eff(D0)={t7[(cat, "N", "D0")]}  '
              f'#suc_eff(D)={t7[(cat, "N", "D")]}')
        print('      time_smooth  FastFMC {:10.2f}   alt1 {:10.2f}'.format(
            t7[(cat, 'smooth', 'FastFMC')], t7[(cat, 'smooth', 'alt1')]))
        for block, who in (('D0', 'FastFMC'), ('D0', 'alt1'),
                           ('D', 'FastFMC'), ('D', 'alt3')):
            print(f'      {block:2s} {who:8s} #node {t7[(cat, block, who, "node")]:12,.0f}   '
                  f'#edge {t7[(cat, block, who, "edge")]:14,.0f}')

    print('\n=== Table VIII : hyper-parameter mu ===')
    if not t8:
        print('  skipped (needs hyper_parameter/)')
    for cat in (('FM', 'Other') if t8 else ()):
        print(f'  [{cat}]')
        for mu_v in (1, 5, 10, 30, 50, 100):
            if (cat, mu_v) not in t8:
                continue
            (so, sdo, po), (sn, sdn, pn) = t8[(cat, mu_v)]
            print(f'      mu={mu_v:<4d} off {r1(so):>8s} +- {sdo:4.1f} / {po:7.1f}   '
                  f'on {r1(sn):>8s} +- {sdn:4.1f} / {pn:7.1f}')

    print('\n=== Table IX : average peak RSS (GB) ===')
    for cat in ('FM', 'Other'):
        cells = []
        for m in [x for x in ALL_TOOLS if (cat, x) in t9]:
            cells.append(f'{m}={t9[(cat, m)]:.2f}')
        print(f'  [{cat}] ' + '  '.join(cells))


if __name__ == '__main__':
    main()
