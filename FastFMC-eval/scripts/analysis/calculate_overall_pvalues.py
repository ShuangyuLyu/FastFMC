"""Tables IV/V: overall paired Wilcoxon tests with Holm correction."""
import argparse
import os

from common import ALL_TOOLS, EFF, MISSING, default_data_dir, effective_set, load_experiment
from stats.correction import holm
from stats.paired import per_benchmark_mean, set_level


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-dir', default=default_data_dir(__file__))
    D = os.path.abspath(parser.parse_args().data_dir)
    data, _, _, FM, OTH = load_experiment(D)

    for table, competitors in (('IV', ALL_TOOLS[1:]), ('V', EFF[1:])):
        print(f'=== Table {table}: overall online p-values ===')
        for cat, bset in (('FM', FM), ('Other', OTH)):
            bset = {b for b in bset if b != MISSING}
            if table == 'V':
                bset = effective_set(data, EFF, bset, 'on')
            names = sorted(bset)
            x = per_benchmark_mean(data['FastFMC'], 'FastFMC', names, 'on')
            rows = []
            for m in competitors:
                y = per_benchmark_mean(data[m], m, names, 'on')
                p = 1.0 if x == y else set_level(x, y)[0]
                rows.append((m, p))

            # One family per table and FM/Other group, across competitors.
            adjusted = holm([r[1] for r in rows])
            print(f'  [{cat}] n={len(names)}')
            for (m, p), pa in zip(rows, adjusted):
                print(f'      vs {m:12s} raw p={p:.10e}  Holm p={pa:.10e}')


if __name__ == '__main__':
    main()
