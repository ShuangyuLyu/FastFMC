"""Tables II/IV: Holm correction across competitors within each benchmark."""
import argparse
import os

from common import ALL_TOOLS, MISSING, REUSE, default_data_dir, load_experiment
from stats.win import win_counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-dir', default=default_data_dir(__file__))
    D = os.path.abspath(parser.parse_args().data_dir)
    data, _, _, FM, OTH = load_experiment(D)
    FM = {b for b in FM if b != MISSING}
    OTH = {b for b in OTH if b != MISSING}

    for table, phase, competitors in (('II', 'off', REUSE[1:]),
                                      ('IV', 'on', ALL_TOOLS[1:])):
        print(f'=== Table {table}: Holm-corrected #win ===')
        for cat, bset in (('FM', FM), ('Other', OTH)):
            counts = win_counts(data, data['FastFMC'], bset, phase, competitors, holm=True)
            print(f'  [{cat}] n={len(bset)}')
            for m in competitors:
                print(f'      vs {m:12s} #win={counts[m]}')


if __name__ == '__main__':
    main()
