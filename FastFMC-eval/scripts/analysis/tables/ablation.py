import os

from common import ALT, load_timings, par2


def compute(base_runs, FM, OTH, data_dir):
    out = {}
    variants = {'FastFMC': base_runs}
    for name, prefix in ALT[1:]:
        variants[name] = load_timings(os.path.join(data_dir, 'ablation'), prefix=f'{prefix}_')
    for cat, bset in (('FM', FM), ('Other', OTH)):
        for name, runs in variants.items():
            out[(cat, name)] = (par2(runs, 'FastFMC', bset, 'off'),
                                par2(runs, 'FastFMC', bset, 'on'))
    return out, variants
