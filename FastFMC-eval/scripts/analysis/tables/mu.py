import os

from common import load_timings, par2


def compute(FM, OTH, data_dir):
    out = {}
    for mu in (1, 5, 10, 30, 50, 100):
        runs = load_timings(os.path.join(data_dir, 'hyper_parameter'), prefix=f'μ={mu}_')
        for cat, bset in (('FM', FM), ('Other', OTH)):
            out[(cat, mu)] = (par2(runs, 'FastFMC', bset, 'off'),
                              par2(runs, 'FastFMC', bset, 'on'))
    return out
