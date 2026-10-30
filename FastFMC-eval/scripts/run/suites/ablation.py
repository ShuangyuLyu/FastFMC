import os

VARIANTS = {
    'LPE': {'fastfmc_flags': ['--not-use-lpe']},
    'Simp': {'use_coprocessor': False},
    'BHM': {'fastfmc_flags': ['--not-use-bhm']},
    'ZNP': {'fastfmc_flags': ['--not-use-znp']},
}


def run(r, args):
    for name, v in VARIANTS.items():
        r.run_tool('FastFMC', args.runs, 'ablation', prefix=name + '_', variant=v)
