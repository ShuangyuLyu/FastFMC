import os

VALUES = [1, 5, 10, 30, 50, 100]


def run(r, args):
    for mu in (args.mu_values or VALUES):
        r.run_tool('FastFMC', args.runs, 'hyper_parameter',
                   prefix='mu=%s_' % mu,
                   variant={'mu': mu, 'fastfmc_flags': []})
