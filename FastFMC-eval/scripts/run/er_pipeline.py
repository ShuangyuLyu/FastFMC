import argparse
import os
import sys

import yaml

from common import find_gtime, load_fm_manifest, log, write_er_csv
from suites import ablation, hyper_parameter, memory
from suites import main as suite_main
from tools import d4query, ddnnife, fastfmc, query_ddnnf, sat

RUNNERS = {'FastFMC': fastfmc.run, 'ddnnife': ddnnife.run,
           'd4-query': d4query.run, 'query-ddnnf': query_ddnnf.run,
           'Ganak': sat.run, 'sharpSAT': sat.run, 'countAntom': sat.run}

SAT = ('Ganak', 'sharpSAT', 'countAntom')

SUITE_ORDER = ['main', 'ablation', 'mu', 'memory']


class Runner:
    def __init__(self, cfg, args):
        self.cfg = cfg
        self.args = args
        self.cut = float(cfg.get('cutoff', 1800))
        self.bench_dir = cfg['benchmarks']
        self.query_dir = cfg['queries']
        self.tools = cfg.get('tools', {})
        self.out = cfg['output']
        self.gtime = find_gtime()
        self.fm = load_fm_manifest(cfg['fm_manifest']) if cfg.get('fm_manifest') else set()

    def benches(self):
        cnfs = [fn[:-4] for fn in sorted(os.listdir(self.bench_dir))
                if fn.endswith('.cnf')
                and os.path.getsize(os.path.join(self.bench_dir, fn)) > 0]
        names = [b for b in cnfs if os.path.isfile(self.config_path(b))]
        missing = len(cnfs) - len(names)
        if missing:
            print(f'  [{len(cnfs)} CNFs, {missing} without a query file '
                  f'in {self.query_dir} -> skipped]')
        if self.args.limit:
            names = names[:self.args.limit]
        return names

    def config_path(self, bench):
        return os.path.join(self.query_dir, bench + '.config')

    def run_tool(self, tool, runs, out_dir, prefix='{r}', variant=None):
        fn = RUNNERS[tool]
        benches = self.benches()
        log('%s: %d benchmarks x %d runs' % (tool, len(benches), runs))
        for run in range(runs):
            out_path = os.path.join(self.out, out_dir,
                                    (prefix.format(r=run) if prefix else '') + str(run) + '.csv')
            if os.path.isfile(out_path) and not self.args.force:
                log('  run %d: exists, skip (%s)' % (run, out_path))
                continue
            rows = {}
            for i, b in enumerate(benches):
                try:
                    if tool == 'FastFMC':
                        res = fn(self, b, variant)
                    elif tool in SAT:
                        res = fn(self, b, tool)
                    else:
                        res = fn(self, b)
                except Exception as e:
                    log('  ERROR %s: %s' % (b, e))
                    res = (-1.0, -1.0)
                if res is None:
                    log('  %s skipped (missing c2d); aborting tool' % tool)
                    return
                rows[b] = res
                if (i + 1) % 50 == 0:
                    log('  run %d: %d/%d' % (run, i + 1, len(benches)))
            write_er_csv(out_path, rows)
            log('  run %d -> %s' % (run, out_path))


def run_one_suite(r, args, suite):
    if suite == 'main':
        suite_main.run(r, args)
    elif suite == 'ablation':
        ablation.run(r, args)
    elif suite == 'mu':
        hyper_parameter.run(r, args)
    elif suite == 'memory':
        memory.run(r, args.runs, args.tools)
    else:
        raise ValueError('unknown suite: %s' % suite)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--config', default='eval.yaml')
    ap.add_argument('--suite', default='main', choices=SUITE_ORDER + ['all'])
    ap.add_argument('--tools', nargs='+', default=None)
    ap.add_argument('--runs', type=int, default=10)
    ap.add_argument('--mu-values', nargs='+', default=[1, 5, 10, 30, 50, 100])
    ap.add_argument('--output', default=None)
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--force', action='store_true')
    args = ap.parse_args()

    with open(args.config) as f:
        cfg = yaml.safe_load(f)
    if args.output:
        cfg['output'] = args.output
    r = Runner(cfg, args)

    suites = SUITE_ORDER if args.suite == 'all' else [args.suite]
    failed = []
    for suite in suites:
        if len(suites) > 1:
            log('================ suite %s ================' % suite)
        try:
            run_one_suite(r, args, suite)
        except Exception as e:
            log('SUITE %s raised: %s' % (suite, e))
            failed.append(suite)
    if failed:
        log('FAILED suites: %s' % ', '.join(failed))
        sys.exit(1)


if __name__ == '__main__':
    main()
