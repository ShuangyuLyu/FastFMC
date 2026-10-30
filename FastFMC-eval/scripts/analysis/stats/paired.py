import statistics

try:
    from scipy.stats import wilcoxon
except ImportError:
    wilcoxon = None

from common import PENALTY, ok_of
from stats.effect import a12


def value(method, rd, bench, phase):
    bt, ct = rd.get(bench, (-1.0, -1.0))
    if not ok_of(method, phase, bt, ct):
        return PENALTY
    return bt if phase == 'off' else ct

def per_benchmark_mean(runs, method, bset, phase):
    return [statistics.mean([value(method, rd, b, phase) for rd in runs]) for b in bset]

def set_level(x, y):
    if len(x) < 3:
        return float('nan'), len(x), float('nan')
    ties = sum(1 for a, b in zip(x, y) if a == b)
    p = wilcoxon(x, y).pvalue
    return p, len(x) - ties, a12(x, y)
