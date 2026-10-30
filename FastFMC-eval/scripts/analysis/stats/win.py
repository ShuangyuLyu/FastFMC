import statistics

try:
    from scipy.stats import wilcoxon
except ImportError:
    wilcoxon = None

from common import MISSING
from stats.correction import holm as holm_adjust
from stats.effect import a12
from stats.paired import value


def win_counts(runs, fn_runs, bset, phase, competitors, holm=False):
    """Benchmarks on which FastFMC beats a competitor (p < 0.05, A12 > 0.71).

    With ``holm=True`` the per-benchmark p-values of all competitors are
    corrected together, so every competitor has to be tested before deciding.
    """
    out = {m: 0 for m in competitors}
    for b in bset:
        if b == MISSING:
            continue
        x = [value('FastFMC', rd, b, phase) for rd in fn_runs]
        rows = []
        for m in competitors:
            y = [value(m, rd, b, phase) for rd in runs[m]]
            if not holm and statistics.mean(x) >= statistics.mean(y):
                continue
            rows.append((m, y, 1.0 if x == y else wilcoxon(x, y).pvalue))
        ps = holm_adjust([r[2] for r in rows]) if holm else [r[2] for r in rows]
        for (m, y, _), p in zip(rows, ps):
            if p < 0.05 and statistics.mean(x) < statistics.mean(y) and a12(x, y) > 0.71:
                out[m] += 1
    return out
