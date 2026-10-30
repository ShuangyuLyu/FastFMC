import statistics

from common import MISSING, fnum, offline_ok


def compute(base_runs, lpe_runs, bhm_runs, size_rows, FM):
    by = {r['file_name'].strip(): r for r in size_rows}

    col_alias = {'FastFMC_smooth_time': 'FastFMC_time_smooth',
                 'alt1_smooth_time': 'alt1_time_smooth',
                 'alt3_D_number_of_nodes': 'alt2_D_number_of_nodes',
                 'alt3_D_number_of_edges': 'alt2_D_number_of_edges'}

    def cell(row, col):
        if col in row:
            return fnum(row[col])
        alt = col_alias.get(col)
        return fnum(row.get(alt)) if alt else -1.0

    def all10(runs):
        return {b for b in runs[0] if b != MISSING
                and all(offline_ok(*runs[i].get(b, (-1.0, -1.0))) for i in range(len(runs)))}

    S1 = all10(base_runs) & all10(lpe_runs)
    S2 = all10(base_runs) & all10(bhm_runs)
    out = {}
    for cat in ('FM', 'Other'):
        s1 = {b for b in S1 if (b in FM) == (cat == 'FM')}
        s2 = {b for b in S2 if (b in FM) == (cat == 'FM')}

        def mean(col, s):
            vals = [cell(by[b], col) for b in s if b in by and cell(by[b], col) > 0]
            return statistics.mean(vals) if vals else float('nan')

        out[(cat, 'N', 'D0')] = len(s1)
        out[(cat, 'N', 'D')] = len(s2)
        out[(cat, 'smooth', 'FastFMC')] = mean('FastFMC_smooth_time', s1)
        out[(cat, 'smooth', 'alt1')] = mean('alt1_smooth_time', s1)
        for who, block in (('FastFMC', 'D0'), ('alt1', 'D0'),
                           ('FastFMC', 'D'), ('alt3', 'D')):
            for kind in ('node', 'edge'):
                out[(cat, block, who, kind)] = mean(
                    f'{who}_{block}_number_of_{kind}s', s1 if block == 'D0' else s2)
    return out
