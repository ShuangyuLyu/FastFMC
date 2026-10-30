import statistics

from common import fnum


def compute(mem_rows, universe):
    cols = {'FastFMC': 'FastFMC_GB', 'ddnnife': 'ddnnife_GB', 'd4-query': 'd4-query_GB',
            'query-ddnnf': 'query-dnnf_GB', 'Ganak': 'Ganak_GB',
            'SharpSAT': 'sharpSAT_GB', 'countAntom': 'countAntom_GB'}

    have = {c.lower().replace('-', ''): c for c in (mem_rows[0] if mem_rows else {})}
    out = {}
    for cat, keep in (('FM', '1'), ('Other', '0')):
        for m, col in cols.items():
            key = have.get(col.lower().replace('-', ''))
            vals = [fnum(r[key]) for r in mem_rows
                    if key and r.get('is_fm', '').strip() == keep
                    and r.get('benchmark', '').strip() in universe and fnum(r[key]) > 0]
            out[(cat, m)] = statistics.mean(vals) if vals else float('nan')
    return out
