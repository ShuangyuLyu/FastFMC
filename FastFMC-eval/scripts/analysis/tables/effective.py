from common import EFF, effective_set, mean_time


def compute(data, FM, OTH):
    out = {}
    for tag, phase in (('III', 'off'), ('V', 'on')):
        for cat, bset in (('FM', FM), ('Other', OTH)):
            common = effective_set(data, EFF, bset, phase)
            for m in EFF:
                out[(tag, cat, m)] = (len(common), mean_time(data[m], common, phase))
    return out
