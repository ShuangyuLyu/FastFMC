from common import ALL_TOOLS, REUSE, par2


def compute(data, FM, OTH, avail=None):
    out = {}
    avail = avail or ALL_TOOLS
    for tag, phase, methods in (('II', 'off', [m for m in REUSE if m in avail]),
                                ('IV', 'on', avail)):
        for cat, bset in (('FM', FM), ('Other', OTH)):
            for m in methods:
                out[(tag, cat, m)] = par2(data[m], m, bset, phase)
    return out
