


def holm(ps):
    order = sorted(range(len(ps)), key=lambda i: ps[i])
    adj = [0.0] * len(ps)
    prev = 0.0
    for rank, i in enumerate(order):
        prev = max(prev, min(1.0, (len(ps) - rank) * ps[i]))
        adj[i] = prev
    return adj
