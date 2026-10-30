


def a12(x, y):
    if not x or not y:
        return float('nan')
    s = sum((1.0 if a < b else 0.5 if a == b else 0.0) for a in x for b in y)
    return s / (len(x) * len(y))
