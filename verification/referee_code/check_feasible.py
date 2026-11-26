#!/usr/bin/env python3
# Exact check of a claimed admissible pair (sigma, tau): sigma_0..sigma_{d-1} given, the rest forced.
import sys, json
from fractions import Fraction as Fr

def check(a, tau, sigma0):
    d = len(a) - 1
    s = [Fr(v) for v in sigma0]
    assert len(s) == d
    assert all(abs(v) <= 1 for v in s), 'initial sigma outside [-1,1]'
    assert all(t % 6 == 3 for t in tau), 'tau not odd multiples of 3'
    for k, t in enumerate(tau):
        c = sum(a[i] * s[k + i] for i in range(d))
        s.append((t - c) / a[d])
    for k, t in enumerate(tau):
        assert sum(a[i] * s[k + i] for i in range(d + 1)) == t
    worst = max(abs(v) for v in s)
    return s, worst

if __name__ == '__main__':
    cert = json.load(open(sys.argv[1]))
    a = cert['f']; tau = cert['tau']; s0 = cert['sigma0']
    s, worst = check(a, tau, s0)
    print('equations:', len(tau), ' sigma count:', len(s), ' K =', len(s) - 1)
    print('max |sigma_n| =', float(worst), ' (<= 1:', worst <= 1, ')')
    print('sigma_n with |sigma_n| > 0.999:', [(n, float(v)) for n, v in enumerate(s) if abs(v) > Fr(999, 1000)])
