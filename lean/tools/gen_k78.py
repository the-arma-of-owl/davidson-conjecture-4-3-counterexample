# Generates the integer data for Sharp78.lean from the published K=78 witness (untrusted: Lean re-checks).
import json, sys
from fractions import Fraction as Fr
from math import lcm
w = json.load(open(sys.argv[1]))
a = w['f']; tau = w['tau']; s = [Fr(x) for x in w['sigma0']]
assert a == [2,2,1,-1,-2,-1,-1,-1,-2,-1,1,2,2] and len(tau) == 67
for k in range(67):
    c = sum(a[i] * s[i + k] for i in range(12))
    s.append((tau[k] - c) / 2)
assert len(s) == 79 and all(abs(x) <= 1 for x in s)
for k in range(67):
    assert sum(a[i] * s[i + k] for i in range(13)) == tau[k] and tau[k] % 3 == 0 and (tau[k] // 3) % 2 == 1
D = 1
for x in s: D = lcm(D, x.denominator)
N = [int(x * D) for x in s]
m = [(t // 3 - 1) // 2 for t in tau]
assert all(3 * (2 * mm + 1) == t for mm, t in zip(m, tau))
print('max |sigma| =', float(max(abs(x) for x in s)), 'digits of D =', len(str(D)))
with open(sys.argv[2], 'w') as fh:
    fh.write('def D78 : ℤ := %d\n\n' % D)
    fh.write('def N78 : List ℤ := [\n  ' + ',\n  '.join(map(str, N)) + ']\n\n')
    fh.write('def M78 : List ℤ := [' + ', '.join(map(str, m)) + ']\n')
