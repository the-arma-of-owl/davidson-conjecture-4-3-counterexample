#!/usr/bin/env python3
# Extras for fB:
#  (1) the deepest nodes of the certified tree and their exact certified ranges of c_67;
#  (2) the rounding 3-colouring of G_78 built from the exact K=78 pair: randomised test of
#      Lambda-invariance (well-definedness on M_78) and properness.
import json, random, math
from fractions import Fraction as Fr
a = [2, 2, 1, -1, -2, -1, -1, -1, -2, -1, 1, 2, 2]; d = 12
nodes = {}
for line in open('data/my_fB_L68.jsonl'):
    e = json.loads(line); nodes[tuple(e['w'])] = e
def bound(g, y, tau):
    r = list(map(Fr, g))
    for k, yk in enumerate(y):
        for i in range(d + 1):
            r[k + i] -= yk * a[i]
    return sum(abs(v) for v in r) + sum(yk * t for yk, t in zip(y, tau))
deep = [w for w in nodes if len(w) == 67]
for w in deep:
    e = nodes[w]; j = 67
    g = [0] * (j + d)
    for i in range(d):
        g[j + i] = a[i]
    ub = bound(g, [Fr(v) for v in e['yu']], w); lb = -bound([-v for v in g], [Fr(v) for v in e['yl']], w)
    print('depth-67 word', ''.join('+' if t > 0 else '-' for t in w), ' |tau|=3 everywhere:', all(abs(t) == 3 for t in w))
    print('   certified range of c_67: [%s, %s] = [%.6f, %.6f]' % (lb, ub, float(lb), float(ub)))
    print('   allowed c-values: union of [t-2,t+2], t in {+-3,+-9,+-15}  -> range lies in a gap:',
          all(not (t - 2 <= ub and t + 2 >= lb) for t in (-15, -9, -3, 3, 9, 15)))
# depth histogram of words using |tau| in {9,15}
big = sum(1 for w in nodes if any(abs(t) > 3 for t in w))
print('nodes whose word uses some |tau| > 3:', big, 'of', len(nodes))
maxd_big = max((len(w) for w in nodes if any(abs(t) > 3 for t in w)), default=0)
print('deepest node whose word uses |tau| > 3:', maxd_big)

# (2) rounding colouring for K = 78
cert = json.load(open('data/fB_K78_feasible_cert.json'))
tau = cert['tau']; s = [Fr(v) for v in cert['sigma0']]
for k, t in enumerate(tau):
    s.append((t - sum(a[i] * s[k + i] for i in range(d))) / 2)
K = len(s) - 1
assert K == 78 and all(abs(v) <= 1 for v in s)
def h(xv):
    H = sum(si * xi for si, xi in zip(s, xv))
    p = sum(xv) % 2
    return 2 * math.floor((H - p + 1) / 2) + p
rng = random.Random(7)
rels = []
for j in range(K - d + 1):
    r = [0] * (K + 1)
    for i in range(d + 1):
        r[i + j] = a[i]
    rels.append(r)
bad_inv = bad_edge = 0
for trial in range(3000):
    xv = [rng.randint(-4, 4) for _ in range(K + 1)]
    yv = list(xv)
    for r in rng.sample(rels, 10):
        m = rng.randint(-3, 3)
        yv = [p + m * q for p, q in zip(yv, r)]
    hx, hy = h(xv), h(yv)
    if (hx - hy) % 3 != 0:
        bad_inv += 1
    n = rng.randrange(K + 1)
    xe = list(xv); xe[n] += 1
    if abs(h(xe) - hx) != 1:
        bad_edge += 1
print(f'(2) K=78 rounding colouring: Lambda-invariance failures {bad_inv}/3000, improper edges {bad_edge}/3000')
