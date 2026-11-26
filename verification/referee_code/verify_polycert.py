#!/usr/bin/env python3
# Exact verifier for the referee's polynomial-multiplier certificates (output of my_dfs_glpk.py).
# Node w=(t_0..t_{j-1}).  Any admissible (s,t) with prefix w satisfies, for every rational y in Q^j,
#     c_j(s) = g.s <= y.t + ||g - y*f||_1 ,   g = x^j (f - a_d x^d),  (y*f)_n = sum_k y_k a_{n-k},
# because g.s = (g - y*f).s + sum_k y_k (sum_i a_i s_{k+i}) and |s_n| <= 1.
# Emptiness: y.t > ||y*f||_1 is impossible for admissible s.
import sys, json
from fractions import Fraction as Fr

def main(a, L, path, sym=True):
    d = len(a) - 1; ad = a[d]
    S1 = sum(abs(c) for c in a)
    T = [t for t in range(-S1, S1 + 1) if t % 6 == 3]
    nodes = {}
    for line in open(path):
        e = json.loads(line)
        k = tuple(e['w'])
        assert k not in nodes
        nodes[k] = e
    def bound(g, y, tau):
        r = list(map(Fr, g))
        for k, yk in enumerate(y):
            for i in range(d + 1):
                r[k + i] -= yk * a[i]
        return sum(abs(v) for v in r) + sum(yk * t for yk, t in zip(y, tau))
    todo = [()]
    seen = 0; I = E = 0; maxd = 0
    while todo:
        w = todo.pop()
        if w not in nodes:
            raise SystemExit(f'missing node {w}')
        e = nodes[w]; j = len(w); seen += 1; maxd = max(maxd, j)
        if e['t'] == 'E':
            y = [Fr(v) for v in e['y']]
            assert len(y) == j
            r = [Fr(0)] * (j + d)
            for k, yk in enumerate(y):
                for i in range(d + 1):
                    r[k + i] += yk * a[i]
            if not (sum(yk * t for yk, t in zip(y, w)) > sum(abs(v) for v in r)):
                raise SystemExit(f'bad emptiness certificate at {w}')
            E += 1
            continue
        if e['t'] != 'I':
            raise SystemExit(f'node {w} is {e["t"]}')
        if j >= L:
            raise SystemExit(f'I node at depth {j} >= {L}')
        yu = [Fr(v) for v in e['yu']]; yl = [Fr(v) for v in e['yl']]
        assert len(yu) == j and len(yl) == j
        g = [0] * (j + d)
        for i in range(d):
            g[j + i] = a[i]
        ub = bound(g, yu, w)
        lb = -bound([-v for v in g], yl, w)
        I += 1
        for t in T:
            if sym and j == 0 and t < 0:
                continue
            if t + ad < lb or t - ad > ub:
                continue
            todo.append(w + (t,))
    print(f'PASS: {seen} required nodes verified (I={I}, E={E}), maxdepth={maxd}, file nodes={len(nodes)}, '
          f'unreferenced={len(nodes)-seen}; => no admissible word of length {L}' + (' with t_0>0' if sym else ''))

if __name__ == '__main__':
    a = json.loads(sys.argv[1]); L = int(sys.argv[2])
    main(a, L, sys.argv[3], sym=(len(sys.argv) <= 4 or sys.argv[4] != 'nosym'))
