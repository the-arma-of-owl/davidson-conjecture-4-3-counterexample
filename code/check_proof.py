# Independent exact checker for proofs written by dfs_proof.py (Python fractions only).
#
# Statement checked: there is no sigma in [-1,1]^{LMAX+d} and no tau_0..tau_{LMAX-1} in 3(2Z+1)
# with tau_0 > 0 and  sum_{i=0}^{d} a_i sigma_{i+k} = tau_k  (0 <= k < LMAX).
# Note: |tau_k| <= sum_i |a_i| = ||f||_1 automatically (each |sigma| <= 1), so only tau in T below need be enumerated.
# (By sigma -> -sigma symmetry the same then holds for tau_0 < 0.)
#
# For a word w = (tau_0..tau_{j-1}) let P_w = {x in [-1,1]^d : tau_k - 2 <= c_k(x) <= tau_k + 2, k<j}
# where sigma_n = x_n (n < d), c_k = sum_{i<d} a_i sigma_{i+k}, sigma_{k+d} = (tau_k - c_k)/a_d.
# Certificates:
#   'E' (P_w empty): multipliers y_k with  B - ||A||_1 > sum_k (y_k tau_k + a_d |y_k|),
#        where sum_k y_k c_k(x) = A.x + B.
#   'I' (interval):  ub = sum_k (y_k tau_k + a_d|y_k|) + ||A||_1 + B  with c_j - sum_k y_k c_k = A.x + B,
#        and the same with -c_j for the lower bound; every tau in T whose slab [tau-a_d, tau+a_d]
#        meets [lb, ub] must occur as a child node.
import sys, json
from fractions import Fraction as Fr

def main(a, LMAX, path):
    d = len(a) - 1; ad = a[-1]
    assert ad >= 1
    L1 = sum(abs(x) for x in a)
    T = [t for t in range(-L1, L1 + 1) if t % 3 == 0 and (t // 3) % 2 != 0]
    nodes = {}
    order = []
    for line in open(path):
        e = json.loads(line)
        key = tuple(e['w'])
        assert key not in nodes, 'duplicate node'
        nodes[key] = e; order.append(key)
    assert () in nodes, 'root missing'
    # recompute affine forms along a DFS stack
    I = [[Fr(int(i == j)) for j in range(d)] for i in range(d)]
    # stack of (key, window, row) along the current root path (file is in DFS preorder)
    stack = [((), [(I[i], Fr(0)) for i in range(d)], None)]
    stats = dict(I=0, E=0, maxdepth=0)
    for key in order:
        e = nodes[key]
        j = len(key)
        stats['maxdepth'] = max(stats['maxdepth'], j)
        if key != ():
            while stack[-1][0] != key[:-1]:
                stack.pop()
                assert stack, f'parent of {key} not on DFS path (file not in preorder?)'
            pwin = stack[-1][1]
            cc = [sum(a[i] * pwin[i][0][k] for i in range(d)) for k in range(d)]
            ck = sum(a[i] * pwin[i][1] for i in range(d))
            tau = Fr(key[-1])
            stack.append((key, pwin[1:] + [([-v / ad for v in cc], (tau - ck) / ad)], (cc, ck, tau)))
        win = stack[-1][1]
        rws = [s[2] for s in stack[1:]]
        if e['t'] == 'FAIL':
            raise SystemExit(f'FAIL entry at {key}')
        if e['t'] == 'E':
            y = {int(k): Fr(v) for k, v in e['y'].items()}
            A = [Fr(0)] * d; B = Fr(0); beta = Fr(0)
            for k, yk in y.items():
                assert 0 <= k < j, f'bad multiplier index {k} at {key}'
                cc, ckk, tau = rws[k]
                beta += yk * tau + ad * abs(yk)
                for i in range(d):
                    A[i] += yk * cc[i]
                B += yk * ckk
            assert B - sum(abs(t) for t in A) > beta, f'bad emptiness certificate at {key}'
            stats['E'] += 1
        else:
            assert e['t'] == 'I'
            assert j < LMAX, f'node at depth {j} >= LMAX not certified empty: {key}'
            cj = [sum(a[i] * win[i][0][k] for i in range(d)) for k in range(d)]
            ckj = sum(a[i] * win[i][1] for i in range(d))
            def ub(c, c0, ydict):
                y = {int(k): Fr(v) for k, v in ydict.items()}
                A = list(c); B = Fr(c0); tot = Fr(0)
                for k, yk in y.items():
                    assert 0 <= k < j, f'bad multiplier index {k} at {key}'
                    cc, ckk, tau = rws[k]
                    tot += yk * tau + ad * abs(yk)
                    for i in range(d):
                        A[i] -= yk * cc[i]
                    B -= yk * ckk
                return tot + sum(abs(t) for t in A) + B
            hi = ub(cj, ckj, e['yu'])
            lo = -ub([-t for t in cj], -ckj, e['yl'])
            for t in T:
                if j == 0 and t < 0:
                    continue
                if t + ad < lo or t - ad > hi:
                    continue
                child = key + (t,)
                assert child in nodes, f'missing child {child}'
            stats['I'] += 1
        # free memory of finished subtrees is not attempted (fits in RAM for this size)
    print('proof OK:', stats, 'nodes', len(nodes))
    print(f'=> no valid word of length {LMAX} with tau_0 > 0 exists')

if __name__ == '__main__':
    main(json.loads(sys.argv[1]), int(sys.argv[2]), sys.argv[3])
