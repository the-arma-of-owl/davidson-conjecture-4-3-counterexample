#!/usr/bin/env python3
# Referee's own exact checker for the tau-prefix search tree (format of runs/proof_fB_L68.jsonl).
# Written independently of check_proof.py: integer arithmetic with explicit power-of-two
# denominators, explicit traversal from the root through *required* children only.
#
# Statement certified (if the check passes):
#   there are no reals s_0..s_{L+d-1} in [-1,1] and integers t_0..t_{L-1}, all odd multiples of 3,
#   with t_0 > 0 and sum_{i=0}^{d} a_i s_{i+k} = t_k for 0 <= k < L.
# Variables: x = (s_0..s_{d-1}) in [-1,1]^d.  For n >= d, s_n is the affine function
#   s_n = (t_{n-d} - sum_{i<d} a_i s_{n-d+i}) / a_d,  with a_d = 2 here,
# and the node w = (t_0..t_{j-1}) stands for P_w = { x in [-1,1]^d : |s_n(x)| <= 1 for d <= n < d+j }.
import sys, json, time
from fractions import Fraction as Fr
from math import gcd

def lcm(a, b):
    return a // gcd(a, b) * b

def main(a, L, path, verbose=True):
    d = len(a) - 1
    ad = a[d]
    assert ad == 2, 'this checker assumes leading coefficient 2 (power-of-two denominators)'
    S1 = sum(abs(c) for c in a)
    # admissible tau values: odd multiples of 3 with |tau| <= sum|a_i| (|tau_k| <= sum|a_i||s| <= S1)
    T = [t for t in range(-S1, S1 + 1) if t % 6 == 3]
    t0 = time.time()
    nodes = {}
    nlines = 0
    with open(path) as fh:
        for line in fh:
            nlines += 1
            e = json.loads(line)
            key = tuple(int(v) for v in e['w'])
            if key in nodes:
                raise SystemExit(f'duplicate node {key}')
            typ = e['t']
            if typ == 'E':
                cert = ('E', {int(k): Fr(v) for k, v in e['y'].items()})
            elif typ == 'I':
                cert = ('I', {int(k): Fr(v) for k, v in e['yu'].items()},
                        {int(k): Fr(v) for k, v in e['yl'].items()})
            else:
                raise SystemExit(f'node {key} has type {typ!r}')
            nodes[key] = cert
    if verbose:
        print(f'loaded {nlines} lines, {len(nodes)} distinct nodes in {time.time()-t0:.1f}s', flush=True)
    if () not in nodes:
        raise SystemExit('root missing')

    # s_n represented as (vec of d ints, const int, exponent e) meaning (vec.x + const)/2^e
    base = [([int(i == n) for i in range(d)], 0, 0) for n in range(d)]

    def c_form(s, k):
        """c_k = sum_{i<d} a_i s_{k+i} as (vec, const, e)."""
        e = max(s[k + i][2] for i in range(d))
        vec = [0] * d; const = 0
        for i in range(d):
            v, c0, ei = s[k + i]
            m = a[i] << (e - ei)
            if m:
                for q in range(d):
                    vec[q] += m * v[q]
                const += m * c0
        return vec, const, e

    def combo(s, mult, cw):
        """Return (vec, const, den) with  sum_k y_k c_k(x) = (vec.x+const)/den  and
           beta = sum_k (y_k t_k + ad|y_k|) as Fraction; cw = list of c_k forms; also check t."""
        den = 1
        for y in mult.values():
            den = lcm(den, y.denominator)
        E = max([cw[k][2] for k in mult] + [0])
        vec = [0] * d; const = 0
        for k, y in mult.items():
            Y = y.numerator * (den // y.denominator)            # integer = y*den
            v, c0, e = cw[k]
            m = Y << (E - e)
            for q in range(d):
                vec[q] += m * v[q]
            const += m * c0
        return vec, const, den << E

    stats = dict(I=0, E=0, maxdepth=0, depth_hist={})
    visited = set()
    # explicit DFS: stack of (key, s-list, c-forms list)
    stack = [((), base, [])]
    while stack:
        key, s, cw = stack.pop()
        j = len(key)
        visited.add(key)
        stats['maxdepth'] = max(stats['maxdepth'], j)
        stats['depth_hist'][j] = stats['depth_hist'].get(j, 0) + 1
        cert = nodes[key]
        for mult in cert[1:]:
            for k in mult:
                if not (0 <= k < j):
                    raise SystemExit(f'multiplier index {k} out of range at {key}')
        tau = key  # tau_k = key[k]
        if cert[0] == 'E':
            mult = cert[1]
            vec, const, den = combo(s, mult, cw)
            # beta*den
            beta_num = 0
            for k, y in mult.items():
                beta_num += (y * tau[k] + ad * abs(y)) * den
            assert beta_num.denominator == 1
            beta_num = beta_num.numerator
            # min over cube of (vec.x+const) is const - sum|vec|; need > beta*den
            if not (const - sum(abs(v) for v in vec) > beta_num):
                raise SystemExit(f'emptiness certificate invalid at {key}')
            stats['E'] += 1
            continue
        # interval node
        if j >= L:
            raise SystemExit(f'interval node at depth {j} >= L at {key}')
        cj = c_form(s, j)
        def upper(sign, mult):
            # bound for sign*c_j:  sign*c_j - sum y_k c_k = A.x + B  ->  <= sum|A|+B + sum(y t + ad|y|)
            vec, const, den = combo(s, mult, cw)
            v1, c1, e1 = cj
            # bring sign*c_j to denominator den (den is den0*2^E, need >= 2^e1)
            # common denominator D = lcm(den, 2^e1)
            D = lcm(den, 1 << e1)
            m1 = D // (1 << e1); m2 = D // den
            A = [sign * m1 * v1[q] - m2 * vec[q] for q in range(d)]
            B = sign * m1 * c1 - m2 * const
            tot = Fr(0)
            for k, y in mult.items():
                tot += y * tau[k] + ad * abs(y)
            return Fr(sum(abs(t) for t in A) + B, D) + tot
        ub = upper(1, cert[1])
        lb = -upper(-1, cert[2])
        stats['I'] += 1
        # the new s_{j+d} for child t:  s_{j+d} = (t - c_j)/ad
        v1, c1, e1 = cj
        for t in T:
            if j == 0 and t < 0:
                continue                       # symmetry (s,t) -> (-s,-t)
            if t + ad < lb or t - ad > ub:     # slab [t-ad,t+ad] misses [lb,ub]
                continue
            child = key + (t,)
            if child not in nodes:
                raise SystemExit(f'missing required child {child}')
            # s_new = (t*2^e1 - (v1.x + c1)) / 2^(e1+1)
            snew = ([-v for v in v1], (t << e1) - c1, e1 + 1)
            s2 = s + [snew]
            # consistency: c_j recomputed via s_new must equal t - 2*s_new
            cw2 = cw + [cj]
            stack.append((child, s2, cw2))
    extra = len(nodes) - len(visited)
    if verbose:
        print('PASS: every required node present and certified;', 'I =', stats['I'], 'E =', stats['E'],
              'maxdepth =', stats['maxdepth'], 'unreferenced extra nodes =', extra,
              f'time {time.time()-t0:.1f}s')
        print('depth histogram:', dict(sorted(stats['depth_hist'].items())))
        print(f'=> no admissible (sigma,tau) with {L} equations (K = {L+d-1}) and tau_0 > 0; by symmetry none at all.')
    return stats, extra

if __name__ == '__main__':
    a = json.loads(sys.argv[1]); L = int(sys.argv[2]); path = sys.argv[3]
    main(a, L, path)
