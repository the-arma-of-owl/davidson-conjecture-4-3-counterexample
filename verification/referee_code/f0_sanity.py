#!/usr/bin/env python3
# Sanity check of the criterion on the paper's monic sextic f0 = x^6 - x^4 - x^3 - x^2 + 1.
#  (1) exact admissible (sigma,tau) for K = 11  -> explicit 3-colouring of G_11 by the rounding construction,
#      verified on the 830-vertex sumset with all edges +-alpha^k, k <= 11, and on a large random sample.
#  (2) the paper's 24-vertex witness: edges use exponents <= 12, not 3-colourable (own backtracking),
#      and its exponent<=11 part is 3-colourable (so exponent 12 is really needed).
#  (3) the 830-vertex sumset graph: 3-colourable with exponents <= 11, not with <= 12 (pysat / CaDiCaL).
import csv, json, random, itertools, sys
from fractions import Fraction as Fr
from pysat.solvers import Cadical153, Glucose4

a = [1, 0, -1, -1, -1, 0, 1]          # f0, a_0..a_6
d = 6

def mul_alpha(v):
    # v = coefficients c_0..c_5 in basis 1..alpha^5 ; alpha^6 = -1 + alpha^2 + alpha^3 + alpha^4
    c0, c1, c2, c3, c4, c5 = v
    return (-c5, c0, c1 + c5, c2 + c5, c3 + c5, c4)

def power_vecs(K):
    p = [(1, 0, 0, 0, 0, 0)]
    for _ in range(K):
        p.append(mul_alpha(p[-1]))
    return p

# ---------- (1) exact admissible pair for K = 11 (from SCIP exact; re-verified here) ----------
sigma = [1, -1, 1, -1, -1, -1, 1, 1, 1, -1, 1, -1]
tau = [3, 3, 3, -3, -3, -3]
K = 11
assert len(sigma) == K + 1 and all(abs(s) <= 1 for s in sigma)
for j, t in enumerate(tau):
    assert sum(a[i] * sigma[i + j] for i in range(d + 1)) == t and t % 6 == 3
print('(1) admissible pair for K=11 verified: sigma =', sigma, 'tau =', tau)

# Rounding construction.  A vertex is v in Z[alpha]; pick ANY integer vector x in Z^{K+1} with
# sum x_n alpha^n = v; h(x) = nearest integer of parity p(x)=sum x_n mod 2 to H(x) = sigma.x (ties up);
# colour = h mod 3.  Well-definedness (independence of x) is the theorem; we TEST it below.
def r_par(t, p):
    # nearest element of 2Z+p to t, ties broken upward  ( = 2*floor((t-p+1)/2) + p )
    t = Fr(t)
    q = (t - p + 1) / 2
    import math
    return 2 * math.floor(q) + p

def colour_of_rep(x):
    H = sum(s * xi for s, xi in zip(sigma, x))
    p = sum(x) % 2
    return r_par(H, p) % 3

P = power_vecs(60)
basisK = P[:K + 1]
def vec_of(x):
    return tuple(sum(xi * P[n][q] for n, xi in enumerate(x)) for q in range(6))

# test well-definedness: x and x + (random combination of x^j f0, j<=K-6) give the same colour
rng = random.Random(1)
rel = []
for j in range(K - d + 1):
    r = [0] * (K + 1)
    for i in range(d + 1):
        r[i + j] = a[i]
    rel.append(r)
for trial in range(20000):
    x = [rng.randint(-6, 6) for _ in range(K + 1)]
    y = list(x)
    for r in rel:
        m = rng.randint(-5, 5)
        y = [yi + m * ri for yi, ri in zip(y, r)]
    assert vec_of(x) == vec_of(y)
    assert colour_of_rep(x) == colour_of_rep(y), 'colouring not well defined!'
print('(1) colour independent of representative on 20000 random (x, x+relation) pairs')

# canonical representative for a vertex v in Z[alpha] = M_5 (basis 1..alpha^5): x = (v, 0, ..., 0)
def colour(v):
    return colour_of_rep(list(v) + [0] * (K + 1 - 6))

# sumset B = {0,1}+{0,alpha}+...+{0,alpha^9} reduced mod f0
B = set()
for bits in itertools.product([0, 1], repeat=10):
    v = (0,) * 6
    for n, b in enumerate(bits):
        if b:
            v = tuple(p + q for p, q in zip(v, P[n]))
    B.add(v)
B = sorted(B)
print('(1) sumset size', len(B))
idx = {v: i for i, v in enumerate(B)}
def edges_upto(V, k):
    dirs = {}
    for n in range(k + 1):
        dirs[P[n]] = n
        dirs[tuple(-c for c in P[n])] = n
    E = []
    Vs = set(V)
    for v in V:
        for dv in dirs:
            w = tuple(p + q for p, q in zip(v, dv))
            if w in Vs and v < w:
                E.append((v, w, dirs[dv]))
    return E
E11 = edges_upto(B, 11); E12 = edges_upto(B, 12); E14 = edges_upto(B, 14)
print('(1) sumset edges with exponents <=11, <=12, <=14:', len(E11), len(E12), len(E14))
bad = [(v, w) for v, w, n in E11 if colour(v) == colour(w)]
print('(1) rounding 3-colouring proper on sumset/exp<=11:', not bad, ' monochromatic edges:', len(bad))
# random big test on G_11: random vertices and all 24 neighbours
bad = 0
for trial in range(20000):
    v = tuple(rng.randint(-50, 50) for _ in range(6))
    cv = colour(v)
    for n in range(K + 1):
        for sgn in (1, -1):
            w = tuple(p + sgn * q for p, q in zip(v, P[n]))
            if colour(w) == cv:
                bad += 1
print('(1) random test on G_11 (20000 vertices x 24 neighbours): monochromatic edges =', bad)
# the same colouring necessarily fails on some exponent-12 edge of the sumset
bad12 = [(v, w) for v, w, n in E12 if n == 12 and colour(v) == colour(w)]
print('(1) monochromatic exponent-12 edges of this colouring on the sumset:', len(bad12))

# ---------- (2) the paper's witness ----------
rows = list(csv.DictReader(open(sys.argv[1])))
W = [tuple(int(r[f'c{k}']) for k in range(6)) for r in rows]
assert len(set(W)) == 24
EW = edges_upto(W, 40)
print('(2) witness: 24 vertices,', len([e for e in EW if e[2] <= 12]), 'edges with exponent <=12;',
      'exponents used:', sorted(set(e[2] for e in EW if e[2] <= 12)), '; extra edges with exponent 13..40:',
      len([e for e in EW if e[2] > 12]))
def three_colourable(V, E):
    nb = {v: set() for v in V}
    for v, w, _ in E:
        nb[v].add(w); nb[w].add(v)
    col = {}
    order = sorted(V, key=lambda v: -len(nb[v]))
    def bt(i):
        if i == len(order):
            return True
        v = order[i]
        used = {col[w] for w in nb[v] if w in col}
        for c in range(3):
            if c not in used:
                col[v] = c
                if bt(i + 1):
                    return True
                del col[v]
        return False
    return bt(0)
print('(2) witness 3-colourable with exponents <=12 edges:', three_colourable(W, [e for e in EW if e[2] <= 12]))
print('(2) witness 3-colourable with exponents <=11 edges:', three_colourable(W, [e for e in EW if e[2] <= 11]))

# ---------- (3) SAT on the sumset ----------
def sat3(V, E, solver_cls):
    var = lambda i, c: 3 * i + c + 1
    cl = []
    for i in range(len(V)):
        cl.append([var(i, 0), var(i, 1), var(i, 2)])
    for v, w, _ in E:
        i, j = idx[v], idx[w]
        for c in range(3):
            cl.append([-var(i, c), -var(j, c)])
    cl.append([var(0, 0)])            # symmetry: fix colour of vertex 0
    with solver_cls(bootstrap_with=cl) as s:
        return s.solve()
for k, E in ((11, E11), (12, E12), (14, E14)):
    print(f'(3) sumset 3-colourable with exponents <= {k}:  CaDiCaL:', sat3(B, E, Cadical153), ' Glucose:', sat3(B, E, Glucose4))
