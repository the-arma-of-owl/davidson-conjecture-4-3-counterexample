#!/usr/bin/env python3
# Falsification attempt (would refute the claim if it found anything):
# look for 3-colourings of Gamma_alpha coming from finite quotients, i.e. characters psi of a finite
# quotient of Z[alpha] = Z[x]/(f) with psi(alpha^n) in [1/3, 2/3] (mod 1) for EVERY n >= 0
# (Davidson's Lemma 2.3 then gives a 3-colouring of the whole Gamma_alpha).
#  (A) ring maps Z[x]/(f) -> Z/N, x -> t with f(t) = 0 mod N, composed with k -> lam*k/N  (N <= NMAX)
#  (B) cyclotomic quotients R_m(f) = Z[zeta_m]/(f(zeta_m)), all characters, for D_m^2 <= LIMIT
#  (C) sanity of the correspondence on the paper's sextic 2x^6-2x^4+x^3-2x^2+2 (chi = 3 by the paper):
#      its norm-31 character must give an admissible (sigma, tau) with sigma = 6u - 3.
import sys, math, itertools
from fractions import Fraction as Fr
import numpy as np
import sympy as sp

A = [2, 2, 1, -1, -2, -1, -1, -1, -2, -1, 1, 2, 2]
x = sp.symbols('x')
f = sp.Poly(sum(c * x**i for i, c in enumerate(A)), x)

def mid(k, N):       # k/N mod 1 in [1/3, 2/3]  <=>  N <= 3k' <= 2N with k' = k mod N
    k %= N
    return N <= 3 * k <= 2 * N

# ---------- (A) ----------
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
hitsA = []
nroots = 0
for N in range(2, NMAX + 1):
    roots = [t for t in range(N) if sum(c * pow(t, i, N) for i, c in enumerate(A)) % N == 0]
    nroots += len(roots)
    for t in roots:
        # orbit of powers t^n mod N (n >= 0): preperiod + cycle; collect the set
        seen = []
        s = set(); v = 1 % N
        while v not in s:
            s.add(v); seen.append(v); v = (v * t) % N
        S = sorted(s)
        if 0 in s:
            continue           # a step mapped to 0 can never be separated
        # need lam with lam*s mod N in middle third for all s in S
        arr = np.array(S, dtype=np.int64)
        lam = np.arange(1, N, dtype=np.int64)
        prod = (lam[:, None] * arr[None, :]) % N
        ok = np.all((3 * prod >= N) & (3 * prod <= 2 * N), axis=1)
        if ok.any():
            hitsA.append((N, t, int(lam[ok][0])))
print(f'(A) N <= {NMAX}: {nroots} roots t of f mod N examined; 3-colouring characters found: {len(hitsA)}', hitsA[:5])

# ---------- (B) ----------
LIMIT = int(sys.argv[2]) if len(sys.argv) > 2 else 400_000
def charcheck(m):
    Phi = sp.Poly(sp.cyclotomic_poly(m, x), x)
    ph = Phi.degree()
    # matrix of multiplication by beta = f(zeta) in basis 1..zeta^{ph-1}; column k = coords of zeta^k f(zeta)
    cols = []
    for k in range(ph):
        r = (sp.Poly(x**k, x) * f).rem(Phi)
        c = [int(r.coeff_monomial(x**i)) for i in range(ph)]
        cols.append(c)
    M = sp.Matrix(ph, ph, lambda i, k: cols[k][i])
    det = abs(int(M.det()))
    if det > LIMIT:
        return m, ph, det, None
    if det == 1:
        return m, ph, det, 0
    # characters: w with M^T w in Z^ph, w mod Z^ph.  Use Smith form of M^T: M^T = U D V  ->  w = V^{-1} D^{-1} z
    from sympy.matrices.normalforms import smith_normal_decomp
    D, U, V = smith_normal_decomp(M.T)       # D = U*M^T*V
    # D = U M^T V  =>  M^T = U^{-1} D V^{-1};  M^T w in Z^n  <=>  D (V^{-1} w) in Z^n  <=>  V^{-1} w in D^{-1} Z^n
    diag = [int(D[i, i]) for i in range(ph)]
    assert math.prod(abs(v) for v in diag) == det
    Vm = np.array(V.tolist(), dtype=object)
    # step coordinates: zeta^j for j = 0..m-1 in basis
    steps = []
    for j in range(m):
        r = sp.Poly(x**j, x).rem(Phi)
        steps.append([int(r.coeff_monomial(x**i)) for i in range(ph)])
    St = np.array(steps, dtype=object)            # m x ph
    # psi(z) = w.z with w = V y, y_i = k_i / d_i ;  psi(step_j) = sum_i y_i (V^T step_j)_i
    G = St.dot(Vm)                                # m x ph integer: (step_j . V)_i
    L = 1
    for v in diag:
        L = L * abs(v) // math.gcd(L, abs(v))
    # numerators over common denominator L: psi = sum_i k_i * (L/d_i) * G[j,i] / L
    coef = np.array([[int(G[j, i]) * (L // abs(diag[i])) % L for i in range(ph)] for j in range(m)], dtype=np.int64)
    rng = [range(abs(v)) for v in diag]
    nontriv = [i for i in range(ph) if abs(diag[i]) > 1]
    found = 0
    it = itertools.product(*[range(abs(diag[i])) for i in nontriv])
    C = coef[:, nontriv].T
    while True:
        chunk = list(itertools.islice(it, 100000))
        if not chunk:
            break
        ks = np.array(chunk, dtype=np.int64)
        vals = (ks.dot(C)) % L     # (#chars) x m
        ok = np.all((3 * vals >= L) & (3 * vals <= 2 * L), axis=1)
        found += int(ok.sum())
    return m, ph, det, found
resB = []
for m in range(3, 61):
    if sp.totient(m) > 24:
        continue
    resB.append(charcheck(m))
for r in resB:
    print('(B) m=%d phi=%d |R_m(f)|=%d  characters with all steps in [1/3,2/3]: %s' % (r[0], r[1], r[2], 'skipped (too many)' if r[3] is None else r[3]))

# ---------- (C) ----------
a2 = [2, 0, -2, 1, -2, 0, 2]        # 2x^6 - 2x^4 + x^3 - 2x^2 + 2
# S_8 = Z/31 with [sqrt2] = 8; [zeta]^2 = 8[zeta] - 1 ; h(a + b zeta) = 19a + 16b mod 31
v = [(1, 0), (0, 1)]
for j in range(2, 8):
    (a0, b0), (a1, b1) = v[-2], v[-1]
    v.append(((8 * a1 - a0) % 31, (8 * b1 - b0) % 31))
lab = [(19 * p + 16 * q) % 31 for p, q in v]
print('(C) labels of zeta_8^j:', lab)
u = [Fr(l, 31) for l in lab]
assert all(Fr(1, 3) <= t <= Fr(2, 3) for t in u)
sig = [6 * t - 3 for t in u]
period_ok = True
taus = []
for j in range(8):
    tj = sum(a2[i] * sig[(i + j) % 8] for i in range(7))
    taus.append(tj)
    period_ok &= (tj.denominator == 1 and int(tj) % 6 == 3)
print('(C) sigma = 6u-3 :', [str(s) for s in sig], ' tau_j (period 8):', [str(t) for t in taus], ' admissible:', period_ok)
