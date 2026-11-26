# Independent polynomial facts for f = 2x^12+2x^11+x^10-x^9-2x^8-x^7-x^6-x^5-2x^4-x^3+x^2+2x+2
# Exact arithmetic only (Fractions / sympy / python-flint).  Referee code, not the claimant's.
import json, math, itertools
from fractions import Fraction as Fr
import sympy as sp
import flint

A = [2, 2, 1, -1, -2, -1, -1, -1, -2, -1, 1, 2, 2]      # a_0..a_12
x, y = sp.symbols('x y')
f = sum(sp.Integer(c) * x**i for i, c in enumerate(A))
out = {}

# ---------- basic facts ----------
out['palindromic'] = A == A[::-1]
out['content_gcd'] = math.gcd(*A)
out['leading'] = A[-1]
out['f(1)'] = sum(A)
out['f(-1)'] = sum(c * (-1)**i for i, c in enumerate(A))
fi = sp.expand(f.subs(x, sp.I))
out['f(i)'] = str(fi)
out['sum|a_i|'] = sum(abs(c) for c in A)

# ---------- irreducibility: sympy, flint, and a mod-p argument ----------
out['sympy_factor_list'] = str(sp.factor_list(f))
fz = flint.fmpz_poly(A)
out['flint_factor'] = str(fz.factor())

# ---------- trace polynomial F with x^6 F(x+1/x) = f ----------
# solve for F by repeated subtraction of (x+1/x)^k x^6 terms (exact)
def trace_poly(coeffs):
    d = len(coeffs) - 1; r = d // 2
    rem = sp.Poly(sum(sp.Integer(c) * x**i for i, c in enumerate(coeffs)), x)
    Fc = [0] * (r + 1)
    for k in range(r, -1, -1):
        c = rem.coeff_monomial(x**(r + k))
        Fc[k] = c
        rem = rem - sp.Poly(c * sp.expand(x**(r - k) * (x**2 + 1)**k), x)
    assert rem.is_zero, rem
    return Fc
Fc = trace_poly(A)
F = sum(sp.Integer(c) * y**k for k, c in enumerate(Fc))
out['F_coeffs_c0..c6'] = [int(c) for c in Fc]
out['F'] = str(sp.expand(F))
out['F_check_identity'] = sp.expand(x**6 * F.subs(y, x + 1/x) - f) == 0
out['F_factored_form_ok'] = sp.expand(F - (y*(y**2-4)*(y+1)*(2*y**2-3) + 1)) == 0
out['F_at'] = {str(v): int(F.subs(y, v)) for v in (-2, -1, 0, 1, 2)}
out['F_factor_list'] = str(sp.factor_list(F))

# F irreducible mod p for which primes p<200 (p odd, p does not divide lc=2)?
irr_primes = []
for p in sp.primerange(3, 200):
    fp = flint.nmod_poly([int(c) % p for c in Fc], p)
    fac = fp.factor()
    degs = sorted(int(g.degree()) for g, e in fac[1] for _ in range(e))
    if degs == [6]:
        irr_primes.append(p)
out['F_irreducible_mod_p_primes_lt_200'] = irr_primes

# ---------- Sturm sequence of F, own implementation, Fractions ----------
def pdiv(a, b):   # a,b lists of Fr, low->high; returns remainder
    a = a[:]
    while len(a) >= len(b) and any(a):
        if a[-1] == 0:
            a.pop(); continue
        q = a[-1] / b[-1]; s = len(a) - len(b)
        for i, c in enumerate(b):
            a[s + i] -= q * c
        a.pop()
    while a and a[-1] == 0:
        a.pop()
    return a
def deriv(a):
    return [i * a[i] for i in range(1, len(a))]
def ev(a, t):
    s = Fr(0)
    for c in reversed(a):
        s = s * t + c
    return s
def sturm(a):
    seq = [a, deriv(a)]
    while True:
        r = pdiv(seq[-2], seq[-1])
        if not r:
            break
        seq.append([-c for c in r])
    return seq
def sign_changes(seq, t):
    vals = [ev(p, t) for p in seq]
    vals = [v for v in vals if v != 0]
    return sum(1 for u, v in zip(vals, vals[1:]) if (u > 0) != (v > 0))
FcF = [Fr(int(c)) for c in Fc]
seq = sturm(FcF)
out['sturm_len'] = len(seq)
out['sturm_last_is_constant'] = len(seq[-1]) == 1
V = lambda t: sign_changes(seq, Fr(t))
out['F(-2),F(2) nonzero'] = (ev(FcF, Fr(-2)) != 0, ev(FcF, Fr(2)) != 0)
out['roots_in_(-2,2)_sturm'] = V(-2) - V(2)
BIG = 10**6
out['real_roots_total_sturm'] = V(-BIG) - V(BIG)
out['sympy_count_roots_(-2,2)'] = int(sp.Poly(F, y).count_roots(-2, 2))
# isolate the roots in (-2,2) with rational intervals (bisection, Sturm counts)
def isolate(lo, hi, depth=0):
    n = V(lo) - V(hi)
    if n == 0:
        return []
    if n == 1 and (hi - lo) < Fr(1, 10**6):
        return [(lo, hi)]
    mid = (lo + hi) / 2
    if ev(FcF, mid) == 0:
        raise SystemExit('hit root exactly')
    return isolate(lo, mid) + isolate(mid, hi)
iv = isolate(Fr(-2), Fr(2))
out['root_intervals_y'] = [[float(a), float(b)] for a, b in iv]
out['root_angles_deg'] = [math.degrees(math.acos(float((a + b) / 2) / 2)) for a, b in iv]
# numeric check: all 12 roots of f have |z| = 1
nr = sp.Poly(f, x).nroots(n=40, maxsteps=500)
out['max_abs_dev_|root|-1'] = float(max(abs(abs(complex(z)) - 1) for z in nr))

# ---------- roots of unity / Mahler ----------
# f has leading coefficient 2 and content 1, so its roots are not algebraic integers -> not roots of unity.
# Direct check anyway: gcd(f, x^m - 1) = 1 for all m <= 400.
out['gcd_with_x^m-1_trivial_m<=400'] = all(sp.gcd(sp.Poly(f, x), sp.Poly(x**m - 1, x)).degree() == 0 for m in range(1, 401))

# ---------- cyclotomic congruence tests mod 3 (and general q) ----------
from sympy import totient
ms = [m for m in range(1, 2 * 12**2 + 1) if totient(m) <= 12]
out['num_m_with_phi<=12'] = len(ms)
div3 = []
gcds = {}
for m in ms:
    Phi = sp.Poly(sp.cyclotomic_poly(m, x), x)
    rem = sp.Poly(f, x).rem(Phi)          # Phi monic -> integer remainder
    cs = [int(c) for c in rem.all_coeffs()]
    g = 0
    for c in cs:
        g = math.gcd(g, c)
    gcds[m] = g      # q | all remainder coeffs  <=> f == 0 mod (q, Phi_m)
    # mod-3 divisibility of f by the full reduction of Phi_m (with multiplicity)
    Pm = flint.nmod_poly([int(c) % 3 for c in reversed(Phi.all_coeffs())], 3)
    fm = flint.nmod_poly([c % 3 for c in A], 3)
    if (fm % Pm) == 0:
        div3.append(m)
out['Phi_m_divides_f_mod_3_for_m'] = div3
out['cyclotomic_congruence_gcds_nontrivial'] = {m: g for m, g in gcds.items() if g != 1}
# ---------- eighth-root norm D_8 and other norms D_m ----------
Fp = sp.Poly(F, y)
r8 = Fp.rem(sp.Poly(y**2 - 2, y))
cB, cA = (r8.all_coeffs() + [0, 0])[:2] if r8.degree() == 1 else (0, r8.all_coeffs()[0])
out['F_mod_y^2-2'] = str(r8.as_expr())
Acoef = int(r8.coeff_monomial(1)); Bcoef = int(r8.coeff_monomial(y))
out['D_8'] = abs(Acoef**2 - 2 * Bcoef**2)
def Dm(m):
    # |N_{Q(t_m)/Q}(F(t_m))| via resultant with the minimal polynomial of 2cos(2pi/m)
    t = sp.symbols('t')
    psi = sp.minimal_polynomial(2 * sp.cos(2 * sp.pi / m), t)
    return abs(int(sp.resultant(sp.Poly(psi, t), sp.Poly(F.subs(y, t), t))))
out['D_m_for_m=3..30'] = {m: Dm(m) for m in range(3, 31)}
print(json.dumps(out, indent=1, default=str))
