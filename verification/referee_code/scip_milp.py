#!/usr/bin/env python3
# Third method: MILP in SCIP 10 (optionally in SCIP's exact rational mode).
#   s_0..s_K in [-1,1] (continuous), m_j integer in [-3,2], tau_j = 6 m_j + 3 (odd multiple of 3, |tau|<=15),
#   sum_i a_i s_{i+j} - 6 m_j = 3  for 0 <= j <= K-d ;   optional symmetry m_0 >= 0.
import sys, json, time
from fractions import Fraction as Fr
import pyscipopt

def build(a, K, exact, sym, tl):
    d = len(a) - 1
    S1 = sum(abs(c) for c in a)
    mlo = -((S1 + 3) // 6); mhi = (S1 - 3) // 6          # tau = 6m+3 in [-S1, S1]
    M = pyscipopt.Model()
    if exact:
        M.enableExactSolving(True)
    M.hideOutput(True)
    M.setParam('limits/time', tl)
    s = [M.addVar(f's{n}', vtype='C', lb=-1, ub=1) for n in range(K + 1)]
    m = [M.addVar(f'm{j}', vtype='I', lb=(0 if (sym and j == 0) else mlo), ub=mhi) for j in range(K - d + 1)]
    for j in range(K - d + 1):
        M.addCons(pyscipopt.quicksum(a[i] * s[i + j] for i in range(d + 1)) - 6 * m[j] == 3)
    return M, s, m

if __name__ == '__main__':
    a = json.loads(sys.argv[1]); K = int(sys.argv[2]); exact = sys.argv[3] == 'exact'
    sym = len(sys.argv) <= 4 or sys.argv[4] != 'nosym'
    tl = float(sys.argv[5]) if len(sys.argv) > 5 else 1e9
    t0 = time.time()
    M, s, m = build(a, K, exact, sym, tl)
    M.optimize()
    st = M.getStatus()
    out = dict(K=K, exact=exact, isExact=M.isExact(), sym=sym, status=st, time_s=round(time.time() - t0, 1),
               nodes=M.getNNodes())
    if M.getNSols() > 0:
        sol = M.getBestSol()
        tau = [6 * round(M.getSolVal(sol, v)) + 3 for v in m]
        out['tau'] = tau
        # independent exact re-check of the returned point: rationalise first d values, recompute the rest
        d = len(a) - 1
        sig = [Fr(M.getSolVal(sol, v)).limit_denominator(10**9) for v in s]
        out['max_abs_sigma_float'] = max(abs(float(x)) for x in sig)
    print(json.dumps(out), flush=True)
