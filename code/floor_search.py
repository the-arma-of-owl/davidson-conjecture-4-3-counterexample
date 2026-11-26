#!/usr/bin/env python3
"""Search for the certificates in data/floor_certificates.json (paper, Remark 3).

MILP (HiGHS via scipy): minimise rho subject to A sigma = t, |sigma_i| <= rho, t_j = 3 + 6 k_j.
Prints JSON with the best t found and an exact rho. Usage: python3 code/floor_search.py K SECONDS
Needs scipy >= 1.9. The exact check is code/check_floor.py."""
import sys, json, time
import numpy as np
from fractions import Fraction as Fr
from scipy.optimize import milp, LinearConstraint, Bounds, linprog
a = [2,2,1,-1,-2,-1,-1,-1,-2,-1,1,2,2]
K = int(sys.argv[1]); TL = float(sys.argv[2]); R = K - 11; n = K + 1
nv = n + 1 + R
Aeq = np.zeros((R, nv)); beq = np.full(R, 3.0)
for j in range(R):
    for i, ai in enumerate(a): Aeq[j, i + j] = ai
    Aeq[j, n + 1 + j] = -6
Aub = np.zeros((2 * n, nv))
for i in range(n):
    Aub[2*i, i] = 1; Aub[2*i, n] = -1; Aub[2*i+1, i] = -1; Aub[2*i+1, n] = -1
c = np.zeros(nv); c[n] = 1
lb = np.r_[np.full(n, -2.0), 0.0, np.full(R, -3.0)]; ub = np.r_[np.full(n, 2.0), 2.0, np.full(R, 2.0)]
lb[n + 1] = 0  # symmetry t_0 > 0
t0 = time.time()
res = milp(c, constraints=[LinearConstraint(Aeq, beq, beq), LinearConstraint(Aub, -np.inf, 0)],
           integrality=np.r_[np.zeros(n + 1), np.ones(R)], bounds=Bounds(lb, ub),
           options={"time_limit": TL, "disp": False})
out = {"K": K, "status": res.status, "msg": res.message, "secs": round(time.time() - t0, 1),
       "dual_bound": getattr(res, "mip_dual_bound", None)}
if res.x is not None:
    t = [3 + 6 * round(v) for v in res.x[n + 1:]]
    # exact sigma: rationalize the 12 free coordinates of an LP optimum for this t, recurrence for the rest
    lp = linprog(np.r_[np.zeros(n), 1], A_eq=np.c_[Aeq[:, :n], np.zeros(R)], b_eq=np.array(t, float),
                 A_ub=Aub[:, :n + 1], b_ub=np.zeros(2 * n), bounds=[(-2, 2)] * n + [(0, 2)], method="highs")
    x = [Fr(round(v * 10**12), 10**12) for v in lp.x[:12]]
    s = x[:]
    for k in range(R):
        s.append((Fr(t[k]) - sum(a[i] * s[k + i] for i in range(12))) / 2)
    assert all(sum(a[i] * s[i + j] for i in range(13)) == t[j] for j in range(R))
    rho = max(abs(v) for v in s)
    out.update(rho_float=float(lp.x[-1]), rho_exact=str(rho), rho_exact_float=float(rho),
               floor=float(2 / (rho - 1)) if rho > 1 else None, t=t)
print(json.dumps(out)); sys.stdout.flush()
