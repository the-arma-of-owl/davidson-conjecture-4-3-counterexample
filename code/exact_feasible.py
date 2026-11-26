# Exact feasibility certificate for a given tau-word: find sigma_0..sigma_{d-1} (rational) such
# that all sigma_n (n <= K) computed exactly from the recurrence lie in [-1,1].
# This proves Cay(M_K, S_K) IS 3-colourable (constructive direction of the criterion).
import sys, json
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog

a = json.loads(sys.argv[1]); tau = json.loads(sys.argv[2])
d = len(a) - 1; ad = a[-1]
# affine forms sigma_n = A_n.x + b_n
forms = [(np.eye(d)[i], 0.0) for i in range(d)]
for j, t in enumerate(tau):
    cA = sum(a[i] * forms[j + i][0] for i in range(d)); cb = sum(a[i] * forms[j + i][1] for i in range(d))
    forms.append((-cA / ad, (t - cb) / ad))
# maximize margin m: -1+m <= sigma_n <= 1-m
nA = []; nb = []
for A, b in forms[d:]:
    nA.append(list(A) + [1.0]); nb.append(1 - b)
    nA.append(list(-A) + [1.0]); nb.append(1 + b)
res = linprog(np.r_[np.zeros(d), -1.0], A_ub=np.array(nA), b_ub=np.array(nb),
              bounds=[(-1, 1)] * d + [(0, 1)], method='highs')
print('LP status', res.status, 'margin', -res.fun if res.status == 0 else None)
x = [Fr(v).limit_denominator(10**12) for v in res.x[:d]]
# exact recurrence
sig = list(x)
for j, t in enumerate(tau):
    c = sum(a[i] * sig[j + i] for i in range(d))
    sig.append((Fr(t) - c) / ad)
ok = all(-1 <= s <= 1 for s in sig)
print('exact check: all', len(sig), 'sigma in [-1,1]:', ok, ' max|sigma| =', float(max(abs(s) for s in sig)))
if ok:
    json.dump(dict(f=a, tau=tau, sigma0=[str(v) for v in x]), open(sys.argv[3], 'w'))
