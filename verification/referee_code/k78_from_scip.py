#!/usr/bin/env python3
# Turn SCIP's floating K=78 solution into an exact certificate: read tau from the log, solve the
# max-margin LP (|s_n| <= 1 - t) for that tau with GLPK, rationalise s_0..s_11, recompute the rest exactly.
import re, sys, json
from fractions import Fraction as Fr
import swiglpk as glp
a = [2, 2, 1, -1, -2, -1, -1, -1, -2, -1, 1, 2, 2]; d = 12; K = 78
log = open(sys.argv[1]).read()
m = {int(k): float(v) for k, v in re.findall(r'^m(\d+)\s+(-?[\d.e+-]+)', log, re.M)}
L = K - d + 1
tau = [6 * round(m.get(j, 0.0)) + 3 for j in range(L)]
print('SCIP tau word:', ''.join({3: '+', -3: '-'}.get(t, '*') for t in tau), ' values used:', sorted(set(tau)))
lp = glp.glp_create_prob(); glp.glp_term_out(glp.GLP_OFF)
glp.glp_set_obj_dir(lp, glp.GLP_MAX)
glp.glp_add_cols(lp, K + 2)       # s_0..s_K, margin t
for n in range(K + 1):
    glp.glp_set_col_bnds(lp, n + 1, glp.GLP_FR, 0, 0)
glp.glp_set_col_bnds(lp, K + 2, glp.GLP_DB, 0.0, 1.0); glp.glp_set_obj_coef(lp, K + 2, 1.0)
rows = 0
def addrow(entries, lo, hi, kind):
    global rows
    rows += 1
    glp.glp_add_rows(lp, 1)
    idx = glp.intArray(len(entries) + 1); val = glp.doubleArray(len(entries) + 1)
    for q, (c, v) in enumerate(entries):
        idx[q + 1] = c; val[q + 1] = v
    glp.glp_set_mat_row(lp, rows, len(entries), idx, val)
    glp.glp_set_row_bnds(lp, rows, kind, lo, hi)
for j in range(L):
    addrow([(j + i + 1, float(a[i])) for i in range(d + 1)], tau[j], tau[j], glp.GLP_FX)
for n in range(K + 1):
    addrow([(n + 1, 1.0), (K + 2, 1.0)], 0, 1.0, glp.GLP_UP)       # s + t <= 1
    addrow([(n + 1, -1.0), (K + 2, 1.0)], 0, 1.0, glp.GLP_UP)      # -s + t <= 1
parm = glp.glp_smcp(); glp.glp_init_smcp(parm); parm.msg_lev = glp.GLP_MSG_OFF
glp.glp_simplex(lp, parm)
t = glp.glp_get_obj_val(lp)
print('max margin t =', t)
s0 = [Fr(glp.glp_get_col_prim(lp, n + 1)).limit_denominator(10**12) for n in range(d)]
s = list(s0)
for j in range(L):
    s.append((tau[j] - sum(a[i] * s[j + i] for i in range(d))) / 2)
ok = all(abs(v) <= 1 for v in s) and all(tt % 6 == 3 for tt in tau)
print('exact recomputation: max |s_n| =', float(max(abs(v) for v in s)), ' admissible:', ok)
json.dump({'f': a, 'tau': tau, 'sigma0': [str(v) for v in s0]}, open('data/my_K78_cert_from_scip.json', 'w'))
