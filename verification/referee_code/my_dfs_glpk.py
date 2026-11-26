#!/usr/bin/env python3
# Referee's independent search, different solver (GLPK) and different LP formulation:
# node w = (t_0..t_{j-1}); variables s_0..s_{j+d-1} in [-1,1]; equality rows
#     sum_{i=0}^{d} a_i s_{k+i} = t_k   (k < j)
# objective g.s with g = coefficient vector of c_j = sum_{i<d} a_i s_{j+i}.
# Certificate for an upper bound: any rational y in Q^j gives
#     g.s = (g - A^T y).s + y.t <= ||g - A^T y||_1 + y.t      for every feasible s,
# where (A^T y)_n = sum_k y_k a_{n-k}  (coefficients of the polynomial y(x) f(x)).
# Emptiness certificate: y with y.t > ||A^T y||_1.
# All bounds used for branching are computed exactly in integers from the rationalised duals.
import sys, json, time
from fractions import Fraction as Fr
from math import gcd
import swiglpk as glp

def lcm(a, b):
    return a // gcd(a, b) * b

def run(a, L, out_path, sym=True, maxnodes=10**8):
    d = len(a) - 1; ad = a[d]
    S1 = sum(abs(c) for c in a)
    T = [t for t in range(-S1, S1 + 1) if t % 6 == 3]
    lp = glp.glp_create_prob()
    glp.glp_term_out(glp.GLP_OFF)
    parm = glp.glp_smcp(); glp.glp_init_smcp(parm)
    parm.msg_lev = glp.GLP_MSG_OFF; parm.presolve = glp.GLP_OFF
    parm.tol_bnd = 1e-10; parm.tol_dj = 1e-10
    glp.glp_add_cols(lp, d)
    for n in range(d):
        glp.glp_set_col_bnds(lp, n + 1, glp.GLP_DB, -1.0, 1.0)
    fh = open(out_path, 'w') if out_path else None
    stats = dict(nodes=0, I=0, E=0, maxdepth=0, rationalised_tighter=0, lp_fail=0)
    word = []
    t0 = time.time()

    def exact_bound(g, y, tau):
        """exact upper bound ||g - A^T y||_1 + y.tau for rational y (list of Fr); returns Fr."""
        Q = 1
        for v in y:
            Q = lcm(Q, v.denominator)
        Y = [v.numerator * (Q // v.denominator) for v in y]
        n = len(g)
        r = [Q * gv for gv in g]
        for k, Yk in enumerate(Y):
            if Yk:
                for i in range(d + 1):
                    r[k + i] -= Yk * a[i]
        num = sum(abs(v) for v in r) + sum(Yk * t for Yk, t in zip(Y, tau))
        return Fr(num, Q)

    def solve(g):
        # set objective g, maximise; return (status, duals list)
        ncol = glp.glp_get_num_cols(lp)
        for n in range(ncol):
            glp.glp_set_obj_coef(lp, n + 1, float(g[n]) if n < len(g) else 0.0)
        glp.glp_set_obj_dir(lp, glp.GLP_MAX)
        ret = glp.glp_simplex(lp, parm)
        if ret != 0:
            glp.glp_std_basis(lp)
            ret = glp.glp_simplex(lp, parm)
        st = glp.glp_get_status(lp)
        nrow = glp.glp_get_num_rows(lp)
        duals = [glp.glp_get_row_dual(lp, k + 1) for k in range(nrow)]
        return ret, st, duals

    def best_bound(g, duals, tau):
        cands = []
        for sgn in (1, -1):
            yd = [Fr(sgn * v) for v in duals]                       # exact dyadic
            yr = [Fr(sgn * v).limit_denominator(10**6) for v in duals]  # rationalised
            cands.append((exact_bound(g, yd, tau), 'd', sgn))
            cands.append((exact_bound(g, yr, tau), 'r', sgn))
        cands.sort(key=lambda c: c[0])
        bd, kind, sgn = cands[0]
        y = [Fr(sgn * v) for v in duals] if kind == 'd' else [Fr(sgn * v).limit_denominator(10**6) for v in duals]
        return bd, y, kind

    def farkas(tau):
        # auxiliary LP: max y.t - sum z  s.t. -z <= A^T y <= z, -1<=y<=1  (built separately)
        j = len(tau); n = j + d
        aux = glp.glp_create_prob()
        glp.glp_set_obj_dir(aux, glp.GLP_MAX)
        glp.glp_add_cols(aux, j + n)
        for k in range(j):
            glp.glp_set_col_bnds(aux, k + 1, glp.GLP_DB, -1.0, 1.0)
            glp.glp_set_obj_coef(aux, k + 1, float(tau[k]))
        for m in range(n):
            glp.glp_set_col_bnds(aux, j + m + 1, glp.GLP_LO, 0.0, 0.0)
            glp.glp_set_obj_coef(aux, j + m + 1, -1.0)
        glp.glp_add_rows(aux, 2 * n)
        for m in range(n):
            ks = [k for k in range(j) if 0 <= m - k <= d and a[m - k] != 0]
            for r, sg in ((2 * m, 1), (2 * m + 1, -1)):
                idx = glp.intArray(len(ks) + 2); val = glp.doubleArray(len(ks) + 2)
                for q, k in enumerate(ks):
                    idx[q + 1] = k + 1; val[q + 1] = float(sg * a[m - k])
                idx[len(ks) + 1] = j + m + 1; val[len(ks) + 1] = -1.0
                glp.glp_set_mat_row(aux, r + 1, len(ks) + 1, idx, val)
                glp.glp_set_row_bnds(aux, r + 1, glp.GLP_UP, 0.0, 0.0)
        p2 = glp.glp_smcp(); glp.glp_init_smcp(p2); p2.msg_lev = glp.GLP_MSG_OFF
        glp.glp_simplex(aux, p2)
        y = [Fr(glp.glp_get_col_prim(aux, k + 1)).limit_denominator(10**6) for k in range(j)]
        glp.glp_delete_prob(aux)
        # exact check: y.t > ||A^T y||_1
        lhs = sum(yk * t for yk, t in zip(y, tau))
        r = [Fr(0)] * n
        for k, yk in enumerate(y):
            for i in range(d + 1):
                r[k + i] += yk * a[i]
        if lhs > sum(abs(v) for v in r):
            return y
        return None

    def emit(obj):
        if fh:
            fh.write(json.dumps(obj) + '\n')

    def fr2s(v):
        return str(v)

    # iterative DFS to avoid recursion limits
    # each frame: (state, list of pending children)
    def node():
        stats['nodes'] += 1
        j = len(word)
        stats['maxdepth'] = max(stats['maxdepth'], j)
        g = [0] * (j + d)
        for i in range(d):
            g[j + i] = a[i]
        ret, st, duals = solve(g)
        if st in (glp.GLP_NOFEAS, glp.GLP_INFEAS) and ret == 0 and st == glp.GLP_NOFEAS:
            y = farkas(list(word))
            if y is None:
                stats['lp_fail'] += 1; emit(dict(w=list(word), t='FAIL')); return []
            stats['E'] += 1
            emit(dict(w=list(word), t='E', y=[fr2s(v) for v in y]))
            return []
        if st != glp.GLP_OPT:
            y = farkas(list(word))
            if y is not None:
                stats['E'] += 1
                emit(dict(w=list(word), t='E', y=[fr2s(v) for v in y]))
                return []
            stats['lp_fail'] += 1; emit(dict(w=list(word), t='FAIL')); return []
        ub, yu, ku = best_bound(g, duals, word)
        gm = [-v for v in g]
        ret2, st2, duals2 = solve(gm)
        if st2 != glp.GLP_OPT:
            stats['lp_fail'] += 1; emit(dict(w=list(word), t='FAIL')); return []
        nlb, yl, kl = best_bound(gm, duals2, word)
        lb = -nlb
        if ku == 'r' or kl == 'r':
            stats['rationalised_tighter'] += 1
        if j >= L:
            stats['lp_fail'] += 1; emit(dict(w=list(word), t='DEEP', ub=str(ub), lb=str(lb))); return []
        stats['I'] += 1
        emit(dict(w=list(word), t='I', yu=[fr2s(v) for v in yu], yl=[fr2s(v) for v in yl]))
        kids = [t for t in T if not (sym and j == 0 and t < 0) and not (t + ad < lb or t - ad > ub)]
        return kids

    def push(t):
        j = len(word)
        col = glp.glp_add_cols(lp, 1)
        glp.glp_set_col_bnds(lp, col, glp.GLP_DB, -1.0, 1.0)
        row = glp.glp_add_rows(lp, 1)
        idx = glp.intArray(d + 2); val = glp.doubleArray(d + 2)
        for i in range(d + 1):
            idx[i + 1] = j + i + 1; val[i + 1] = float(a[i])
        glp.glp_set_mat_row(lp, row, d + 1, idx, val)
        glp.glp_set_row_bnds(lp, row, glp.GLP_FX, float(t), float(t))
        word.append(t)

    def pop():
        nrow = glp.glp_get_num_rows(lp); ncol = glp.glp_get_num_cols(lp)
        ri = glp.intArray(2); ri[1] = nrow
        glp.glp_del_rows(lp, 1, ri)
        ci = glp.intArray(2); ci[1] = ncol
        glp.glp_del_cols(lp, 1, ci)
        word.pop()
        if glp.glp_get_status(lp) == glp.GLP_UNDEF:
            pass

    stack = [node()]
    while stack:
        if stats['nodes'] >= maxnodes:
            break
        if not stack[-1]:
            stack.pop()
            if word:
                pop()
            continue
        t = stack[-1].pop(0)
        push(t)
        stack.append(node())
        if stats['nodes'] % 10000 == 0:
            print('progress', stats, f'{time.time()-t0:.0f}s', flush=True)
    if fh:
        fh.close()
    stats['time_s'] = round(time.time() - t0, 1)
    print('final', json.dumps(stats), flush=True)
    return stats

if __name__ == '__main__':
    a = json.loads(sys.argv[1]); L = int(sys.argv[2]); out = sys.argv[3] if len(sys.argv) > 3 else None
    sym = (len(sys.argv) <= 4) or sys.argv[4] != 'nosym'
    run(a, L, out, sym)
