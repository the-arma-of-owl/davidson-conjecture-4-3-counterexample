# Emits a checkable proof that no valid tau-word of length LMAX (with tau_0 > 0) exists.
# Proof file (JSON lines), one entry per explored node:
#   {"w": [tau_0..tau_{j-1}], "t": "I", "yu": {k: "p/q"}, "yl": {k: "p/q"}}   interval certificate
#   {"w": [...], "t": "E", "y": {k: "p/q"}}                                       emptiness certificate
# Multipliers refer to the rows  c_k(x) in [tau_k - 2, tau_k + 2]  (k < j), where
#   c_k(x) = sum_{i<d} a_i sigma_{i+k}(x),  sigma_n = x_n (n<d),  sigma_{k+d} = (tau_k - c_k)/a_d.
# check_proof.py verifies everything with exact rational arithmetic, independently of HiGHS.
import sys, json, time
from fractions import Fraction as Fr
import numpy as np
import highspy

def fl(v):
    return np.array([float(t) for t in v], dtype=np.float64)

def main(a, LMAX, out):
    d = len(a) - 1; ad = a[-1]
    L1 = sum(abs(x) for x in a)
    T = [t for t in range(-L1, L1 + 1) if t % 3 == 0 and (t // 3) % 2 != 0]
    h = highspy.Highs(); h.setOptionValue('output_flag', False)
    h.setOptionValue('primal_feasibility_tolerance', 1e-10)
    h.setOptionValue('dual_feasibility_tolerance', 1e-10)
    for i in range(d):
        h.addVar(-1.0, 1.0)
    idx = np.arange(d, dtype=np.int32)
    rows = []   # exact (cc, ck, tau): c_k(x) = cc.x + ck, constraint tau-2 <= c_k <= tau+2
    fh = open(out, 'w')
    stats = dict(nodes=0, I=0, E=0, fail=0)
    word = []
    t0 = time.time()

    def ub_cert(c, ck0, y):
        # exact upper bound of c.x + ck0 over P from multipliers y on rows; returns (bound, ydict)
        best = None
        for sgn in (1, -1):
            yy = {k: Fr(sgn * float(v)) for k, v in enumerate(y) if v != 0.0}
            A = list(c); B = Fr(ck0); tot = Fr(0)
            for k, yk in yy.items():
                cc, ckk, tau = rows[k]
                tot += yk * tau + ad * abs(yk)
                for i in range(d):
                    A[i] -= yk * cc[i]
                B -= yk * ckk
            ub = tot + sum(abs(t) for t in A) + B
            if best is None or ub < best[0]:
                best = (ub, yy)
        return best

    def empty_cert(y):
        for sgn in (1, -1):
            yy = {k: Fr(sgn * float(v)) for k, v in enumerate(y) if v != 0.0}
            A = [Fr(0)] * d; B = Fr(0); beta = Fr(0)
            for k, yk in yy.items():
                cc, ckk, tau = rows[k]
                beta += yk * tau + ad * abs(yk)
                for i in range(d):
                    A[i] += yk * cc[i]
                B += yk * ckk
            if B - sum(abs(t) for t in A) > beta:
                return yy
        return None

    def solve(c, sense):
        h.changeColsCost(d, idx, fl(c))
        h.changeObjectiveSense(sense)
        h.run()
        return h.getModelStatus(), list(h.getSolution().row_dual)

    def emit(obj):
        fh.write(json.dumps(obj) + '\n')

    sys.setrecursionlimit(100000)
    I = [[Fr(int(i == j)) for j in range(d)] for i in range(d)]

    def rec(win):
        stats['nodes'] += 1
        j = len(word)
        cc = [sum(a[i] * win[i][0][k] for i in range(d)) for k in range(d)]
        ck = sum(a[i] * win[i][1] for i in range(d))
        st, y = solve(cc, highspy.ObjSense.kMaximize)
        if st == highspy.HighsModelStatus.kInfeasible or j >= LMAX:
            if st != highspy.HighsModelStatus.kInfeasible:
                stats['fail'] += 1
                emit(dict(w=list(word), t='FAIL'))
                return
            _, ok, ray = h.getDualRay()
            yy = empty_cert(list(ray)) if ok else None
            if yy is None:
                stats['fail'] += 1
                emit(dict(w=list(word), t='FAIL'))
                return
            stats['E'] += 1
            emit(dict(w=list(word), t='E', y={str(k): str(v) for k, v in yy.items()}))
            return
        if st != highspy.HighsModelStatus.kOptimal:
            stats['fail'] += 1; emit(dict(w=list(word), t='FAIL')); return
        ub, yu = ub_cert(cc, ck, y)
        st2, y2 = solve([-t for t in cc], highspy.ObjSense.kMaximize)
        if st2 != highspy.HighsModelStatus.kOptimal:
            stats['fail'] += 1; emit(dict(w=list(word), t='FAIL')); return
        nub, yl = ub_cert([-t for t in cc], -ck, y2)
        lb = -nub
        stats['I'] += 1
        emit(dict(w=list(word), t='I', yu={str(k): str(v) for k, v in yu.items()},
                  yl={str(k): str(v) for k, v in yl.items()}))
        for t in T:
            if j == 0 and t < 0:
                continue
            if t + ad < lb or t - ad > ub:
                continue
            rows.append((cc, ck, Fr(t)))
            h.addRow(float(Fr(t - ad) - ck), float(Fr(t + ad) - ck), d, idx, fl(cc))
            word.append(t)
            rec(win[1:] + [([-v / ad for v in cc], (Fr(t) - ck) / ad)])
            word.pop()
            h.deleteRows(1, np.array([len(rows) - 1], dtype=np.int32))
            rows.pop()

    rec([(I[i], Fr(0)) for i in range(d)])
    fh.close()
    print('stats', stats, 'time %.1f' % (time.time() - t0))

if __name__ == '__main__':
    main(json.loads(sys.argv[1]), int(sys.argv[2]), sys.argv[3])
