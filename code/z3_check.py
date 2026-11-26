# Independent exact check with z3 (exact rational/integer arithmetic):
# exists sigma in [-1,1]^{K+1} (reals), t_j integers, sum_i a_i sigma_{i+j} = 6 t_j + 3 ?
# sat  <=> Cay(M_K, S_K) is 3-colourable (exact criterion).
import sys, json, time
import z3

a = json.loads(sys.argv[1]); K = int(sys.argv[2]); tl = int(sys.argv[3]) if len(sys.argv) > 3 else 0
d = len(a) - 1
L1 = sum(abs(x) for x in a)
s = z3.SolverFor('QF_LIRA') if hasattr(z3, 'SolverFor') else z3.Solver()
if tl:
    s.set('timeout', tl * 1000)
sig = [z3.Real(f's{n}') for n in range(K + 1)]
ts = [z3.Int(f't{j}') for j in range(K - d + 1)]
for v in sig:
    s.add(v >= -1, v <= 1)
tmax = L1 // 3
for j, t in enumerate(ts):
    s.add(6 * t + 3 >= -L1, 6 * t + 3 <= L1)
    s.add(z3.Sum([a[i] * sig[i + j] for i in range(d + 1)]) == 6 * t + 3)
s.add(ts[0] >= 0)  # symmetry sigma -> -sigma
t0 = time.time()
r = s.check()
print('K=', K, 'z3:', r, 'time %.1f' % (time.time() - t0), flush=True)
if r == z3.sat:
    m = s.model()
    sigma = [m.eval(v, model_completion=True) for v in sig]
    taus = [6 * m.eval(t).as_long() + 3 for t in ts]
    # exact re-check with fractions
    from fractions import Fraction as Fr
    def q(x):
        x = x.as_fraction() if hasattr(x, 'as_fraction') else Fr(str(x))
        return Fr(x)
    sg = [q(v) for v in sigma]
    assert all(-1 <= v <= 1 for v in sg)
    for j in range(K - d + 1):
        assert sum(a[i] * sg[i + j] for i in range(d + 1)) == taus[j]
    print('exact re-check of z3 model OK; tau =', taus)
