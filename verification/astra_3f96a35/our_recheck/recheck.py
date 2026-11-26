# Independent checks of Astra's 3f96a35 audit claims (does not import Astra's code).
import json, sys, random
from fractions import Fraction as Fr
from math import prod

a = [2,2,1,-1,-2,-1,-1,-1,-2,-1,1,2,2]          # f, ascending degree
K, R = 79, 68                                    # 80 coords, 68 relations

def odd3(t):                                     # t in 3(2Z+1)
    return t.denominator == 1 and t.numerator % 3 == 0 and (t.numerator // 3) % 2 != 0

# 1) omission witnesses
W = json.load(open(sys.argv[1]))
assert sorted(map(int, W)) == list(range(R))
for key, vals in W.items():
    j0 = int(key); s = [Fr(v) for v in vals]
    assert len(s) == K + 1 and all(abs(x) <= 1 for x in s)
    tau = [sum(a[i] * s[i + j] for i in range(13)) for j in range(R)]
    assert all(odd3(tau[j]) for j in range(R) if j != j0), key
    assert not odd3(tau[j0]), key
print("omissions: 68/68 OK (each row alone can be dropped -> feasible)")

# 2) vertex bound: remainders of X^k mod f over Q, k = 0..79
def rem(k):
    p = [Fr(0)] * (k + 1); p[k] = Fr(1)
    for d in range(k, 11, -1):
        q = p[d] / a[12]
        if q:
            for i in range(13): p[d - 12 + i] -= q * a[i]
    return p[:12] + [Fr(0)] * max(0, 12 - len(p[:12]))
Rk = [rem(k) for k in range(K + 1)]
choices = [int(20 * sum(abs(Rk[k][i]) for k in range(K + 1))) + 1 for i in range(12)]
bound = 2**68 * prod(choices)
print("choices:", choices); print("bound: %.4e" % bound, "  21^80 = %.3e" % 21**80)

# 3) scheduling lemma (step 4 of sonlu_tanik.md): random m, simulate walk, max |coord|
ell = [[a[i - j] if 0 <= i - j <= 12 else 0 for i in range(K + 1)] for j in range(R)]
colsum = [sum(abs(ell[j][i]) for j in range(R)) for i in range(K + 1)]
assert max(colsum) == 19
random.seed(1)
worst = 0
for trial in range(300):
    scale = random.choice([1, 5, 50, 1000])
    m = [random.randint(-scale, scale) if random.random() < 0.7 else 0 for _ in range(R)]
    z = [sum(m[j] * ell[j][i] for j in range(R)) for i in range(K + 1)]
    types = [(abs(m[j]), [ (1 if m[j] > 0 else -1) * x for x in ell[j]]) for j in range(R) if m[j]]
    types += [(abs(z[i]), [(-1 if z[i] > 0 else 1) if t == i else 0 for t in range(K + 1)]) for i in range(K + 1) if z[i]]
    events = sorted(((Fr(2 * k - 1, 2 * N), random.random(), idx) for idx, (N, v) in enumerate(types) for k in range(1, N + 1)))
    pos = [0] * (K + 1)
    for _, _, idx in events:
        v = types[idx][1]
        for i in range(K + 1):
            pos[i] += v[i]
            worst = max(worst, abs(pos[i]))
    assert pos == [0] * (K + 1)
print("scheduling: 300 random m, max |coordinate| on walk =", worst, "(claim: <= 10)")
