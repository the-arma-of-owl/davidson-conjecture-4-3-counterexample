# Independent exact verification (Python fractions only) of periodic characters proving chi <= 3.
# A periodic sequence u_0..u_{m-1} in Q/Z with
#   (i)  sum_i a_i u_{(n+i) mod m} in Z for all n      (Shift Criterion => character of Z[alpha])
#   (ii) 1/3 <= u_n <= 2/3                             (separation >= 1/3)
# gives a proper 3-colouring of Gamma_alpha (Davidson, Lemma "character separation").
import sys, json
from fractions import Fraction as Fr

def check(a, u):
    m = len(u)
    for n in range(m):
        s = sum(a[i] * u[(n + i) % m] for i in range(len(a)))
        if s.denominator != 1:
            return False, f'relation fails at n={n}: {s}'
    for x in u:
        if not (Fr(1, 3) <= x <= Fr(2, 3)):
            return False, f'value {x} outside [1/3,2/3]'
    return True, 'ok'

if __name__ == '__main__':
    data = json.load(open(sys.argv[1]))
    bad = 0
    for row in data:
        a = row['f']; u = [Fr(s) for s in row['u']]
        ok, msg = check(a, u)
        print(a, 'period', len(u), ok, msg)
        bad += (not ok)
    print('all verified' if bad == 0 else f'{bad} FAILED')
