#!/usr/bin/env python3
# Write the (sigma, tau) feasibility MILP in CPLEX-LP format for the SCIP binary.
#   s_n in [-1,1] (n=0..K), m_j integer (tau_j = 6 m_j + 3), sum_i a_i s_{i+j} - 6 m_j = 3.
import sys, json
a = json.loads(sys.argv[1]); K = int(sys.argv[2]); out = sys.argv[3]
sym = len(sys.argv) <= 4 or sys.argv[4] != 'nosym'
d = len(a) - 1
S1 = sum(abs(c) for c in a)
mlo = -((S1 + 3) // 6); mhi = (S1 - 3) // 6
L = []
L.append('Minimize\n obj: 0 s0\nSubject To')
for j in range(K - d + 1):
    terms = ' '.join(f'{"+" if a[i] >= 0 else "-"} {abs(a[i])} s{i+j}' for i in range(d + 1) if a[i] != 0)
    L.append(f' c{j}: {terms} - 6 m{j} = 3')
L.append('Bounds')
for n in range(K + 1):
    L.append(f' -1 <= s{n} <= 1')
for j in range(K - d + 1):
    lo = 0 if (sym and j == 0) else mlo
    L.append(f' {lo} <= m{j} <= {mhi}')
L.append('General')
L.append(' ' + ' '.join(f'm{j}' for j in range(K - d + 1)))
L.append('End')
open(out, 'w').write('\n'.join(L) + '\n')
