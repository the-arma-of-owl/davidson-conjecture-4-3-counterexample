#!/usr/bin/env python3
"""Exact check of the lower bounds in Remark 3 (finite witnesses).

For each K in the certificate file we have t in 3(2Z+1)^(K-11) and rationals sigma_0..sigma_11.
The recurrence sigma_{k+12} = (t_k - sum_{i<12} a_i sigma_{k+i}) / 2 then gives A sigma = t exactly.
With rho = max_n |sigma_n| > 1, every finite non-3-colourable subgraph of G_K contains a cycle of
length >= 2/(rho-1), so it has at least ceil(2/(rho-1)) vertices (paper, Remark 3).

Usage: python3 code/check_floor.py data/floor_certificates.json
"""
import json
import math
import sys
from fractions import Fraction as Fr

a = [2, 2, 1, -1, -2, -1, -1, -1, -2, -1, 1, 2, 2]
certs = json.load(open(sys.argv[1]))
for key in sorted(certs, key=int):
    K = int(key)
    t, R = certs[key]["t"], K - 11
    assert len(t) == R and all(isinstance(v, int) and v % 6 == 3 for v in t)
    s = [Fr(v) for v in certs[key]["sigma_first12"]]
    assert len(s) == 12
    for k in range(R):
        s.append((Fr(t[k]) - sum(a[i] * s[k + i] for i in range(12))) / 2)
    assert len(s) == K + 1
    assert all(sum(a[i] * s[i + j] for i in range(13)) == t[j] for j in range(R))
    rho = max(abs(v) for v in s)
    assert rho > 1
    bound = 2 / (rho - 1)
    print(f"K={K}: rho = {float(rho):.10f}, 2/(rho-1) = {float(bound):.3f}"
          f"  =>  every non-3-colourable finite subgraph of G_{K} has >= {math.ceil(bound)} vertices")
