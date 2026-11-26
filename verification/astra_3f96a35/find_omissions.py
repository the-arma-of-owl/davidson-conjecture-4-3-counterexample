"""Optional discovery code. Use check_omissions.py for fast deterministic verification."""
import argparse
import json
from fractions import Fraction
from itertools import product
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from witness_bound import A
from check_omissions import verify


def matrix():
    mat = np.zeros((68,80), dtype=int)
    for j in range(68):
        mat[j,j:j+13] = A
    return mat


def rational_solution(mat, j, word):
    keep = np.arange(68) != j
    # Minimise max |sigma_i| so that rounding the free coordinates has room.
    cube = np.c_[np.r_[np.eye(80), -np.eye(80)], -np.ones(160)]
    lp = linprog([0]*80+[1], A_eq=np.c_[mat[keep], np.zeros(67)],
                 b_eq=np.asarray(word)[keep], A_ub=cube, b_ub=np.zeros(160),
                 bounds=[(-1,1)]*80+[(0,1)], method="highs")
    if not lp.success or lp.x[-1] > 1-1e-7:
        return None
    def near(x):
        return Fraction(round(x*10**9), 10**9)
    sigma = [near(x) for x in lp.x[:12]]
    for k,t in enumerate(word):
        if k == j:
            sigma.append(near(lp.x[k+12]))
        else:
            sigma.append((int(t)-sum(a*s for a,s in zip(A[:-1],sigma[k:])))/2)
    numbers = list(map(str,sigma))
    verify({str(j):numbers})
    return numbers


def find(mat, j, base, seconds):
    words = [base, base[::-1], [-t for t in base], [-t for t in base[::-1]]]
    seen = set()
    for left,right in product(words[:2],words):
        rows = [left[:j]+[0]+right[j:]]
        rows += [left[:j]+[0]+right[j+1:]+[t] for t in (-3,3)]
        for row in rows:
            if tuple(row) in seen:
                continue
            seen.add(tuple(row))
            result = rational_solution(mat,j,row)
            if result:
                return result
    # Fix a feasible suffix. Search for a +/-3 prefix by mixed-integer LP.
    suffix_size = 67-j
    equations = np.vstack([np.c_[mat[:j],-6*np.eye(j)],
                           np.c_[mat[j+1:],np.zeros((suffix_size,j))]])
    for start in range(j+1):
        for pattern in words[:2]:
            suffix = pattern[start:start+suffix_size]
            rhs = np.r_[[3]*j,suffix]
            fit = milp(np.zeros(80+j), integrality=np.r_[np.zeros(80),np.ones(j)],
                       bounds=Bounds([-0.999999]*80+[-1]*j,[0.999999]*80+[0]*j),
                       constraints=LinearConstraint(equations,rhs,rhs),
                       options={"time_limit":seconds})
            if fit.x is not None:
                row = [3+6*round(x) for x in fit.x[80:]]+[0]+suffix
                result = rational_solution(mat,j,row)
                if result:
                    return result
    raise RuntimeError(f"No witness found within search budget for row {j}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("repo", type=Path)
    parser.add_argument("--seconds", type=float, default=2.0)
    parser.add_argument("--output", type=Path, default=Path("regenerated_omissions.json"))
    args = parser.parse_args()
    old = args.repo/"certificate"/"fB_K78_feasible_cert.json"
    base = json.loads(old.read_text())["tau"]
    mat = matrix()
    cases = {}
    for j in range(34):
        result = find(mat,j,base,args.seconds)
        cases[str(j)] = result
        cases[str(67-j)] = result[::-1]   # palindromic f
    assert verify(cases) == list(range(68))
    args.output.write_text(json.dumps(cases,indent=1))
