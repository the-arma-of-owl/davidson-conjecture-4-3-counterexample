"""Bounded SAT pilot and exact calibration. Run with Python 3 and python-sat."""
import argparse
import csv
import random
from functools import reduce
from math import lcm
from time import perf_counter

from pysat.solvers import Minisat22
from witness_bound import A, powers_mod_f


def integer_directions(poly, k):
    rows = powers_mod_f(poly, k)
    scale = reduce(lcm, (z.denominator for row in rows for z in row), 1)
    return [tuple(int(z*scale) for z in row) for row in rows]


def add(v, w):
    return tuple(a+b for a,b in zip(v,w))


def edges(vertices, directions):
    lookup = {v:i for i,v in enumerate(vertices)}
    pairs = []
    for i,v in enumerate(vertices):
        for d in directions:
            j = lookup.get(add(v,d))
            if j is not None:
                pairs.append((i,j))
    return pairs


def test(label, vertices, directions, extract=False):
    start = perf_counter()
    vertices = sorted(vertices)
    pairs = edges(vertices, directions)
    n = len(vertices)
    guards = [3*n+i+1 for i in range(n)]
    def colour(i,c):
        return 3*i+c+1
    # Each active vertex needs at least one colour; disjoint sets of colours on
    # neighbours give a proper colouring by picking one colour from each set.
    with Minisat22() as sat:
        for i in range(n):
            sat.add_clause([-guards[i]]+[colour(i,c) for c in range(3)])
        for i,j in pairs:
            for c in range(3):
                sat.add_clause([-colour(i,c),-colour(j,c)])
        sat.conf_budget(100000)
        verdict = sat.solve_limited(assumptions=guards)
        if verdict is True:
            model = {v for v in sat.get_model() if v>0}
            col = [next(c for c in range(3) if colour(i,c) in model) for i in range(n)]
            assert all(col[i]!=col[j] for i,j in pairs)
        print(f"{label}: V={n} E={len(pairs)} SAT={verdict} wall={perf_counter()-start:.3f}s",flush=True)
        if extract and verdict is False:
            core = sorted(sat.get_core())
            for guard in tuple(core):
                if guard in core:
                    trial = [other for other in core if other!=guard]
                    if not sat.solve(assumptions=trial):
                        core = sorted(sat.get_core())
            assert not sat.solve(assumptions=core)
            print("  blind vertex-minimal core:",len(core),flush=True)
        return verdict


def calibration(csv_path):
    dirs = integer_directions((1,0,-1,-1,-1,0,1),12)
    subset = {(0,)*6}
    for d in dirs[:10]:
        subset |= {add(v,d) for v in subset}
    assert len(subset)==830
    assert test("sextic sumset K11",subset,dirs[:12]) is True
    assert test("sextic sumset K12",subset,dirs,extract=True) is False
    if csv_path:
        with open(csv_path) as fp:
            known = [tuple(int(row[f'c{i}']) for i in range(6)) for row in csv.DictReader(fp)]
        assert len(set(known))==24
        assert test("published witness K11",known,dirs[:12]) is True
        assert test("published witness K12",known,dirs) is False


def target():
    dirs = integer_directions(A,79)
    zero = (0,)*12
    vertices = {zero}
    # Four orders per relation. Swapping successive steps adds a square.
    indices = [(i,1 if a>0 else -1) for i,a in enumerate(A) for _ in range(abs(a))]
    rng = random.Random(43)
    for _ in range(4):
        rng.shuffle(indices)
        for j in range(68):
            path = [zero]
            for i,sign in indices:
                path.append(add(path[-1],tuple(sign*t for t in dirs[i+j])))
            assert path[-1]==zero
            vertices.update(path)
            for k,(i,sign) in enumerate(indices[1:]):
                vertices.add(add(path[k],tuple(sign*t for t in dirs[i+j])))
    seeds = vertices.copy()
    for k in (0,39,79):
        vertices.update(add(p,dirs[k]) for p in seeds)
    return test("fB all 68 relation loops, swaps, translations, K79",vertices,dirs)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--csv",help="anc/sextic-witness.csv from Davidson's arXiv sources")
    calibration(parser.parse_args().csv)
    target()
