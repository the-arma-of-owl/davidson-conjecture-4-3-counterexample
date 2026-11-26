"""Exact verification of inclusion-minimality for the 68 row conditions."""
import json
from fractions import Fraction
from pathlib import Path
from witness_bound import A


def verify(cases):
    for key, numbers in cases.items():
        omitted = int(key)
        assert 0 <= omitted < 68
        sigma = list(map(Fraction, numbers))
        assert len(sigma) == 80 and all(abs(s) <= 1 for s in sigma)
        tau = [sum(a*s for a,s in zip(A,sigma[j:])) for j in range(68)]
        assert all(t % 6 == 3 for j,t in enumerate(tau) if j != omitted)
        assert tau[omitted] % 6 != 3
    return sorted(map(int,cases))


if __name__ == "__main__":
    file = Path(__file__).with_name("omission_witnesses.json")
    indices = verify(json.loads(file.read_text()))
    assert indices == list(range(68))
    print("PASS: deleting any one of the 68 rows makes the system feasible.")
