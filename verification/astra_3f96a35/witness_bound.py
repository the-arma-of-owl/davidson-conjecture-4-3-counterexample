"""Exact upper bound for the cardinality of the image of [-10,10]^80."""
from fractions import Fraction
from math import prod

A = (2, 2, 1, -1, -2, -1, -1, -1, -2, -1, 1, 2, 2)


def powers_mod_f(coefficients, last):
    """Remainders X^k mod f as vectors in the power basis, ascending degree."""
    degree = len(coefficients) - 1
    row = (Fraction(1),) + (Fraction(0),) * (degree - 1)
    rows = [row]
    for _ in range(last):
        high = row[-1] / coefficients[-1]
        shifted = (Fraction(0),) + row[:-1]
        row = tuple(v - high*a for v, a in zip(shifted, coefficients[:-1]))
        rows.append(row)
    return rows


if __name__ == "__main__":
    rows = powers_mod_f(A, 79)
    assert sum(map(abs, A)) == 19
    widths = [20 * sum(abs(row[i]) for row in rows) for i in range(12)]
    choices = [int(width) + 1 for width in widths]
    bound = 2**68 * prod(choices)
    print("Integer-coordinate choice bounds:", choices)
    print("Projected vertex upper bound:", bound, f"({bound:.6e})")
    print("Unprojected box:", 21**80)
