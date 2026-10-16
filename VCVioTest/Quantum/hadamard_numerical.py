"""Independent small-cell numerical checks; run with python3 (standard library only).

These tests compare explicit matrix multiplication with the accepting-map formulas.
They supplement kernel proofs; no numerical result is imported into Lean.
"""

from itertools import product
from math import sqrt


def identity(n):
    return [[float(i == j) for j in range(n)] for i in range(n)]


def multiply(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def transpose(a):
    return list(map(list, zip(*a)))


def conjugate(f, a):
    return multiply(multiply(f, a), transpose(f))


def diagonal(v):
    return [[x if i == j else 0.0 for j in range(len(v))] for i, x in enumerate(v)]


def check_close(a, b):
    error = max(abs(x - y) for ra, rb in zip(a, b) for x, y in zip(ra, rb))
    assert error < 1e-12, error
    return error


def check_cell(n):
    amp = 1 / sqrt(n)
    # Label zero denotes the empty cell; labels 1..n denote answers 0..n-1.
    f = [[0.0] + [amp] * n]
    f += [[amp] + [float(y == z) - 1 / n for z in range(n)] for y in range(n)]
    w = [[amp * (-1) ** ((r & s).bit_count()) for s in range(n)] for r in range(n)]
    check_close(multiply(w, w), identity(n))
    check_close(multiply(f, f), identity(n + 1))
    states = list(product(range(n), range(n + 1)))
    joint_f = [[float(r == s) * f[a][b] for s, b in states] for r, a in states]
    c = [[(w[r][s] if a == 0 else float(r == (s ^ (a - 1))))
          if a == b else 0.0 for s, b in states] for r, a in states]
    oracle = conjugate(joint_f, c)
    check_close(multiply(oracle, oracle), identity(len(states)))
    kraus = []
    error = 0.0
    for y in range(n):
        actual = [[oracle[y * (n + 1) + a][b] for b in range(n + 1)]
                  for a in range(n + 1)]
        expected = conjugate(f, diagonal([amp] + [float(z == y) for z in range(n)]))
        error = max(error, check_close(actual, expected))
        kraus.append(actual)
    # Includes empty lists, repetitions, and every conflicting list through length three.
    for length in range(4):
        for ys in product(range(n), repeat=length):
            actual = identity(n + 1)
            for y in ys:
                actual = multiply(kraus[y], actual)
            weights = [amp ** length]
            weights += [float(all(z == y for y in ys)) for z in range(n)]
            expected = conjugate(f, diagonal(weights))
            error = max(error, check_close(actual, expected))
            filled = [float(length == 0)]
            filled += [float(all(z == y for y in ys)) for z in range(n)]
            # Simultaneous diagonalization makes these exactly the norm/effect tests.
            assert max(abs(x - y) for x, y in zip(weights, filled)) <= amp + 1e-12
            assert all(x * x >= y - 1e-12 for x, y in zip(weights, filled))
    print(f"N={n}: unitarity, Kraus, repeated/conflicting lists, norm/effect OK; "
          f"max error={error:.3g}")


if __name__ == "__main__":
    for cardinality in (2, 4, 8):
        check_cell(cardinality)
