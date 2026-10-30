#!/usr/bin/env python3
"""Independently compare the Lean evaluator's CSV against exact Stirling arithmetic."""

import argparse
import csv
from fractions import Fraction
from itertools import product
from math import comb, factorial
from pathlib import Path
import subprocess
import tempfile


def surjections(digits: int) -> list[int]:
    row = [1] + [0] * digits
    for _ in range(digits):
        row = [0] + [r * row[r] + row[r - 1] for r in range(1, digits + 1)]
    return [factorial(r) * row[r] for r in range(digits + 1)]


def coverage(h: int, a: int, k: int, qs: int, qh: int, weight: Fraction) -> Fraction:
    counts = surjections(k)
    return sum((
        Fraction(comb(qs, r - j) * comb(qh, j) * counts[r], 2 ** (h * r + a * k))
        * weight ** j
        for r in range(k + 1) for j in range(r + 1)
        if r - j <= qs and j <= qh
    ), Fraction(0))


def check(path: Path) -> None:
    for k in range(5):
        for r, count in enumerate(surjections(k)):
            direct = sum(len(set(f)) == r for f in product(range(r), repeat=k))
            if direct != count:
                raise ValueError(f"surjection mismatch at {k}, {r}")
    parameters = [
        ("128s", 16, 63, 7, 9, 12, 14, 1591788895347057694892543),
        ("128f", 16, 66, 22, 3, 6, 33, 512534878340559730413511),
        ("192s", 24, 63, 7, 9, 14, 17, 7714313990982286445273599),
        ("192f", 24, 66, 22, 3, 8, 33, 1936665684817391308429255),
        ("256s", 32, 64, 8, 8, 14, 22, 19966778066156452796772607),
        ("256f", 32, 68, 17, 4, 9, 35, 16195218117312364562383887),
    ]
    with path.open() as source:
        records = list(csv.DictReader(source))
    rows = {(row["parameters"], row["model"]): row for row in records}
    if len(records) != 18 or len(rows) != 18:
        raise ValueError("expected exactly eighteen distinct parameter/model records")
    q = 2 ** 64
    for name, n, h, d, hp, a, k, addresses in parameters:
        card = 2 ** (8 * n)
        verifier = 2 + k * (a + 1) + d * ((2 * n + 3) * 15 + 1 + hp)

        def structured(qh: int) -> Fraction:
            return (qh + 1) * coverage(h, a, k, q, qh, Fraction(q, card)) + Fraction(
                2 * (qh + verifier), card
            )

        three = structured(q)
        deterministic = three + Fraction(q + 1, card)
        hedged = three + Fraction(1, card) + Fraction(q * (2 * q + 1), card * card)
        every = structured(q + verifier) + Fraction(2 * (q + 1), card)
        every_hedged = structured(q + verifier) + Fraction(1, card) + Fraction(
            q * (2 * q + verifier + 1), card * card
        ) + Fraction(q + 1, card)
        weak = Fraction(addresses, 2 ** 256)
        deterministic += weak * (min(Fraction(1), every) if n == 32 else 1)
        hedged += weak * (min(Fraction(1), every_hedged) if n == 32 else 1)
        for model, expected in [
            ("three-oracle", three), ("single-SHAKE-deterministic", deterministic),
            ("single-SHAKE-hedged", hedged),
        ]:
            row = rows[name, model]
            if int(row["qh"]) != q or int(row["qs"]) != q:
                raise ValueError(f"{name}/{model}: unexpected budgets")
            actual = Fraction(int(row["numerator"]), int(row["denominator"]))
            if actual != expected / q:
                raise ValueError(f"{name}/{model}: exact rational coefficient differs")
    print("Small exhaustive surjection checks and all 18 exact rational coefficients: PASS")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("csv", type=Path, help="checked-in evaluator CSV")
    parser.add_argument("--generator", type=Path, help="built Lean CSV generator executable")
    args = parser.parse_args()
    if args.generator is None:
        check(args.csv)
    else:
        with tempfile.TemporaryDirectory(prefix="slhdsa-bound-table-") as directory:
            generated = Path(directory) / "bounds.csv"
            with generated.open("wb") as output:
                subprocess.run([str(args.generator.resolve())], stdout=output, check=True)
            if generated.read_bytes() != args.csv.read_bytes():
                raise SystemExit(
                    f"{args.csv}: differs from regenerated Lean output; regenerate with "
                    f"`lake exe slhdsa_bound_table > {args.csv}`"
                )
            print("Regenerated Lean CSV matches checked-in artifact: PASS")
            check(generated)
