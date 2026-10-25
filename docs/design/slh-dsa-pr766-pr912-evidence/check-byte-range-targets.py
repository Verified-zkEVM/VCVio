#!/usr/bin/env python3
"""Check the planned byte-range coefficients against the retained exact bound formulas."""

import argparse
from fractions import Fraction
import importlib.util
import json
from pathlib import Path


PARAMETERS = [
    ("128s", 16, 63, 7, 9, 12, 14, 1591788895347057694892543),
    ("128f", 16, 66, 22, 3, 6, 33, 512534878340559730413511),
    ("192s", 24, 63, 7, 9, 14, 17, 7714313990982286445273599),
    ("192f", 24, 66, 22, 3, 8, 33, 1936665684817391308429255),
    ("256s", 32, 64, 8, 8, 14, 22, 19966778066156452796772607),
    ("256f", 32, 68, 17, 4, 9, 35, 16195218117312364562383887),
]


def check(source_root: Path, coefficient_path: Path) -> None:
    checker_path = source_root / "scripts/check-slh-dsa-bound-table.py"
    spec = importlib.util.spec_from_file_location("slhdsa_bound_check", checker_path)
    if spec is None or spec.loader is None:
        raise ValueError(f"cannot load {checker_path}")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    checker.check(source_root / "docs/design/slh-dsa-security-bounds.csv")

    records = json.loads(coefficient_path.read_text())
    by_key = {(r["set"], r["maxSignExponent"]): r for r in records}
    if len(records) != 18 or len(by_key) != 18:
        raise ValueError("expected 18 distinct parameter/lifetime records")

    low, high = 2**32, 2**64
    for name, n, h, d, hp, a, k, addresses in PARAMETERS:
        cardinality = 2 ** (8 * n)
        verifier = 2 + k * (a + 1) + d * ((2 * n + 3) * 15 + 1 + hp)
        weak = Fraction(addresses, 2**256)
        for exponent in (20, 32, 64):
            signing = 2**exponent

            def coverage(hashes: int) -> Fraction:
                return checker.coverage(
                    h, a, k, signing, hashes, Fraction(signing, cardinality)
                )

            def structured(hashes: int) -> Fraction:
                return (hashes + 1) * coverage(hashes) + Fraction(
                    2 * (hashes + verifier), cardinality
                )

            every = structured(high + verifier) + Fraction(
                2 * (signing + 1), cardinality
            )
            every_hedged = (
                structured(high + verifier)
                + Fraction(1, cardinality)
                + Fraction(
                    signing * (high + verifier + signing + 1), cardinality**2
                )
                + Fraction(signing + 1, cardinality)
            )
            structured_coefficient = (
                (1 + Fraction(1, low)) * coverage(high)
                + Fraction(2, cardinality)
                + Fraction(2 * verifier, low * cardinality)
            )
            deterministic = structured_coefficient + (
                Fraction(signing + 1, cardinality)
                + weak * (min(Fraction(1), every) if n == 32 else 1)
            ) / low
            hedged = structured_coefficient + (
                Fraction(1, cardinality)
                + Fraction(signing * (high + signing + 1), cardinality**2)
                + weak * (min(Fraction(1), every_hedged) if n == 32 else 1)
            ) / low

            row = by_key[name, exponent]
            for mode, coefficient, bits in (
                ("deterministic", deterministic, 8 * n - (33 if exponent == 64 else 2)),
                ("hedged", hedged, 8 * n - 2),
            ):
                expected = Fraction(*map(int, row[mode + "Coefficient"]))
                if coefficient != expected or row[mode + "Bits"] != bits:
                    raise ValueError(f"{name}/{exponent}/{mode}: coefficient or target differs")
                if coefficient > Fraction(1, 2**bits):
                    raise ValueError(f"{name}/{exponent}/{mode}: proposed floor fails")
    print("All 36 byte-range coefficient targets: PASS (exact rational arithmetic)")
    print("Lean range transport and kernel certificates remain implementation deliverables.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source_root", type=Path, help="pinned PR 766 or retained integration tree")
    parser.add_argument(
        "--coefficients",
        type=Path,
        default=Path(__file__).with_name("byte-range-coefficients.json"),
    )
    args = parser.parse_args()
    check(args.source_root, args.coefficients)
