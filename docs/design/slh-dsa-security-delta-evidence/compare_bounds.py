#!/usr/bin/env python3
"""Compare existing deterministic SHAKE-128s envelopes using exact rational arithmetic."""

from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb, factorial
import json

CARD = 2**128
VERIFIER = 3929
HONEST_ADDRESSES = 1591788895347057694892543
stirling = [1] + [0] * 14
for _ in range(14):
    stirling = [0] + [r * stirling[r] + stirling[r - 1] for r in range(1, 15)]


def coverage(hashes, signatures):
    return sum((
        Fraction(
            comb(signatures, r - j) * comb(hashes, j) * factorial(r) * stirling[r],
            2 ** (63 * r + 12 * 14),
        ) * Fraction(signatures, CARD)**j
        for r in range(15) for j in range(r + 1)
        if r - j <= signatures and j <= hashes
    ), Fraction(0))


def decimal(value):
    with localcontext() as context:
        context.prec = 30
        return str(Decimal(value.numerator) / Decimal(value.denominator))


rows = []
weak = Fraction(HONEST_ADDRESSES, 2**256)
for hashes, signatures in [(0, 0), (2**64, 2**64), (2**80, 2**64),
                           (2**120, 2**64), (2**126, 2**64)]:
    cover = (hashes + 1) * coverage(hashes, signatures)
    general = cover + Fraction(2 * (hashes + VERIFIER) + signatures + 1, CARD) + weak
    work = Fraction(hashes + signatures + VERIFIER, 2**127)
    assert general - work == cover + Fraction(1 - signatures, CARD) + weak
    assert general < 1 and work < 1
    rows.append({
        "qh": str(hashes), "qs": str(signatures),
        "general": decimal(general), "specialized": decimal(work),
        "specializedOverGeneral": decimal(work / general),
        "smaller": "specialized" if work < general else "general",
    })
assert coverage(0, 0) == 0
assert rows[1]["smaller"] == "general"
assert all(rows[index]["smaller"] == "specialized" for index in [0, 2, 3, 4])
print(json.dumps({"exactRationalComparisonsOnly": True, "rows": rows}, indent=2))
