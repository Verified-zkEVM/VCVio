# Independent moment specialization

The original seven FORS moment interfaces retain their complete kernel types,
universe parameters, owners and axiom sets. Five actual proof bodies use the
existing generic moment API. `sumMoment` is its all-order polynomial, including
the zero fallback above six and empty/singleton cases. The original product-Poisson
proof still calls the actual finite-sum helper; its sixth-moment client adds only
the qualified polynomial head to its existing unfolding list. Numerical constants
and the sharper tail argument are unchanged.

[original-kernel.json](original-kernel.json) stores the original 42-record capture
with insignificant JSON whitespace removed. [specialization.json](specialization.json)
stores the finite named image and inverse map in the same compact form. Every JSON
token is unchanged: string bytes and escapes, numeric spellings, field order, array
order and all values are preserved. No field is added or removed.

The original producer capture has SHA-256
`14fb4aa108969a5391b2003895a5c61af003921ca32a243576181352c8a3265f`.
That hash remains the raw-producer provenance recorded by `originalCaptureSha256`;
it is not the stored compact asset hash. The original pretty specialization asset
has SHA-256
`bcab8f0eefe07f8e57736ae713fa218087bc3bf106f752eca1e638b2c2a7d91b`.
Both original byte archives are retained in the sealed implementation evidence.
The stored assets are:

| Asset | Bytes | SHA-256 |
| --- | ---: | --- |
| `original-kernel.json` | 560,264 | `daf8471ac671008da599cb53ecf2810550a497fedb810afcc356ae67bc6cc103` |
| `specialization.json` | 408,246 | `52e3d3e0683cff593078f5f3e9651a0a42809bb2bd74a3a94b850095c43f705f` |

Each stored asset occupies one JSON line. Inspect an expanded view with
`python3 -m json.tool original-kernel.json` or
`python3 -m json.tool specialization.json` from this directory. A parsed-data
round trip can be checked without rewriting either stored file:

```python
import json
from pathlib import Path

for name in ("original-kernel.json", "specialization.json"):
    stored = json.loads(Path(name).read_bytes())
    expanded = json.dumps(stored, ensure_ascii=False, indent=2)
    assert json.loads(expanded) == stored
```

The packaging evidence additionally compares the original and compact lexical
token streams and ordered parsed values exactly; parsed equality alone is not a
claim about escape spelling. Archived matcher rows support data recovery, not
newly proved matcher lemmas. The all-order mathematical equality is separately
kernel checked in `HashSigTest/SLHDSA/Refactor/IndependentPowersRecovery.lean`.

That ordinary test module compiles literal expectations into Lean source; it does
not read these JSON files to learn accepted values. It checks the full 31-record
semantic closure, external boundary, all original types and the single exact
Nat.AtLeastTwo proof relocation, including its full proof value. Direct dependency
checks require the five specific generic APIs and the four downstream proof edges.
Paired public imports and private `import all` dependencies ensure ordinary cached
builds track both exported types and the inspected implementations. There is no
legacy-profile fallback or alpha/proof normalization.

This is the finite moments extraction, not broad construction migration or a new
security certificate. The original exact 127-bit, weak-seed and verifier-cost
certificates and the 18-row arithmetic artifact retain their existing contracts.
