# Certifying `expm_p63_error`

Working notes for the last `sorry` in `Extern/Falcon/FPRBridge.lean`. Everything here is
measured, not estimated; the numbers are what a proof attempt has to beat.

## The obligation

```
|expm_p63 x ccs / 2 ^ 63 - ccs * exp (-x)| ≤ 2 ^ (-51)
```
for `x ∈ [0, log 2)` and `ccs ∈ [0, 1)`. Throughout, one **unit** means `2 ^ (-63)`, so the
budget is **4096 units**.

## Why it is tight

`FPR.facctCoeffs` is a minimax fit of degree 12, not a Taylor truncation — every coefficient
is perturbed from `2 ^ 63 / k!` (the linear one by `-47104`, the degree-12 one by `-1.3e8`).
Its uniform error against `exp (-x)` over the interval is **3562 units**, i.e. 87% of the
budget on its own. The fixed-point work — the `mtwop63` conversions and twelve `mulHi64`
truncations — is comparatively free, contributing on the order of 15 units. So a proof has
about **534 units of slack**, and any bound that overestimates `sup |P - exp|` by more than
that cannot close.

## What does not work, and why

Write `Q = P - T_n`, the difference between the coefficient polynomial and a Taylor
truncation of `exp (-x)`. `Q` has `O(1)` coefficients while being `O(2 ^ -51)` — the fit
earns its accuracy from cancellation *across* the interval. Every bound that applies a
triangle inequality to coefficients throws that cancellation away:

| approach | result | vs 4096 |
| --- | --- | --- |
| Taylor, coefficient-wise + Lagrange remainder | `2 ^ (-35.8)` | ~38000x too weak |
| Chebyshev over the whole interval | 7529 units | 1.8x too weak |
| Midpoint + Lipschitz, 256 pieces | 2988783 units | 730x too weak |

The Lipschitz failure is the instructive one: bounding `sup |Q'|` coefficient-wise suffers
the *identical* pathology, so subdividing does not rescue it. What works is subdivision that
restores locality, applied to `Q` itself.

## What does work

| basis | pieces | bound | margin |
| --- | --- | --- | --- |
| Taylor form (shifted power basis) | 64 | 4083 | 0.3% — fails once truncation is added |
| Taylor form | 128 | 3589 | 12% |
| Taylor form | 256 | 3569 | 13% |
| **Chebyshev** | **32** | **3585** | **12%** |

Chebyshev at 32 pieces matches Taylor form at 128 — a 4x reduction in certificate count for
the price of needing `|T_j t| ≤ 1` on `[-1, 1]`.

The Taylor degree is irrelevant to the bound: `n = 18`, `22` and `26` all give the same
figure, because the remainder is already negligible at 18 (0.07 units). Use 18.

## The cost problem

Each certificate is a rational polynomial identity of degree `n` under a linear substitution.
Measured in this repo, with Mathlib imported:

- degree 26, 481-digit coefficients: **13.4 s**
- degree 18, 326-digit coefficients: **18.3 s**

Degree reduction did **not** help — the cost tracks the rational arithmetic, not the degree.
At roughly 15 s per certificate, Chebyshev/32 is about 8 minutes added to a single file and
Taylor form/128 about 32 minutes. The whole repository currently builds in about 15 minutes,
and CI times per-file builds, so **build time is the binding constraint, not the mathematics**.

## Untested levers, in the order worth trying

1. **Clear denominators and work over `ℤ`.** Every measurement above used `ℚ`. The 481- and
   326-digit figures are dominated by denominators (`2 ^ 63`, `m ^ n`, `n!`); a single common
   scaling makes every coefficient an integer. Untested, and the most likely large win.
2. **Prove the shift once, instantiate cheaply.** The per-certificate `ring` is re-deriving
   the binomial shift each time. A single general lemma
   `Q (c + h * u) = ∑ k, (∑ j ≥ k, q j * (j.choose k) * c ^ (j - k) * h ^ k) * u ^ k`
   would reduce each certificate to `norm_num` evaluations of the coefficient sums — 19
   scalar evaluations rather than a degree-18 polynomial normalisation.
3. Only if both fail: reconsider whether the statement's `2 ^ (-51)` should be relaxed. It
   cannot be relaxed silently — see the docstring note; the constant is 87% saturated, so a
   weaker constant is a real change to what the file claims, and belongs to the file owner.

## Shape of the eventual proof

1. Fixed-point layer: `mtwop63` semantics, the twelve-step Horner truncation over `UInt64`,
   the final `mulHi64`. Comparable in size to `mul_error`; no novel mathematics, and it can
   be built and landed independently of the certification layer.
2. Certification layer: `n = 18` Taylor truncation with `Real.exp_bound` for the remainder,
   plus the 32 (or 128) subinterval certificates.
3. Assembly: add the two, compare against 4096 units.

Step 1 is worth doing first regardless — it is ordinary proof engineering, it is needed under
every variant of step 2, and it will confirm the ~15-unit truncation figure that the whole
margin analysis rests on.
