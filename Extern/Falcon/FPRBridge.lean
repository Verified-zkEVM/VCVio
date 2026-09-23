/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Extern.Falcon.FPR.Decode
public import Extern.Falcon.FPR.Rounding
public import Extern.Falcon.FPR.Common
public import Extern.Falcon.FPR.AddPipeline
public import Extern.Falcon.FPR.Add
public import Extern.Falcon.FPR.Mul
public import Extern.Falcon.FPR.Loop
public import Extern.Falcon.FPR.Div
public import Extern.Falcon.FPR.Sqrt
public import Extern.Falcon.FPR.Witnesses
public import Extern.Falcon.FPR.Verify

/-!
# FPR ↔ ℝ Bridge Theorems

Error bounds connecting the integer-only FPR emulation layer to the exact `ℝ` arithmetic used
in the abstract Falcon specification.

`toReal` reads the IEEE-754 binary64 fields straight off the `UInt64` word (`FPR.decode` into
`FPR.Bits`, denoted by `FPR.Bits.toReal`), so the denotation is elementary arithmetic on `Nat`,
`Bool` and `ℝ` and reduces in the kernel. Non-finite patterns denote `0`.

## Module layout

The proofs live in `Extern/Falcon/FPR/`, split so the four operation proofs compile in parallel:

```
Decode ─► Rounding ─► Common ─┬─► AddPipeline ─► Add ─┐
                              ├─► Mul ────────────────┼─► Witnesses
                              └─► Loop ─┬─► Div ──────┤
                                        └─► Sqrt ─────┘
Verify (independent of the error bounds)
```

This module re-exports all of them.

## Per-Operation Error Bounds

Each FPR arithmetic operation is correctly rounded, hence carries at most the relative error
`2 ^ (-52)` of IEEE-754 binary64 — on the domain the format is closed under, and not outside it:

- `add_error`, `sub_error`, `mul_error`, `div_error` bound `|fpr_op a b - (a_real ⋆ b_real)|`
  by `2 ^ (-52) · |a_real ⋆ b_real|`, for operands in `FPR.IsNormalOrZero` whose *exact* result
  lands in `FPR.InNormalMagnitudeRange`.
- `sqrt_error` needs no result-side restriction: a square root cannot leave the window.
- `expm_p63_error` (in `Extern/Falcon/ExpmBridge.lean`) bounds the FACCT sampler kernel.

Both restrictions are load-bearing rather than defensive. Two maximal-magnitude normals overflow
the exponent field, which this decoder sends to `0`; two normals whose exact difference is
subnormal are mis-rounded by the alignment step; and `FPR.sqrt` at `+∞` returns `2 ^ 512` against
a right-hand side of `0`. The unrestricted readings of these statements are false, and the
non-vacuity witnesses in `Extern.Falcon.FPR.Witnesses` show the restricted ones still admit ordinary
values — including, since the widening, exact zeros.

The matching closure facts (`add_isNormalOrZero` and friends) say the domain is closed under each
operation, which is what lets a compound expression derive *validity* for its intermediate
results. The range side does not come for free: whether an exact intermediate lands in
`FPR.InNormalMagnitudeRange` depends on the values an algorithm feeds in, so it stays an explicit
premise. Together they discharge `FloatLike.HasRealSemantics FPR` in
`Extern/Falcon/ApproxArith.lean`.

## Accumulated Error in ffSampling

The statistical distance between the FPR-based sampler output and the
ideal discrete Gaussian is bounded by the Rényi divergence analysis
from Pornin 2019, Section 3:

  `R_∞(D_FPR ‖ D_ideal) ≤ 1 + ε_renyi`

where `ε_renyi < 2^{-64}` for 53-bit mantissa precision. That analysis is quoted from the
literature here; it is not established in these modules.

## References

- Pornin 2019 (eprint 2019/893), Section 3 (precision analysis)
- Falcon specification v1.2, Section 2.5.2 (sampler quality)
-/
