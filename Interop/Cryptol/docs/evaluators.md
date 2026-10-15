# Evaluator target and upstream discrepancies

The semantic target remains the pinned reference evaluator. Production evaluation
is an independent compatibility target. Replacing the reference target would
change integer arithmetic, strictness and partial-value observations already
covered by Lean theorems. Upstream discussion also favors changing production
integer division toward the reference behavior, so production behavior is not a
stable substitute for that specification.

## Reproduced versions

The [audit report](../artifacts/evaluator-audit.json) records 152 observations:
both evaluator modes at Cryptol 3.6.0
(`61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b`) and a separately built upstream
revision `51405420cb90cf9959ca4349eea0ae8b77487855`. Foundation remains pinned at
`7d0528bd998682788f4e23661f2829298f9e47db`.

The matrix checks signed integer division/remainder and zero divisors, lazy
function and aggregate demand, partial-word comparison, updates, shifts,
empty and infinite sequences, comprehensions, folds, productive recursion and
Foundation theta. Expected disagreements are distinct outcomes. An external
timeout fails validation and is never classified as semantic divergence.

Run `test_evaluators.py --cryptol … --upstream-cryptol … --foundation … --report …`,
or set `CRYPTOL_UPSTREAM_BINARY` alongside the usual external-validation inputs.
The validation driver compares the newly generated report to the committed one.
Revision checks reject an unrelated binary; a changed evaluator outcome requires
an explicit audit update.

## Known upstream work

| Observation | Upstream evidence | Disposition |
|---|---|---|
| Negative `Integer` division and remainder differ between normal and reference modes | [Cryptol #2060](https://github.com/GaloisInc/cryptol/issues/2060), open; [#2061 closing discussion](https://github.com/GaloisInc/cryptol/pull/2061#issuecomment-4670449512) | Exact known issue. The proposed reference change was closed unmerged; the discussion favors moving other backends to `quot/rem`. Both audited binaries still disagree. |
| Concrete/symbolic integer rounding has changed before | [#662](https://github.com/GaloisInc/cryptol/issues/662) | Historical context, not evidence that the current mismatch is fixed. |
| Partial packed-word comparison and aggregate demand differ | [#408](https://github.com/GaloisInc/cryptol/issues/408), [#406](https://github.com/GaloisInc/cryptol/issues/406), [#1925](https://github.com/GaloisInc/cryptol/issues/1925) | Related laziness/strictness work. The exact checked observations still differ; these links do not establish that each example has a matching open issue. |
| Negative update index is ignored by reference evaluation and rejected by normal evaluation | [#415](https://github.com/GaloisInc/cryptol/issues/415) | Related out-of-bounds update discussion, not an exact duplicate claim. Keep the regression and seek upstream classification before opening a new issue. |
| Error and demand behavior | [#619](https://github.com/GaloisInc/cryptol/issues/619), [#866](https://github.com/GaloisInc/cryptol/issues/866), [#1136](https://github.com/GaloisInc/cryptol/issues/1136) | Existing design history. Preserve value/error/bottom distinctions and test individual observations. |

The audit reviewed the issue tracker and the closing discussion, rather than
inferring intended semantics solely from one backend's code. This is a versioned
engineering decision; it is not a proof of the Haskell implementation or a claim
that every difference has an upstream resolution.

## Foundation theta

The original `StepMappings.cry` uses `(x-1)%5`. At `x=0`, reference remainder
produces `-1`; forcing that lane fails. Production remainder produces `4` and the
same zero-state observation succeeds. This is an application-level consequence
of #2060, not a newly discovered integer arithmetic bug.

The audit constructs a separate temporary module replacing this one expression
with `(x+4)%5`. The original checkout and imported artifacts are unchanged.
Both evaluator modes accept the portable variant at widths 1, 8 and 64.
`KeccakCodec.theta_predecessor` proves the index identity for every `Fin 5`;
`theta_predecessor_range` proves its bounds. These component facts and probes do
not claim full Keccak correspondence or validate a change to upstream Foundation.

A useful upstream follow-up is to add this Foundation consequence to #2060's
discussion and propose the portable indexing expression separately to Foundation.
No upstream issue, comment or patch is published by this development.
