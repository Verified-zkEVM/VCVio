# Generalized XMSS

`HashSig/GXMSS` formalizes the generalized XMSS construction and conditional
security bounds of Drake, Khovratovich, Kudinov and Wagner,
[*Hash-Based Multi-Signatures for Post-Quantum Ethereum*](https://eprint.iacr.org/2025/055).
The security development uses the interval scheme first. Complete-tree bounds
specialize it to the full range. PRF-derived schemes separately account for
deriving secret values from one shared key.

## Construction and correctness

The generic scheme accepts an arbitrary globally incomparable encoding from
[`VCVio.CryptoFoundations.IncomparableEncoding`](../../VCVio/CryptoFoundations/IncomparableEncoding.lean).
Incomparability concerns distinct codewords. It does not assert message
injectivity or collision resistance. Winternitz and target-sum encodings have
separate instances in that namespace; neither is required by general GXMSS.

[`Scheme.lean`](../../HashSig/GXMSS/Scheme.lean) captures configuration before
parameterless key generation. Hash input embeddings may overlap, while chain
and tree tweaks have disjoint images. Positive chain steps use the paper's
`k + 1` convention. Merkle collision witnesses place the honest ordered child
pair in `first` and the forged pair in `second`.

For `N = 2^h`, the interval `I = [a,b]` is inclusive, with `a ≤ b < N`.
[`Interval/Scheme.lean`](../../HashSig/GXMSS/Interval/Scheme.lean) retains a
complete sampled start array and independent uniform filler digests at maximal
inactive subtrees. Only active starts affect its honest public tree.
Verification remains defined at every epoch.

The shared synchronized interface distinguishes correctness observations:

| API | Observation |
| --- | --- |
| `SyncSignatureAlg.CompletePerKey` | Correctness at every generated key. |
| `SyncSignatureAlg.Complete` | Joint keygen-sign-verify correctness. |
| `SyncSignatureAlg.CompleteOnPerKey` | Per-key correctness at selected epochs. |
| `SyncSignatureAlg.CompleteOn` | Joint correctness at selected epochs. |

[`Completeness.lean`](../../HashSig/GXMSS/Completeness.lean) proves both complete
forms from the pointwise canonical encoding bound `CanonicalErrorAtMost δ`.
The correctness error is at most `δ^K` for retry budget `K`. The separate
`complete_of_uniform` corollary consumes the uniform encoding-error law.
Keygen losslessness needs no additional public-seed premise.
[`Interval/Completeness.lean`](../../HashSig/GXMSS/Interval/Completeness.lean)
proves `completePerKey_isActive` and `complete_isActive`. Inactive signing has
zero success mass; the full range gives correctness at every epoch.

Returned signing failure, retry exhaustion, returned `false`, and unreturned
mass are distinct. A first signing request consumes its epoch even when it
fails. `SigningQueryBound qs A` counts all requests along supported executions,
including repeated, failed and inactive requests. Strong freshness excludes
the exact previously returned message/signature pair at the forged epoch.
A different valid signature for the same message can remain strongly fresh.

## Direct security endpoints

Import
[`Security/Interval/Unforgeability.lean`](../../HashSig/GXMSS/Security/Interval/Unforgeability.lean).
Its `strong_unforgeability_reduction_bound` uses `NoMaximumOutput`, explicit
`0 < v` and `0 < w`, the stated sampling/equality instances and the all-request
signing-query bound. Positivity does not follow from `NoMaximumOutput` alone.
The `_of_two_codewords` corollaries derive these encoding premises from two
distinct members of one globally incomparable code.

Write `D = 2^w`, `L = b-a+1` and `C = L*v*(D-1)`. The adjacent numerical
definition `strongUnforgeabilityBound` has ten terms:

```text
MerkleTCR + EncodingTCR + SameMessageRandomizerChainTCR + ChainCutTCR
+ C*ChainPRE + C*(D-1)*ChainUD
+ VectorUD + VectorPRE + PairUD + PairPRE.
```

Every term names an actual native reduction. Merkle TCR has capacity
`2*N*v*D`, each chain TCR has capacity `N*v*D`, and the encoding game retains
`qs` records with retry budget `K`. Failed eligible encoding queries retain
their consumed slots. Chain PRE/UD use one selected challenge in the original
digest domain. Filler challenges retain endpoint-vector and ordered-pair
domains, with their respective frontier capacities. No `min(qs,L)` improvement
is asserted. The public seed uses the actual hash `seedGen`.

`strong_unforgeability_power_of_two_reduction_bound` relaxes the chain
coefficients to `L*v*D` and `L*v*D²`. It retains four separate filler terms.
[`Security/Interval/FullRange.lean`](../../HashSig/GXMSS/Security/Interval/FullRange.lean)
removes the empty-frontier terms at full range. The complete endpoint in
[`Security/Unforgeability.lean`](../../HashSig/GXMSS/Security/Unforgeability.lean)
names the six full-range interval reductions. Its sharp `reductionBound` and
relaxed `powerOfTwoReductionBound` have respective chain contributions
`N*v*(D-1)*PRE + N*v*(D-1)²*UD` and `N*v*D*(D*UD + PRE)`.
These numerical identities are separate from whole interaction and
strong-experiment transport. Encoding-specific hash-bridge corollaries live in
[`Security/EncodingInstances.lean`](../../HashSig/GXMSS/Security/EncodingInstances.lean).

## Shared-response PRF derivation

[`PRFDerived/Query.lean`](../../HashSig/GXMSS/PRFDerived/Query.lean) owns the
complete public-seed, chain-start and retry query families. The interval adds
a filler family. The generic simulation in
[`PRF/QuerySimulation.lean`](../../VCVio/CryptoFoundations/PRF/QuerySimulation.lean)
stores each complete response before projection. Repeated coordinates reuse
that response. Projections of the same response need not be independent.
The scheme samples its actual `prf.keygen`.

[`Security/Interval/PRFDerivedUnforgeability.lean`](../../HashSig/GXMSS/Security/Interval/PRFDerivedUnforgeability.lean)
adds one native PRF advantage to the interval bound. The endpoint uses four
projection laws: the actual public-seed distribution, uniform chain starts,
uniform retry randomizers, and uniform filler digests. Its function-query cap
is `1 + L*v + F + qs*K`, where `F` is the frontier cardinality. Eager retry
suffixes are charged even after an earlier success. This counts function calls,
including repeats, rather than distinct cache misses or running time.

[`Security/PRFDerivedUnforgeability.lean`](../../HashSig/GXMSS/Security/PRFDerivedUnforgeability.lean)
proves the complete endpoint on its original three-family domain. The actual
full-range interaction never queries a filler coordinate. This supports the
three-law idealization and function-query cap `1 + N*v + qs*K` without a filler
law or a security assumption about an arbitrary extended PRF.
[`PRF/DomainTransport.lean`](../../VCVio/CryptoFoundations/PRF/DomainTransport.lean)
preserves the actual key sampler, whole ideal cache and query budget under
injective input transport.
[`Security/Interval/PRFDerivedFullRange.lean`](../../HashSig/GXMSS/Security/Interval/PRFDerivedFullRange.lean)
contains `fullRangeRealCorrespondence`, `fullRangeIdealCorrespondence`,
`fullRangeStrongExperiment`, `fullRangeDisplayedBound` and
`fullRangeStrongReductionBound`. The final bound uses three projection laws;
its `_of_two_codewords` corollary supplies the paper-facing encoding premise.

## Applications and scope

The ordinary public-import tests
[`CompleteEndpointApplication.lean`](../../HashSigTest/GXMSS/CompleteEndpointApplication.lean)
and
[`CompletePRFEndpointApplication.lean`](../../HashSigTest/GXMSS/CompletePRFEndpointApplication.lean)
apply expanded six-term bounds. The
[`PRFProductResponse.lean`](../../HashSigTest/GXMSS/PRFProductResponse.lean)
fixture proves the projection laws, proves its captured key distribution is
nonuniform, and applies interior, complete and full-range interval endpoints.
Its full-range filler projection fails the global filler law, while the
three-law theorem still applies. Separate singleton-code tests exercise the
`NoMaximumOutput` core without assuming two codewords.

Generic encodings, retry, chains, checksums, Merkle adapters and oracle
simulation belong below `HashSig` in VCVio or ToMathlib. GXMSS construction and
scheme-specific security remain in `HashSig/GXMSS`. Complete security uses the
interval proof; it does not maintain a second complete reduction proof cone.

These are conditional standard-model bounds. They do not establish hardness
of a concrete hash, a concrete parameter recommendation, PRF correctness,
Rust extraction, implementation refinement, measured runtime or SLH-DSA
certificate discharge. The finite-query bounds do not supply the paper's
asymptotic runtime claims.
