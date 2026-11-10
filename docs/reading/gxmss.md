# Generalized XMSS

`HashSig/GXMSS` specifies generalized XMSS from Construction 3 of
[Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for
Post-Quantum Ethereum*](https://eprint.iacr.org/2025/055). The principal security
interface is the original-domain interval scheme. Complete-tree security is its
full-range specialization. Separate PRF-derived schemes account for deriving
secret values from one shared key.

The generic interface accepts an arbitrary globally incomparable code. It does
not require a target-sum encoding. Incomparability compares distinct codewords;
it does not assert that messages encode injectively or that the encoding is
collision resistant. Winternitz-checksum and target-sum encodings have separate
instance results under `Encoding/` and security corollaries in
[`Security/EncodingInstances.lean`](../../HashSig/GXMSS/Security/EncodingInstances.lean).

## Construction and observation

Let `N = 2^h`, `D = 2^w`, and let `I = [a,b]` be a nonempty inclusive interval
with `a ≤ b < N`. The constructor captures `I` and the finite retry budget `K`
before sampling public parameters. Key generation is parameterless. The ideal
interval scheme retains a complete sampled chain-start array and independent
uniform digests at the roots of maximal inactive subtrees. Only active starts
affect its public tree and honest signatures. Verification remains defined at every
epoch, including inactive epochs.

[`Interval/Merkle.lean`](../../HashSig/GXMSS/Interval/Merkle.lean) defines the
frontier and its addressed tree interpretation.
[`Interval/Scheme.lean`](../../HashSig/GXMSS/Interval/Scheme.lean) defines
`GXMSS.Interval.scheme`. Shared complete-tree keys, signatures and verification
live in [`Scheme.lean`](../../HashSig/GXMSS/Scheme.lean). Chain tweaks advance
from `k + 1`; Merkle collision witnesses retain the honest ordered child pair as
`first` and the forged pair as `second`.

The synchronized signature games use native returned-output measures. Missing
mass remains unreturned mass. The encoding and retry `missingMass` definitions
observe returned outputs through the constant Boolean `true` map and subtract
that returned mass from one; `LosslessSampler` requires the same Boolean mass to
be one. A returned `none` signature, retry exhaustion,
and a returned `false` experiment outcome are distinct observations. A signing
request consumes its epoch even when signing fails. `SigningQueryBound qs A`
counts every request along every supported execution, including repeated,
failed and inactive requests. Strong freshness excludes the exact previously
returned epoch/message/signature triple; a different signature for the same
message can remain strongly fresh. Deterministic signing alone does not imply
uniqueness of valid signatures.

[`Interval/Completeness.lean`](../../HashSig/GXMSS/Interval/Completeness.lean) proves
`GXMSS.Interval.complete_isActive`: for every generated key, signing at each active epoch
has correctness error at most `δ^K` under the encoding's uniform error bound `δ`.
`SyncSignatureAlg.CompleteOn` restricts the epoch quantifier while retaining per-key
correctness and all failure mass. Its unrestricted form agrees with `Complete`.
Inactive epochs have zero success mass; full-range interval correctness recovers `Complete`.

## Interval security

Import
[`HashSig.GXMSS.Security.Interval.Unforgeability`](../../HashSig/GXMSS/Security/Interval/Unforgeability.lean).
The theorem
`GXMSS.Interval.Unforgeability.strong_unforgeability_reduction_bound`
bounds strong synchronized unforgeability by the adjacent numerical definition
`strongUnforgeabilityBound`.
Writing `L = b-a+1` and `C = L*v*(D-1)`, its ten terms are

```text
MerkleTCR + EncodingTCR + SameMessageRandomizerChainTCR + ChainCutTCR
+ C*ChainPRE + C*(D-1)*ChainUD
+ VectorUD + VectorPRE + PairUD + PairPRE.
```

Each term uses a named reduction. Chain challenges use the original digest
domain `H`; filler challenges use endpoint vectors `Fin v → H` and ordered
child pairs `H × H`. The Merkle TCR capacity is `2*N*v*D`, each chain TCR
capacity is `N*v*D`, the encoding problem holds `qs` records with retry budget
`K`, and chain PRE/UD use one selected challenge. Filler capacities count the
frontier nodes in their respective vector and pair families. They are not
padded into the chain domain.

The theorem requires sampleable `H` and retry-randomizer type `R`, the declared
decidable equalities, `0 < v`, `0 < w`, two distinct members of the same global
code, and `SigningQueryBound qs A`. The public seed is drawn from the actual
`TweakableHash.seedGen` of `hash.thf`; the direct theorem adds no uniform-public-seed assumption.
`strong_unforgeability_power_of_two_reduction_bound` relaxes
the chain coefficients to `L*v*D` and `L*v*D²`, retaining the four separate
filler terms.

## Complete-tree specialization

[`Security/Interval/Reductions/FullRange.lean`](../../HashSig/GXMSS/Security/Interval/Reductions/FullRange.lean)
transports actual named experiments and advantages at `Interval.full h`.
The frontier is empty, so its filler terms vanish. `strongUnforgeabilityBound_full`
identifies the exact chain contribution as

```text
N*v*(D-1)*PRE + N*v*(D-1)²*UD.
```

`powerOfTwoStrongUnforgeabilityBound_full` identifies the relaxed contribution
as `N*v*D*(D*UD + PRE)`. Both identities retain the four complete-tree collision
reductions. These displayed right-hand-side identities are separate from
scheme equality and whole regular/strong experiment transport.

The ordinary theorem module
[`Security/Unforgeability.lean`](../../HashSig/GXMSS/Security/Unforgeability.lean)
defines and proves
`GXMSS.Unforgeability.strong_unforgeability_reduction_bound`.
Its adjacent `reductionBound` definition gives the numerical sum of four collision
advantages and the two weighted chain advantages. The proposition
`StrongUnforgeabilityReductionBound` retains the pathwise signing-query implication
and applies that sum to the named reductions. The proof applies the interval theorem
at full range and transports the experiment and displayed bound. Lower reductions
remain independently inspectable under `Security/Reductions/`; encoding-specific
corollaries require the separate `Security/EncodingInstances.lean` import.

## Shared-response PRF derivation

[`PRFDerivedScheme.lean`](../../HashSig/GXMSS/PRFDerivedScheme.lean) defines
`GXMSS.PRFDerived.Query`, with public-seed, chain-start and retry families.
[`Interval/PRFDerivedScheme.lean`](../../HashSig/GXMSS/Interval/PRFDerivedScheme.lean)
adds a typed filler family. Distinct typed coordinates separate the families.
One persistent cache stores the full response before applying a projection;
repeated coordinates reuse that response. No independence between projections
of the same response is assumed.

The complete endpoint
`GXMSS.PRFDerived.Unforgeability.strong_unforgeability_reduction_bound` in
[`Security/PRFDerivedUnforgeability.lean`](../../HashSig/GXMSS/Security/PRFDerivedUnforgeability.lean)
uses its adjacent numerical `GXMSS.PRFDerived.Unforgeability.strongUnforgeabilityBound`:
one named shared-response PRF advantage plus the complete direct bound. It
uses the complete additive PRF hop and three projection laws:

- Public parameters have the actual hash public-seed distribution.
- Chain starts have the uniform `H` distribution.
- Retry randomizers have the uniform `R` distribution.

It also requires the PRF's actual `UniformKey` law and its declared sampling
and equality instances. Its function-query bound is `1 + N*v + qs*K`.

The general interval endpoint
`GXMSS.Interval.PRFDerived.Unforgeability.strong_unforgeability_reduction_bound`
in
[`Security/Interval/PRFDerivedUnforgeability.lean`](../../HashSig/GXMSS/Security/Interval/PRFDerivedUnforgeability.lean)
uses its adjacent numerical
`GXMSS.Interval.PRFDerived.Unforgeability.strongUnforgeabilityBound`:
one named PRF advantage plus the exact ten-term interval bound. It requires
all direct-theorem premises, `UniformKey`, and four separate projection laws:
the three above plus uniform `H` filler digests. Its function-query bound is
`1 + L*v + F + qs*K`, where `F` is the frontier cardinality. The bound charges
eager retry suffixes even when an earlier retry succeeds. It bounds function
queries, not runtime or distinct cache misses.

[`Security/Interval/Reductions/PRFDerivedFullRange.lean`](../../HashSig/GXMSS/Security/Interval/Reductions/PRFDerivedFullRange.lean)
restricts the four-family PRF evaluator to the three complete families while
preserving its actual key generator. `fullRangeRealCorrespondence`,
`fullRangeIdealCorrespondence` and `fullRangePRFAdvantage` transport whole
experiment measures and the distinguishing advantage. Real transport assumes
no key-distribution or projection law; ideal transport needs sampleable
responses and query equality, with no projection law or finite query-domain
premise. `fillerQueries_full_bound` proves zero filler queries.
`fullRangeDisplayedBound` gives the complete displayed right-hand side.
`fullRangeStrongReductionBound` is a three-law full-range corollary with the
adjacent numerical `fullRangeStrongUnforgeabilityBound`. It needs no filler
projection law because the full range has no filler coordinate.

## Modules and consumer evidence

Construction files live at the GXMSS root and under `Encoding/` and `Interval/`.
Security endpoints live under `Security/` and `Security/Interval/`, named reductions
under their `Reductions/` directories, and support under their `Auxiliary/`
directories. PRF-derived components use descriptive `PRFDerived` filenames in
these same directories. Their namespaces still distinguish complete and interval
PRF games.

| Responsibility | Module or namespace |
| --- | --- |
| Generic synchronized interfaces and games | `VCVio.CryptoFoundations.SyncSignatureAlg` |
| Codewords and arbitrary incomparable encoding | `HashSig.GXMSS.Encoding.*`, `GXMSS.Encoding` |
| Shared simulation and witness support | `HashSig.GXMSS.Security.Auxiliary.*` |
| Named complete-tree reductions | `HashSig.GXMSS.Security.Reductions.*`, `GXMSS.Reductions` |
| Interval reductions and full-range transports | `HashSig.GXMSS.Security.Interval.Reductions.*`, `GXMSS.Interval.Reductions` |
| Interval simulation and witness support | `HashSig.GXMSS.Security.Interval.Auxiliary.*` |
| Interval final bounds | `HashSig.GXMSS.Security.Interval.Unforgeability`, `GXMSS.Interval.Unforgeability` |
| Complete shared-response PRF hop | `GXMSS.PRFDerived.Unforgeability` |
| Interval shared-response PRF hop and full-range transports | `GXMSS.Interval.PRFDerived.Unforgeability` |

[`DirectEndpointApplications.lean`](../../HashSigTest/GXMSS/DirectEndpointApplications.lean)
and [`PRFEndpointApplications.lean`](../../HashSigTest/GXMSS/PRFEndpointApplications.lean)
are ordinary public-import consumers. The direct consumer states and applies
the expanded ten-term theorem.
[`CompleteEndpointApplication.lean`](../../HashSigTest/GXMSS/CompleteEndpointApplication.lean)
imports only the ordinary `Security.Unforgeability` theorem module and applies its theorem to
its expanded separate-term inequality, including the pathwise signing-query premise.
The PRF consumer applies the complete three-law, interval four-law and full-range three-law
security endpoints.
The construction tests retain
height-three `[2,4]` frontier examples, inactive vector/pair openings,
honest-first collision orientation, retry failures and exact-pair freshness.
Some implementation regressions import private kernels explicitly; the public
endpoint consumers do not. The repository axiom sweep checks the production libraries
under the unchanged zero-debt policy.

These statements do not establish a concrete LeanSig parameter instantiation,
Rust extraction, implementation refinement, measured runtime, the paper's full
asymptotic running-time claims, or cryptographic hardness of the named
problems. Optional padded or weighted variants, concrete runtimes and
extraction tools are outside the generic proof and consumer closure.
