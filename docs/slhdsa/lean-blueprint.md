# Lean blueprint

## Current module ladder

```text
Bytes -> Params -> Address -> Encoding -> Position
  -> Primitives.Interface -> Concrete.Sha2 / Concrete.Keccak / Concrete.FIPS
  -> WotsEncoding -> Wots
  -> Xmss -> XmssConformance
  -> Fors -> ForsConformance
  -> HypertreeGeneral -> GeneralScheme
  -> external API / codecs

Security.Notions -> OracleSurface -> Transcript -> Architecture
  -> ReachableTargets -> CanonicalGames -> TraceTargets
  -> component reductions -> composition -> asymptotics
```

The construction kernel already contains arbitrary-depth typed hypertree and internal-scheme
programs. Their pure/fixed-answer honest correctness, naturality, and finite structural query upper
bounds are proved. Callback-parametric XMSS and arbitrary-depth hypertree programs refine the
canonical explicit-query programs and their fixed-answer pure interpretations, including the
intentional discarded final recovery at depth one. WOTS, XMSS, and FORS retain one canonical
algorithm each; conformance modules are thin typed/refinement layers rather than competing
implementations.

## Remaining technical order

1. Implement fixed-width signature/key codecs and external pure/pre-hash APIs, including context
   length, OID/output-strength records, deterministic/hedged modes, and rejection laws.
2. Complete implementation-level ACVP key-generation/signing/verification evidence for every
   claimed parameter/hash cell with independently reproducible provenance.
3. Refine construction execution into the security transcript: encoded address injectivity,
   target-input pairing, nonempty distinct-target batches, FORS/XMSS/hypertree query coverage, and
   the outer-CMA signing-log correspondence.
4. Relate the construction-specific experiments to the canonical generic games; implement the
   selected `CountingInterface` and concrete `ReductionAdversaries`.
5. Prove component WOTS/FORS/XMSS/HT, PRF/PRFmsg, and Hmsg/ITSR reductions with exact target/query
   transformations; bound the same-message SUF residual and prove the classical master inequality.
6. Add parameter-family polynomial/negligibility results. Treat QROM lifting as a separate semantic
   development, not a relabeling of classical `OracleComp` theorems.
7. Once a deployment repository, revision, ABI, and toolchain are selected, prove the executable
   byte/API refinement and document its operational assumptions.

## Proof discipline

Construction theorems state width, bounds, canonicality, erasure/refinement, and deterministic
correctness explicitly. Security theorems use generated public-key material and actual adversary
query predicates. Formula-derived target counts are upper bounds; an execution may make fewer or no
target queries. Executability and elaboration are checked separately, and neither is substituted
for cryptographic hardness or standards conformance.
