# End-to-End Crypto Examples

This page collects compact examples that show how the cryptographic framework
layers compose on concrete schemes.

## Schnorr Signature EUF-CMA

An end-to-end EUF-CMA reduction for the Schnorr digital signature lives in
[`Examples/Schnorr/Signature.lean`](../../Examples/Schnorr/Signature.lean). It is a compact
illustration of how the main composition layers of the framework fit together
on a single concrete scheme. Reading order:

1. **Σ-protocol:** [`Examples/Schnorr/SigmaProtocol.lean`](../../Examples/Schnorr/SigmaProtocol.lean)
   defines `Schnorr.sigma` and proves perfect completeness, special soundness,
   and perfect HVZK, plus the two simulator-distribution facts the
   Fiat-Shamir reduction needs (`sigma_simCommitPredictability` and
   `sigma_simChalUniformGivenCommit`).
2. **Generic Fiat-Shamir transform:**
   [`VCVio/CryptoFoundations/FiatShamir/Sigma.lean`](../../VCVio/CryptoFoundations/FiatShamir/Sigma.lean)
   builds a signature scheme `FiatShamir σ hr M` from any Σ-protocol `σ` and
   generable relation `hr`, with a fresh random-oracle runtime
   `FiatShamir.runtime`.
3. **Reductions:**
   [`VCVio/CryptoFoundations/FiatShamir/Sigma/Security.lean`](../../VCVio/CryptoFoundations/FiatShamir/Sigma/Security.lean)
   exposes `euf_cma_to_nma` (CMA → managed-RO NMA via HVZK simulation, for the
   NMA adversary `cmaToNmaAdv`) and `euf_nma_bound` (managed-RO NMA → witness
   extraction via the replay forking lemma and special soundness, for the
   witness finder `nmaReduction`), composed in `euf_cma_bound` for
   `cmaReduction`. The reductions are named in every statement:
   `∃ reduction, bound ≤ Pr[= true | hardRelationExp hr reduction]` holds
   trivially, because a classical choice of witness per statement succeeds with
   probability `1`.
4. **Forking lemma:** the replay-based forking lemma lives in
   [`VCVio/CryptoFoundations/ReplayFork.lean`](../../VCVio/CryptoFoundations/ReplayFork.lean)
   and is specialized to Fiat-Shamir managed-RO traces in
   [`VCVio/CryptoFoundations/FiatShamir/Sigma/Fork.lean`](../../VCVio/CryptoFoundations/FiatShamir/Sigma/Fork.lean)
   as `Fork.replayForkingBound`.
5. **Hardness:** the discrete-log assumption and the generable relation lift
   live in
   [`VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`](../../VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean).

The combined statement, `Schnorr.signature_euf_cma`, instantiates
`FiatShamir.euf_cma_bound` with the Schnorr Σ-protocol facts and delivers the
Pointcheval-Stern bound

```
ε' · ( ε' / (qH + 1)  -  1 / |F| )   ≤   Pr[ dlogReduction adv qH succeeds in dlogExp g ],
ε' := ε  -  qS · (qS + qH) / |F|,
```

where `ε` is the EUF-CMA advantage of an adversary with `qS` signing-oracle
queries and `qH` random-oracle queries. The denominator `qH + 1` is the
textbook Pointcheval-Stern denominator. The Fiat-Shamir reduction wraps the
source adversary so the forgery's hash point is always among the forkable
positions: it appends one explicit `(message, commit)` query for the forgery's
hash point on top of the source's `qH` queries, and applies the replay-forking
lemma at fork slot parameter `qH`. The framework's
`Fork.forkPoint qH : Option (Fin (qH + 1))` provides exactly enough slots for
the wrapped adversary's `qH + 1` total queries (no double-counting). As a
result, the bound is *unconditional* in `pk`: there is no remaining "verifier
accepts a uniform challenge" term that would have to be discharged separately
for keys on which verification is independent of the challenge.

## Fixed-Statement Fiat–Shamir Extraction

[`FiatShamir/Sigma/KnowledgeExtraction.lean`](../../VCVio/CryptoFoundations/FiatShamir/Sigma/KnowledgeExtraction.lean)
starts with an ordinary prover given its statement and message before execution. Its named
adapter appends the final verification query to an initially empty cached oracle and proves
that forkable acceptance equals acceptance of the actual verifier. `knowledgeExtractor_success`
then gives the existing replay reduction's valid-witness bound at that fixed statement.
Failed forks retain the reduction's uniform-witness fallback.

[`FiatShamir/Sigma/ExtractionCost.lean`](../../VCVio/CryptoFoundations/FiatShamir/Sigma/ExtractionCost.lean)
proves an all-branch bound of `2 * (Q + 1)` fresh challenge requests for the replay program
used by that same extractor, from a bound of `Q` source hash calls. The appended verifier slot
is counted once. Internal uniform randomness, cache hits, and pure cursor traversal are separate
from this resource; the bound is not a machine-time or PPT certificate.
The reusable replay bound is in
[`ReplayForkCost.lean`](../../VCVio/CryptoFoundations/ReplayForkCost.lean).

[`VCVioTest/FiatShamirKnowledgeExtraction.lean`](../../VCVioTest/FiatShamirKnowledgeExtraction.lean)
checks zero-query acceptance with a challenge-independent verifier, adaptive final-query
cache hits and misses, and the corresponding extraction budgets.

## Restricted Schnorr Challenges

[`VCVio/CryptoFoundations/SigmaProtocol/ChallengeRestriction.lean`](../../VCVio/CryptoFoundations/SigmaProtocol/ChallengeRestriction.lean)
transports perfect completeness and unique responses along any challenge map, and special
soundness along an injective map. The retained commitment simulator does not by itself certify
the distribution of full transcripts after changing the challenge policy.

[`Examples/Schnorr/ChallengeRestriction.lean`](../../Examples/Schnorr/ChallengeRestriction.lean)
proves equality of the honest and simulated transcript measures for the actual restricted
challenge distribution. That simulation theorem allows noninjective encodings.
[`Examples/Schnorr/BoundedChallenges.lean`](../../Examples/Schnorr/BoundedChallenges.lean)
embeds `Fin c` into `ZMod p` injectively when `c ≤ p`; primality of `p` is a separate
requirement for instantiating Schnorr over a field.

[`VCVioTest/SigmaChallengeRestriction.lean`](../../VCVioTest/SigmaChallengeRestriction.lean)
checks the field-of-order-seven instance, the empty and full-size embedding boundaries,
aliasing above the modulus, and a noninjective restriction that destroys special soundness.
These are algebraic fixtures, not concrete security parameters.

## ROM Commitment Scheme

A second end-to-end example, exercising a different axis of the framework
(caching, logging, identical-until-bad, birthday bounds), lives in
[`Examples/CommitmentScheme.lean`](../../Examples/CommitmentScheme.lean). It
proves binding, extractability, and hiding bounds for the textbook ROM
commitment scheme

```
Commit(m) = (H(m, s), s),     s ←$ S,
Check(c, m, s) = (H(m, s) == c).
```

Reading order:

1. **Shared ROM definitions:**
   [`Examples/CommitmentScheme/Common.lean`](../../Examples/CommitmentScheme/Common.lean)
   defines the random oracle `CMOracle : (M × S) → C`, the scheme algorithms
   `CMCommit` and `CMCheck`, and the basic single-fresh-query unpredictability
   bound `probEvent_from_fresh_query_le_inv` (`1/|C|`) that all three security
   proofs reduce to.
2. **Binding:**
   [`Examples/CommitmentScheme/Binding.lean`](../../Examples/CommitmentScheme/Binding.lean)
   proves both a tight bound `binding_bound` (`(t·(t-1) + 2) / (2·|C|)`) by
   direct case-split on cache collisions versus fresh verification queries,
   and a looser standard-model-style bound `binding_bound_via_cr_chain`
   mirroring `bindingAdvantage_toCommitment_le_keyedCRAdvantage` from
   [`VCVio/CryptoFoundations/HashCommitment.lean`](../../VCVio/CryptoFoundations/HashCommitment.lean).
3. **Extractability:**
   [`Examples/CommitmentScheme/Extractability.lean`](../../Examples/CommitmentScheme/Extractability.lean)
   exhibits the explicit log-scanning extractor `CMExtract` and proves
   `extractability_bound` (`(t·(t-1) + 2) / (2·|C|)`, for `t ≥ 3`).
4. **Hiding:** the
   [`Examples/CommitmentScheme/Hiding/`](../../Examples/CommitmentScheme/Hiding/)
   subtree builds the identical-until-bad chain. The packaged theorem
   `hiding_bound_finite` in
   [`Examples/CommitmentScheme/Hiding/Main.lean`](../../Examples/CommitmentScheme/Hiding/Main.lean)
   delivers the bound

```
tvDist(hidingMixedReal A, hidingMixedSim A)  ≤  t / |S|,
```

where the salt is sampled inside the experiment and `t` is the adversary's
total query budget. The bound is intrinsically averaged over the salt: the
per-salt version is false.

The framework machinery exercised: `cachingOracle`, `loggingOracle`,
`IsTotalQueryBound`, the birthday bound
`probEvent_cacheCollision_le_birthday_total_tight`, and the identical-until-bad
TVD bound `tvDist_simulateQ_le_probEvent_bad_dist`.

## PRF Tag/Reader Network Unlinkability

[`Examples/PRFTagReader/NetworkUnlinkability.lean`](../../Examples/PRFTagReader/NetworkUnlinkability.lean)
connects the actual bounded FIFO packet run to the named multiple- and single-session PRF
reductions. Its ideal services use the association-list cache from
[`CacheRepresentation.lean`](../../Examples/PRFTagReader/CacheRepresentation.lean), including
the instrumented service's retained collision flag.

`NetworkUnlinkability.full_unlinkability` bounds the absolute real-network verdict gap by the
two named PRF advantages and four explicit losses:

- session collisions: `sessionsPerTag² · |TagId| / |Nonce|`;
- multiple-session reader cells: `qReader · |TagId| / |Digest|`;
- reader/tag nonce aliasing: `qReader · qTag / |Nonce|`;
- single-session reader cells: `qReader · |TagId| · sessionsPerTag / |Digest|`.

`named_reduction_budgets` gives the actual distinguishers' PRF-query bounds:
`qTag + qReader · |TagId|` and `qTag + qReader · |TagId| · sessionsPerTag`. These are
pathwise oracle-query counts, not machine-time or PPT certificates.
The FIFO service model and its derived schedule remain those of `Network.lean`.
The free-program uniform-sampling model supplies probability measures for the real runs;
there is no additional losslessness assumption.

The PRF-real faithfulness lemmas in `PRFReductions/Reductions.lean` expose equality of the
whole programs. `multipleBad_bad_le_sessionCollisionBound` takes a native event bound on
the nonce sampler and bounds the measure of the final Boolean collision observation.
The underlying legacy collision induction remains at its existing compatibility boundary.

## Fischlin extraction and log inspections

`VCVio/CryptoFoundations/Fischlin/ExtractionGuarantee.lean` retains the actual verifier verdict
and the optional witness from `onlineExtract` in one run. The verifier continues the prover's
random-oracle cache, while extraction uses only the log captured before verification. The
single-proof soundness bound therefore gives an acceptance-minus-error lower bound for that
named extractor at a fixed statement and message.

`ExtractionCost.lean` instruments the same nested log search. Erasing the counter recovers the
actual extractor as a program equality; each execution inspects at most `ρ * log.length` records.
Empty logs and zero repetitions cost zero, and a first-record match in a single repetition stops
after one inspection. Record comparisons and sigma verification have separate computational cost.
`VCVioTest/FischlinExtraction.lean` exercises these laws through ordinary imports.

## Merkle Checkpoint Observation

[`Examples/MerkleCheckpoints.lean`](../../Examples/MerkleCheckpoints.lean) contains two
concrete executions using the library's Merkle tree constructor, multi-extractability
game, and batch verifier.

A commitment made before querying has frozen-checkpoint failure probability `1/2`.
Reconstructing that checkpoint from the terminal adversarial log instead reports zero
failure. The generic laws in
[`MultiExtractability/DelayedObservation.lean`](../../VCVio/CryptoFoundations/MerkleTree/MultiExtractability/DelayedObservation.lean)
retain the required extraction-drift charge. The charge is exactly `1/2` in this example,
so it cannot simply be dropped. Recorded-checkpoint membership and honest acceptance
stay fixed when comparing the observers.

The second execution compares honest construction and verification with shared versus
fresh random-oracle responses. A shared live cache accepts with probability one;
resampling between phases accepts with probability `1/2`. Clearing memoization while
keeping the same underlying fixed hash function still accepts, as
`reset_same_table_accepts` proves. This distinguishes a representation change from a
change to the oracle's stateful behavior.

## Bounded Schnorr transform guarantees

`Examples/Schnorr/Transforms.lean` instantiates the Fiat–Shamir and Fischlin extraction bounds
with one challenge-restricted Schnorr protocol. An injective scalar encoding gives special
soundness; an injective scalar action by the generator also supplies Fischlin's unique-response
hypothesis. The theorems name their actual extractors and preserve the generic error terms.

Fiat–Shamir uses a finite, sampleable challenge type and has a pathwise replay budget of
`2 * (Q + 1)` fresh challenge requests. Fischlin additionally enumerates challenges for its
honest signing search and inherits the exact finite-geometric expected hash-call formula.
Completeness uses the existing bundled Fischlin runtime over actual keygen/sign/verify code.
`VCVioTest/SchnorrTransforms.lean` checks these interfaces with three challenges in `ZMod 7`,
including a concrete accepting transcript pair that recovers scalar `3` after one log inspection.
