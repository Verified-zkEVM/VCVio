# Strong unforgeability of deterministic SLH-DSA-SHAKE-128s

The FIPS byte-game theorem `slhDsa_sufCma_le` bounds the probability of a fresh verifying request/signature pair by `jointWorkBound q`. Its linear corollary `slhDsa_sufCma_127` gives at most `q / 2^127` for every positive budget. Both theorems concern classical queries to a random oracle and assume at most 2⁶⁴ signing attempts with probability one. [Native theorems](../../HashSig/SLHDSA/SHAKE128s/Statement/Theorems/StrongUnforgeability.lean) · [All profiles and algorithms](../agents/slh-dsa.md)

## Scheme and experiment

The external pure-mode interface takes a message and context and uses canonical signature bytes. Key generation samples independent uniform seeds. Deterministic signing sets `opt_rand = PK.seed`. All hash roles use one SHAKE oracle on byte strings. Each answer contains 30 bytes. The tweakable hashes, PRF and message PRF read the first 16 bytes. The concrete interpretation of the oracle by SHAKE256 recovers the library's internal algorithms. The security estimate uses random answers. [Scheme](../../HashSig/SLHDSA/SHAKE128s/Statement/FIPS205.lean) · [SHAKE interpretation](../../HashSig/SLHDSA/Security/ByteConformance.lean)

On each execution, the budget counts every signing attempt, every direct adversary hash query and every hash query made while verifying the final forgery. Repeats cost a query even on a cache hit. The cap holds with probability one. Key-generation and signer hashes use the same cache and have zero weight in this measure. [Counted game](../../HashSig/SLHDSA/SHAKE128s/Statement/Game.lean)

## How the two security arguments fit together

Both arguments use the native construction's classification of an accepting fresh forgery. Given a cache that replays key generation, the signing log and successful verification, the classification yields a target collision, a hidden hit, coverage at a fresh message-hash point, or a previously returned pair. Strong freshness excludes the last case. The structural reduction and the actual-work proof both invoke `bad_event_or_logged_of_settled`. [Shared classification](../../HashSig/SLHDSA/Security/RomSchemeBridge.lean) · [Structural client](../../HashSig/SLHDSA/Security/ByteLinkedView.lean) · [Actual-work client](../../HashSig/SLHDSA/SHAKE128s/Proof/ActualWork/Settlement/Coverage.lean)

The structural argument bounds the relevant events under separate adversary hash and signing caps. It covers the six SHAKE sets, with results for deterministic and hedged signing. The actual-work argument follows the events and resources of the same sampled run. Different executions can maximize different costs. Bounding each cost separately by its maximum can exceed the original joint allowance, and a bound observed on real runs need not bound every branch of an oracle program. This is why substituting query budgets in the structural theorem does not recover the specialized result. At the common fixed-context interface Lean applies the two estimates to one advantage and takes their minimum. [Structural bounds](slh-dsa-classical-rom-bound.md) · [Worked budget obstruction](slh-dsa-security-delta.md) · [Wire theorem](../../HashSig/SLHDSA/SHAKE128s/Statement/Theorems/WireStrongUnforgeability.lean)

## Proof of the actual-work bound

The public game starts with an empty cache for its single byte-string oracle. Each signing
request carries its own message and context. The log records the request and its optional
reply, so even an overlong context costs one signing attempt. Freshness checks the pair
of request and signature. A different valid signature on a previously signed request can
therefore win. The verifier contributes the hash calls it actually makes on winning and
losing runs. Invalid framing or an undecodable signature returns false before hashing.
[External scheme](../../HashSig/SLHDSA/SHAKE128s/Statement/FIPS205.lean) ·
[Counted game](../../HashSig/SLHDSA/SHAKE128s/Statement/Game.lean)

To apply the construction proof with this budget, the reduction uses a guarded
execution. An admitted query returns the handler's reply and updated cache and cost. An
over-budget query, or any later query, receives the fallback and leaves the cache and
paid count fixed. The accounting proof follows the logged adversary through its direct
queries and signing callbacks. It follows final verification through the construction's
address ledger and the message hash at the returned public key. These local steps use
the calls that actually occur. The public theorem takes the almost-sure joint cap and
the signing lifetime.
[Query guard](../../VCVio/OracleComp/QueryTracking/Enforcement.lean) ·
[Signing](../../HashSig/SLHDSA/SHAKE128s/Proof/ActualWork/Work/Signing.lean) ·
[Verification](../../HashSig/SLHDSA/SHAKE128s/Proof/ActualWork/Work/Verification.lean)

For each supported guarded run, `native_whole_reserve` relates the final cache entries,
signer and forger digest counts, and paid work of that same run. Those quantities bound
the charge for graph conflicts and hidden-value queries. The remaining fresh forgeries
require FORS coverage. The finite-tape FORS estimates apply to the digest blocks actually
consumed. Completing the deferred cache and drawing the final secret preserve the joint
distribution of both tapes and the original terminal result. The proof can therefore
price coverage and the weak-key event using that result's counters and public key.
[Terminal accounting](../../HashSig/SLHDSA/SHAKE128s/Proof/ActualWork/Work/Terminal.lean) ·
[Tape distribution](../../HashSig/SLHDSA/SHAKE128s/Proof/ActualWork/Coupling/Tapes.lean) ·
[Residual probability](../../HashSig/SLHDSA/SHAKE128s/Proof/ActualWork/Settlement/Probability.lean)

For a budget below 569, accepted verification alone would exceed the budget, so success
has probability zero. For `569 ≤ q < 2^127`, success is at most

```text
(32q − 1) / (16 · 2^128) + 34 · 1591788895347057694892543 / 2^256.
```

This is strictly smaller than `q / 2^127`. At and above `2^127`, the unit bound on a
probability gives the stated bit-security inequality. Both the middle-range bound and
the bit-security theorem assume the signing lifetime. The zero-success result only
requires the joint work cap.

For a different cost model, `ScalarPolicy.advantage_le_jointWorkBound` gives the
same piecewise bound at any natural budget `q`. The client proves that each event's
weight covers its original selected cost, that total weighted cost is at most `q` with
probability one, and that the signing lifetime holds. The byte-sensitive example charges
one per signing attempt and one plus the input length per direct adversary or verifier
hash. The example proves domination for these weights, so below 569 its caller supplies only
the weighted cap. A custom policy also needs the eventwise domination proof.
[Scalar policy certificates](../../HashSig/SLHDSA/SHAKE128s/Bridge/SharedExperiment/ScalarPolicy/Certificates.lean) ·
[Byte-sensitive example](../../Examples/SLHDSA/WeightedPolicy/Certificates.lean)

For a fixed valid context, structural caps `qh` and `qs`, and `qs ≤ 2^64`, `wireStrongAdvantage_le_jointWorkBound` takes the minimum of the parameterized
construction bound and `jointWorkBound (qh + qs + 3824)`. The 3824-call allowance is a
proved upper bound on verifier work for SHAKE-128s. The companion `wireStrongAdvantage_le`
gives the same minimum with
the linear work term `(qh + qs + 3824) / 2^127`.
[Wire theorem](../../HashSig/SLHDSA/SHAKE128s/Statement/Theorems/WireStrongUnforgeability.lean)

The bit-vector transcription presents the same deterministic algorithms with a different
representation of answers and keys. The component bridges identify hash queries, framing,
canonical signature bytes and verification results. Transporting the security result gives
the transcription's `WorkFinal.hasSecurityBits_work` at its original query accounting.
[Transcription theorem](../../HashSig/SLHDSA/SHAKE128s/Proof/WorkFinal.lean)

For a paper-model client that erases counts or proves zero success, the entry points are
`WorkFinal.map_fst_runAll` and `WorkFinal.advantage_eq_zero`. Clients that adapt the
observation or cost policy can use the shared experiment's count bounds and acceptance
certificate. The former `WorkFinal.setupBound`, `verifierFiles` and `hsharedFused` were
specific to the retired coupling and its records. Code that imported those intermediate
runs needs a new argument for its chosen experiment.
[Shared certificates](../../HashSig/SLHDSA/SHAKE128s/Bridge/SharedExperiment/Certificates.lean)

## Scope

The joint-work theorem covers deterministic pure-mode SHAKE-128s. It permits a different context on each request. The structural family supplies the pure-mode hedged and other SHAKE-profile results at a fixed valid context. A proof for a concrete implementation must also relate its bytes, randomness and charged operations to the relevant experiment. [Structural interface](../../HashSig/SLHDSA/Security/Wire.lean) · [Profile examples](../../Examples/SLHDSA/Profiles.lean)
