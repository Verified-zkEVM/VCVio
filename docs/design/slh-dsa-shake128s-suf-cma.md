# SLH-DSA-SHAKE-128s: 127 bits of strong unforgeability in the random-oracle model

Status: design record for `HashSig/SLHDSA/SHAKE128s/`, established 2026-10-24.

## The statement

`SLHDSA.SHAKE128s.slhDsa_sufCma_127`
(`HashSig/SLHDSA/SHAKE128s/Statement/Theorems/StrongUnforgeability.lean`):

```lean
theorem slhDsa_sufCma_127 : Game.HasSecurityBits FIPS205.scheme Game.adversaryWork 127
```

* **The scheme** (`Statement/FIPS205.lean`): the library's FIPS 205 SLH-DSA at the
  SLH-DSA-SHAKE-128s parameters over one SHAKE256 random oracle on byte strings
  (`SLHDSA.Security.shakeRomScheme`, whose oracle answered by SHAKE256 is the library's FIPS 205
  SHAKE internal algorithms, `shakeRomScheme_map_shakeAnswer`), with deterministic signing
  (`opt_rand = PK.seed`) and the pure-mode external interface of Algorithms 22 and 24: requests
  carry a message and a context (`SLHDSA.External.encodePureMessage`), signatures are byte strings
  in the library's canonical encoding (`SLHDSA.encodeSignature`, `SLHDSA.decodeSignature`).
  Every SHAKE256 call, `PRF` and `PRF_msg` included, is a query of the shared oracle; the oracle
  answers 30 bytes and `F`, `H`, `T_ℓ`, `PRF`, `PRF_msg` read the first 16.
* **The game** (`Statement/Game.lean`): the adversary gets the public key, the random oracle and
  a signing oracle and outputs a request and a byte string; it wins when the string verifies and
  the signing oracle never returned that pair (strong unforgeability). Every hash call is counted
  by its source (adversary, key generation, signer, verification) and signing requests are
  counted too.
* **Bit security** (`Game.HasSecurityBits`): every adversary that makes at most `2 ^ 64` signing
  requests and whose counted work is at most `q ≥ 1` with probability one wins with probability at
  most `q / 2 ^ 127`. The counted work (`Game.adversaryWork`) is its signing requests, its own hash
  calls and the hash calls of verifying its forgery; key generation's and the signer's hash calls
  are free.

## The proof

The public game starts with an empty cache for its single byte-string oracle. Each signing
request carries its own message and context. The log records the request and its optional
reply, so even an overlong context costs one signing attempt. Freshness checks the pair
of request and signature. A different valid signature on a previously signed request can
therefore win. The verifier contributes the hash calls it actually makes on winning and
losing runs. Invalid framing or an undecodable signature returns false before hashing.
[External scheme](../../HashSig/SLHDSA/SHAKE128s/Statement/FIPS205.lean) ·
[Counted game](../../HashSig/SLHDSA/SHAKE128s/Statement/Game.lean)

To apply the construction proof from #766 with this budget, the reduction uses a guarded
execution. An admitted query returns the handler's reply and updated cache and cost. An
over-budget query, or any later query, receives the fallback and leaves the cache and
paid count fixed. The accounting proof follows the logged adversary through its direct
queries and signing callbacks. It follows final verification through the construction's
address ledger and the message hash at the returned public key. These local steps use
the calls that actually occur. The public theorem takes the almost-sure joint cap and
the original signing lifetime.
[Query guard](../../VCVio/OracleComp/QueryTracking/Enforcement.lean) ·
[Signing](../../HashSig/SLHDSA/SHAKE128s/Proof/ActualWork/Work/Signing.lean) ·
[Verification](../../HashSig/SLHDSA/SHAKE128s/Proof/ActualWork/Work/Verification.lean)

For each supported guarded run, `native_whole_reserve` relates the final cache entries,
signer and forger digest counts, and paid work of that same run. Those quantities bound
the charge for graph conflicts and hidden-value queries. The remaining fresh forgeries
require FORS coverage. The estimates from #912 apply to the digest blocks actually
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
hash. Below 569 its separate zero-success theorem needs only the weighted cap.
[Scalar policy certificates](../../HashSig/SLHDSA/SHAKE128s/Bridge/SharedExperiment/ScalarPolicy/Certificates.lean) ·
[Byte-sensitive example](../../Examples/SLHDSA/WeightedPolicy/Certificates.lean)

For fixed-context adversaries with separate structural caps on their hash and signing
queries, `wireStrongAdvantage_le_jointWorkBound` takes the minimum of the parameterized
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

* SLH-DSA-SHAKE-128s, pure mode, deterministic signing. Hedged signing, the prehash mode and the
  other parameter sets are not covered.
* The oracle has fixed 30-byte answers, the longest SHAKE256 output FIPS 205 reads at this set.
* Classical random-oracle model; nothing is quantum.
