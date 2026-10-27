# Generalized XMSS

The GXMSS development specifies the abstract construction of
[DKKW25](../../REFERENCES.md#dkkw25), proves completeness under explicit sampling laws,
and gives concrete bounds for strong synchronized unforgeability. The general construction
accepts an arbitrary incomparable encoding. Checksum and target-sum encodings have their own
incomparability, error, target-collision, and specialized scheme bounds.

The formal argument differs from the paper's proof in some technical details and assumes that
the global code contains at least two distinct codewords. This is a natural nondegeneracy
condition excluding empty and singleton codes. The generic encoding interface still admits those
codes; the security theorem states the extra premise explicitly. Formal running-time analysis
is outside this development.

## Reading order

| Component | Entry point | Content |
| --- | --- | --- |
| Generic signature foundations | [Single](../../VCVio/CryptoFoundations/SyncSignatureAlg.lean), [multi](../../VCVio/CryptoFoundations/SyncMultiSignatureAlg.lean) | Algorithms, completeness, regular and strong single-signature security, and regular multi-signature security. |
| Encodings | [Incomparable encoding](../../HashSig/GXMSS/Encoding/Incomparable.lean), [retry](../../HashSig/GXMSS/Encoding/Retry.lean) | A global incomparable code, randomized encoding with failure, and retry laws retaining returned failure and missing mass. |
| Scheme | [Construction](../../HashSig/GXMSS/Scheme.lean), [completeness](../../HashSig/GXMSS/Completeness.lean) | Independent chain starts, bounded encoding retries, chain verification, and Merkle authentication. |
| General security | [Reduction games](../../HashSig/GXMSS/Security/Reductions/JointReductions.lean), [bound](../../HashSig/GXMSS/Security/Unforgeability.lean) | Explicit reductions to the authoritative tweakable-hash and encoding target-collision games. |
| Encoding instances | [Checksum](../../HashSig/GXMSS/Encoding/Winternitz.lean), [target sum](../../HashSig/GXMSS/Encoding/TargetSum.lean) | Incomparability, error bounds under the stated distribution premises, and code-size facts. |
| PRF-derived sibling | [Derived construction](../../HashSig/GXMSS/PRFDerivedScheme.lean), [conditional strong bound](../../HashSig/GXMSS/Security/PRFDerived/Unforgeability.lean) | One abstract keyed evaluator supplies the public parameter, chain starts, and retry randomizers; a named PRF reduction connects its strong game to the ideal scheme. |
| Specialized security | [Encoding-specific bounds](../../HashSig/GXMSS/Security/Unforgeability.lean) | Composition with reductions from encoding collisions to the message hash's SM-DT-rTCR game. |

## Security statement

`Security/Unforgeability.lean` contains the signing-query predicate, the complete
reduction-bound proposition, and the generic and encoding-specific final theorems.
The modules under `Security/Reductions` establish the individual reduction bounds
and encoding-advantage comparisons used in their proofs.

`GXMSS.Unforgeability.strong_unforgeability_reduction_bound` bounds the
strong-unforgeability advantage of the ideal scheme by the advantages of named reductions.
It assumes positive chain count and digit width, two distinct members of the global code,
and `GXMSS.Unforgeability.SigningQueryBound`. This last premise counts every signing call
on every execution path, including repeated calls and calls answered with failure.

The bound has separate Merkle, encoding, first-chain, and second-chain target-collision terms,
and a joint undetectability/preimage term. Writing `N = 2^h`, `b = 2^w`, and `v` for the number
of chains, its shape is

```text
Adv_strong(A) ≤ Adv_Merkle(Bm) + Adv_encoding(Be) + Adv_chain(B1) + Adv_chain(B2)
               + N·v·b · (b·Adv_UD(Bu) + Adv_PRE(Bp)).
```

The actual statement names every reduction and fixes its authoritative hardness experiment.
It compares unnormalized returned-output measures. The encoding target-collision game has
capacity for the stated signing-query bound. The proof retains unused, successfully used,
and failed-but-consumed epochs. No running-time or reduction-query complexity theorem is asserted.

`GXMSS.Unforgeability.SpecificEncoding.winternitz_strong_unforgeability_bound` discharges
the two-codeword premise using the checksum parameters. The target-sum theorem uses the exact
condition that at least two words meet the target, with a sufficient small-target corollary.
Both instances require injective epoch-to-tweak addressing and agreement of the encoding and
scheme public-seed samplers. Their encoding term is charged to a named SM-DT-rTCR reduction.

Completeness is separate from this security inequality. Under the stated lossless sampling laws
and a one-attempt error bound `δ`, the retry completeness loss is bounded by `δ^K`.
The paper construction samples chain starts independently. The abstract PRF-derived sibling below
has a separate conditional reduction. Neither development establishes a concrete deployed hash
instantiation.

## Abstract PRF-derived sibling

`GXMSS.PRFDerived.scheme` captures one evaluator of type `Key → Query PP M h v → Response`
and an `Interpretation` of the common abstract response. The query constructors separate
`publicSeed`, parameter-indexed chain starts, and parameter/epoch/message/attempt-indexed retries.
Key generation samples only the evaluator key. Its distinguished response determines the public
parameter used by all later queries and the public root; the secret key is the evaluator key.
The arbitrary incomparable encoding and the ordinary GXMSS verifier remain shared.

`GXMSS.PRFDerived.Security.randgenPRFReduction` queries the public parameter and starts once,
retains the resulting signing material, forwards the source adversary's ambient sampling, and
answers each first signing request with its full finite retry-query budget. Duplicate epochs make
no function queries. A first request that returns signing failure still consumes its epoch. The
strong observation checks the exact message/signature pair against the complete signing history.
The ideal PRF experiment retains one persistent random-function cache across this interaction.
The signing operation records its first-success consumed prefix; the reduction's function-query
count charges the complete queried retry budget even when signing succeeds earlier.

The final `strong_reduction_bound` adds the advantage of this named PRF
reduction to every generic hardness term above, with the same target counts and coefficients.
Its explicit premises are `PRFScheme.UniformKey`, `PublicSeedSamplingLaw`,
`ChainStartSamplingLaw`, `RetrySamplingLaw`, the generic signing-query bound, positive chain count
and digit width, and two distinct global codewords. The three projection laws identify a uniform
abstract response with the THF public-parameter law, uniform chain starts, and uniform retry
randomizers respectively. They are obligations for an instantiation. The real-game theorem
identifies the full oracle program; the ideal correspondence compares unnormalized returned-output
measures, preserving returned failure and missing mass.

`randgenPRFReduction_functionQuery_bound` separately bounds right-summand function calls on every
path by `1 + 2^h * v + qs * budget`. It bounds this reduction's calls, and does not provide a
running-time or PPT transfer. The conditional strong theorem supplies no concrete PRF bound,
Ethereum encoding or filler-tree result, Rust correspondence, or implementation-security transfer.
It retains the generic two-codeword restriction and does not remove the paper proof's stated limits.

## Validation and review

The tests under `HashSigTest/GXMSS/` check concrete chain and Merkle conventions, retry failure
and missing mass, checksum and target-sum examples, and applications of the public security
theorems. The PRF-derived importing tests additionally check typed query separation, seed-only
keys, indexed retries and consumed prefixes, the five public security theorem statements, and
compiler origins and transitive axioms across the complete PRF security module family.
The synchronized-signature tests under `VCVioTest/`
distinguish regular from strong freshness, replay from alternative valid signatures, and failed
signing from an unused epoch. The repository axiom sweep checks the proof modules for axiom and `sorry` dependencies.

Review the scheme and the statement of each bound first, then the encoding or game component
of interest. A successful build checks the Lean statements; choosing the intended encoding,
hash assumptions, and sampling interpretation remains a mathematical review responsibility.
