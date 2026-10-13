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
| Generic signature interfaces | [Single](../../VCVio/CryptoFoundations/SyncSignatureAlg.lean), [multi](../../VCVio/CryptoFoundations/SyncMultiSignatureAlg.lean) | Captured configuration, abstract epochs, optional signing failure, deterministic verification, and completeness. |
| Generic security notions | [Single](../../VCVio/CryptoFoundations/SyncSignatureAlg/Security.lean), [multi](../../VCVio/CryptoFoundations/SyncMultiSignatureAlg/Security.lean) | Regular and strong single-signature security, and regular multi-signature security. |
| Encodings | [Incomparable encoding](../../HashSig/GXMSS/Encoding/Incomparable.lean), [retry](../../HashSig/GXMSS/Encoding/Retry.lean) | A global incomparable code, randomized encoding with failure, and retry laws retaining returned failure and missing mass. |
| Scheme | [Construction](../../HashSig/GXMSS/Scheme.lean), [completeness](../../HashSig/GXMSS/Completeness.lean) | Independent chain starts, bounded encoding retries, chain verification, and Merkle authentication. |
| General security | [Reduction games](../../HashSig/GXMSS/Security/ReductionGames.lean), [bound](../../HashSig/GXMSS/Security/Unforgeability.lean) | Explicit reductions to the authoritative tweakable-hash and encoding target-collision games. |
| Encoding instances | [Checksum](../../HashSig/GXMSS/Encoding/Winternitz.lean), [target sum](../../HashSig/GXMSS/Encoding/TargetSum.lean) | Incomparability, error bounds under the stated distribution premises, and code-size facts. |
| Specialized security | [Encoding-specific bounds](../../HashSig/GXMSS/Security/EncodingSpecializedUnforgeability.lean) | Composition with reductions from encoding collisions to the message hash's SM-DT-rTCR game. |

## Security statement

`GXMSS.Unforgeability.strong_unforgeability_reduction_bound_of_two_codewords` bounds the
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

`GXMSS.Encoding.SpecializedUnforgeability.winternitz_strong_unforgeability_bound` discharges
the two-codeword premise using the checksum parameters. The target-sum theorem uses the exact
condition that at least two words meet the target, with a sufficient small-target corollary.
Both instances require injective epoch-to-tweak addressing and agreement of the encoding and
scheme public-seed samplers. Their encoding term is charged to a named SM-DT-rTCR reduction.

Completeness is separate from this security inequality. Under the stated lossless sampling laws
and a one-attempt error bound `δ`, the retry completeness loss is bounded by `δ^K`.
The model samples chain starts independently; it does not claim security of a PRF-derived
implementation or a concrete deployed hash instantiation.

## Validation and review

The tests under `HashSigTest/GXMSS/` check concrete chain and Merkle conventions, retry failure
and missing mass, checksum and target-sum examples, and imported security theorem types,
compiler origins, and transitive axioms. The synchronized-signature tests under `VCVioTest/`
distinguish regular from strong freshness, replay from alternative valid signatures, and failed
signing from an unused epoch. The repository axiom sweep covers the new proof modules.

Review the scheme and the statement of each bound first, then the encoding or game component
of interest. A successful build checks the Lean statements; choosing the intended encoding,
hash assumptions, and sampling interpretation remains a mathematical review responsibility.
