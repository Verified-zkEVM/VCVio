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

The bound is proved on a direct transcription of SLH-DSA-SHAKE-128s and its game
(`Statement/Scheme.lean`, `Statement/Security.lean`, digests as bit vectors, answers as 240-bit
vectors) in `Proof/`, and carried to the library's scheme in `Bridge/`.

**On the transcription** (`Proof/WorkFinal.lean`, `hasSecurityBits_work`). The game is first
rewritten so that the honest hash graph is drawn before the adversary runs (`WarmedGame`,
`Presample`: the canonical graph of honest inputs is walked in topological order, every query
fresh, which leaves the outcome's law unchanged). A forgery then either reuses honest cells, which
forces FORS coverage of a fresh digest (bounded through the load-concentration lemmas `Fors*`),
or deviates, which forces a query to hit an honest cell or the message-PRF key. The two halves are
charged on separate ledgers: an answer half at `q / 2 ^ 128 + 2 ^ -126`
(`BySourceTarget.answerBound`) and a shared half at `(q - 8) / 2 ^ 128` on accepted forgeries
(`ShareJointShared.hshared`), counted in one game that is blind to both the secret seeds and the
message-PRF key (`Share*`); `WorkTarget` sums them to `q / 2 ^ 127`. Below 569 counted calls nothing
wins, since verifying an accepted forgery alone costs that many (`WorkFinal.advantage_eq_zero`).

**The bridge** (`Bridge/`). `Bridge.model` is the transcription as a `Game.ExternalScheme`, whose
game is the transcription's game by definition (`PaperGame.lean`). `Transfer.lean` proves that
`HasSecurityBits` transfers along a `SchemeBridge`: a bijection of oracle answers that maps the
uniform answer to the uniform answer, under which signing and verification agree as programs and
key generation agrees in law (`hasSecurityBits_of_bridge`). `Encodings.lean` relates the data
(digests, answers, addresses, framing, digest parsing, WOTS+ digits, signature codecs), and
`Wots`, `Xmss`, `Fors`, `Hypertree` and `Scheme` prove the program equalities component by
component, with the same queries in the same order on both sides; `Scheme.schemeBridge` is the
bridge and `hasSecurityBits_fips205` the transfer.

## Scope

* SLH-DSA-SHAKE-128s, pure mode, deterministic signing. Hedged signing, the prehash mode and the
  other parameter sets are not covered.
* The oracle has fixed 30-byte answers, the longest SHAKE256 output FIPS 205 reads at this set.
* Classical random-oracle model; nothing is quantum.
