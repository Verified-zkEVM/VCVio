# SLH-DSA in the classical random-oracle model: the target bound and leanVM's 127-bit proof

Status: design record, established 2026-10-05. It fixes how the classical random-oracle bound for
FIPS 205 SLH-DSA is accounted, records the levels that accounting reaches, and compares the result
with the 127-bit proof for a SPHINCS variant in
[`leanEthereum/leanVM`](https://github.com/leanEthereum/leanVM) (`formal/sphincs`), whose argument
this work draws on. The development is in pull request #766; the implementation status of `main`
is in [`slh-dsa-status-and-roadmap.md`](slh-dsa-status-and-roadmap.md). No bound below is proved
yet: the levels are evaluations of the target formula, and their evaluation in Lean is owed.

## The statement

- **Model.** FIPS 205's internal functions (Algorithms 18–20) with the tweakable hash, `H_msg` and
  `PRF_msg` as random oracles (`hashSpec`, `romScheme` in `HashSig/SLHDSA/Security/Target.lean`).
  `PRF` is the tweakable hash at the PRF address types, which coincides with FIPS 205's `PRF` in
  both instantiations, so no separate PRF assumption enters. A faithfulness theorem, still owed, is
  to relate this three-oracle model to the byte-level scheme over a single SHAKE256; only that
  byte-level statement is to be presented as the result.
- **Budgets.** `UnforgeableAdversary.RomQueryBound adv q_h q_s` bounds, on every path of the
  forger's own program, its hash queries `q_h` (`PRF_msg` included, repeated queries counted) and
  its signing queries `q_s`. Key generation, signing and verification are not charged to `q_h`. The
  bound is stated for each fixed public seed.
- **Signing modes.** Hedged (`opt_rand` uniform) and deterministic (`opt_rand = PK.seed`) signing
  are both instances of the same statement.

## How the bound is accounted

A winning forgery fires one of three events (`bad_event_of_wins_romSchemeRun`): a same-key target
collision with an honest entry, a hit on a hidden chain value or unopened FORS secret, or coverage
of every FORS coordinate of the forgery's digest by logged signatures. Two further losses come from
the proof itself: the forger guessing a secret seed (the hidden-seed coupling,
`VCVio/OracleComp/QueryTracking/RandomOracle/HiddenSeed.lean`) and, in the faithfulness step,
forger strings that begin with `SK.prf`.

Each loss is to be charged against the **expected number of queries of the kind that can cause
it**, rather than against `q_h`: target collisions and hidden-value hits against queries at honest
(ledger) keys under `PK.seed`, seed guessing against queries at secret-derivable points, and the
faithfulness loss against strings beginning with `SK.prf`. The design claims, still to be checked,
are that under the address-injectivity hypothesis these kinds are disjoint, and that a query at an
honest key causes at most two unit hazards: its input can equal a hidden value, or its fresh
answer can equal the honest answer. The losses then sum to at most `2·q_h / 2^{8n}`. Both hazards
are reachable at that rate, so an accounting that charges hazards rather than forgeries cannot go
below 2; going lower requires showing that a single hazard is not yet a forgery, as leanVM's
refined route does (below). Adding the losses as separate `q_h`-bounded terms instead gives a
constant of 4. The expected counts are to be taken with
`VCVio/OracleComp/QueryTracking/ExpectedQueryCount.lean`.

Three terms remain outside that charge:

- the interleaved-target coverage `(q_h + 1) · targetCoverBound h a k q_s`
  (`VCVio/CryptoFoundations/HardnessAssumptions/KeyedHash/Covering.lean`), which equals
  `2^{−ak}·E[Bin(q_s, 2^{−h})^k]`;
- the verifier's own queries, `(r + 1) · verifyInternalQueryBound` at `r = 1`, two hazards each;
- for deterministic signing, a term `q_s / 2^{8n}` from honest strings in the faithfulness step,
  not yet known to be absorbable. `securityBound` in `Target.lean` carries this term in both
  modes; the hedged target below drops it.

### Levels

Per-query level `−log₂(bound / q_h)` at `q_h = q_s = 2^64`. "Two-hazard limit" is the level with the
coverage term and the constant 2 alone; `8n − 1` is the level of `Adv ≤ q_h / 2^{8n−1}`. The last
column is the coverage term's cost in units of `q_h / 2^{8n}`.

| Set | Hedged | Deterministic | Losses added separately (deterministic) | Two-hazard limit | `8n − 1` | Coverage cost |
|---|---|---|---|---|---|---|
| 128s | 126.99 | 126.41 | 125.67 | 126.99 | 127 | 0.02 |
| 128f | 126.54 | 126.09 | 125.48 | 126.54 | 127 | 0.76 |
| 192s | 190.82 | 190.29 | 189.60 | 190.82 | 191 | 0.27 |
| 192f | 190.87 | 190.33 | 189.62 | 190.87 | 191 | 0.19 |
| 256s | 254.41 | 254.00 | 253.41 | 254.41 | 255 | 1.00 |
| 256f | 254.27 | 253.89 | 253.34 | 254.27 | 255 | 1.32 |

`targetCoverBound` relaxes the exact coverage probability of the interleaved-target event. With
the exact probability instead, the coverage costs drop to 0.10 (128f), 0.11 (192f) and 1.06
(256f), and the hedged levels rise to 126.93, 190.92 and 254.39; the other sets change by at most
0.01. At `q_s ≤ 2^62` the coverage term is negligible at every set, and the two-hazard limit is
`8n − 1`.

The levels are those of the three-oracle model. The byte-level statement over a single SHAKE256
adds the losses of the faithfulness step. At `n = 32` one of them, a forger string that reads as
two different typed queries, costs about `2^{−172}` if bounded directly, which would bring the
256-bit sets down to about 236 bits; the `n = 32` rows assume the randomised routing argument that
removes it.

## leanVM's 127-bit proof

`sphincs_has_127_bits_of_classical_security` (`formal/sphincs/SphincsSecurity.lean`) proves
`HasClassicalSecurityBits 127`: every adversary whose whole experiment makes at most `q ≥ 1`
random-oracle queries produces a **strong** forgery with probability at most `q / 2^127`. The
budget counts key generation, signing and verification, cache hits included; private sampling is
free; and a win requires at most `2^24` signing queries. Its axioms are pinned to `propext`,
`Classical.choice` and `Quot.sound` with `#guard_msgs`. The development also proves correctness
(`sphincs_is_correct`) and completeness (`sphincs_is_complete`: the probability that signing fails
or verification rejects, summed over all messages, is at most `2^{−256}`), and `formal/xmss` proves
a 127-bit bound for XMSS (`XmssSecurityStatement`). It is built on VCVio.

How it reaches 127, from its `PROOF.md`:

1. **Two hazards per query.** Every fresh query is charged the potential `1 − (1 − 2^{−128})²` for
   its two unit hazards, giving `2x − x²` with `x = q / 2^128`. This is the observation behind the
   constant above.
2. **Small remaining terms.** Its master seed has 256 bits, so replacing seed derivation by
   independent secrets costs `(q − 1) / 2^256`, absorbed by the query that public-parameter
   derivation consumes; and a key signs at most `2^24` messages, so its few-time excess is `δx`
   with `δ = 11/65536`.
3. **Two routes.** For `q ≥ 3·2^114` the `−x²` slack absorbs `δx`. Below that it proves that a
   single chain contact is not a forgery, which lowers the first-order coefficient to `7/4`. That
   refined route is 246 modules and about 27k lines; `PROOF.md` reports that the crude route
   alone (372 modules, 39k lines) would give 126 bits at every budget.

### Differences

| | This work | leanVM |
|---|---|---|
| Scheme | FIPS 205, all twelve parameter sets | A SPHINCS variant: target-sum Winternitz with counter search, three layers, its own few-time signature |
| Budget | Forger's queries `q_h` and `q_s`; honest work free | Every query of the experiment, key generation, signing and verification included |
| Signatures per key | Evaluated at `2^64` | At most `2^24`, enforced by the game |
| Secret seeds | `SK.seed`, `SK.prf` of `n` bytes: guessing costs `q_h / 2^{8n}` | 256-bit master seed |
| Signing | Never fails; hedged or deterministic randomizer | Can fail (randomizer and counter searches); a completeness theorem bounds failure |
| Unforgeability | EUF-CMA first, then SUF-CMA | SUF-CMA |
| Bound | `2·q_h / 2^{8n}` plus coverage, verifier and deterministic terms | `q / 2^127` |

Counting the whole experiment suits a scheme capped at `2^24` signatures. At FIPS 205's `2^64`,
honest signing alone makes about `2^81` to `2^86` hash queries depending on the set, so at the
128-bit sets a whole-experiment `q / 2^127` bound would exceed `2^{−47}`; the forger-only budget is
what makes the statement informative at that signature count.

### What this work takes from it

- The existence proof: a `q / 2^127`-shaped classical bound for a SPHINCS-type scheme is reachable
  in Lean with VCVio, which de-risks the target.
- The two-hazard accounting behind the constant.
- The expected charged-query count, `VCVio/OracleComp/QueryTracking/ExpectedQueryCount.lean`,
  which follows `formal/xmss/XmssSecurity/Proof/ExpectedQueryCount.lean`.
- Guidance on the hidden-value event: relabelling honest nodes and deferring their values, which
  plays a role like that of leanVM's canonical graph of honest hash inputs (`Proof/Hypertree`)
  and the exact adaptive posteriors of its uniform tables (`Proof/Base`).

Its file layout, length and the refined second-order analysis are not followed. The comparison
above is against leanVM commit `48a90420` (`formal/sphincs` last changed in `b7a10725`).

## Consequences for implementations

None of the accounting choices above changes the scheme: the bound is about FIPS 205's algorithms,
so an implementation proved to refine the Lean byte-level specification inherits it. The facts an
implementation does depend on are:

- **Signing mode.** Deterministic signing carries the extra `q_s / 2^{8n}` term.
- **Signature count.** The bound is a function of `q_s`; a deployment that signs fewer than `2^64`
  messages per key obtains the corresponding smaller coverage term.
- **Address encoding.** The key hypothesis `CorePrimitives.KeyDiscipline` bundles injectivity of
  the address-to-key encoding on in-range addresses (`CorePrimitives.KeyInjective`), the address
  width bounds (`CanonicalAddressBounds`; SHA-2's compressed `ADRSc` needs `ApprovedAddressBounds`
  for injectivity), and key separation of secret-key addresses from hash addresses at every address
  (`CorePrimitives.KeySeparated`). These are facts about the encoding, and they are discharged for
  the twelve parameter sets and the compatibility bundle. At SHA-2, key separation holds because
  the model keys an address outside the checked `ADRSc` domain, which FIPS 205 never compresses, by
  a type-tagged fallback that is the key of no checked-domain address; on the checked domain the
  key is `ADRSc`, so every address FIPS 205 evaluates is keyed as the standard prescribes. An
  implementation is covered when its encoding agrees with the specification's, which the
  known-answer tests check on fixed inputs and a refinement proof would check for all.
- **Interface.** The statement covers the internal functions; implementations expose the external
  functions (Algorithms 21–25), which the theorem reaches only once the external layer is added.
- **Hash functions.** SHAKE256 and SHA-2 are idealized as random oracles. The SHA-2 instantiation,
  with `MGF1` in `H_msg` and `HMAC` in `PRF_msg`, is to be modelled separately from SHAKE.

## References

- NIST FIPS 205, *Stateless Hash-Based Digital Signature Standard*, August 2024.
- Emile, `leanEthereum/leanVM`, `formal/sphincs` (`SphincsSecurity.lean`, `PROOF.md`) and
  `formal/xmss`, dual Apache-2.0/MIT; maintained by Tom Wambsgans (@TomWambsgan).
- D. J. Bernstein, A. Hülsing, S. Kölbl, R. Niederhagen, J. Rijneveld, P. Schwabe, *The SPHINCS+
  Signature Framework*, CCS 2019; SPHINCS+ round-3.1 specification (2022).
- M. Barbosa, F. Dupressoir, A. Hülsing, M. Meijers, P.-Y. Strub, *A Tight Security Proof for
  SPHINCS+, Formally Verified*, Cryptology ePrint Archive, Report 2024/910.
