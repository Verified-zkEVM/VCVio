# SLH-DSA in the classical random-oracle model: the target bound and leanVM's 127-bit proof

Status: design record, established 2026-10-05. It fixes how the classical random-oracle bound for
FIPS 205 SLH-DSA is accounted, records the levels that accounting reaches, and compares the result
with the 127-bit proof for a SPHINCS variant in
[`leanEthereum/leanVM`](https://github.com/leanEthereum/leanVM) (`formal/sphincs`), whose argument
this work draws on. The development is in pull request #766; the implementation status of `main`
is in [`slh-dsa-status-and-roadmap.md`](slh-dsa-status-and-roadmap.md).

**What is proved.** Every bound below is a bound on the strong forging advantage (SUF-CMA): the
forger wins with a valid pair of message and signature that the signing oracle never returned, so
a second signature on a signed message counts. Each holds at the right-hand side of the
corresponding existential (EUF-CMA) bound, and every existential bound follows from its strong one
through `shakeAdvantage_le_shakeStrongAdvantage` (three-oracle model:
`unforgeableAdvantage_le_strongUnforgeableAdvantage`), so the levels below are the same for both
notions. Existential forms are stated under their own names only for the target
(`unforgeableAdvantage_romScheme_le`), the bounds the guides cite
(`shakeAdvantage_pure_le_securityBound`, `shakeAdvantage_le_securityBound`,
`shakeAdvantage_le_securityBound_hedged`) and the six `shakeAdvantage_*_validatedParams` forms. The three-oracle bound `securityBound` at
`c = 2` and `r = 1` is proved in Lean for each fixed public seed, in both signing modes: `securityTarget_two_one`
(`HashSig/SLHDSA/Security/CoverageBound.lean`) proves `SecurityTarget core e optRand 2 1` under the
byte laws, the key discipline and `|Y| ≤ |SK.prf|`, all three discharged at every FIPS 205 bundle,
with `optRand` arbitrary. `strongUnforgeableAdvantage_romScheme_le_securityBound` averages it over any
distribution of the public seed, the uniform one of FIPS 205 included. The bound is stated over
`|Y|`, which is `2^{8n}` at the FIPS 205 bundles, and is the sum of two proved terms:

- the joint target-collision and hidden-value term `2(q_h + V) / 2^{8n}`, with `V` the verifier's
  query bound `verifyInternalQueryBound` and the seed guess charged inside it
  (`prEvent_romSchemeRun_runTargetCollision_or_runHiddenHit_le`,
  `HashSig/SLHDSA/Security/JointBound.lean`). With the union bound split after the first game hop,
  the strong forging advantage is at most that term plus the probability of interleaved-target coverage in
  the ideal hidden-seed game (`strongUnforgeableAdvantage_romScheme_pure_le_add_idealDraw`), in which
  every secret value and randomizer is sampled independently of the public answers;
- the coverage term `(q_h + 1) · weightedTargetCoverBound h a k q_s q_h (q_s / 2^{8n})`, which
  bounds that coverage probability (`prEvent_idealDraw_runItsrCovered_le`).

The same bound with the coverage probability of the run in place of the ideal one
(`strongUnforgeableAdvantage_romScheme_pure_le_add`) also holds, but for deterministic signing its
coverage term is not bounded at the size of the target's coverage term
([Coverage after the seed hop](#coverage-after-the-seed-hop)).

**The byte-level bound is proved.** For SLH-DSA over a single SHAKE256 random oracle on byte
strings (`shakeRomScheme`, `HashSig/SLHDSA/Security/ByteModel.lean`), whose oracle answered by
SHAKE256 gives FIPS 205's SHAKE internal algorithms (`shakeRomScheme_map_shakeAnswer`), the
faithfulness step is proved across `ByteRouter`, `ByteClash`, `PrfKeyBound` and `WeakKeyBound`,
at `n = 32` also across `ByteRedirect`, `ByteLinkedRun`, `ByteLinkedView`, `HonestTransfer`,
`ByteLinkedBound` and `LinkedHazards`, and assembled in `HashSig/SLHDSA/Security/ByteBound.lean`,
in both signing modes, for `16 ≤ n ≤ 32`,
`n ≤ m` and address fields within their FIPS 205 widths (`CanonicalAddressBounds`):

- per public seed, `shakeStrongAdvantage ≤ securityBound p 2^{8n} 2 1 q_h q_s + (q_s + 1) / 2^{8n} +
  weakKeyMass vp PK.seed` (`shakeStrongAdvantage_pure_le_securityBound`), where `weakKeyMass` is the
  probability over the uniform public root that the public key is weak
  ([The 256-bit sets](#the-256-bit-sets));
- per public seed of weak-key mass zero, the same without a weak-key term
  (`shakeStrongAdvantage_pure_le_securityBound_of_weakKeyMass_eq_zero`); at `n = 32` these are the
  seeds outside the weak set (`shakeStrongAdvantage_pure_le_securityBound_of_n_eq_32`);
- at `n = 32`, at every public seed, weak seeds included,
  `shakeStrongAdvantage ≤ securityBound p 2^256 2 1 (q_h + V) q_s + 2 (q_s + 1) / 2^256`, with `V` the
  verifier's query bound (`shakeStrongAdvantage_pure_le_securityBound_add_of_n_eq_32`,
  `HashSig/SLHDSA/Security/LinkedHazards.lean`), so per seed the smaller of the two bounds
  (`shakeStrongAdvantage_pure_le_min_of_n_eq_32`);
- over the uniform `PK.seed` of FIPS 205, the per-seed bound with the weak-key term replaced by
  `|A_hon| / 2^256 · weakSeedFactor vp ε`, `|A_hon| = honestAdrsCount vp`, where `ε` is the bound
  at every seed of the previous item and the factor is `min 1 ε` at `n = 32` and `1` otherwise
  (`shakeStrongAdvantage_le_securityBound`). At `n < 32` the weak-key term is `|A_hon| / 2^256`; at
  `n = 32` it is the weak seeds' share `|A_hon| / 2^256 · min 1 ε`, about `2^{−362}` at
  `q_h = q_s = 2^64`, and the averaged level equals the per-seed level outside the weak set to two
  decimals;
- in hedged signing (`opt_rand` uniform), the per-seed, averaged and `n = 32` forms with
  `1 / 2^{8n} + q_s (q_h + q_s + 1) / 2^{16n}` in place of `(q_s + 1) / 2^{8n}`
  (`shakeStrongAdvantage_pure_le_securityBound_hedged`, `shakeStrongAdvantage_le_securityBound_hedged`,
  `shakeStrongAdvantage_pure_le_securityBound_hedged_of_n_eq_32`,
  `shakeStrongAdvantage_pure_le_min_hedged_of_n_eq_32`). Per public seed of weak-key mass zero and over
  the uniform public seed they reach the three-oracle level
  ([How the bound is accounted](#how-the-bound-is-accounted)).

At the six SHAKE parameter sets every side condition is discharged and the adversary's budget is
the only hypothesis (`shakeStrongAdvantage_pure_le_securityBound_validatedParams`,
`shakeStrongAdvantage_pure_le_securityBound_add_validatedParams`,
`shakeStrongAdvantage_le_securityBound_validatedParams`, and in hedged signing
`shakeStrongAdvantage_pure_le_securityBound_hedged_validatedParams`,
`shakeStrongAdvantage_pure_le_securityBound_add_hedged_validatedParams`,
`shakeStrongAdvantage_le_securityBound_hedged_validatedParams`). These theorems are stated over all twelve
`FipsParameterSet` values, a SHA-2 value contributing only its parameters, which equal its SHAKE
twin's. The `(q_s + 1) / 2^{8n}` term is the
faithfulness hook, charged jointly with the three-oracle events
(`prEvent_romSchemeRun_strongWins_or_runPrfKeyHit_le`, `HashSig/SLHDSA/Security/PrfKeyBound.lean`); the
weak-key term is bounded per seed and averaged in `HashSig/SLHDSA/Security/WeakKeyBound.lean`, and
at `n = 32` replaced at the weak seeds by the bound at every seed.
The hedged terms are `prEvent_romSchemeRun_strongWins_or_runPrfKeyClash_le`
(`HashSig/SLHDSA/Security/HedgedKeyBound.lean`).

**Oracle output length (modelling choice).** The oracle answers every string with `m` bytes, the
longest SHAKE256 output FIPS 205 reads (`H_msg`; every other call reads the first `n ≤ m` bytes).
A proposed simulation of a variable-length XOF adversary must sample and cache the unused
suffix at each input, preserving it on repeated queries and extending it consistently on longer
requests. That game transport and its query budget are not formalised. Deterministic SHAKE prefix
consistency at arbitrary widths is proved in `VCVio/Algorithms/KeccakPrefix.lean`; it does not by
itself establish the adversarial game transport.

**What is not proved.** The SHA-2 parameter sets have no byte-level model. The pure-mode wire interface is covered by
`wireStrongAdvantage_le_securityBound_validatedParams` and its hedged form, using the canonical
parsers already proved in `Codec.lean`. Prehash-mode security still needs collision accounting:
colliding prehashes can turn distinct external messages into the same internal message. Of the levels below,
"Three-oracle", the two "Byte level" and the two "Hedged" columns evaluate proved bounds; the other
columns evaluate formulas that are not Lean results.

## Validated review follow-up (2026-10-23)

The review at `66f1750ca6e13a4233e96666451f7aa0bd630974` correctly identified missing wire-game
transport and executable certified evaluation. It did not demonstrate a soundness defect in the
internal theorem. The documentation's claim that one-to-one signature parsing was unproved was
incorrect: `decodeSignature_eq_ok_iff` and `encodeSignature_injective` already establish it.

`SignatureAlg/Wire.lean` supplies the named adversary `reduce`, its signing-log transport,
accepted-pair freshness, probability bound, and unchanged `RomQueryBound`. `Security/Wire.lean`
instantiates this adapter at the actual SHAKE public-key/signature codecs and fixes a checked
pure-mode context. Arbitrary byte lists are accepted at the public boundary and malformed lengths
are rejected before verification. `Security/Profile.lean` binds the SHAKE family, parameters,
mode, context, uniform public-seed sampler, codecs, and matching bound evaluator. The existing
internal scheme draws the secret seeds independently and uniformly; master-seed-derived public
parameters need a separate distribution proof.

`slhdsa_wire_tests` executes small adversaries against the wire wrapper and the reduced
structured experiment. Its computable experiment runner is proved equal to the SUF experiment.
Exact replay loses, a distinct valid signature on the signed message wins, and malformed
signatures reject before invoking the underlying verifier. Exact call traces check repeated
ambient requests and signing-query forwarding; malformed public keys also reject without
underlying verification.

`CoveringEval.lean` computes surjection counts with a table-based triangular recurrence proved by
partitioning functions by image size. Binomial coefficients use descending factorials; budgets
such as `2^64` are never enumerated. `Security/BoundEval.lean` proves that exact nonnegative
rational evaluators equal the structured bound, the deterministic and hedged byte bounds, and
the averaged weak-seed bounds. Its honest-address count uses the proved closed form.
`lake exe slhdsa_bound_table` prints exact coefficient numerator/denominator pairs and a
floating-point presentation. Its checked-in output is
[`slh-dsa-security-bounds.csv`](slh-dsa-security-bounds.csv); regenerate it with
`lake exe slhdsa_bound_table > docs/design/slh-dsa-security-bounds.csv` and independently compare
every exact rational using
`python3 scripts/check-slh-dsa-bound-table.py docs/design/slh-dsa-security-bounds.csv`.
`lake test` builds the generator, regenerates its CSV into a temporary file, compares it
byte-for-byte with the checked-in artifact, and runs that independent exact-arithmetic check
on the generated output. This also runs through `scripts/validate.sh --test`; a mismatch
fails without rewriting the published artifact.
`Security/BoundCertificates.lean` kernel-checks all 18 rounded
entries in the six-row table via rational power inequalities, without native proof axioms.

`Security/RangeBound.lean` proves a separate uniform coefficient theorem for a positive minimum
hash budget, a maximum hash budget, and a signing lifetime. `rangeCoefficients_certified`
certifies **the three-oracle bound** at all six sets for `2^32 ≤ qh ≤ 2^64`, at each signing
lifetime `qs ≤ 2^20`, `2^32`, or `2^64`: `securityBound ≤ qh / 2^(8n - 2)` throughout each
rectangle. The sharper rounded table remains a point evaluation at `qh = qs = 2^64`; it is not
claimed as a uniform floor for either wire signing mode.

`SignatureAlg/RomWork.lean` proves whole-experiment budget transport:
`K + qh + qs * S + V`, assuming certificates for key generation, signing, and verification of the
actual oracle-backed scheme. Those honest certificates must include provider and `PRF_msg`
traffic. `GeneralSchemeQueryBound.lean` alone does not discharge them because its PRFs are pure.
SLH-DSA-specific honest derivation counts, randomness caps, input-length-weighted deployment
costs, and time or cycle guarantees remain open.

Independent NIST ACVP evidence now includes key generation, deterministic/hedged signing, and
valid/invalid verification at SHAKE-128f, 192f, and 256f. The additional fixtures preserve the
pinned `975de31e` source revision and hashes. `scripts/check-slh-dsa-byte-vectors.py` verifies
record projections against a local copy of that corpus. Wire regressions cover short and appended
signatures, exact replay, and a distinct signature on the same signed message. Multi-block SHAKE
prefix tests include zero output, exact rate boundaries, and extended requests.

The reuse concern is also valid. The current
[leanSPHINCS specification](https://raw.githubusercontent.com/leanEthereum/leanVM/main/doc/lean_sphincs/main.tex)
uses WOTS+C counter search, a different forest and address grammar, 256-bit secrets with 128-bit
nodes, failure, pruning, and master-seed-derived public parameters. Its correctness and security
are not obtained by selecting an SLH-DSA parameter bundle. A pinned second construction with
those proofs remains required. Consolidating provider-parametric programs is a design follow-up;
the existing specialization equations do not certify provider call counts. Neither a new
construction theorem nor a variable-length-XOF game theorem is supplied by these adapters.

## The statement

- **Model.** FIPS 205's internal functions (Algorithms 18–20) with the tweakable hash, `H_msg` and
  `PRF_msg` as random oracles (`hashSpec`, `romScheme` in `HashSig/SLHDSA/Security/Target.lean`).
  `PRF` is the tweakable hash at the PRF address types, which coincides with FIPS 205's `PRF` in
  both instantiations, so no separate PRF assumption enters. The faithfulness theorem relates
  this three-oracle model to the byte-level scheme over a single SHAKE256
  (`shakeRomScheme`, `HashSig/SLHDSA/Security/ByteBound.lean`); the byte-level statement is the
  result for the SHAKE parameter sets.
- **Budgets.** `StrongUnforgeableAdversary.RomQueryBound adv q_h q_s` bounds, on every path of the
  forger's own program, its hash queries `q_h` (`PRF_msg` included, repeated queries counted) and
  its signing queries `q_s`. Key generation, signing and verification are not charged to `q_h`. The
  bound is stated for each fixed public seed.
- **Signing modes.** Hedged (`opt_rand` uniform) and deterministic (`opt_rand = PK.seed`) signing
  are both instances of the same statement. At byte level a second statement holds for hedged
  signing, with a smaller faithfulness term.

## How the bound is accounted

A strong forgery fires one of three events (`bad_event_of_strongWins_romSchemeRun`): a same-key
target collision with an honest entry, a hit on a hidden chain value or unopened FORS secret, or
coverage of every FORS coordinate of the forgery's digest by logged signatures while the forgery's
`H_msg` point (randomizer and message) is that of no logged signature. A forgery at a logged
point has the logged digest, so the descent from the cached root runs through the logged
signature's own trees, and each layer and the FORS signature either equal the logged ones or
give a target collision (`bad_event_or_logged_of_settled`); coverage is not needed there, and the
same-message case adds no term. Two further losses come from
the proof itself: the forger guessing a secret seed (the hidden-seed coupling,
`VCVio/OracleComp/QueryTracking/RandomOracle/HiddenSeed.lean`) and, in the faithfulness step,
forger and signer strings that begin with `SK.prf`.

Each loss is charged against the **queries of the kind that can cause it**, rather than against
`q_h`, on every run: one joint potential over the deferred relabelled game covers the hidden-value
hit, the target collision (at oracle-key level, so a forger input of any length at a node's key
counts) and the seed guess, and, at byte level, the faithfulness misroute, with each forger or
verifier query charged by its kind. The generic joint potential is
`VCVio/OracleComp/QueryTracking/RandomOracle/JointPotential.lean`. Its SLH-DSA
instantiation for the target collision, the hidden-value hit and the seed guess is proved
(`HashSig/SLHDSA/Security/JointBound.lean`, through the event transport of
`HashSig/SLHDSA/Security/Transport.lean`), and so is the faithfulness hook (`Fev`), which joins
the faithfulness event into the same potential (`prEvent_romSchemeRun_strongWins_or_runPrfKeyHit_le`,
`HashSig/SLHDSA/Security/PrfKeyBound.lean`). A query at an honest (ledger) key under `PK.seed`
causes at most two unit hazards: its input can equal a hidden value, or its fresh answer can
equal the honest answer. A query at a secret-derivable point (a `PRF` key or `PRF_msg`) causes
one, the seed guess. At byte level, an `H_msg` query causes one, the faithfulness event, when its
string begins with `SK.prf`; these points are at no key, so this kind is disjoint from the others.
Under the key-separation hypothesis (`CorePrimitives.KeySeparated`) no
derivable point is at an honest key, so the kinds are disjoint for the target collision, the
hidden-value hit and the seed guess. The faithfulness theorem states its loss as an event of the
typed run: a clash of two byte strings is a hit of the message-`PRF` key, joined into the
potential, or a weak public key, charged separately
(`shakeStrongAdvantage_pure_le_strongWins_or_runPrfKeyHit_or_isWeakKey`,
`HashSig/SLHDSA/Security/ByteClash.lean`). The forger's
queries then cost at most `2·q_h / 2^{8n}`, and the verifier's are charged in the same potential
(below). Both hazards are reachable at that rate, so an accounting that charges hazards rather than
forgeries cannot go below 2; going lower requires showing that a single hazard is not yet a forgery,
as leanVM's refined route does (below). Adding the losses as separate `q_h`-bounded terms instead
gives a constant of 4.

Beside the forger's `2·q_h / 2^{8n}`, the bound has two terms:

- the interleaved-target coverage `(q_h + 1) · weightedTargetCoverBound h a k q_s q_h w` at
  `w = q_s / 2^{8n}` (`VCVio/CryptoFoundations/HardnessAssumptions/KeyedHash/Covering.lean`),
  outside the potential. A FORS digit of the target can be covered by the digest of one of the
  `q_s` signing queries, at weight one, or by one of the forger's own `H_msg` answers at another
  position, at weight `w`: a signature carries such an answer only if a fresh randomizer of a
  signing query hits that answer's point, which has probability at most `q_s / 2^{8n}`. For
  `w ≤ 1` the term equals `2^{−ak}·E[(Bin(q_s, 2^{−h}) + Bin(q_h, w·2^{−h}))^k]`; at `w = 0` or
  `q_h = 0` it is the unweighted `targetCoverBound h a k q_s`, which equals
  `2^{−ak}·E[Bin(q_s, 2^{−h})^k]` and is at most the weighted term at every weight
  (`targetCoverBound_le_weightedTargetCoverBound`);
- the verifier's own queries, `(r + 1) · verifyInternalQueryBound` at `r = 1`, two hazards each.

The three-oracle bound (`securityBound` in `Target.lean`) has no term linear in `q_s`, in either
signing mode: signing queries enter only through the coverage term. The byte-level statement adds
`q_s / 2^{8n}`, the faithfulness event for the signer's strings: a signing query whose randomizer
equals `SK.prf`, so that its `H_msg` string begins with `SK.prf`. It also adds `1 / 2^{8n}` for
`SK.prf = PK.seed`. Both are joined into the same joint potential, not added as separate
probabilities, and both are charged in either signing mode, so this byte-level bound is the same
for hedged and deterministic signing.

For hedged signing a sharper statement is proved. A signer's `PRF_msg` string
`SK.prf ‖ opt_rand ‖ M` clashes with an `H_msg` string only if its `opt_rand` equals `PK.seed`, so
the clash classification keeps that condition (`RunPrfKeyClash`,
`shakeStrongAdvantage_pure_le_strongWins_or_runPrfKeyClash_or_isWeakKey`). After the seed hop the condition
is a randomizer derivation at `opt_rand = PK.seed` in the ideal game, which depends on the run
only: each signing query draws its `opt_rand` and makes one derivation with it, so the condition
has probability at most `q_s · ε` when `Pr[opt_rand = PK.seed] ≤ ε`
(`prEvent_idealRun_randDerivedAt_le`, through the generic
`SignatureAlg.prEvent_run_unforgeableTranscriptExperiment_le`). Given the run, the drawn `SK.prf`
hits one of the at most `q_h + q_s + 1` cached `H_msg` points with probability at most
`(q_h + q_s + 1) / 2^{8n}`, so the joint event costs `q_s · ε · (q_h + q_s + 1) / 2^{8n}`
(`prEvent_idealDraw_hmsgAtPrfKey_and_randDerivedAt_le`), added outside the potential; the
`1 / 2^{8n}` for `SK.prf = PK.seed` stays inside it. For a uniform `opt_rand`, `ε = 2^{−8n}` and
`q_s / 2^{8n}` becomes `q_s (q_h + q_s + 1) / 2^{16n}`, which reaches the three-oracle level per
public seed of weak-key mass zero (`shakeStrongAdvantage_pure_le_securityBound_hedged`). Deterministic
signing has `ε = 1` and keeps the mode-independent statement.

### Coverage after the seed hop

With deterministic signing the randomizer of a signature is `PRF_msg(SK.prf, PK.seed, M)`. A forger
that guesses `SK.prf` through its `PRF_msg` queries therefore predicts the randomizer of every
message it will have signed, grinds `H_msg` over candidate messages, and has signed only messages
whose digests cover the digest of a target it has queried. Coverage in the run is then at least
about as likely as that guess, about `q_h / |SK.prf|`: at 128s, about `2^{−28}` after `2^{100}`
`PRF_msg` queries, against a coverage term of about `2^{−127}`. So at the FIPS 205 parameter sets
the coverage probability of the run is not bounded by the coverage term of `securityBound`. The
guess itself is a seed guess, which the joint term already charges.

A proof that bounds coverage as a separate summand therefore takes it after the seed hop, in the
ideal hidden-seed game, as `strongUnforgeableAdvantage_romScheme_pure_le_add_idealDraw` does. There the
coverage event reads only the `H_msg` answers of the public cache, and its probability does not
depend on the secret seeds (`prEvent_idealDraw_runItsrCovered_eq`). A forger can still query a
signer's `H_msg` point before the signer does, by guessing the signer's fresh randomizer, so the
coverage bound proved in that game carries a term for forger pre-queries hitting signer points:
the forger's own `H_msg` answers count as coverers at weight `q_s / 2^{8n}`, which is the
coverage term `(q_h + 1) · weightedTargetCoverBound h a k q_s q_h (q_s / 2^{8n})` of
`securityBound` (`prEvent_idealDraw_runItsrCovered_le`). The proof runs the ideal game on
class-indexed answer tapes, the forger's and the signer's `H_msg` answers on separate tapes, and
bounds every witness of coverage by the product of its tape mass and the probability that fresh
randomizer draws hit its forger-tape coverers. The unweighted form
`(q_h + 1) · targetCoverBound h a k q_s` is not proved in the ideal game; at the budgets of the
levels table the two forms give the same levels to four decimals.

### Levels

Per-query level `−log₂(bound / q_h)` at `q_h = q_s = 2^64`. "Three-oracle" evaluates the
three-oracle bound `securityBound` at `c = 2`, `r = 1`, which is proved per public seed and holds
in both signing modes (`securityTarget_two_one`); with the weighted coverage term these levels are
those of the unweighted term to four decimals at every set. It is the level of the three-oracle
model, not of the byte-level scheme. The two "Byte level" columns are levels of proved bounds on
`shakeStrongAdvantage`, in hedged and deterministic signing alike. "Byte level, per seed" adds to the
three-oracle bound the terms `1 / 2^{8n}` (`SK.prf = PK.seed`) and `q_s / 2^{8n}` (the signer's
faithfulness event) and omits the weak-key term: it is the level of
`shakeStrongAdvantage_pure_le_securityBound_of_weakKeyMass_eq_zero`, at every public seed of weak-key
mass zero, which at `n = 32` is every seed outside the weak set
(`shakeStrongAdvantage_pure_le_securityBound_of_n_eq_32`; [The 256-bit sets](#the-256-bit-sets)).
"Byte level, averaged" adds the weak seeds' share
`|A_hon| / 2^256 · weakSeedFactor vp ε`, with `|A_hon| = honestAdrsCount vp` evaluated in
`HashSigTest/SLHDSA/WeakKeyBound.lean`: it is the level of `shakeStrongAdvantage_le_securityBound` over
the uniform public seed. At `n < 32` the share is `|A_hon| / 2^256`; at `n = 32` it is
`|A_hon| / 2^256 · min 1 ε`, at most `2^{−171.6}` times the per-seed bound at
`q_h = q_s = 2^64`, so the two columns agree at every set. The two "Hedged"
columns are the same two bounds for hedged signing, with `1 / 2^{8n} + q_s (q_h + q_s + 1) /
2^{16n}` in place of `(q_s + 1) / 2^{8n}`: the levels of
`shakeStrongAdvantage_pure_le_securityBound_hedged` at a seed of weak-key mass zero (at `n = 32`,
`shakeStrongAdvantage_pure_le_securityBound_hedged_of_n_eq_32`) and of
`shakeStrongAdvantage_le_securityBound_hedged`. They equal the three-oracle levels to two decimals.
The levels at the weak seeds themselves are in [The 256-bit sets](#the-256-bit-sets). The remaining
columns are evaluations of formulas, not Lean results. "Losses added separately" charges the
losses of "Byte level, per seed" as separate `q_h`-bounded terms, the constant 4 above, and also
omits the weak-key term. "Two-hazard limit" is the level with the coverage term and the constant
2 alone; `8n − 1` is the level of `Adv ≤ q_h / 2^{8n−1}`. The last column is the coverage term's
cost in units of `q_h / 2^{8n}`.

| Set | Three-oracle | Byte level, per seed | Byte level, averaged | Hedged, per seed | Hedged, averaged | Losses added separately | Two-hazard limit | `8n − 1` | Coverage cost |
|---|---|---|---|---|---|---|---|---|---|
| 128s | 126.99 | 126.41 | 126.41 | 126.99 | 126.99 | 125.67 | 126.99 | 127 | 0.02 |
| 128f | 126.54 | 126.09 | 126.09 | 126.54 | 126.54 | 125.48 | 126.54 | 127 | 0.76 |
| 192s | 190.82 | 190.29 | 190.29 | 190.82 | 190.82 | 189.60 | 190.82 | 191 | 0.27 |
| 192f | 190.87 | 190.33 | 190.33 | 190.87 | 190.87 | 189.62 | 190.87 | 191 | 0.19 |
| 256s | 254.41 | 254.00 | 254.00 | 254.41 | 254.41 | 253.41 | 254.41 | 255 | 1.00 |
| 256f | 254.27 | 253.89 | 253.89 | 254.27 | 254.27 | 253.34 | 254.27 | 255 | 1.32 |

The coverage term relaxes the exact coverage probability of the interleaved-target event. With
the exact probability instead, the coverage costs drop to 0.10 (128f), 0.11 (192f) and 1.06
(256f), and the three-oracle levels rise to 126.93, 190.92 and 254.39; the other sets change by
at most 0.01. At `q_s ≤ 2^62` the coverage term is negligible at every set, and the two-hazard
limit is `8n − 1`.

#### The 256-bit sets

FIPS 205 §11.1 lays out the `H_msg` input as `R‖PK.seed‖PK.root‖M` and a tweakable-hash input as
`PK.seed‖ADRS‖M_1‖…‖M_ℓ`. At `n = 32` the 32-byte `ADRS` field sits where the `H_msg` input has
`PK.seed`. Let `A_hon` be the set of address encodings that honest key generation, signing and
verification evaluate. When `PK.seed ∈ A_hon` (a weak seed) and `R = PK.seed`, the `H_msg` input
`PK.seed‖PK.seed‖PK.root‖M` is also the tweakable-hash input at the honest address `ADRS* = PK.seed`
with blocks `PK.root‖M`; this holds at every address type the verifier evaluates, from FORS leaves
and WOTS chains to tree nodes, FORS roots and WOTS public keys. A forger can use such a string in
both roles. It can query the string as a node and forge with `R* = PK.seed`. And the verifier's own
`H_msg` input at `R* = PK.seed` is then also a tweakable-hash input on its own verification path
whenever that path reaches `ADRS*` with first block `PK.root` (self-reference).

The byte-level bound carries this case in a weak-key term. Per public seed it is
`weakKeyMass vp PK.seed`, the probability over the uniform public root that the first 32 bytes of
`PK.seed‖PK.root` are an honest address key (`IsWeakKey`); the public root is uniform at every seed
(`prEvent_romSchemeRun_isWeakKey_le`). For `16 ≤ n` its average over the uniform `PK.seed` is at
most `|A_hon| / 2^256` (`lintegral_weakKeyMass_le`), about `2^{−171.95}` at 256s and
`2^{−172.26}` at 256f. At `n = 32` the term depends only on `PK.seed`, not on the adversary: it is
one at a weak seed and zero at every other seed (`weakKeyMass_eq_zero_or_eq_one_of_n_eq_32`).

At `n = 32` a second bound holds at every public seed, the weak seeds included. A tweakable-hash
query at the address `PK.seed` whose first block is `PK.root` is *linked*: its string is that of
the `H_msg` query `H_msg(PK.seed, PK.seed, PK.root, ·)` (`IsLinked`,
`HashSig/SLHDSA/Security/ByteRedirect.lean`). The single-oracle verification is the three-oracle
verification with each linked query answered by the first `n` bytes of its `H_msg` reading
(`shakeRomScheme_verify_eq`), so the proof runs the three-oracle game against an adversary that
performs this redirected verification of its own forgery, with budget `(q_h + V, q_s)`
(`verifyingAdv`, `romQueryBound_verifyingAdv`). Its events are read on the run's cache through the
redirect (`ByteLinkedRun`, `ByteLinkedView`, `HonestTransfer`) and bounded in one game hop and one
potential (`ByteLinkedBound`), with two further events: a *virtual hit*, an honest value equal to
the first `n` bytes of a cached `H_msg` answer at a linked reading, and an honest input at a linked
point. The first is charged `1 / 2^{8n}` per cached `H_msg` entry at a linked reading and the
second `1 / 2^{8n}` once, which widens the joint budget by `(q_s + 1) / 2^{8n}` (`LinkedHazards`).
The bound at every seed is `securityBound p 2^256 2 1 (q_h + V) q_s + 2 (q_s + 1) / 2^256`
(`shakeStrongAdvantage_pure_le_securityBound_add_of_n_eq_32`; in hedged signing
`shakeStrongAdvantage_pure_le_securityBound_add_of_n_eq_32_hedged`).

Per seed the advantage is at most the smaller of the two bounds
(`shakeStrongAdvantage_pure_le_min_of_n_eq_32`): the first outside the weak set, the second at a weak
seed. As the weak-key mass is zero or one, that minimum is at most the first bound with the
weak-key mass multiplied by `min 1 ε`, `ε` the second bound (`min_add_weakKeyMass_le_of_n_eq_32`),
and its average over the uniform `PK.seed` is the first bound plus `|A_hon| / 2^256 · min 1 ε`
(`shakeStrongAdvantage_le_securityBound`, `shakeStrongAdvantage_le_securityBound_of_n_eq_32`). At
`q_h = q_s = 2^64` the byte-level levels are:

- per seed, outside the weak set: 254.00 (256s) and 253.89 (256f)
  (`shakeStrongAdvantage_pure_le_securityBound_of_n_eq_32`), and in hedged signing 254.41 (256s) and
  254.27 (256f) (`shakeStrongAdvantage_pure_le_securityBound_hedged_of_n_eq_32`);
- per seed, at every seed, weak seeds included: 253.68 (256s) and 253.59 (256f)
  (`shakeStrongAdvantage_pure_le_securityBound_add_validatedParams`), and in hedged signing 254.00 (256s)
  and 253.89 (256f) (`shakeStrongAdvantage_pure_le_securityBound_add_hedged_validatedParams`);
- averaged over the uniform `PK.seed`: 254.00 (256s) and 253.89 (256f)
  (`shakeStrongAdvantage_le_securityBound_validatedParams`), and in hedged signing 254.41 (256s) and
  254.27 (256f) (`shakeStrongAdvantage_le_securityBound_hedged_validatedParams`).

At `q_h = q_s = 2^40` the averaged levels are 254.42 at both sets, and 255.00 at both in hedged
signing; the bound at every seed is at 254.00, and 254.42 in hedged signing.

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
| Secret seeds | `SK.seed`, `SK.prf` of `n` bytes: guessing costs `q_h / 2^{8n}` (inside the constant 2) | 256-bit master seed |
| Signing | Never fails; hedged or deterministic randomizer | Can fail (randomizer and counter searches); a completeness theorem bounds failure |
| Unforgeability | SUF-CMA, EUF-CMA as its corollary at the same bound | SUF-CMA |
| Bound | `2·q_h / 2^{8n}` plus coverage and verifier terms; byte level adds `(q_s + 1) / 2^{8n}` and the weak-key term, averaged `\|A_hon\| / 2^256` at `n < 32` and at `n = 32` a weak-seed share `\|A_hon\| / 2^256 · min 1 ε`, binding at no set | `q / 2^127` |

Counting the whole experiment suits a scheme capped at `2^24` signatures. At FIPS 205's `2^64`,
honest signing alone makes about `2^81` to `2^86` hash queries depending on the set, so at the
128-bit sets a whole-experiment `q / 2^127` bound would exceed `2^{−47}`; the forger-only budget is
what makes the statement informative at that signature count.

### What this work takes from it

- The existence proof: a `q / 2^127`-shaped classical bound for a SPHINCS-type scheme is reachable
  in Lean with VCVio, which de-risks the target.
- The two-hazard accounting behind the constant.
- The expected charged-query count, `VCVio/OracleComp/QueryTracking/ExpectedQueryCount.lean`,
  which follows `formal/xmss/XmssSecurity/Proof/ExpectedQueryCount.lean`. The expected-count
  form of the hidden-seed coupling (`HiddenSeed.lean`) is stated with it; the bound above charges
  pathwise instead.
- Guidance on the hidden-value event: relabelling honest nodes and deferring their values, which
  plays a role like that of leanVM's canonical graph of honest hash inputs (`Proof/Hypertree`)
  and the exact adaptive posteriors of its uniform tables (`Proof/Base`).

Its file layout, length and the refined second-order analysis are not followed. The comparison
above is against leanVM commit `48a90420` (`formal/sphincs` last changed in `b7a10725`).

## Consequences for implementations

None of the accounting choices above changes the scheme: the bound is about FIPS 205's algorithms,
so an implementation proved to refine the Lean byte-level specification inherits it. The facts an
implementation does depend on are:

- **Signing mode.** The three-oracle bound is the same in both modes. At byte level the bound
  for every signing mode charges `q_s / 2^{8n}` for the signer's strings; hedged signing, with
  `opt_rand` uniform, has the sharper proved bound with `q_s (q_h + q_s + 1) / 2^{16n}` instead,
  which per public seed (at `n = 32`, outside the weak set) and over the uniform public seed is at
  the three-oracle level, 0.38–0.58 bits above the mode-independent bound at
  `q_h = q_s = 2^64`. An implementation in
  deterministic mode gets the mode-independent bound.
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
  key is `ADRSc`, so every address FIPS 205 evaluates is keyed as the standard prescribes. That
  the honest keys are unchanged by the fallback is a theorem: under `ApprovedAddressBounds` every
  in-range address is keyed by its checked `ADRSc`
  (`compressSha2Checked_eq_ok_sha2AdrsKey_of_addressFacts`), and the construction-trace theorems
  place every `thash` query of honest key generation, signing and verification at such an address.
  The SHA-2 known-answer test runs the compatibility bundle, whose unchecked `ADRSc` key agrees
  with the FIPS SHA-2 key on the checked domain but which never evaluates the latter; the FIPS
  SHA-2 bundle is exercised at runtime by the primitive vectors, the SHA2-128f round trips and the
  trace-target tests. An implementation is covered when its encoding agrees with the
  specification's, which these tests check on fixed inputs and a refinement proof would check for
  all.
- **Interface.** The pure wire theorem fixes context and mode and reuses the strict codecs.
  Prehash collision accounting and external entropy-failure contracts require separate proofs.
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
