# SLH-DSA in the classical random-oracle model: the target bound and leanVM's 127-bit proof

Status: design record, established 2026-10-05. It fixes how the classical random-oracle bound for
FIPS 205 SLH-DSA is accounted, records the levels that accounting reaches, and compares the result
with the 127-bit proof for a SPHINCS variant in
[`leanEthereum/leanVM`](https://github.com/leanEthereum/leanVM) (`formal/sphincs`), whose argument
this work draws on. The development is in pull request #766; the implementation status of `main`
is in [`slh-dsa-status-and-roadmap.md`](slh-dsa-status-and-roadmap.md).

**What is proved.** The three-oracle bound `securityBound` at `c = 2` and `r = 1` is proved in Lean
for each fixed public seed, in both signing modes: `securityTarget_two_one`
(`HashSig/SLHDSA/Security/CoverageBound.lean`) proves `SecurityTarget core e optRand 2 1` under the
byte laws, the key discipline and `|Y| ≤ |SK.prf|`, all three discharged at every FIPS 205 bundle,
with `optRand` arbitrary. `unforgeableAdvantage_romScheme_le_securityBound` averages it over any
distribution of the public seed, the uniform one of FIPS 205 included. The bound is stated over
`|Y|`, which is `2^{8n}` at the FIPS 205 bundles, and is the sum of two proved terms:

- the joint target-collision and hidden-value term `2(q_h + V) / 2^{8n}`, with `V` the verifier's
  query bound `verifyInternalQueryBound` and the seed guess charged inside it
  (`prEvent_romSchemeRun_runTargetCollision_or_runHiddenHit_le`,
  `HashSig/SLHDSA/Security/JointBound.lean`). With the union bound split after the first game hop,
  the forging advantage is at most that term plus the probability of interleaved-target coverage in
  the ideal hidden-seed game (`unforgeableAdvantage_romScheme_pure_le_add_idealDraw`), in which
  every secret value and randomizer is sampled independently of the public answers;
- the coverage term `(q_h + 1) · weightedTargetCoverBound h a k q_s q_h (q_s / 2^{8n})`, which
  bounds that coverage probability (`prEvent_idealDraw_runItsrCovered_le`).

The same bound with the coverage probability of the run in place of the ideal one
(`unforgeableAdvantage_romScheme_pure_le_add`) also holds, but for deterministic signing its
coverage term is not bounded at the size of the target's coverage term
([Coverage after the seed hop](#coverage-after-the-seed-hop)).

**What is not proved.** The faithfulness step relating the three-oracle model to the byte-level
scheme over a single SHAKE256 is not proved. Nor, therefore, are its losses: the terms
`(q_s + 1) / 2^{8n}` of the faithfulness hook, and at `n = 32` a weak-key term of about
`2^{−172}` that no designed argument removes ([The 256-bit sets](#the-256-bit-sets)). Of the
levels below, the "Three-oracle" column evaluates the proved three-oracle bound, which is not a
level of the byte-level scheme; the other columns evaluate formulas that are not Lean results.

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
forger and signer strings that begin with `SK.prf`.

Each loss is charged against the **queries of the kind that can cause it**, rather than against
`q_h`, on every run: one joint potential over the deferred relabelled game covers the hidden-value
hit, the target collision (at oracle-key level, so a forger input of any length at a node's key
counts) and the seed guess, and is to cover, at byte level, the faithfulness misroute, with each
forger or verifier query charged by its kind. The generic joint potential is
`VCVio/OracleComp/QueryTracking/RandomOracle/JointPotential.lean`. Its SLH-DSA
instantiation for the target collision, the hidden-value hit and the seed guess is proved
(`HashSig/SLHDSA/Security/JointBound.lean`, through the event transport of
`HashSig/SLHDSA/Security/Transport.lean`); the faithfulness hook (`Fev`), which is to join the
faithfulness event into the same potential, is owed. A query at an honest (ledger) key under
`PK.seed` causes at most two unit hazards: its input can equal a hidden value, or its fresh answer
can equal the honest answer. A query at a secret-derivable point (a `PRF` key or `PRF_msg`) causes
one, the seed guess. At byte level, an `H_msg` query causes one, the faithfulness event, when its
string begins with `SK.prf`; these points are at no key, so this kind is disjoint from the others.
Under the key-separation hypothesis (`CorePrimitives.KeySeparated`) no
derivable point is at an honest key, so the kinds are disjoint for the target collision, the
hidden-value hit and the seed guess. That the faithfulness theorem states its loss as an event of
the typed run, joined into the potential and charged nowhere else, is owed with it. The forger's
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
`SK.prf = PK.seed`. Both are to be joined into the same joint potential, not added as separate
probabilities, and both are charged in either signing mode, so the byte-level bound is the same
for hedged and deterministic signing. For hedged signing the faithfulness event misroutes only if
some signing query's `opt_rand` equals `PK.seed`; a hedged statement that bounds the two jointly
would replace `q_s / 2^{8n}` by `q_s (q_h + q_s + 1) / 2^{16n}` and keep the three-oracle level.

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
ideal hidden-seed game, as `unforgeableAdvantage_romScheme_pure_le_add_idealDraw` does. There the
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
model, not of the byte-level scheme. The other columns are evaluations of formulas, not Lean
results, and the faithfulness step that would make them levels of the byte-level scheme is not
proved. "Byte level" adds to the three-oracle bound the terms `1 / 2^{8n}` (`SK.prf = PK.seed`)
and `q_s / 2^{8n}` (the signer's faithfulness event) and omits the weak-key term; with the
faithfulness hook charged in both signing modes it is the byte-level level of hedged and
deterministic signing alike, and at `n = 32` it holds per public seed for every seed outside the
weak set ([The 256-bit sets](#the-256-bit-sets)). "Byte level, averaged" adds the weak-key term
`|A_hon| / 2^256`, the byte-level bound averaged over the key pair; it differs from "Byte level"
only at `n = 32`. "Losses added separately" charges the losses of "Byte level" as separate
`q_h`-bounded terms, the constant 4 above, and also omits the weak-key term. "Two-hazard limit"
is the level with the coverage term and the constant 2 alone; `8n − 1` is the level of
`Adv ≤ q_h / 2^{8n−1}`. The last column is the coverage term's cost in units of `q_h / 2^{8n}`.

| Set | Three-oracle | Byte level | Byte level, averaged | Losses added separately | Two-hazard limit | `8n − 1` | Coverage cost |
|---|---|---|---|---|---|---|---|
| 128s | 126.99 | 126.41 | 126.41 | 125.67 | 126.99 | 127 | 0.02 |
| 128f | 126.54 | 126.09 | 126.09 | 125.48 | 126.54 | 127 | 0.76 |
| 192s | 190.82 | 190.29 | 190.29 | 189.60 | 190.82 | 191 | 0.27 |
| 192f | 190.87 | 190.33 | 190.33 | 189.62 | 190.87 | 191 | 0.19 |
| 256s | 254.41 | 254.00 | 235.95 | 253.41 | 254.41 | 255 | 1.00 |
| 256f | 254.27 | 253.89 | 236.26 | 253.34 | 254.27 | 255 | 1.32 |

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

The randomised routing argument sends each ambiguous forger string to one of its two readings by a
fair coin. It removes the forger-query case but not self-reference, since no router sees the
verifier's queries. The argument is therefore incomplete, and it does not establish the `n = 32`
byte-level rows. The faithfulness analysis that proposed the routing argument already required a
separate self-reference lemma for this case, stated over a cache of byte strings rather than typed
points; that lemma is not designed. Without it the byte-level bound at `n = 32` carries the weak-key
term `|A_hon| / 2^256`, about `2^{−171.95}` at 256s and `2^{−172.26}` at 256f. The term depends only
on `PK.seed`, not on the adversary: it is the probability that the uniform `PK.seed` is weak. At
`q_h = q_s = 2^64` the byte-level levels are:

- averaged over the uniform `PK.seed`: 235.95 (256s) and 236.26 (256f);
- per seed, for every `PK.seed` outside the weak set: 254.00 (256s) and 253.89 (256f).

The averaged level loses about one bit per halving of `q_h`, because the weak-key term is fixed
while the per-query normalisation changes: at `q_h = q_s = 2^40` it is about 212 (211.95 at 256s,
212.26 at 256f), against 254.42 per seed outside the weak set.

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
| Unforgeability | EUF-CMA first, then SUF-CMA | SUF-CMA |
| Bound | `2·q_h / 2^{8n}` plus coverage and verifier terms; byte level adds `(q_s + 1) / 2^{8n}` and, at `n = 32`, the weak-key term `\|A_hon\| / 2^256` | `q / 2^127` |

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

- **Signing mode.** The three-oracle bound is the same in both modes, and so is the byte-level
  bound with the faithfulness hook charged in both, `q_s / 2^{8n}` included. Only a hedged
  statement that bounds the faithfulness event jointly with `opt_rand = PK.seed` would remove
  that term for hedged signing.
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
