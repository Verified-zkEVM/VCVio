# S02 independent security-architecture review r4

Verdict: **PASS**

Blocking findings: **0**
Nonblocking findings: **0**

Reviewer: fresh independent S02 r4 reviewer; not the S02 implementer.
Review date: 2026-08-25.
Reviewed tree: VCVio commit `c5d6cb03d11126e6290bec58ef8824f36fc3a73b` on branch
`codex/sphincsplus-formalization`, plus the current uncommitted S02 worktree.

Independence and write-scope statement: I began from the pinned EasyCrypt sources, inspected all
four new Lean modules and both current S02 design/session documents in full, and replayed the r1-r3
counterexamples against the current types. Read-only commands and a new
`/tmp/S02R4IndependentProbe.lean` were the only actions before this verdict. This r4 file is my only
repository edit. I did not modify the implementation, `HashSig.lean`, the S02 design/session
documents, the r1/r2/r3 artifacts, accepted S00/S01 infrastructure or harness, the rejected legacy
`HashSig/SLHDSA/Security.lean`, or any construction file.

## Decision summary

The r3 blockers are fixed in the load-bearing architecture. The impossible honest-target provider
and its exact-family certificates are absent. TCR, DSPR, SPprob, PRE-C, and UD-C are standalone
stateful two-phase games: the program's `pick` phase makes the target and, for `-C`, collection
queries; the sampled public seed and retained private state are supplied only to the oracle-free
`finish` phase. The challenger logs that single `pick` execution and derives its count,
distinctness, selected-target, and disjointness events from the log.

The real PRE/UD target oracle samples a fresh hidden input on every call and returns only its F
output; the ideal UD oracle samples a fresh output on every call. DSPR and SPprob independently run
the identical stateful program and use the program's selected index, with SPprob ignoring only the
guess. The ITSR challenger supplies only fresh message randomizers; post-SKG/post-MKG setup and
public Hmsg parameters belong to the reduction program, and the challenger no longer generates or
injects a real full-SLH key pair.

The original EUF experiment separately retains generated-key seed/root coupling, full-request
freshness, and structural `qS`/`qH` predicates on the actual public adversary. The RHS contains
exactly the twelve authoritative terms and coefficients, with no arbitrary component scalar,
target sampler, birthday/interleaving term, or additive budget loss. Quantifier order fixes the
conditions, encoder, and complete reduction system before quantifying over the original adversary
and its budget witnesses. The architecture remains explicitly classical and makes no QROM or
proved-reduction claim.

I found no blocking or nonblocking defect.

## Primary-source correspondence

The authority checkout `/home/alh/SPHINCS/FV-SPHINCSPLUS-EC` was clean at exactly
`a28e4c53897a4bb57b575a177225862d48f824b7`. The reviewed source hashes were:

- `3bb1ce65aec7...` — `proofs/SPHINCS_PLUS.ec`;
- `67b0031db0fb...` — `proofs/KeyedHashFunctions.eca`;
- `ac5e354b298b...` — `proofs/FORS_ES.ec`;
- `1e1f5c82fa6d...` — `proofs/TweakableHashFunctions.eca`.

The exact source checks were:

- `SPHINCS_PLUS.ec:4338-4370` gives, in order, SKG PRF difference, MKG PRFmsg difference,
  Hmsg/ITSR, truncated DSPR-minus-SPprob, `3 *` FORS-F TCR, FORS-H TCR-C, FORS-Tl TCR-C,
  `(w - 2) *` WOTS-F UD-C difference, WOTS-F TCR-C, WOTS-F PRE-C, WOTS-Tl TCR-C, and XMSS-H
  TCR-C. `Architecture.lean:505-535,553-571` matches this order and these coefficients exactly.
- `TweakableHashFunctions.eca:57-68,71-134` samples a fresh hidden PRE input per target query,
  runs `pick` before `find(pp)`, and checks selected-index range, query cap, and distinct tweaks.
  Lean matches this at `Architecture.lean:181-204,225-235,252-274,296-299,441-456`.
- `TweakableHashFunctions.eca:261-335` and `350-454` give the TCR and DSPR/SPprob chosen-target
  interfaces. Lean's target oracle accepts `(address,input)`, logs actual calls, and reveals the
  public seed only to `finish` (`Architecture.lean:177-196,225-294,383-439`). Both FORS-F terms use
  `system.forsFDspr adversary` at `Architecture.lean:520-522`, so each experiment independently runs
  the same program and SPprob ignores only its Boolean.
- `TweakableHashFunctions.eca:483-507,523-542` samples a fresh real input or fresh ideal output on
  every UD query and checks the actual target log. Lean does the same at
  `Architecture.lean:198-208,252-274,458-488` without recording the hidden real input.
- The collection games at `TweakableHashFunctions.eca:613-646,712-745,839-869` expose target and
  collection oracles during the same `pick` and derive disjointness from those two logs. Every Lean
  `-C` program receives a sum oracle; one `withLogging` run covers both sides, and the event projects
  both target and collection tweaks from that log (`Architecture.lean:184-221,230-277,396-411,
  441-488`).
- `KeyedHashFunctions.eca:1486-1505,1513-1567` supplies a fresh ITSR key for every query and leaves
  adversary setup inside `find`. `FORS_ES.ec:2175-2239` constructs the post-hop M-FORS-NPRF state
  inside the reduction and caches repeated messages there. Lean's `PostHopITSRAdversary` owns
  `setup`, private `State`, and public Hmsg parameters; the generic challenger supplies only the
  fresh-key oracle (`Architecture.lean:313-340,490-501`). No `generateKeyPair`, `GeneratedKeyPair`,
  or `SecretKey` occurs in this component-game path.
- The post-SKG/post-MKG world is also visible at `SPHINCS_PLUS.ec:2132-2178`, where the intermediate
  games use `keygen_nprf` and then random message keys. The S02 docs accurately leave the concrete
  NPRF setup correspondence as a later proof obligation rather than asserting it now.

## Lean architecture evidence

### Original EUF coupling and budgets

`generateKeyPair` samples `SkSeed`, `SkPrf`, and `PkSeed`, calls `slhKeygenInternal` once, and
packages public/secret seed and root equalities (`OracleSurface.lean:32-72`). The complete query
language is indexed by that generated public key, while the public adversary language has no PRF or
PRFmsg constructor (`OracleSurface.lean:101-162`). `queryImpl` uses only the generated key's seed and
root (`OracleSurface.lean:186-204`).

`honestTranscriptDistribution` owns key generation and runs the actual adversary through the
seed-coupled logging handler (`Transcript.lean:130-146`). `ForgerySuccess` verifies under that same
public key and checks freshness of the complete `MessageInput` (`Transcript.lean:116-121`).
`AdversaryBounds` requires `IsQueryBoundP` signing and public-hash bounds on `adversary.main pk` for
every `pk` (`OracleSurface.lean:206-227`); the one-query/zero-budget and pure/zero-budget regression
lemmas elaborate.

The original transcript's ITSR projection is also locally correct: signing responses supply their
actual R, explicit public Hmsg entries are excluded, and every reconstructed digest is recomputed
under the generated public key (`Transcript.lean:36-128`). This scheme-transcript predicate is not
substituted for the standalone quantitative ITSR term.

### Game timing, visibility, and events

The independent `#check` output fixed the decisive types as:

```text
TwoPhaseAdversary.pick   : OracleComp spec State
TwoPhaseAdversary.finish : Public -> State -> ProbComp Answer
runTwoPhase              : ... -> Public -> ProbComp (Answer × QueryLog spec)
```

`runTwoPhase` interprets and logs `pick`, then runs `finish` with the public parameter and retained
state (`Architecture.lean:223-235`). Thus target selection happens in-game before public-seed
disclosure, and `finish` has no target or collection oracle.

For chosen-target games, the log records the address and input and the challenger recomputes the
success predicate. For sampled-target games, the query contains only the address and the dependent
response log contains only the F output; the sampled preimage is not present. `TargetTraceValid` and
`SampledTraceValid` enforce the formula cap and `Nodup` tweaks on actual queries, selected-list lookup
rejects invalid indices, and `CollectionDisjoint` rejects any common target/collection tweak
(`Architecture.lean:237-299`). These are event failures, not context hypotheses.

The independent probe compiled all of the following counterexample gates:

- an empty actual target trace is valid, matching the source's `0 <= nrts`, but TCR, DSPR, SPprob,
  and PRE success are all false for every selection on that trace;
- index `1` is invalid for a singleton chosen-target trace and makes TCR success false;
- two identical target tweaks make `TargetTraceValid` false;
- a replicated trace of `targetCount + 1` entries makes `TargetTraceValid` false;
- `CollectionDisjoint [address] [address]` is false;
- the real sampled handler unfolds to a fresh `Y` sample followed by F evaluation, while the ideal
  handler unfolds to a fresh `Y` output sample.

This closes the impossible-provider, post-hoc-game, leaked/preloaded-UD, unrelated-collection-log,
invalid-index, duplicate, overflow, and overlap counterexamples without introducing an impossible
assumption.

### Roles, caps, master shape, and quantifiers

The independent runtime evaluations were:

```text
construction / primitive / master / target role cards: 8 / 6 / 12 / 8
FORS F:       422212465065984
FORS H:       422212439900160
FORS Tl:      4194304
WOTS F UD-C:  285212672
WOTS F TCR-C: 1140850688
WOTS F PRE-C: 285212672
WOTS Tl:      4194304
XMSS H:       4194303
```

These values follow `2^h` FORS instances, the per-layer XMSS tree sum, and the per-layer WOTS
instance sum at `slhdsaSha2_128_24` (`Architecture.lean:76-149`). `targetCount_pos` excludes a zero
formula cap; source-shaped games may issue fewer queries, including zero. `ParameterConditions`
requires `h = hp*d` and exactly `lgw = 2`, `4`, or `8` (`Notions.lean:49-64`).

`ReductionSystem` has one typed program constructor per authoritative term and no probability or
sampler field (`Architecture.lean:342-375`). `ClassicalSecurityContext` contains only parameter
conditions and this reduction system (`Architecture.lean:537-543`). `RepairedMasterStatement`
therefore fixes parameters, instances, encoder, conditions, and the complete reduction system before
`forall adversary qS qH`; the premise is the actual program bound and the conclusion compares the
original EUF probability with the experiment-derived RHS (`Architecture.lean:545-580`). No free
public seed, target count, target/transcript sampler, or component scalar remains.

## R1-r3 finding dispositions

| earlier finding | r4 disposition |
| --- | --- |
| S02-R1-001 signing ITSR history | **Fixed.** Only signing entries provide `(R,request)` history; explicit Hmsg entries are excluded, with coherence proved. |
| S02-R1-002 arbitrary component scalars | **Fixed.** All twelve values are computed from typed PRF, ITSR, target, or collection experiments. |
| S02-R1-003 disconnected counts/targets | **Fixed.** Formula caps validate the actual challenger-owned target-oracle trace in each source-shaped game. |
| S02-R1-004 missing lgw restriction | **Fixed.** `lgw_approved` is exactly `2 or 4 or 8`. |
| S02-R2-001 original-transcript ITSR term | **Fixed.** The quantitative term is a standalone default-oracle ITSR game with program-owned post-hop setup. |
| S02-R2-002 uniform-index SPprob | **Fixed.** DSPR and SPprob independently execute the same stateful program and use its selected index. |
| S02-R2-003 leaking/unchecked UD | **Fixed.** Real inputs are fresh and hidden, ideal outputs are fresh, and actual trace validity is in both events. |
| S02-R2-004 vacuous separation/role aliasing | **Fixed.** The impossible provider is gone; eight roles are distinct; disjointness is only a same-execution `-C` event. |
| S02-R3-001 impossible honest-target provider | **Fixed.** Provider/package/view declarations are absent; an empty original execution log requires no certificate. |
| S02-R3-002 post-hoc TCR/DSPR/SPprob/PRE | **Fixed.** Each is an in-game target-oracle program with state across `pick` and `finish`. |
| S02-R3-003 wrong UD input/collection execution | **Fixed.** Fresh-input real calls and target/collection calls occur in one logged `pick` in both worlds. |
| S02-R3-004 real full-SLH ITSR setup | **Fixed.** The generic ITSR challenger does not generate or inject an SLH key; reduction-owned setup is the admitted post-hop boundary. |

No disposition relies on the session narrative alone; each was checked against the current type,
definition body, source game, and compiled counterexample probe.

## Classical boundary and documentation claims

`ClassicalModel` has only the `oracleComp` constructor, and `QROMClaim` has no constructors
(`Notions.lean:228-239`). No quantum state, superposition query, unitary oracle, lifting theorem, or
classical-to-QROM cast occurs in the new modules.

The two S02 documents accurately state that this is a design contract, not a proved master
reduction; that concrete reduction construction, post-hop NPRF correspondence, component
losslessness, request encoding, and signer-internal instrumentation remain future work; and that the
rejected legacy placeholder remains untouched. I found no documentation overclaim or contradiction
with the Lean surface.

## Build, scope, scan, and axiom evidence

```text
git rev-parse HEAD; git branch --show-current; git status --short
  PASS: requested branch/commit confirmed. Before this artifact, scope was exactly HashSig.lean,
        the four S02 modules, the two S02 documents, and r1/r2/r3 artifacts.

git -C /home/alh/SPHINCS/FV-SPHINCSPLUS-EC rev-parse HEAD
git -C /home/alh/SPHINCS/FV-SPHINCSPLUS-EC status --short --branch
sha256sum proofs/{SPHINCS_PLUS.ec,KeyedHashFunctions.eca,FORS_ES.ec,TweakableHashFunctions.eca}
  PASS: clean pinned authority and recorded hashes.

lake env lean HashSig/SLHDSA/Security/Notions.lean
lake env lean HashSig/SLHDSA/Security/OracleSurface.lean
lake env lean HashSig/SLHDSA/Security/Transcript.lean
lake env lean HashSig/SLHDSA/Security/Architecture.lean
  PASS: all four modules elaborated independently with no output.

lake env lean /tmp/S02R4IndependentProbe.lean
  PASS: field signatures, role/count evaluations, empty/invalid/duplicate/overflow/overlap events,
        fresh handler unfoldings, and load-bearing axiom prints compiled.

lake build HashSig
  PASS: 2748 jobs; only the frozen rejected HashSig/SLHDSA/Security.lean:150 sorry warning.

lake build
  PASS: 3007 jobs. Replayed warnings were pre-existing non-S02 VCVio/ToMathlib admissions.

git diff --check
  PASS.
```

Source scans over the four new modules found no `sorry`, `admit`, axiom declaration, `unsafe`,
`extern`, `partial`, initializer, implementation override, linter suppression, false elimination,
runtime/compiler/meta import, or forbidden interop import. The twelve `noncomputable` definitions are
exactly probability/ENNReal evaluations and experiment-derived master expressions. Removal scans
found no `HonestTargetProvider`, certified outcome/package, public target view, post-hoc component
runner, component probability scalar, or target/transcript sampler.

The independent `#print axioms` audit covered parameter and target positivity, digest mapping and
ITSR, key coupling and query interpretations, signing-history coherence, EUF and transcript
distributions, all role cards and query-bound regressions, all target/collection handlers and trace
events, every standalone component probability, `componentTerm`, `eufAdvantage`, `repairedRHS`,
`RepairedMasterStatement`, and budget independence. Every root was axiom-free or used only the S00
allowlist `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or other axiom appeared.

The reviewed new-file hashes before this artifact were:

```text
a6cf29ea8886...  HashSig/SLHDSA/Security/Notions.lean
f6a5d44566b1...  HashSig/SLHDSA/Security/OracleSurface.lean
575663befe8d...  HashSig/SLHDSA/Security/Transcript.lean
d6bc2cc9b277...  HashSig/SLHDSA/Security/Architecture.lean
51080bfdae3f...  docs/slhdsa/security-architecture.md
943fd8ecaca8...  docs/slhdsa/sessions/S02-security-architecture.md
```

## Immutable final decision

Final verdict: **PASS with zero blocking findings and zero nonblocking findings**. The current S02
worktree defines an inhabitable, source-shaped classical security architecture with the exact
repaired master boundary, genuine in-game target/collection timing, post-hop ITSR ownership,
generated-key EUF coupling, actual budget predicates, and explicit nonclaims. S02 is accepted at
this reviewed tree. No commit, push, or PR was created.
