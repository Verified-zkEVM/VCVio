# S02 security architecture session

Status: accepted by independent r8 PASS at exact commit `a80e4d336276cd86fb80be64e82d9d57e7dfc8b3`.

Date: 2026-08-25
Branch: `codex/sphincsplus-formalization`
Accepted predecessor: S01 R16, PASS with zero blocking findings.

Repair base commit: `7b77e700b3d24a6ab94ed741a650954bbd90859a`.

## Scope

S02 began from accepted S00/S01 infrastructure. The initial implementation did not reopen the
descriptor/AST machinery, change rejected `HashSig/SLHDSA/Security.lean`, or touch construction
files. The r5/r6 repairs make narrow changes to the shared harness only for concrete S02
provenance/revision and exact declaration-metadata regressions; the frozen S01 parser subsystem is
otherwise unchanged. COV-005 and F-015/F-016/F-018 remain outside this session.

The implementation is isolated in four new `SLHDSA.Security` modules plus generated umbrella
imports. The originally accepted implementation commit was `7b77e700`; r5 reopened it after the
complete compiled-policy, provenance, traceability, and semantic audit.

## Authority extraction

The session checked:

- `proofs/SPHINCS_PLUS.ec:4338-4370` at pinned revision
  `a28e4c53897a4bb57b575a177225862d48f824b7`;
- `SPHINCS_EC.pdf`, especially pages 10-11, 15, 18, 23, and 28;
- CCS 2019 Theorem 17 for the historical PRF/PRFmsg/ITSR/FORS boundary;
- the repaired Hülsing-Kudinov and EasyCrypt WOTS UD/TCR/PRE development;
- FIPS 205 Algorithms 2, 4, and 18-24.

The master theorem has twelve roles, no birthday/interleaving term, and no additive qS/qH loss.
The FORS instance multiplier maps to `2^h`, not `Params.d`.

## Current architecture

- Original EUF execution owns generated keys, public-seed/root coupling, full-request freshness, and
  an ordered dependent query log.
- Public and internal query types are separate; PRF and PRFmsg are unrepresentable publicly.
- qS/qH use `IsQueryBoundP` on the actual public program for every public key.
- Target counts are formula-derived positive caps for the exact eight theorem roles.
- TCR, DSPR, SPprob, PRE, and UD-C are standalone two-phase oracle games. `pick` has oracle access
  and returns private state; `finish` has the sampled public seed and no oracle access.
- DSPR and SPprob independently run the same two-phase program and use its selected natural index;
  invalid indices make the event false.
- TCR/DSPR target queries choose `(tweak,input)`. PRE and real UD target queries sample a fresh
  hidden input per query and return only its hash output. Ideal UD samples a fresh output.
- Every `-C` program receives target and collection oracles together. The same execution log supplies
  the target-count, distinctness, and collection-disjointness checks.
- `PostHopITSRAdversary.setup` owns hybrid/NPRF setup state. The ITSR challenger supplies only fresh
  message-randomizer queries and never injects a real generated SLH secret key.
- The RHS has exactly the two PRF differences, ITSR probability, DSPR-minus-SPprob, five TCR terms
  (one with coefficient three), UD-C difference with coefficient `w-2`, PRE-C, and remaining TCR-C
  terms in authoritative order.
- The architecture is classical only and asserts no master theorem.

## Adversarial gates

| gate | current result |
| --- | --- |
| zero formula cap | excluded by `targetCount_pos` |
| zero actual target trace | admitted, but any selected-target event fails |
| arbitrary original transcript/target sampler | absent from `ClassicalSecurityContext` |
| free public seed | absent from original EUF and sampled internally by component games |
| secret primitive exposure | absent from `AdversaryQuery` |
| target overflow or duplicates | event false via actual oracle trace validation |
| collection overlap | event false in the same `-C` execution |
| fake qS/qH | blocked by structural query predicates |
| invented scalar loss | absent; `289/256` counterexample compiled |
| missing role | cards compile at construction/primitive/master/target = `8/6/12/8` |
| fake QROM | absent; `QROMClaim` is uninhabited |

## Review history and dispositions

R1 returned FAIL with four blocking findings:

| finding | current disposition |
| --- | --- |
| R1-001 signing ITSR history | signing entries supply `(R,request)`; explicit Hmsg is excluded |
| R1-002 arbitrary component scalars | removed; every term is computed by a concrete experiment |
| R1-003 disconnected counts/targets | formula caps validate actual challenger-owned oracle traces |
| R1-004 missing lgw restriction | exact `lgw = 2 or 4 or 8` condition added |

R2 returned FAIL with four blocking findings:

| finding | current disposition |
| --- | --- |
| R2-001 original-transcript ITSR | quantitative term is a dedicated default-oracle ITSR game |
| R2-002 uniform-index SPprob | same two-phase DSPR program chooses the index in both games |
| R2-003 leaking/unchecked UD | fresh real inputs, output-only oracle, actual logged validity |
| R2-004 vacuous separation/role aliasing | no package-level separation; eight distinct origin roles |

R3 returned FAIL with four blocking findings. The immutable artifact is
`reviews/S02-security-architecture-review-r3.md`:

| finding | current disposition |
| --- | --- |
| R3-001 impossible honest-target provider | provider and certified exact families removed from the load-bearing context; empty original logs are ordinary outcomes |
| R3-002 post-hoc TCR/DSPR/SPprob/PRE | replaced by in-game target-oracle programs with state across `pick` and `finish` |
| R3-003 wrong UD input/collection execution | real target calls sample fresh inputs; target and collection calls share one program/log in both worlds |
| R3-004 real full-SLH ITSR setup | challenger no longer calls `generateKeyPair`; program-owned post-hop setup supplies public Hmsg parameters and private NPRF state |

R4 independently replayed all earlier counterexamples and primary-source comparisons, then returned
PASS with zero blocking and zero nonblocking findings. Its immutable acceptance artifact is
`reviews/S02-security-architecture-review-r4.md`. It records successful focused and full builds,
source scans, event counterexamples, and the load-bearing axiom audit. This independent verdict,
rather than the implementation narrative, initially accepted S02. R5 later showed that r4 did not
run the authoritative compiled policy or complete traceability/provenance gates, so that acceptance
is no longer current.

R5 returned FAIL with six blocking findings in the immutable artifact
`reviews/S02-security-architecture-review-r5.md`:

| finding | accepted r8 disposition |
| --- | --- |
| R5-001 generated partial helpers | all eight source-recursive projections use total `List.map`, `filterMap`, or `foldr`; the seven-helper policy is unchanged |
| R5-002 unreproducible acceptance revision | an exact `repair_base_revision` is cross-checked with this session and exact active bytes are separately hashed |
| R5-003 omitted S02 source provenance | the composite includes all four `Security/*.lean` modules; exact command/glob correspondence and a Security-byte mutation regression are gated |
| R5-004 absent traceability | matrices, declarations, findings, decisions, TCB, report, and indexes are synchronized |
| R5-005 generic LHS hardwired to d=1 | direct hardwiring is removed, but `SchemeInterface` is honestly classified as arbitrary and F-079/PO-003 remain open for construction refinement |
| R5-006 stale transcript-derived target contract | standalone games are the D-009 candidate; D-009 remains proposed and no prose treats it as accepted supersession |

R6 returned FAIL with five blocking findings in the immutable artifact
`reviews/S02-security-architecture-review-r6.md`:

| finding | accepted r8 disposition |
| --- | --- |
| R6-001 uncoupled scheme bundle overstated | classify the bundle as an arbitrary signature-scheme experiment interface and leave F-079/PO-003 open for S08/S09 |
| R6-002 unapproved decisions treated as operative | retain D-006/D-009 as proposed and make PO-006/PO-008 provisional rather than discharged |
| R6-003 inconsistent source-composite commands/no mutation | require the exact four-glob commands and execute a controlled temporary Security-source byte mutation |
| R6-004 arbitrary ancestor revision | require the exact repair-base identity, cross-check this session marker, and correct the source ledger |
| R6-005 false inventory/scope facts | correct all dependency names, record full declaration spans, and accurately describe the harness edits |

R7 independently confirmed all five r6 repairs and every technical gate, then returned FAIL with
one blocking finding in the immutable artifact `reviews/S02-security-architecture-review-r7.md`:

| finding | accepted r8 disposition |
| --- | --- |
| R7-001 stale S03 predecessor routing | state that no accepted predecessor exists, retain invalidated `7b77e700` only as evidence, and forbid S03 until the exact repaired commit receives r8 PASS |

R8 returned PASS with zero blocking and zero nonblocking findings in
`reviews/S02-security-architecture-review-r8.md`. It accepts only exact commit
`a80e4d336276cd86fb80be64e82d9d57e7dfc8b3` and preserves D-006/D-009 as proposed,
F-079/F-080 as open, and the theorem/conformance/QROM boundaries.

## Validation

Before r3, all four modules, the focused architecture target, and `lake build HashSig` passed; the
full build's only warning was the pre-existing rejected `Security.lean:150` `sorry`. Axiom probes
reported only `propext`, `Classical.choice`, and `Quot.sound`, never `sorryAx`.

After the r3 rewrite, the focused architecture build and `lake build HashSig` both passed; the full
build completed 2748 jobs and replayed only the pre-existing legacy `Security.lean:150` warning.
`/tmp/S02R4Probe.lean` compiled the two-phase field signatures, zero-target-valid/invalid-selection
regressions, and axiom prints for every new handler, trace predicate, component experiment, master
term, RHS, and statement. Results were axiom-free or used only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` occurred. `git diff --check`, the admission/runtime scan, removal scan for
the impossible provider/post-hoc views, and repository scope audit all passed.

R5 exposed one concrete manifest-semantic regression in the harness: exact-`HEAD` checking made a
committed manifest self-referential and unreproducible. R6 showed that merely accepting any ancestor
was too weak. The second repair requires the exact invalidated implementation commit above as the
named repair input, cross-checks this session, verifies ancestry only as an additional consistency
check, and binds active source bytes through the expanded composite. The frozen descriptor/AST
subsystem is otherwise unchanged.

The first repaired pre-r6 gates reported: all four focused modules and `lake build HashSig` PASS; the only
build warning is the pre-existing legacy `Security.lean:150` admission; the static policy import
observes 27 HashSig modules and 1,629 owned constants; the exact seven compiler helpers PASS; and
the transitive axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`, and the one
allowlisted legacy `sorryAx`. `/tmp/S02R6Probe.lean` prints only the three standard axioms on every
completed load-bearing root and no `sorryAx`. The docs/provenance gate verifies the 26-file source
composite and passes. The second repair adds the exact command/glob check and controlled mutation
regression; its complete pre-r7 evidence is recorded after the gates run.

The complete second-repair pre-r7 run passes `lake build HashSig`, the focused
`S02InventoryProbe.lean`, the authoritative `PolicyAudit.lean`, docs-only validation, and
`./scripts/slhdsa/validate.sh`. The probe elaborates all eighteen S02 inventory roots plus
`CollectionDisjoint`, `SPprobSuccess`, and `sampledTargetRealImpl`; the structured gate checks their
full source spans. The policy audit again observes 27 modules, 1,629 owned constants, the exact seven
generated helpers, and only the three standard axioms plus the one allowlisted legacy `sorryAx`.
The full baseline runtime suite, both existing KATs, exact repair-base check, four-glob composite,
and controlled Security-byte mutation all report PASS.

## R4 review focus

1. exact role order, coefficients, and formula caps;
2. two-phase target-oracle timing and private-state flow;
3. independently run same-program DSPR/SPprob;
4. fresh-input real PRE/UD and fresh-output ideal UD;
5. same-execution target/collection logging and event checks;
6. post-SKG/post-MKG program-owned ITSR setup with no generated full-SLH key injection;
7. absence of the impossible honest-target provider and post-hoc public views;
8. generated-key coupling and actual qS/qH on the original EUF LHS;
9. zero-target, invalid-index, duplicate, overflow, and overlap behavior;
10. build, axiom, source-scan, scope, and classical/QROM gates;
11. absence of overclaim while the reduction theorem and external request encoder remain future work.

## Remaining obligations

- Construct each named reduction from the original adversary and prove its component correspondence.
- Prove the concrete post-hop/NPRF setup used by the ITSR reduction.
- Refine honest signing internals when later construction proofs need their execution trace.
- Prove component losslessness and the repaired master inequality.
- Replace or retire the rejected legacy placeholder only in an authorized later session.
- Successor work begins only from exact accepted S02 commit
  `a80e4d336276cd86fb80be64e82d9d57e7dfc8b3`.
