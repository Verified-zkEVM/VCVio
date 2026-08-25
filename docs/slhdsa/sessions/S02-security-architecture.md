# S02 security architecture session

Status: r1/r2/r3 failed; independent r4 PASS with zero findings; S02 accepted.

Date: 2026-08-25
Branch: `codex/sphincsplus-formalization`
Accepted predecessor: S01 R16, PASS with zero blocking findings.

## Scope

S02 began from accepted S00/S01 infrastructure. It did not reopen descriptor/AST machinery, edit
the frozen harness, change rejected `HashSig/SLHDSA/Security.lean`, or touch construction files.
COV-005 and F-015/F-016/F-018 remain outside this session.

The implementation is isolated in four new `SLHDSA.Security` modules plus generated umbrella
imports. No commit, S02 push, or PR has been created.

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
rather than the implementation narrative, accepts S02.

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

The frozen S00/S01 harness has not been modified or rerun because S02 introduced no concrete
descriptor/AST regression.

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
- Begin successor work only from this independently accepted S02 boundary.
