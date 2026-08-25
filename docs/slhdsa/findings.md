# Validated findings

This register integrates the completed research/audit review FAIL findings rechecked during S00.
`VALIDATED` means the evidence and impact were confirmed; it never means the defect was fixed. The
future independent session reviews add dispositions under the protocol rather than erasing rows.

| ID | Severity | Status | Finding | Evidence | Required action |
|---|---|---|---|---|---|
| F-001 | CRITICAL | OPEN | `slhdsa_euf_cma_security` is entirely `sorry` | `Security.lean:150–175`; `#print axioms` includes `sorryAx` | Replace only after reviewed component/composition proof |
| F-002 | CRITICAL | OPEN | Zero target counts are admitted | Four unrestricted naturals; samplers over `Fin numTargets` | Use positive formula-derived target families |
| F-003 | CRITICAL | OPEN | Security primitive seed is not coupled to attacked key | Free `pkSeed` parameter; EUF game generates another key | Carry generated seed through experiment/transcript |
| F-004 | HIGH | OPEN | `qS/qH` do not bound adversary queries | They occur only in `slhdsaInterleavingLoss` | Add execution predicates and enforced instrumentation |
| F-005 | HIGH | OPEN | Invented loss is unproved and unbounded above by one | Natural query inputs unrestricted; source calls it a stand-in | Remove from target theorem; derive an ITSR hop/loss |
| F-006 | CRITICAL | OPEN | `Hmsg` ITSR and `T_l` security surfaces are absent | Current RHS has only PRFs, F-preimage, H-TCR, placeholder loss | Formalize selected primary notions and actual mapping |
| F-007 | HIGH | OPEN | `yToBytes` has no coherence/injectivity law | `Primitives.lean:77` is an arbitrary function | Add only the laws required by construction/security bridge |
| F-008 | CRITICAL | OPEN | Target samplers can be arbitrary and unrelated to honest use | Caller supplies `forsLeafInputs`/`wotsChainInputs` | Derive challenges from honest transcripts |
| F-009 | HIGH | OPEN | No asymptotic security theorem or quantum semantics | One finite classical VCVio inequality | Add finite accounting then explicit asymptotic/classical-QROM layer |
| F-010 | HIGH | OPEN | Main implementation is `d=1` and one legacy reduced set | Hypertree/Scheme fix tree/layer zero; Params names SHA2-128-24 | Generalize and implement all 12 sets |
| F-011 | HIGH | OPEN | Final external pure/pre-hash API is absent | Wrapper has empty-context hedged message only | Implement domain/context/OID modes and rejection |
| F-012 | HIGH | VALIDATED-REPORT-ERROR | Reports misstate CCS 2019 coefficients and omit invalidation of its full tight proof | Theorem 17 has `TCR(Th)+3*TCR(F)+DSPR(F)`; later literature identifies the WOTS reasoning flaw and HK22 repair | Treat CCS as historical statement/games, select repaired proof authority in S02 |
| F-013 | HIGH | VALIDATED-REPORT-ERROR | Reports conflate two FIPS Appendix-A FORS extraction changes | Appendix A separately describes reference-alignment and ambiguous per-tree-index clarification, then records incompatibility; Algorithm 4 is MSB-first | Pin operations/version and add discriminating fixtures |
| F-014 | HIGH | VALIDATED-REPORT-ERROR | Reports overstate EasyCrypt scope and quantum mechanization | Local development has abstract types/axioms and classical probabilistic games; it does not mechanize QROM/quantum lifting | Cite repaired abstract evidence and state classical/PQ boundary |
| F-015 | HIGH | OPEN | Existing KATs are not FIPS/ACVP conformance | Embedded vectors claim C-reference signer provenance; reduced/C13 profiles | Preserve as regression and ingest pinned normative evidence |
| F-016 | HIGH | OPEN | ACVP pre-hash positive-vector coverage is incomplete | ACVP-Server issue #469: 24/144 cells; two functions globally uncovered in measured file | Track positive cells; supplement without overclaim |
| F-017 | CRITICAL | BLOCKED | Deployment/refinement target is unresolved | No repository/commit/ABI selected | Owner must pin exact target before S19 |
| F-018 | MEDIUM | OPEN | Declaration inventory is manual/bootstrap | S00 JSONL is seeded from source, not kernel export | Build elaborated exporter before completeness claim |
| F-019 | MEDIUM | OPEN | EasyCrypt was not rerun | `easycrypt` absent from PATH at S00 | Reproduce pinned release/solver run before claiming reproduction |
| F-020 | HIGH | VALIDATED-REPORT-ERROR | Reports omit the FIPS WOTS checksum-shift correction | Appendix A changes line 6 of sign/recovery because submission pseudocode can shift incorrectly when `lgw != 4` | Use FIPS formula and add non-4 regression even though approved sets use 4 |
| F-021 | CRITICAL | FIXED | Source policy missed `attribute [init]`/`[builtin_init]` commands | S00 r4 counterexample; independent r9 PASS | Semantic audit checks regular/builtin initializer entries by defining module; direct token fixtures added |
| F-022 | CRITICAL | FIXED | Source policy missed unprefixed interpolation carrying `sorry` | S00 r4 counterexample; independent r9 PASS | Semantic audit rejects transitive `sorryAx`; compiled and token fixtures added |
| F-023 | HIGH | FIXED | Source policy missed option/label macros that generate initializers | S00 r4 counterexamples; independent r9 PASS | Semantic audit checks generated initializer entries; direct fixtures added |
| F-024 | HIGH | FIXED | Source policy missed `native_decide` generated axiom declarations | S00 r4 footprint; independent r9 PASS | Semantic audit rejects generated axiom constants; compiled fixture added |
| F-025 | CRITICAL | FIXED | Semantic audit allowed a HashSig theorem to depend on a nonstandard axiom owned by another module | S00 r5 reproducer; independent r9 PASS | Audit every owned declaration's complete transitive axiom set against the exact standard allowlist and placeholder exception |
| F-026 | HIGH | FIXED | Aggregate compiled-fixture assertions could mask a regressed historical detector | S00 r5 fixture-table audit; independent r9 PASS | Require a bijection between every actual finding and every expected declaration/kind/detail pattern |
| F-027 | HIGH | FIXED | Raw persistent-extension fixture handcrafted its finding and covered only regular init | S00 r6 inspection; independent r9 PASS | Share one surface-labelled production mapper; inject and extract real current state for all four ordinary surfaces |
| F-028 | CRITICAL | FIXED | Ordinary source import left regular-initializer IR entries invisible to the production audit | S00 r7 counterexample; independent r9 PASS | Programmatically meta-import with `loadExts := false`; require exact production-path ordinary/IR rejection and an absent sentinel |
| F-029 | MEDIUM | FIXED | Harness prose falsely attributed the 647-to-680 inventory delta to IR-visible declarations | S00 r8 controlled imports; independent r9 PASS | Attribute the delta to private visibility; keep IR coverage tied to compiled entries and the absent sentinel |
| F-030 | HIGH | FIXED | S01 normal gates did not fail closed over the exact ACVP-Server v1.1.0.38 compatibility commit or SP 800-230 draft status | S01 r0 finding S01-R0-001 | Hard-pin all coupled metadata in both normal gates and execute corrupt-commit/false-status negative mutations |
| F-031 | MEDIUM | FIXED | `SP800-230-128-24` ambiguously named both a six-set draft authority profile and the single-set current implementation | S01 r0 finding S01-R0-002 | Use `SP800-230-IPD-6SET` and `LEGACY-SHA2-128-24` as distinct gated identities everywhere |
| F-032 | LOW | FIXED | The pinned `draft-livelsberger-acvp-slh-dsa-01` bibliography entry used 2026 instead of its 2024 document year | S01 r0 finding S01-R0-003; pinned root `revdate` | Cite 25 June 2024 and gate the exact document identity/date |
| F-033 | LOW | FIXED | Four untracked S01 JSON artifacts contained terminal blank lines and ordinary `git diff --check` did not inspect them | S01 r0 finding S01-R0-004 | Normalize EOF and validate whitespace over all active tracked/untracked S01 files with only exact immutable-line exclusions |
| F-034 | HIGH | FIXED | S01 r1 accepted false FIPS 205 publication-date and authority-classification metadata | S01 r1 finding S01-R1-001 | Validate the complete exact FIPS authority record separately from genuine sibling-PDF byte verification and reject date/authority mutations |
| F-035 | MEDIUM | FIXED | S01 r1 did not make profile separation fail closed across canonical scope and active documentation | S01 r1 finding S01-R1-002 | Parse exact unique scope rows, scan every active surface, require cross-document associations, and reject reconflation mutations |
| F-036 | MEDIUM | FIXED | S01 r2 omitted the outer test scope from active-file checks and allowed added or contradictory profile associations | S01 r2 finding S01-R2-001 | Scan all test-support files and require an exact occurrence manifest plus complete exact matrix records and negative mutations |
| F-037 | MEDIUM | FIXED | S01 r2 overstated parser evidence and miscounted the canonical six-profile matrix | S01 r2 finding S01-R2-002 | Qualify parser evidence as schema-format only and gate the report count against exact scope rows |
| F-038 | HIGH | FIXED | S01 r3 did not complete-record validate the canonical FIPS profile artifact | S01 r3 finding S01-R3-001 | Require exact bytes plus exact authority API randomness pre-hash ordered parameter/OID and grammar records; reject focused mutations |
| F-039 | MEDIUM | FIXED | S01 r3 active-scope scanning skipped symlinks/special entries and allowed syntactically reconstructed profile identities | S01 r3 finding S01-R3-002 | Use a no-follow lstat scanner and require normalized identity counts to equal registered literal occurrences |
| F-040 | MEDIUM | FIXED | S01 r3 accepted added contradictory matrix rows outside the named-record checks | S01 r3 finding S01-R3-003 | Pin the exact current matrix file set and bytes in addition to semantic checks; update pins deliberately in future sessions |
| F-041 | MEDIUM | FIXED | S01 r4 queued checked directory pathnames and could later follow a replacement symlink outside the active tree | S01 r4 finding S01-R4-001 | Anchor the repository and every child with descriptor-relative no-follow opens and require metadata/opened inode identity before read or recurse |
| F-042 | LOW | FIXED | S01 r4 publicly exposed parsed-JSON helpers that could not preserve duplicate-key provenance | S01 r4 finding S01-R4-002 | Make parsed-JSON helpers private and expose only strict duplicate-safe string roots including an exact wrapper root |
| F-043 | LOW | FIXED | S01 r4 publicly exposed typed pair validation while relying on parser-established uniqueness invariants | S01 r4 finding S01-R4-003 | Make typed pair validation private document its parser-established invariant boundary and inventory only safe public string roots |
| F-044 | LOW | FIXED | S01 r5 declaration rows presented private source helpers and a nonexistent qualified executable entrypoint as Lean dependency names | S01 r5 finding S01-R5-001 | Use typed public/private/root/Lake dependency tokens, exact source anchors, direct/transitive labels, and three fail-closed mutations |
| F-045 | MEDIUM | FIXED | S01 r6 token checks accepted nonexistent public names commented private anchors and namespace-shifted root main | S01 r6 finding S01-R6-001 | Source-resolve exact active declarations with comment/namespace state and run an inventory-driven post-build external Lean visibility probe |
| F-046 | MEDIUM | FIXED | S01 r6 accepted a comment-shadowed Lake mapping and the full wrapper accepted successful non-parser executables | S01 r6 finding S01-R6-002 | Parse unique active Lake stanzas comment-aware and require the parser command's exact three stdout records and 16/52/68 counts |
| F-047 | LOW | FIXED | S01 r6 report rendered `extttmain` because a literal tab replaced the TeX command backslash | S01 r6 finding S01-R6-003 | Restore `\texttt{main}` and reject internal tabs across active scope with a focused mutation |
| F-048 | MEDIUM | FIXED | S01 r7 source and Lake checks treated unexpanded command quotations as active declarations/configuration | S01 r7 finding S01-R7-001 | Reject unsupported quotation/metaprogramming in the frozen source grammar and make Lake's re-elaborated disposable TOML the executable-root authority |
| F-049 | LOW | FIXED | S01 r7 command-substitution capture erased extra terminal blank lines before parser-output comparison | S01 r7 finding S01-R7-002 | Capture stdout in an ordinary temporary file and byte-compare it to the exact 154-byte three-record file while preserving status and stderr |
| F-050 | MEDIUM | FIXED | S01 r8 validated the executable root but not effective target/package source-directory selection, allowing alternate source bytes to emit accepted stdout | S01 r8 finding S01-R8-001 | Reject every package/target source/path selector, require Lake `-R -H -J query` structured traces to bind the exact pinned source through its export object to the resolved ordinary executable, then execute that exact binary |
| F-051 | MEDIUM | FIXED | S01 r9 compared executable trace and sidecar metadata without hashing the current executable bytes, so a changed ordinary binary could retain accepted behavior and metadata | S01 r9 finding S01-R9-001 | Compute the exact ordinary executable's current SHA-256, bind the exact path/hash through ordinary files, check before and after execution, and trace all three frozen parser/schema modules |
| F-052 | MEDIUM | FIXED | S01 r10 trusted a reusable root-package build whose source and trace records could be made internally consistent with an unrelated executable, while its Lake hash token was not a cryptographic content identity | S01 r10 finding S01-R10-001 | Build the parser in an initially absent private root with Lake reconfiguration, rehashing, and caches disabled; require all root artifacts there; SHA-256 the exact fresh binary before and after execution |
| F-053 | MEDIUM | FIXED | S01 r11 did not require current module outputs, generated C, export objects, or their sidecars to be ordinary files, so 18 simultaneous symlink substitutions passed the resolver | S01 r11 finding S01-R11-001 | Enforce the exact eight-path manifest for each of all three modules with descriptor-relative no-follow checks and bind each module/C/object sidecar to its trace token |
| F-054 | LOW | FIXED | S01 r11's lexical containment accepted a `..` path that hashed an ordinary sibling outside the supplied root | S01 r11 finding S01-R11-002 | Reject every non-canonical raw path and use a nonempty proper relative component list with descriptor-relative no-follow traversal from `/` |
| F-055 | LOW | FIXED | S01 r12 leaked a newly opened directory child when post-open `fstat` or identity validation failed before ownership transfer | S01 r12 finding S01-R12-001 | Own every opened child immediately, close it on all pre-transfer failures, and repeat exact root/relative identity and `fstat` failures while proving the process descriptor set is unchanged |
| F-056 | LOW | FIXED | S01 r12 active assurance prose double-counted the SHA CLI subset, added a nominal case, and retained stale focused totals | S01 r12 finding S01-R12-002 | Derive and observe one exact category mapping, exclude nominal success, state the SHA CLI subset once, and reject stale/double-counted active documentation |
| F-057 | LOW | FIXED | S01 r13 retained a parent descriptor when an unexpected pre-`fstat` hook exception bypassed typed outer cleanup | S01 r13 finding S01-R13-001 | Close every retained parent on all propagated exceptions without masking the original; repeat root/relative `RuntimeError` failures sixteen times with exact descriptor maps and a sentinel |
| F-058 | LOW | FIXED | S01 r13 restored the temporary Lake build-directory override only on explicit success, leaving failure and signal exits contaminated until later re-elaboration | S01 r13 finding S01-R13-002 | Arm restoration immediately before resolve and restore unconditionally from a status-preserving EXIT trap before deleting the temp root; test seven success/failure/signal paths |
| F-059 | LOW | FIXED | S01 r14 left direct and sequential close paths across the older active-tree walker and parser consumers, allowing close-after-release failure to mask an original exception, leak a later owner, or retry a reused fd | S01 r14 finding S01-R14-001 | Use one non-retrying owner helper for every production descriptor, preserve active exceptions, deterministically report nominal cleanup failure after all owners, and repeat thirteen bounded production families sixteen times with two sentinels and exact fd maps |
| F-060 | LOW | FIXED | Root's pre-review r15 audit found cleanup evidence dynamically invoked an active exception's overridable `add_note` and a cleanup exception's potentially hostile string conversion, which could mask the exact original | Root pre-review r15 hardening audit | Invoke `BaseException.add_note` explicitly, format cleanup evidence without dynamic exception display, and repeat hostile active/nominal cleanup families sixteen times with exact fd maps and two sentinels |
| F-061 | LOW | FIXED | S01 r15 still formatted a cleanup exception class `__name__`; a hostile nonempty `str` subclass masked both the active original and nominal deterministic failure | S01 r15 finding S01-R15-001 | Derive cleanup evidence only from fixed strings and builtin integer counts, retain the first cleanup object only as nominal cause, and repeat hostile active/nominal type-name and base-note families 32 times with exact descriptor maps and two sentinels |
| F-062 | LOW | FIXED | S01 r15's shallow AST gate accepted alias/import/getattr/discard/rebinding bypasses and runtime cleanup did not detect distinct live owners holding the same descriptor integer | S01 r15 finding S01-R15-002 | Preflight all owners, mark them unowned, close each unique integer once, reject nominal owner aliasing deterministically, and enforce an exact scoped AST inventory of descriptor references, owner retention, takes, cleanup consumers, and registered test aliases with 30 mutation regressions |
| F-063 | CRITICAL | FIXED | S02 r1 derived ITSR history from explicit adversarial Hmsg calls rather than honest signing requests | S02-R1-001; r4 replay | Signing entries supply `(R,request)` and explicit public Hmsg entries are excluded |
| F-064 | CRITICAL | FIXED | S02 r1 allowed arbitrary component scalars instead of the twelve named games | S02-R1-002; r4 source comparison | Compute every RHS term from a concrete source-shaped experiment |
| F-065 | CRITICAL | FIXED | S02 r1 disconnected target counts and component targets | S02-R1-003; r4 trace probes | Validate actual challenger-owned oracle traces against formula caps |
| F-066 | HIGH | FIXED | S02 r1 omitted the authoritative `lgw ∈ {2,4,8}` restriction | S02-R1-004; compiled `lgw_ne_one` | Require the exact approved disjunction in `ParameterConditions` |
| F-067 | CRITICAL | FIXED | S02 r2's ITSR summand used the original transcript rather than the standalone post-hop experiment | S02-R2-001; r4 source comparison | Use a dedicated default-oracle ITSR game with program-owned setup |
| F-068 | CRITICAL | FIXED | S02 r2's SPprob did not run the same DSPR program and selected index | S02-R2-002; r4 counterexample replay | Independently run the same two-phase program in both experiments |
| F-069 | CRITICAL | FIXED | S02 r2's WOTS UD game exposed preimages and omitted the sourced validity event | S02-R2-003; r4 source comparison | Sample fresh hidden real inputs or ideal outputs and check the actual trace |
| F-070 | HIGH | FIXED | S02 r2's provider certificate admitted role substitution and vacuous separation | S02-R2-004; r4 role-card probes | Use eight distinct target roles and same-execution target/collection logs |
| F-071 | CRITICAL | FIXED | S02 r3's exact honest-target provider was uninhabitable for a valid no-query adversary | S02-R3-001; r4 zero-trace probe | Remove the impossible provider; empty component traces are ordinary and selected-target events fail |
| F-072 | CRITICAL | FIXED | S02 r3 modeled TCR/DSPR/SPprob/PRE as post-hoc events rather than named oracle games | S02-R3-002; r4 source comparison | Use stateful two-phase target-oracle programs |
| F-073 | CRITICAL | FIXED | S02 r3 used the wrong UD input distribution and an unrelated collection execution | S02-R3-003; r4 source comparison | Sample fresh hidden inputs and share one target/collection program log |
| F-074 | CRITICAL | FIXED | S02 r3 injected a real full-SLH key into the post-SKG/post-MKG ITSR world | S02-R3-004; r4 source comparison | Put NPRF/hybrid setup in the reduction program and expose only public Hmsg parameters |
| F-075 | CRITICAL | REMEDIATED-PENDING-REVIEW | S02 added eight compiler-generated partial helpers outside the exact policy allowlist | S02-R5-001; compiled policy audit | Rewrite projections with total library combinators and replay the compiled audit |
| F-076 | CRITICAL | REMEDIATED-PENDING-REVIEW | S02 acceptance edits were not reviewed and the manifest demanded an impossible self-revision pin | S02-R5-002; S02-R6-004 | Require the exact session-linked repair input plus active-source hash; review the complete repaired tree |
| F-077 | HIGH | REMEDIATED-PENDING-REVIEW | The source-tree composite omitted all four S02 modules | S02-R5-003; S02-R6-003 | Include `Security/*.lean`; gate exact command/glob correspondence and a Security-byte mutation |
| F-078 | HIGH | REMEDIATED-PENDING-REVIEW | S02 omitted mandatory matrix, inventory, findings, decisions, TCB, and report traceability | S02-R5-004; S02-R6-005 | Synchronize every contract surface and correct dependency/span/scope facts |
| F-079 | CRITICAL | OPEN | The generic master LHS called the known `d = 1` transitional scheme, while its replacement has no general-construction coupling witness | S02-R5-005; S02-R6-001 | Retain the arbitrary experiment interface but construct and review an S08/S09 refinement witness coupling keygen/sign/verify/signature R/digest |
| F-080 | HIGH | OPEN | Standalone source-shaped component games contradict the earlier transcript-derived-target contract and have no named decision approval | S02-R5-006; S02-R6-002 | Keep D-009 proposed and PO-008 provisional until named owner approval or rejection |
| F-081 | CRITICAL | REMEDIATED-PENDING-REVIEW | S02 claimed a bare scheme function bundle established general-construction coupling | S02-R6-001 | Classify it as an arbitrary signature-scheme experiment boundary and leave F-079/PO-003 open |
| F-082 | HIGH | REMEDIATED-PENDING-REVIEW | Authoritative prose and obligations treated proposed D-006/D-009 as accepted or superseding | S02-R6-002 | Retain proposed status and keep PO-006/PO-008 provisional without accepted-selection language |
| F-083 | HIGH | REMEDIATED-PENDING-REVIEW | Source-composite commands omitted Security and no focused mutation proved its coverage | S02-R6-003 | Gate the exact four-glob commands and reject a controlled Security-source byte mutation |
| F-084 | HIGH | REMEDIATED-PENDING-REVIEW | Repository revision validation accepted any ancestor and mislabeled the invalidated repair base | S02-R6-004 | Require the exact session-linked repair-base field and correct its ledger meaning |
| F-085 | HIGH | REMEDIATED-PENDING-REVIEW | Declaration dependencies/spans and S02 harness-edit scope prose were false | S02-R6-005 | Correct exact dependencies/full spans and describe the narrow harness repair accurately |
| F-086 | HIGH | REMEDIATED-PENDING-REVIEW | The retained S03 bootstrap named no current accepted predecessor and could route work to invalidated commit `7b77e700` | S02-R7-001 | State that no accepted predecessor exists until r8 PASS and bind S03 only to that exact accepted repair commit |

Independent S00 re-review r9 accepted the repairs for F-021 through F-029. Their `FIXED` statuses
administratively propagate that verdict; they are not an S01 self-review. Historical FAIL artifacts
remain immutable. Finding statuses are `OPEN`, `BLOCKED`, `FIXED`, `ACCEPTED-RISK`,
`REJECTED-WITH-EVIDENCE`, `DUPLICATE`, `VALIDATED-REPORT-ERROR`, or
`REMEDIATED-PENDING-REVIEW`. Report errors remain visible after canonical prose is corrected.

Independent S01 review r0 failed with F-030 through F-033. The r1 repair records them as
`REMEDIATED-PENDING-REVIEW`, not fixed. Independent r1 also failed, adding F-034/F-035. Repair r2
records both new findings as `REMEDIATED-PENDING-REVIEW`. Independent r2 failed with F-036/F-037;
repair r3 records them as `REMEDIATED-PENDING-REVIEW`. Independent r3 failed with F-038/F-039/F-040;
repair r4 records them as `REMEDIATED-PENDING-REVIEW`. Independent r4 failed with F-041/F-042/F-043;
repair r5 records them as `REMEDIATED-PENDING-REVIEW`. Independent r5 accepted the parser boundary
repair but failed with F-044; repair r6 records that inventory defect as
`REMEDIATED-PENDING-REVIEW`. Independent r6 confirmed the corrected call graph but failed with
F-045/F-046/F-047; repair r7 records all three as `REMEDIATED-PENDING-REVIEW`. Independent r7
confirmed the current call graph and report repair but failed with F-048/F-049; repair r8 records
both as `REMEDIATED-PENDING-REVIEW`. Independent r8 confirmed those exact repairs but failed with
F-050; repair r9 records the source-selection/build-input defect as
`REMEDIATED-PENDING-REVIEW`. Independent r9 confirmed that repair but failed with F-051; repair r10
records current executable-byte validation as `REMEDIATED-PENDING-REVIEW`. Independent r10 confirmed
that current-byte and three-module checking but failed with F-052; repair r11 records the private
fresh-build and SHA-256 boundary as `REMEDIATED-PENDING-REVIEW`. Independent r11 confirmed the core
fresh-build repair but failed with F-053/F-054; repair r12 records exact current-artifact and
canonical descriptor-relative path enforcement as `REMEDIATED-PENDING-REVIEW`. Independent r12
confirmed those repairs but failed with F-055/F-056; repair r13 records immediate child ownership
and mechanically reconciled focused accounting as `REMEDIATED-PENDING-REVIEW`. Independent r13
confirmed those two repairs but failed with F-057/F-058; repair r14 records all-exception retained-
parent cleanup and unconditional status-preserving Lake-override restoration as
`REMEDIATED-PENDING-REVIEW`. Independent r14 confirmed those narrow repairs but failed with F-059;
repair r15 records the bounded production descriptor inventory as `REMEDIATED-PENDING-REVIEW`.
Root's pre-review r15 audit then found F-060; the same repair iteration hardens note recording and
cleanup evidence before independent review. Independent r15 failed with F-061/F-062; repair r16
records constant/count-only evidence, runtime duplicate-owner preflight, and the exact scoped AST
lifecycle policy as `REMEDIATED-PENDING-REVIEW` at handoff. Independent r16 then passed with no
blocking findings. The `FIXED` statuses for F-030--F-062 administratively propagate that verdict;
they are not S01 self-review. S01 is accepted and S02 is eligible. The accepted descriptor/AST
machinery is frozen and is not ratcheted in successor sessions absent a concrete regression.

Independent S02 reviews r1, r2, and r3 failed and remain immutable. Independent r4 passed with zero
findings, but the complete independent r5 audit invalidated that acceptance with F-075 through
F-080. Independent r6 then failed with F-081 through F-085. The second repair keeps underlying
construction coupling F-079 and the unapproved target-contract choice F-080 open, while recording
the five r6 defects and the other r5 repairs as `REMEDIATED-PENDING-REVIEW`. Independent r7
confirmed those repairs and every technical gate but failed with F-086. The routing repair records
F-086 as `REMEDIATED-PENDING-REVIEW`; no accepted S03 predecessor exists until r8 accepts the exact
repair commit. R4 did close the twelve earlier S02 findings F-063 through F-074, whose
`FIXED` statuses preserve that reviewed disposition. None of this globally closes F-001 through
F-009: the legacy theorem remains rejected, concrete reductions/composition remain future work, and
the QROM/asymptotic boundaries remain open.
