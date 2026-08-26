# Sessionized implementation plan

## Universal session contract

Every session starts from an accepted predecessor and its pinned inputs. It may change only its
listed components plus this harness. It must update coverage, obligations, assumptions, TCB,
declaration inventory, findings, decisions, report traceability, and a session record. Its commands
must pass at runtime where execution is claimed and at elaboration where proofs are claimed.

The implementer does not write the independent review. A fresh reviewer writes the named
`reviews/Sxx-*.md`, checks source correspondence and `#print axioms` for changed load-bearing roots,
and records PASS or FAIL. Any issue means FAIL; the implementation session reopens, disposes every
finding with evidence, reruns all gates, and receives another independent review. No successor starts
until PASS. Review history is append-only; a re-review never overwrites the failed record.

## Sessions

### S00 — baseline and harness

- Inputs: prompt; AGENTS/CONTRIBUTING; VCV commit `f1853af...`; local reports and pinned sources.
- Allowed: `docs/slhdsa/**`, `scripts/slhdsa/**`; no formalization/library Lean source. Validation-only
  Lean scripts may live under `scripts/slhdsa/**` and must not add declarations to `HashSig` modules.
- Deliverables: this complete harness, initialized matrices/report, reproducible baseline, corrected
  findings and authority rules.
- Gates: `./scripts/slhdsa/validate.sh --docs-only`; TeX build; review artifact
  `reviews/S00-adversarial-review.md`.

### S01 — authority and pinned conformance anchors

- Inputs: accepted S00; FIPS 205; current ACVP protocol/server; public NIST sample JSON artifacts.
- Allowed: source ledger, vector provenance/fixtures under `HashSigTest/SLHDSA/**`, parser/test support;
  the minimal `lakefile.lean` parser-executable target; no construction or security statements.
- Deliverables: immutable copies or hashes, exact 12-set parameter/API tables, pinned `FIPS205`
  protocol-schema/current v1.1.0.43 sample artifacts (with v1.1.0.38 only as the compatibility
  boundary),
  schema, positive-cell coverage for issue #469, vector license/provenance.
- Gates: parser negative tests; provenance hash check; `lake build HashSigTest`; docs validator;
  independently accepted re-review `reviews/S01-authority-and-conformance-review-r16.md` after immutable
  r0/r1/r2/r3/r4/r5/r6/r7/r8/r9/r10/r11/r12/r13/r14/r15 FAILs. Repair r16 retains the initially absent private
  no-cache build, requires the exact 24-file current manifest for all three parser modules, and binds
  the module/C/export-object sidecars to their structured trace tokens. All accepted file operations
  use canonical absolute spellings and descriptor-relative no-follow traversal from `/`; sibling,
  nested-parent, and symlink aliases reject. Every opened directory child is immediately owned and
  closed through one non-retrying owner discipline on every propagated exception and nominal
  cleanup failure across both walkers and all descriptor consumers. F-061/F-062 remove dynamic
  exception-derived evidence, preflight distinct owners that alias one descriptor integer, and
  exact-register scoped acquisitions, closes, owner retention, `take` transfers, cleanup consumers,
  and test-only real-close/real-dup calls. The deliberately narrow AST policy bans the enumerated
  import/assignment/`getattr`/dynamic alias forms; it is not a claim about arbitrary Python
  reflection. Its EXIT cleanup restores the Lake build-dir
  override before temp deletion on ordinary shell exits and handled signals (not SIGKILL). The
  sequential gate assumes no concurrent writer. Independent r16 accepted S01. S02 r4 initially
  passed, but the complete r5 audit reopened S02 and r6 found five residual blockers. R7 confirmed
  those repairs but found stale successor routing; independent r8 then passed with zero findings
  and accepted exact S02 commit `a80e4d336276cd86fb80be64e82d9d57e7dfc8b3`.
  The descriptor/AST policy is frozen and is not extended in later sessions absent a concrete
  regression; successor work centers on Lean deliverables.

focused-parser-partition: legacy=8; source-object-link=21; imports=4; sha-output-binding=9; path-cli=20; output-types=2; artifacts=130; wrong-srcdir=2; stale=2; fresh-root=5; query-output=5; replacement-cache=3; descriptor-lifecycle=6; descriptor-ownership=17; total=234; sha-cli-is-subset-of-path-cli=6; nominal-success-excluded=true

### S02 — theorem, oracle, and security architecture (reopened after independent r5 FAIL)

- Inputs: S01; CCS 2019 historical Theorem 17 statement/games; the HK22 repaired WOTS-TW proof;
  tight EasyCrypt declarations; VCVio query/transcript APIs.
- Allowed: design docs and new isolated `HashSig/SLHDSA/Security/{Notions,OracleSurface,
  Transcript,Architecture}.lean`; no component refactor or claimed reduction.
- Deliverables: proposed repaired master theorem with exact quantifiers/coefficients and an explicit
  account of why the invalidated CCS WOTS proof is not reused; generated `PK.seed`
  coupling; an abstract signature-scheme experiment interface, with general construction coupling
  explicitly left to S08/S09; strictly positive formula-derived caps
  on standalone source-shaped component-game target traces;
  actual `qS/qH` predicates; ITSR/digest mapping; `F/H/T_l/Hmsg/PRF/PRFmsg` surfaces; explicit
  classical/QROM boundary. Remove the invented loss from the target architecture.
- Gates: counterexample tests for zero-target/unbounded-loss/arbitrary-sampler loopholes; `lake build
  HashSig`; `#print axioms` on notions; review `reviews/S02-security-architecture-review.md`.

Review state: r1/r2/r3 failed and remain immutable; r4 passed but did not run the full compiled and
traceability gates. Independent r5 failed with six blockers and r6 failed with five residual
claim/provenance/traceability blockers. R7 confirmed all five repairs but failed on the retained
S03 record's stale predecessor routing. Independent r8 accepted the exact routing-repaired commit
with zero findings. D-006/D-009 remain proposals and do not discharge their dependent obligations
without named owner approval.

### S03 — data, widths, parameters, ADRS, and codecs (initial review FAIL; repairs pending r1)

- Inputs: S01 tables and FIPS Sections 3–5/11; accepted S02 interfaces.
- Allowed: `Params`, `Address`, `Encoding`, new byte/codec modules and focused tests.
- Deliverables: valid parameter type, all 12 sets, width/range laws, exact ADRS operations,
  `base_2b` big-endian characterization, rejecting codecs.
- Gates: `lake build HashSig`; all-set `#eval` sizes; codec/property tests; ACVP fixtures. Initial
  exact-commit review failed with five blockers; after repair gates, fresh independent review r1 is
  recorded in `reviews/S03-data-codec-review-r1.md`.

### S04 — primitive interfaces and SHA2/SHAKE instantiations (bootstrap only; blocked on S03 r1)

- Inputs: S03; FIPS Section 11; pinned hash standards/vectors.
- Allowed: `Primitives`, `Concrete/Sha2`, `Concrete/Keccak` or new SHAKE/concrete modules.
- Deliverables: width-indexed primitives, `yToBytes` coherence, SHA2/SHAKE definitions for all sets,
  hash/MGF/HMAC/XOF vector evidence.
- Gates: runtime primitive vectors plus elaboration; no unreviewed extern; review
  `reviews/S04-primitives-review.md`.

### S05 — WOTS+ construction

- Inputs: S03–S04; FIPS Section 6.
- Allowed: WOTS/checksum modules and tests; no security reduction.
- Deliverables: exact algorithms, including the Appendix-A checksum-shift correction (with a
  non-`lgw=4` discriminating test), chain/address invariants, executable
  recovery correctness for approved sets.
- Gates: component vectors/properties; `#print axioms` on WOTS correctness; review
  `reviews/S05-wots-construction-review.md`.

### S06 — Merkle and XMSS construction

- Inputs: S03–S05; FIPS Section 7; generic Merkle theory.
- Allowed: Merkle/XMSS modules and adapters; no reduction.
- Deliverables: bounded nodes/paths, exact address evolution, sign/recovery correctness, reviewed
  adapter to generic Merkle semantics.
- Gates: exhaustive tiny trees, runtime vectors, axioms on roots; review
  `reviews/S06-xmss-construction-review.md`.

### S07 — FORS construction

- Inputs: S03–S06; FIPS Section 8 and Appendix-A extraction delta.
- Allowed: FORS modules/tests; no reduction.
- Deliverables: FIPS big-endian indices, valid trees/paths, sign/recovery correctness, separate
  fixtures for Appendix A's reference-alignment and per-tree-index clarification, and an explicit
  incompatibility test against round-3 LSB-first behavior.
- Gates: extraction fixtures, tiny exhaustive tests, axioms; review
  `reviews/S07-fors-construction-review.md`.

### S08 — general hypertree construction

- Inputs: S03–S07; FIPS Section 9; C13 `d=2` only as a non-normative design comparison.
- Allowed: main hypertree and digest-split internals.
- Deliverables: general `d` fold, exactly `d` signatures, tree/leaf index evolution, correctness for
  every FIPS set; no C13 merge.
- Gates: `d=1/2/>2` tests, all-set execution, axioms; review
  `reviews/S08-hypertree-review.md`.

### S09 — internal and external FIPS APIs

- Inputs: S03–S08; FIPS Sections 9–10.
- Allowed: Scheme, pure/pre-hash API, signature/key codecs.
- Deliverables: internal algorithms, pure/HashSLH-DSA domain separation, context/OID rules,
  deterministic/hedged modes, completeness and reject behavior.
- Gates: positive/negative API tests; all-set execution; zero `sorryAx` on completeness roots;
  review `reviews/S09-api-review.md`.

### S10 — ACVP conformance evidence

- Inputs: S01 fixtures and S09 executable APIs.
- Allowed: test/vector runners and coverage docs; no spec changes except reviewed defect fixes.
- Deliverables: keyGen/sigGen/sigVer results for supported cells; separate internal/external and
  pure/pre-hash reporting; issue #469 uncovered cells remain explicit.
- Gates: runtime ACVP suite and provenance check; review `reviews/S10-acvp-review.md`.

### S11 — security notions and finite quantitative statements

- Inputs: accepted S02 architecture and S09 scheme; historical CCS games plus repaired
  HK22/EasyCrypt primary declarations.
- Allowed: `Security/Notions`, PRF/tweakable-hash/ITSR games; no component reductions.
- Deliverables: precise games, distinct-tweak advice, freshness, positive targets, finite losses,
  exact theorem statement candidates with all side conditions.
- Gates: vacuity/adversarial model tests; quantitative `#eval`; axioms; review
  `reviews/S11-security-notions-review.md`.

### S12 — instrumentation, query bounds, and transcripts

- Inputs: S11; VCVio QueryTracking/SimSemantics.
- Allowed: security oracle/transcript/instrumentation modules.
- Deliverables: enforced `qS/qH` predicates, query mapping/cost proofs, transcript projections,
  honest target distributions and generated-seed coupling.
- Gates: enforcement transparency/count tests, runtime trace examples, axioms; review
  `reviews/S12-instrumentation-review.md`.

### S13 — WOTS security reduction

- Inputs: S05, S11–S12; selected primary WOTS-TW proof.
- Allowed: `Security/WOTS` and generic adapters only.
- Deliverables: WOTS forgery-to-selected-notion reduction with exact target/query transformation;
  incomparability linked to executable digits.
- Gates: theorem elaboration, quantitative evaluation, axioms, no new sorry; review
  `reviews/S13-wots-security-review.md`.

### S14 — FORS security reduction

- Inputs: S07, S11–S13; ITSR and primary FORS proof.
- Allowed: `Security/FORS`.
- Deliverables: few-time reduction, ITSR bad-event bridge, F/T_l tree targets and coefficients.
- Gates: same security gates; review `reviews/S14-fors-security-review.md`.

### S15 — XMSS/hypertree security reduction

- Inputs: S06/S08, S11–S12; Merkle adapter and primary XMSS-MT proof.
- Allowed: `Security/XMSS`, `Security/Hypertree`.
- Deliverables: extraction/collision reduction across `d` layers with exact addresses/counts.
- Gates: same security gates; review `reviews/S15-xmss-security-review.md`.

### S16 — top-level composition

- Inputs: S13–S15 and PRF/ITSR hops.
- Allowed: `Security/Composition` and master statement.
- Deliverables: sorry-free finite EUF-CMA composition, exact coefficients and reductions; current
  Security placeholder removed only when the new root passes.
- Gates: full build/tests; zero `sorryAx` on all load-bearing roots; `#print axioms`; review
  `reviews/S16-composition-review.md`.

### S17 — asymptotics and classical/QROM accounting

- Inputs: S16 finite theorem; VCVio asymptotic layer; selected quantum semantics.
- Allowed: `Security/Asymptotics`, quantitative reports.
- Deliverables: parameter-family/negligibility theorem; polynomial time/query hypotheses; concrete
  12-set evaluation; separate classical and QROM claims. If no quantum semantics exists, QROM remains
  a labeled external-assumption statement, not a mechanized claim.
- Gates: finite expression runtime and asymptotic elaboration; axioms; review
  `reviews/S17-asymptotics-review.md`.

### S18 — explicit C13 disposition

- Inputs: accepted normative/security architecture; pinned C13 design/deployment sources.
- Allowed: decision docs and C13 only after decision acceptance.
- Deliverables: choose `separate-supported`, `merge-reusable-core`, or `deprecate`; define C13 spec,
  security, vector, grinding, and compatibility obligations; never call it FIPS 205.
- Gates: decision evidence and affected tests; review `reviews/S18-c13-decision-review.md`.

### S19 — deployment and refinement

- Inputs: owner-pinned Ethereum verifier repository/commit/ABI and accepted construction.
- Allowed: new refinement/interop/test modules and deployment docs. **Blocked until target exists.**
- Deliverables: byte/ABI refinement theorem, toolchain/TCB account, error/word/endian/gas boundaries,
  differential evidence. RISC-V/Sail applies only if explicitly selected here.
- Gates: target build/differential tests, refinement root axioms, review
  `reviews/S19-deployment-review.md`.

### S20 — final expert report and release audit

- Inputs: every accepted session and review; no unresolved critical/high finding.
- Allowed: report/harness and defect fixes routed back to owning sessions.
- Deliverables: compiled report, declaration/coverage/TCB appendices, reproducibility package,
  achievements/limitations, precise master-theorem and deployment boundaries.
- Gates: full validation and clean rebuild; report compile; independent whole-project review
  `reviews/S20-final-audit.md`. A final-audit finding reopens the owning session and S20 is re-reviewed.
