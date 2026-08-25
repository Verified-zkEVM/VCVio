# S01 adversarial re-review r9 — effective source and build-input binding

Verdict: **FAIL**

Reviewer: fresh independent S01 r9 software-quality reviewer; not an S01 implementer or a prior
S01 reviewer

Reviewed tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r9 tree

Date: 2026-08-24

Independence statement: I did not design or implement S01 or its r9 repair. The implementation and
administrative state remained frozen during review. Disposable build/configuration checks were
confined to `/tmp`. This review artifact is my only repository edit. I made no commit or PR.

## Verdict summary

R9 materially improves the r8 repair. The configuration checks reject the tested executable- and
package-level source-directory redirects, argument-based source selectors, aliases, and the prior
wrong-root project. The structured build records identify the canonical ParserTests source, its
generated C output, its export object, and the expected executable link input. The queried path is
also restricted to the expected ordinary worktree executable.

One build-integrity defect remains. The production check compares the executable trace's output
token with the adjacent executable `.hash` file, but does not calculate the current executable
file's hash. An independent disposable-project check replaced the executable with a different
ordinary executable after the build metadata had been produced. Lake's reconfigure/rehash query
reused the recorded state and did not restore the expected executable bytes. The production trace
validation still accepted the unchanged trace and adjacent hash metadata. The exact runtime-output
gate can confirm the replacement program's three expected records, but it cannot justify the
stronger claim that the current executable bytes are the build output described by the trace.

This is finding S01-R9-001, severity MEDIUM. The acceptance threshold is zero findings, so S01 r9
fails. S01 remains blocked and S02 must not start.

## Frozen state and immutable history

Before reviewer authorship, the live state was:

- branch `codex/sphincsplus-formalization`;
- HEAD `f1853af40da1efa11a71c2d7011996eebdbf6938`;
- one tracked `lakefile.lean` modification and untracked S01 content under
  `HashSigTest/SLHDSA/ACVP/`, `docs/slhdsa/`, and `scripts/slhdsa/`;
- no recorded `HashSig/**` construction/security change and no S02 implementation work;
- no commit or PR.

The r9 checklist initially measured 10,309 bytes and 162 lines, had SHA-256
`629d1b6360ab694f9cd73278ad45c7d8d8dfaa4e7ee4373baf663927385649f3`, and contained exactly one
canonical pending verdict. The immutable S01 review chain reproduced with exactly one canonical
`FAIL` in every artifact:

| Review | Bytes | Lines | SHA-256 |
|---|---:|---:|---|
| r0 | 18,990 | 354 | `ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76` |
| r1 | 16,956 | 296 | `9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec` |
| r2 | 24,924 | 513 | `3a8e5afe4d1b17c0b29febd18f993442f41e4f3137a994badce7d54946420ad8` |
| r3 | 16,809 | 335 | `bb84cb7380c9a5a1aa0c78018898389a7d1ac436dfa39caa987f170670542662` |
| r4 | 14,465 | 250 | `3a334dfe161d1475a48e44385fdd114615897d8416bf8026d15dcc2dddaa3c89` |
| r5 | 32,298 | 559 | `03ae3b07aee41ddf90a30ee42edd388b2c3921c42f8a27807180262b4397ca97` |
| r6 | 22,677 | 429 | `8f4f477ce19484a20bf1af6af4acce2bb10707bbab9c88e803593ef6ff797d22` |
| r7 | 23,261 | 413 | `fd8f9483e973ebca7388080e9218aa3c9b9d5857722a60bc42e5458de89941aa` |
| r8 | 13,492 | 220 | `a09fc3b7fffacb2e83f69f968c5b2c4ba81b91cee3258e5848fea1734735dd9d` |

The frozen ACVP Lean source pins also reproduced:

| Source | Bytes | Lines | SHA-256 |
|---|---:|---:|---|
| `StrictJson.lean` | 2,849 | 114 | `20f9aff3f5339e54d7fc5e148fadb0e37d8f4b4bd816938f0a81b4cf7b087089` |
| `Schema.lean` | 18,619 | 417 | `3ccab70a3ff8e2e6f39cc09e4b2296fad035267b4def0e6c8bb002062f5733a0` |
| `ParserTests.lean` | 12,290 | 205 | `1a56fd4fef9880a464583749d27e14840b2f48afc81fe007db473bb167585cd5` |

The eight current matrix files were enumerated and hashed without changing them. The prior review
artifacts r0 through r8 were not edited.

## Effective configuration and structured-build review

The live Lake configuration re-elaborated to an ordinary disposable TOML file. Its HashSigTest
library record retains the expected `HashSigTest.+` module glob, and its unique parser executable
record retains only the expected name and root. The production checks reject package-level
`srcDir`, `moreLeanArgs`, and `weakLeanArgs` fields, reject extra parser-target fields, and reject
the tested literal or translated aliases and source-directory overrides.

The production resolver ran Lake's reconfigure/rehash JSON query and returned the exact absolute
worktree executable path. Current records use the expected non-synthetic Lake schema. For
ParserTests, the module record names the exact canonical source path and module identity. The
structured edges then connect ParserTests generated C to its export object and that export object
to one entry in the executable's `linkObjs` input. The current source hash agrees with the frozen
SHA-256 above.

The resolver's built-in mutation group passed: malformed or duplicate JSON, wrong/missing/
duplicated ParserTests source entries, synthetic module data, wrong executable path, linked or
special output entries, both prior WrongSrc cases, and stale source-selection transitions were
reported rejected. These checks demonstrate useful source and configuration binding, but they do
not validate the final executable file's current contents.

## Executable-content reproduction

The production logic was inspected at the point where it completes the structured chain. It
requires the executable path, trace, adjacent `.hash`, ParserTests module trace, and ParserTests
export-object trace to be ordinary files. It then validates structured metadata and requires the
text in the adjacent `.hash` file to equal the executable trace's `outputs` token. No step reads the
executable and derives its authoritative Lake file hash for comparison with either value.

The independent reproduction used an ordinary disposable Lake project and ordinary file
replacement. A normal build first produced an executable, trace, and adjacent hash file. The
executable file was then replaced while the trace and adjacent hash file were left intact. The same
reconfigure/rehash query used by production returned the expected path without restoring the
original executable bytes. Production-equivalent structured validation accepted the unchanged
metadata. Direct byte measurement distinguished the current executable from the build output
described by that metadata.

This result also explains why the exact 154-byte stdout gate is not an executable-content check.
That gate correctly detects output differences, extra records, missing records, terminal blank
lines, and nonzero status. A different ordinary program that emits the same three records can
still satisfy it. The report therefore may claim exact runtime output, but may not claim that the
current executable bytes are exactly the output authenticated by the structured build chain.

## Imported-module provenance observation

ParserTests imports Schema, which imports StrictJson. Their live module traces are current and
non-synthetic, and each independently records its canonical source path and module identity. The
executable trace's `linkObjs` group contains separate export objects for ParserTests, Schema, and
StrictJson.

The r9 validator reads and follows only the ParserTests module and export-object traces. It does not
read the Schema or StrictJson module/export-object traces, does not compare their source paths and
bytes with the frozen source pins, and does not follow their object hashes into the executable.
Accordingly, the structured-trace claim should be described as direct ParserTests binding rather
than a complete transitive imported-source proof.

An independent disposable configuration attempted to leave the root ParserTests source exact while
selecting alternate imported Schema/StrictJson sources through library/source-directory settings.
The existing Lake selector controls rejected that configuration. No accepted alternate-import
case was reproduced through the current combined checks, so this observation is not assigned a
separate finding. It remains useful scope information for the repair: extending trace validation to
the two imported modules would make the evidence match the stronger transitive provenance wording.

## Prior-repair and gate status

The following independent checks completed in this r9 review:

- governing prompt, repository instructions, S01 session/current records, and immutable S01 r0--r8
  review history were inspected;
- branch, HEAD, working-tree shape, prior-review hashes/sizes/line counts, one-verdict invariants,
  frozen source pins, and matrix hashes were recomputed;
- the live translated Lake configuration and HashSigTest/parser target records were inspected;
- the production reconfigure/rehash resolver and its focused structured-build mutation group ran;
- live ParserTests, Schema, and StrictJson module traces and the executable `linkObjs` group were
  inspected;
- the executable-content replacement case was reproduced in a disposable project;
- the alternate imported-source configuration was tested and rejected by existing selector
  controls.

The following heavy or broad gates were not independently completed in this r9 review after the
blocking finding was confirmed:

- the complete focused harness normal mode and real-sibling docs-only suite;
- offline and optional checkout-backed ACVP provenance regeneration;
- direct production parser runtime and the complete 154-byte mutation corpus;
- full `lake build HashSigTest` and the inventory-driven external dependency probe;
- explicit `update-lib.sh`;
- complete full `validate.sh`;
- independent Python/Bash/JSON/JSONL syntax, comprehensive active-scope hygiene, generated-debris,
  and final diff checks;
- TeX compilation and PDF-text inspection.

Those gates have implementer-recorded passing evidence in the frozen S01 session, and prior r7/r8
reviews independently reproduced many predecessor surfaces. They are not reported here as fresh r9
reviewer passes. Their omission does not weaken the verdict because the confirmed finding already
violates the zero-finding acceptance rule.

Administrative inspection retained F-050 as remediated pending review rather than accepted,
F-044 through F-049 pending S01 acceptance, F-015/F-016 and F-018 open, COV-005 missing/S10/pending,
and S02 blocked. No construction, implementation-conformance, certificate, or security claim was
accepted by this review.

## Finding

### S01-R9-001 — MEDIUM — current executable bytes are not validated against the accepted build metadata

#### Reproducible QA evidence

The production checker establishes equality between two metadata values: the executable trace's
output token and the adjacent `.hash` file's text. It does not calculate the current executable's
Lake file hash. In a disposable project, replacing only the ordinary executable left both metadata
values unchanged. Lake's reconfigure/rehash query reused that state and returned the expected path
without restoring the expected executable. The production-equivalent trace check therefore
accepted metadata describing bytes that were no longer present at that path.

#### Impact

The gate does not establish the claimed exact-binary binding at the time of execution. It binds the
canonical ParserTests build inputs to recorded link metadata and separately checks behavior through
exact stdout, but a current ordinary executable with different bytes can sit between those two
checks and be accepted when it produces the expected records. This is a test/build-integrity defect;
it does not change HashSig construction or security declarations.

#### Requested repair

Fail closed by verifying the actual executable bytes with Lake's authoritative file-hash algorithm
and comparing that value with the structured trace and adjacent hash metadata. If that algorithm
cannot be invoked reliably, produce and run the parser executable in a fresh isolated output
location whose contents and metadata are checked immediately before and after execution. Retain
ordinary-file and no-symlink checks, exact path capture, exact 154-byte stdout comparison, visible
stderr, and authoritative exit status.

Add a regression that performs ordinary executable replacement after valid metadata exists, reruns
the same reconfigure/rehash query, and requires rejection before execution. The regression should
also distinguish file-content verification from metadata-to-metadata equality and should verify
that a replacement emitting the expected records is still rejected.

For completeness, extend the structured chain to Schema and StrictJson or narrow the public claim
to direct ParserTests-source binding. This imported-module hardening is requested as evidence-scope
alignment, not as a second finding, because the tested alternate imported-source configuration was
already rejected by current selector checks.

## Verdict rationale

R9 closes the two exact r8 source-directory cases at both configuration and direct ParserTests
trace levels, and its query/path/trace controls are materially stronger than r8. The attempted
alternate Schema/StrictJson source selection did not pass the existing selector controls.

However, the final executable-content claim is not supported: the checker compares adjacent
metadata with trace metadata without validating the current executable bytes, and the independent
disposable reproduction confirmed that Lake's query can reuse that state after ordinary file
replacement. Exact stdout is a separate behavioral check and does not establish byte identity.

Under the mandatory zero-finding threshold, S01 r9 **FAILS** independent review. F-050 remains
pending, S01 remains blocked, and S02 must not start. No implementation repair, administrative
promotion, commit, or PR was made.
