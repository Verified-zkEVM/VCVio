# S01 independent re-review r10 — current executable and imported-source chain

Verdict: **FAIL**

Reviewer: fresh independent S01 r10 software-QA reviewer; not an S01 implementer or any prior
S01 reviewer

Reviewed tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r10 tree

Date: 2026-08-24

Independence statement: I did not design or implement S01 or its r10 repair, and I did not conduct
r0 through r9. The implementation and administrative state remained frozen during review.
Disposable build checks were confined to `/tmp`. This review artifact is my only repository edit.
I made no commit or PR.

## Verdict summary

R10 correctly computes Lake's current file hash rather than trusting the adjacent `.hash` file,
checks that value before and after exact-path execution, retains byte-exact stdout and process
status, and extends the structured records to ParserTests, Schema, and StrictJson. The helper
script's source, CLI, output record, and current-file behavior passed direct inspection and tests.
The focused 55-case suite also passed as implemented.

One build-integrity defect remains. Lake's query accepts an internally consistent cached record in
which the executable trace's output token and adjacent sidecar have both been updated to the hash of
different current executable contents while all expected source, generated-C, export-object, link,
and import fields remain unchanged. The production resolver then accepts the unrelated current
executable as if those retained structured fields described its build. This was reproduced in an
exact three-module disposable project with the production validator.

Lake's content token is also only a 16-hex `UInt64` value produced with Lean's built-in hash. The
installed Lake source explicitly records that a secure hash should replace it. It is useful for
ordinary incremental-build freshness, but it cannot support strong byte-identity
wording. Current controls therefore establish the current 64-bit token and exact runtime output,
not that the executable was produced from the pinned inputs.

This is S01-R10-001, severity MEDIUM. The mandatory threshold is zero findings, so S01 r10 fails.
F-044 through F-051 remain pending, S01 remains blocked, and S02 must not start.

## Frozen state and immutable history

Before reviewer authorship, the live state was:

- branch `codex/sphincsplus-formalization`;
- HEAD `f1853af40da1efa11a71c2d7011996eebdbf6938`;
- one tracked `lakefile.lean` modification and untracked S01 content only below
  `HashSigTest/SLHDSA/ACVP/`, `docs/slhdsa/`, and `scripts/slhdsa/`;
- no `HashSig/**` source change and no S02 implementation;
- no commit or PR.

The r10 handoff initially measured 7,585 bytes and 124 lines, had SHA-256
`f3ed05df575faa3d9ca71734a1bfa6465d60e0e74c4a665be7bc84c1316522f8`, and contained exactly one
canonical `PENDING` verdict. Every predecessor remained byte-identical with one canonical `FAIL`:

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
| r9 | 14,161 | 231 | `52db8de84cf122c066fa4dd2928dd4d93c99f45754d95681cbfe7ed2610759fa` |

The three frozen ACVP Lean sources also reproduced:

| Source | Bytes | Lines | SHA-256 |
|---|---:|---:|---|
| `StrictJson.lean` | 2,849 | 114 | `20f9aff3f5339e54d7fc5e148fadb0e37d8f4b4bd816938f0a81b4cf7b087089` |
| `Schema.lean` | 18,619 | 417 | `3ccab70a3ff8e2e6f39cc09e4b2296fad035267b4def0e6c8bb002062f5733a0` |
| `ParserTests.lean` | 12,290 | 205 | `1a56fd4fef9880a464583749d27e14840b2f48afc81fe007db473bb167585cd5` |

The complete `lakefile.lean` and exact helper suffix matched their handoff pins: 17,413 bytes with
SHA-256 `d7c91f35fe23c276335327ab00c8119eafd88a306bb6a27ae82b96ad6dbdde0e`, and 603 bytes with
SHA-256 `fc859c45e415af2340b4c2b0f796d11ab042d9fc2dd3387647426386bf89fd0e`, respectively. The eight
current matrix paths and byte pins passed the normal harness. R0 through r9 were not edited.

## Hash helper and runtime review

The pinned Lake script accepts exactly one path, rejects zero or two arguments, and checks the
input with no-follow metadata before calling `Lake.computeBinFileHash`. It prints one lowercase
16-hex token and one LF. It does not call `fetchFileHash`, does not read adjacent hash metadata,
and is invoked through `lake -R run`; there is no repository-built persistent helper executable.

Independent direct CLI checks produced one exact 17-byte record for an ordinary file and nonzero
status, empty stdout, and visible stderr for zero arguments, two arguments, a directory, a symlink,
and a FIFO. Static inspection and the exact source pin also confirmed the installed Lake process is
the intended trusted component.

The runtime output gate passed its claimed narrow behavior. Direct parser execution emitted exactly
154 bytes, three LF-terminated records, and SHA-256
`0e726bc985fa93c02e34c66d79b5b3a52947cecd93e0803a611a9be3ab581c07`, reporting 16 positive,
52 fail-closed negative, and 68 total cases. The file-based gate rejects space changes, reordered,
duplicated, missing, nonterminated, NUL-extended, nonblank-extended, and extra-terminal-blank
variants. It also rejects an unrelated successful producer and an exact-output nonzero producer.
The wrapper recomputes the current Lake token after execution on success and retains the explicit
sequential/no-concurrent-writer limitation.

These checks do not cure S01-R10-001 because exact output and current contents are distinct from
proof of which inputs produced those contents.

## Structured module-chain review

The production validator requires all three exact module sets and their canonical sources:
ParserTests imports Schema, and Schema imports StrictJson. For each it checks the frozen SHA-256,
module identity, generated-C-to-export-object record, and one corresponding export object in the
executable's `linkObjs`. It also checks both direct import-artifact relationships. The current
records have the expected paths and shapes.

I inspected the full focused mutation implementation rather than relying on its printed count. Its
55 cases are exactly:

- eight legacy structured/JSON cases;
- 21 source, generated-C, export-object, and executable-link cases across the three modules;
- four direct-import cases;
- eight helper-output or hash-binding cases;
- five live helper CLI cases;
- two queried-output type cases;
- two WrongSrc selection cases;
- two stale configuration-transition cases; and
- three simple executable-replacement/current-byte cases.

All 55 passed. The source cases cover wrong, missing, and duplicate entries for every module; the
link cases cover wrong, missing, and duplicate entries; the prior quotation, wrong-root, target and
package source-directory, selector, alias, malformed JSON, non-synthetic trace, path-type, and stale
configuration surfaces also remain rejected.

The missing case is a coherent cached state: the built-in replacement tests intentionally retain
the old trace and sidecar and therefore demonstrate only that a one-sided byte change is detected.
They do not update those two records consistently with the replacement while retaining the claimed
input graph.

## Reproduction of S01-R10-001

I created an initially ordinary disposable project containing the exact frozen ParserTests,
Schema, and StrictJson sources, their direct imports, the expected executable name/root, and the
same toolchain. A normal `lake -R -H -J query` built all three modules and the executable.
Production `query_and_validate_parser_build_input` accepted this initial state and returned Lake
token `23c949be032278f7`.

I then changed only the ordinary executable contents to a distinguishable successful program whose
stdout was nevertheless the exact expected 154 bytes. Its current Lake token was
`fbe59f9a7ba0fd9e`. I changed only the executable trace's output token and adjacent `.hash` record
to that new value. Every source path/hash, module identity, generated-C/export-object link,
`linkObjs` entry, and direct import record remained the original expected structured data.

Rerunning the exact `lake -R -H -J query slhdsa_acvp_parser:exe` returned the expected executable
path without rebuilding it or replacing the modified trace. The production resolver then accepted
the complete state and returned `fbe59f9a7ba0fd9e`. Executing the resolved file produced a separate
sentinel and the exact 154-byte stdout, confirming that the unrelated contents ran.

This result is stronger than a malformed or mismatched metadata mutation: the trace output,
sidecar, and actual current-file token agree, and all structured fields accepted by production are
internally consistent. The records are not authenticated as records generated by the build whose
inputs they describe. Rehashing checks internal freshness relative to those records; it does not
establish their origin.

The installed Lake primary source gives `Hash` a single `UInt64` field and derives the binary-file
token from Lean's built-in byte-array hash. Its nearby maintenance note says a secure hash should
replace that mechanism. A 64-bit token necessarily admits collisions and is not an appropriate
identity digest for a strong integrity claim. This does not make Lake unsuitable as an
incremental build tool; it limits the assurance that S01 may derive from that token.

## Other completed independent gates

The following checks completed before the blocking disposition:

- governing prompt, repository instructions, S01 current/session documents, and immutable r0--r9
  reviews were read and compared;
- branch, HEAD, working-tree scope, no `HashSig/**` diff, review pins, source pins, Lake pins, and
  current matrix path/pin set were checked;
- `python3 -B scripts/slhdsa/check-harness.py`: PASS;
- real-sibling `./scripts/slhdsa/validate.sh --docs-only`: PASS for 18 local references, authority,
  profile, source, matrix, descriptor-walker, and normal mutation surfaces;
- offline provenance and optional exact checkout-backed provenance: PASS at server commit
  `975de31eb83d87039ec88934fdc47d8c312b892d` and protocol commit
  `892fd14710f3a7edbea230d0aecc5511e0257f8e`;
- independent provenance outputs retained exact full-suite counts 12/120, 72/624, and 36/504 split
  72 positive/432 negative, plus 144 pre-hash cells with 24 positive cells;
- direct helper CLI behavior and direct parser runtime: PASS;
- `lake build HashSigTest`: PASS, 2,743 jobs;
- inventory-derived external Lean probe: PASS, eight public/root names resolved, thirteen
  private/false names and dynamic `Does.Not.Exist` rejected;
- complete focused `--resolve-s01-parser-executable` suite: PASS for the enumerated 55 cases; and
- the full wrapper reached and passed the 3,007-job repository, 2,744-job HashSig, and 2,743-job
  HashSigTest builds, dependency probe, stdout/hash self-tests, focused 55 cases, and direct parser
  16/52/68 execution.

After the blocking finding was confirmed, reviewer direction stopped further execution. The
remainder of that full-wrapper invocation, a separate update-lib run, independent syntax/hygiene
commands beyond the normal harness, and a fresh TeX/PDF run are therefore not represented as
completed r10 reviewer gates. Their implementer-recorded passes do not affect this verdict.

No distinct second defect was confirmed in the completed scope. The current authority distinctions,
sample-only qualification, parser/schema-only assurance boundary, COV-005 missing/S10 status,
F-015/F-016/F-018 open state, and S02 block remain correctly documented.

## Finding

### S01-R10-001 — MEDIUM — self-consistent cached records do not prove the executable was produced from the pinned inputs

#### Reproducible QA evidence

An exact three-module disposable build first passed the production resolver. After the current
executable contents were changed, the executable trace output and adjacent sidecar were updated to
the replacement's current Lake token while every expected structured input and link field remained
unchanged. The exact reconfigured/rehash query did not rebuild the artifact, and the production
resolver accepted the resulting path, records, and current token. The accepted executable then
emitted the exact runtime records while a separate sentinel proved that the replacement contents
ran.

Lake's token is a non-secure 64-bit built-in hash. Equality of that token supports ordinary build
freshness checks, not exact byte identity under the assurance wording used by the S01 documents.

#### Impact

The gate does not establish its claimed source-to-executable binding. It separately establishes
that the frozen sources and structured records have expected fields, that the current executable
has the token named by the trace/sidecar, and that its stdout is exact. Because a coherent cached
record can describe unrelated current contents, those facts do not show that the pinned sources
produced the executed artifact.

This is a parser/schema-format test-build integrity issue. It does not change any `HashSig/**`
declaration, does not create implementation-conformance evidence, and
does not affect the correctness of the strict parser source itself.

#### Requested repair

Build the parser in a fresh isolated output root that is initially absent or empty, with
configuration re-elaboration, rehashing, and no reusable build cache or pre-existing trace,
sidecar, object, or executable. Validate only structured records generated during that same fresh
run, resolve the executable inside that root, and execute exactly that artifact.

Use a cryptographic content digest such as SHA-256 for the executable immediately before and after
execution, while retaining the stated sequential/no-concurrent-writer boundary, ordinary-file and
no-symlink checks, exact 154-byte stdout comparison, visible stderr, and authoritative status. Add
the coherent cached-record reproduction above as a mandatory negative regression. If a fresh
isolated build is not adopted, narrow all source-to-executable and exact-byte claims to the weaker
facts actually established by the current records and 64-bit freshness token.

## Verdict rationale

R10 fixes the precise one-sided executable replacement reported by r9 and materially improves
current-file, imported-module, output-byte, status, and path checking. The helper and all 55 existing
focused cases passed, and no regression was found in the completed authority, provenance, parser,
source-selection, declaration-visibility, or administrative surfaces.

However, the build records can be made internally consistent with different current executable
contents while retaining the exact expected input graph, after which Lake's query and the production
validator accept them. The 64-bit Lake freshness token also cannot support exact
byte-identity language. Under the mandatory zero-finding threshold, S01 r10 **FAILS** independent
review. F-044 through F-051 remain pending, S01 remains blocked, and S02 must not start. No
implementation repair, administrative promotion, commit, or PR was made.
