# S01 independent re-review r11 — private fresh parser build

Verdict: **FAIL**

Reviewer: fresh independent S01 r11 software-QA reviewer; not an S01 implementer or any prior
S01 reviewer

Reviewed tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r11 tree

Date: 2026-08-24

Independence statement: I did not design or implement S01 or its r11 repair, and I did not conduct
r0 through r10. The implementation and administrative state remained frozen during review.
Disposable build, mutation, and rendering checks were confined to `/tmp`. This review artifact is
my only repository edit. I made no commit or PR.

## Verdict summary

R11 repairs the core reusable-build defect reported by r10. The accepted query uses an initially
absent child below a mode-700 owned private directory, passes the exact build-directory override to
Lake with configuration re-elaboration, rehashing, and cache downloads disabled, resolves the
expected executable in that child, and ignores the coherently changed reusable default executable.
The fresh executable emits the exact 154 bytes, is SHA-256 hashed before and after exact-path
execution, and does not emit the replacement sentinel. The wrapper also restores Lake's persistent
default configuration before subsequent commands.

Two current defects nevertheless violate mandatory r11 contracts:

1. **S01-R11-001 (MEDIUM):** the resolver does not actually require the three module artifacts,
   generated C files, export objects, or their sidecars to be ordinary files under the fresh
   child. I replaced 18 such files with symlinks to an outside ordinary file after the real fresh
   build returned and before production validation. The production resolver accepted all 18
   substitutions and returned the executable SHA-256.
2. **S01-R11-002 (LOW):** the standalone SHA-256 mode's lexical containment check accepts a path
   containing `..` that names an ordinary sibling outside the supplied root. It returned the exact
   outside file's SHA-256 with status zero. The live wrapper uses the exact canonical resolved
   executable path, so this helper-scope defect did not escape the accepted runtime path.

The complete nominal validation stack, optional provenance, hygiene, and report build pass. The
review protocol nevertheless requires zero findings. S01 r11 therefore fails, F-044 through F-052
remain pending, S01 remains blocked, and S02 must not start.

## Frozen state and immutable history

Before reviewer authorship, the live state was:

```text
git branch --show-current
codex/sphincsplus-formalization

git rev-parse HEAD
f1853af40da1efa11a71c2d7011996eebdbf6938

git status --short
 M lakefile.lean
?? HashSigTest/SLHDSA/ACVP/
?? docs/slhdsa/
?? scripts/slhdsa/
```

The tracked change was the seven-line root-package `buildDir`/parser-target addition to
`lakefile.lean`. Untracked content was confined to the three declared S01 roots. Separate tracked,
staged, and untracked queries found no `HashSig/**` source change, no S02 implementation, and no
commit or PR.

The r11 handoff initially measured 8,682 bytes and 140 lines, had SHA-256
`db242f3b7b40a8f1a50206ecdfaa92d7dd82c56e0b6484b45d0d0930dab8ab28`, and contained exactly
one canonical `PENDING` verdict. Every predecessor remained byte-identical with exactly one
canonical `FAIL`:

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
| r10 | 15,852 | 258 | `cccabc4e95357055838ae8052f00f6d372ca8a29185d408dee81d916c5a138c1` |

The three ACVP Lean sources also retained their frozen bytes:

| Source | Bytes | Lines | SHA-256 |
|---|---:|---:|---|
| `StrictJson.lean` | 2,849 | 114 | `20f9aff3f5339e54d7fc5e148fadb0e37d8f4b4bd816938f0a81b4cf7b087089` |
| `Schema.lean` | 18,619 | 417 | `3ccab70a3ff8e2e6f39cc09e4b2296fad035267b4def0e6c8bb002062f5733a0` |
| `ParserTests.lean` | 12,290 | 205 | `1a56fd4fef9880a464583749d27e14840b2f48afc81fe007db473bb167585cd5` |

`lakefile.lean` was 17,087 bytes and 380 lines with SHA-256
`ed17f54b243bed2ed6db5e4ab5f3a83e29ca5c3dcaeabd7f714eff01ce3e5f8f`. The exact eight-file
matrix set and current pins passed. The only r11 matrix changes were the documented assumptions
pin `861b7aeec6bfcdf3773fa25908fc729f1887b972cbd7057dcd207a5a8d89cb1a` and TCB pin
`e23aefab388904004a155391e5d5b97836c6bab6a57682a92fc30cf705abb7ce`.

## Fresh-root mechanics and r10 regression

The installed tools reported Lake 5.0.0 and Lean 4.32.2. Lake's own help defines the relevant
options as follows: `-R` re-elaborates configuration, `-H` hashes inputs rather than trusting hash
files, `--no-cache` builds locally without downloading build caches, `-K` supplies a configuration
option, and `-J` gives JSON query results.

The production invocation is exactly:

```text
lake -R -H --no-cache -KbuildDir=<absolute-child> -J query \
  slhdsa_acvp_parser:exe
```

The checker requires an absolute `fresh-root-build` child directly beneath an owned, ordinary,
non-symlink, mode-700 parent. It rejects a pre-existing empty directory, nonempty directory,
ordinary file, symlink, or FIFO before Lake runs. The wrapper separately checks initial absence,
and the Python resolver checks it again. Query failure, noisy or malformed output, a wrong JSON
type, and an outside or aliased result path reject. The successful query creates the child and
returns exactly `<child>/bin/slhdsa_acvp_parser` as one LF-terminated JSON string.

The focused suite rebuilt the exact r10 three-module counterexample. Its reusable default build was
changed to an unrelated executable that produced the exact expected records; the historical
metadata-only predicate accepted coherent retained records. The r11 gate then populated a distinct
initially absent child, returned a different executable path, produced the exact parser records,
and left the replacement sentinel absent. The complete built-in focused suite reported all 67
cases rejected or reproduced as intended:

```text
8 legacy structured/JSON
21 three-module source/object/link
4 direct import
9 SHA-256 output/binding
6 SHA-256 CLI
2 output type
2 WrongSrc
2 stale transition
5 fresh-root
5 query-output
3 replacement/cache
```

This establishes that the accepted binary does not come from the coherently changed default build.
It does not cure the incomplete current artifact-type enforcement in S01-R11-001.

## Structured source and artifact-chain review

The fresh traces name exactly the canonical worktree ParserTests, Schema, and StrictJson sources,
and direct hashing reproduced their frozen SHA-256 values. The trace schemas are current and
non-synthetic. The checker validates unique module identities, follows each generated-C hash into
the corresponding export-object trace, requires each export object exactly once in the executable
`linkObjs`, and requires the exact ParserTests-to-Schema and Schema-to-StrictJson direct import
relationships.

The nominal fresh build visibly performed 16 actions, including all three Lean modules, their
generated objects, four root-package native stub libraries, and the executable. All observed root
link inputs were under the fresh child; external dependency artifacts remained under their
documented package build roots and TCB boundary.

The production path-type list, however, contains only:

- the executable, its trace, and its `.hash` sidecar;
- each module trace; and
- each export-object trace.

The generated C and export-object names are compared as strings inside trace records. Current
module outputs and their sidecars are not enumerated by the ordinary-file checker. That exact gap
is reproduced in S01-R11-001.

## Default-configuration restoration

I independently checked the persistent Lake configuration transition. Immediately after a fresh
override query, an ordinary no-`-R` query attempted to use that disposable build directory,
confirming that Lake had retained the override in its elaborated package configuration. Running the
production `--audit-s01-lake-config` mode without `-KbuildDir` re-elaborated the byte-pinned default
configuration. The next ordinary no-override query returned exactly:

```text
/home/alh/SPHINCS/VCV-io/.lake/build/bin/slhdsa_acvp_parser
```

A fresh translated TOML record had no package `buildDir` field and had the unique exact parser
name/root record. The same ordinary query continued to return the default path after the disposable
build root was removed. Full validation then located default HashSig oleans and completed the
policy audit. I found no stale temporary build-directory state after restoration.

## SHA-256 and wrapper review

For the exact live path, `sha256_ordinary_file` uses `lstat`, `O_NOFOLLOW`, `fstat`, and post-read
metadata. It requires regular type, path/fd device and inode equality, and stable device, inode,
size, and nanosecond modification time across the complete read. It streams bytes through Python
`hashlib.sha256` and emits exactly 64 lowercase hexadecimal characters plus one LF. Direct tests
rejected wrong arity, a directory, symlink, FIFO, and a directly expressed outside path.

The wrapper transports the resolved path and expected digest in new ordinary exact-record files.
It compares the resolved path byte-for-byte with the one permitted fresh location. It recomputes
the fresh executable digest immediately before execution and again after every success, output
mismatch, or nonzero execution status. It executes that one resolved path without a second target
lookup. Stderr remains visible, the real status is retained, and the post-execution digest is
checked before propagating a failure.

Direct parser execution produced exactly:

```text
154 bytes; 3 LF bytes
SHA-256 0e726bc985fa93c02e34c66d79b5b3a52947cecd93e0803a611a9be3ab581c07
SLH-DSA ACVP parser positive suite: PASS (16 cases)
SLH-DSA ACVP parser negative suite: PASS (52 cases)
SLH-DSA ACVP parser runtime gate: PASS (68 cases)
```

File comparison and focused checks reject changed spaces, NUL or nonblank extension, reordering,
duplication, missing records, missing final LF, and one or multiple terminal blank records. A
successful wrong executable and an exact-output nonzero producer reject. The sequential limitation
and no-concurrent-writer assumption are explicitly recorded in ASM-012 and TCB-013; no atomic
replacement claim is made.

The lexical outside-root defect in S01-R11-002 is separate. It affects the callable helper mode's
documented scope check, not the exact path that the live wrapper obtains and compares.

## Authority, parser, and administrative regression

The normal and checkout-backed provenance gates reproduced the exact ACVP-Server commit
`975de31eb83d87039ec88934fdc47d8c312b892d` and protocol commit
`892fd14710f3a7edbea230d0aecc5511e0257f8e`. They verified nine committed artifacts, all fifteen
server artifacts, protocol root/sections/composite, and deterministic projections. Independent
outputs remained:

```text
keyGen 12 groups / 120 tests
sigGen 72 groups / 624 tests
sigVer 36 groups / 504 tests = 72 positive + 432 negative
external pre-hash matrix 144 cells / 24 positive
```

The authority boundaries, final FIPS twelve-set profile, six-set non-normative IPD profile,
one-set legacy profile, sample-only qualification, NIST notice, final-LF normalization, declaration
inventory qualification, parser/schema-only assurance, and COV-005 missing/S10 state remain
consistent with the prior exhaustive reviews. The live parser still has 16 positive and 52
fail-closed negative cases. The elaborated dependency probe resolved eight public/root names,
rejected thirteen private/false names, and rejected `Does.Not.Exist`.

Before authorship, current docs consistently recorded r0 through r10 as failed, r11 pending,
F-052 as `REMEDIATED-PENDING-REVIEW`, F-044 through F-051 pending S01 acceptance, F-015/F-016/F-018
open, COV-005 missing/S10/pending, and S02 blocked. No self-certification, implementation-
conformance, certificate, construction, or security claim was introduced.

## Complete nominal gates and hygiene

The following commands completed successfully on the frozen tree:

```text
python3 -B scripts/slhdsa/check-harness.py
./scripts/slhdsa/validate.sh --docs-only
python3 -B scripts/slhdsa/check-acvp-provenance.py
SLHDSA_ACVP_SERVER_ROOT=/tmp/slhdsa-s01-acvp-server \
SLHDSA_ACVP_PROTOCOL_ROOT=/tmp/slhdsa-s01-acvp-protocol \
  python3 -B scripts/slhdsa/check-acvp-provenance.py
lake exe slhdsa_acvp_parser
lake build HashSigTest
PYTHONDONTWRITEBYTECODE=1 python3 -B scripts/slhdsa/check-harness.py \
  --elaborated-s01-dependencies
./scripts/update-lib.sh
./scripts/slhdsa/validate.sh
```

The complete wrapper passed its 3,007-job repository, 2,744-job HashSig, and 2,743-job HashSigTest
builds; 67-case fresh resolver; parser execution; both configuration audits; elaborated policy;
compiled initializer fixture; generated umbrella check; extern/interop isolation; and both legacy
KATs. Only the documented inherited `sorry` and absent optional native-backend warnings remained.
`update-lib.sh` reported no update necessary for all nine generated surfaces.

Independent AST and Bash syntax checks passed. Duplicate-aware parsing passed for thirteen JSON
files and one fourteen-record JSONL file. A 71-file active-scope scan found no NUL, missing final LF,
symlink, special entry, Python bytecode, `__pycache__`, or unauthorized path. The production
whitespace/tab checks, `git diff --check`, empty staged diff, and empty `HashSig/**` diff passed.

`latexmk` built the canonical report into
`/tmp/slhdsa-s01-r11-review-tex-4x4NJr`. The final PDF is six pages and 284,735 bytes. Only the
documented minor overfull boxes remain. `pdftotext` confirms F-052, fresh private output, SHA-256,
the TCB and sequential no-concurrent-writer limitation, r11 pending, and S02 blocked.

Passing nominal gates do not waive the two findings below.

## Prior-finding disposition

S01-R10-001's precise reusable-build counterexample is repaired. The exact coherent default
replacement remains accepted by the historical metadata-only predicate, while the accepted r11
gate builds and executes a distinct canonical fresh executable and never runs the replacement
sentinel. SHA-256, rather than Lake's 16-hex incremental token, supplies the current executable
content check before and after runtime. Default root-package output contributes no accepted parser
evidence.

The r11 documentation also promises that every named fresh root artifact is an ordinary non-symlink
file and that helper path scope fails closed. Those new controls are incomplete, as demonstrated
below. F-052 cannot be administratively promoted while r11 as a whole fails.

## Findings

### S01-R11-001 — MEDIUM — fresh module, C, object, and sidecar file types are not enforced

#### Reproducible QA evidence

`query_and_validate_fresh_parser_build` calls `require_ordinary_file_under` for the executable,
executable trace and sidecar, three module traces, and three export-object traces. It does not call
that check for the current module artifacts, generated C files, export objects, or their sidecars.
`validate_parser_build_trace_data` only compares the expected C/object path strings and recorded
tokens.

I invoked the production resolver on a genuinely absent private child. A wrapper around only its
Lake subprocess call let the real 16-action query complete, then synchronously replaced these 18
ordinary files with symlinks to `/etc/hosts` before returning control to the unmodified production
validation logic:

```text
lib/lean/HashSigTest/SLHDSA/ACVP/ParserTests.olean
lib/lean/HashSigTest/SLHDSA/ACVP/ParserTests.olean.hash
ir/HashSigTest/SLHDSA/ACVP/ParserTests.c
ir/HashSigTest/SLHDSA/ACVP/ParserTests.c.hash
ir/HashSigTest/SLHDSA/ACVP/ParserTests.c.o.export
ir/HashSigTest/SLHDSA/ACVP/ParserTests.c.o.export.hash

lib/lean/HashSigTest/SLHDSA/ACVP/Schema.olean
lib/lean/HashSigTest/SLHDSA/ACVP/Schema.olean.hash
ir/HashSigTest/SLHDSA/ACVP/Schema.c
ir/HashSigTest/SLHDSA/ACVP/Schema.c.hash
ir/HashSigTest/SLHDSA/ACVP/Schema.c.o.export
ir/HashSigTest/SLHDSA/ACVP/Schema.c.o.export.hash

lib/lean/HashSigTest/SLHDSA/ACVP/StrictJson.olean
lib/lean/HashSigTest/SLHDSA/ACVP/StrictJson.olean.hash
ir/HashSigTest/SLHDSA/ACVP/StrictJson.c
ir/HashSigTest/SLHDSA/ACVP/StrictJson.c.hash
ir/HashSigTest/SLHDSA/ACVP/StrictJson.c.o.export
ir/HashSigTest/SLHDSA/ACVP/StrictJson.c.o.export.hash
```

The exact production result was:

```text
MUTATED_COUNT 18
PRODUCTION_RESOLVER_ACCEPTED \
  <private-parent>/fresh-root-build/bin/slhdsa_acvp_parser \
  86aecd2efa37ff1f09b64457213ab79b125e0d5a2d5134d08d4e15a1a445d9b1
SYMLINKS_ACCEPTED 18
```

The reproduction was removed after recording. No implementation file was changed.

#### Impact

This contradicts `validation.md`, the S01 session, TCB-013, and the mandatory r11 checklist, all of
which say every relevant root module, generated-C, object, trace, and sidecar artifact is an
ordinary non-symlink file inside the new child. The 67-case suite mutates structured metadata but
has no current-file type case for these 18 paths.

The reproduced executable itself remained the fresh ordinary file and retained its SHA-256; the
test does not show that a wrong source produced or replaced the accepted executable. Trusted Lake
had already created and linked the original files before substitution. The defect is nevertheless
material to the stated source-to-executable evidence boundary: the validator accepts current
filesystem state that its mandatory artifact predicate explicitly excludes. This narrower impact,
and the fact that the issue is test-only rather than construction/security code, keeps the severity
at MEDIUM.

#### Requested repair

Define the exact per-module artifact set that supports the claim and require every current file to
exist uniquely as an ordinary non-symlink path below the fresh child. At minimum this includes the
`.olean` module output, generated `.c`, export object, each consumed `.trace`, and each corresponding
`.hash` sidecar for ParserTests, Schema, and StrictJson. Include `.ilean`, `.ir`, setup records, or
other outputs only if they are claimed or consumed, and state that scope precisely.

Add independent missing, symlink-to-inside, symlink-to-outside, FIFO/special, and path-alias cases
for the module, C, object, trace, and sidecar classes. These must fail in the same production
resolver after a real fresh build and before any executable run.

### S01-R11-002 — LOW — `..` lets the SHA-256 helper hash a file outside its supplied root

#### Reproducible QA evidence

`require_ordinary_file_under` uses `Path.relative_to(root)` as its containment decision. That
operation is lexical and retains `..`; it does not normalize or reject parent components. The
subsequent component loop therefore checks `root/..` as an ordinary directory and eventually
accepts the outside sibling.

In a disposable mode-700 parent I created ordinary `root/` and sibling `outside`, then ran:

```text
python3 -B scripts/slhdsa/check-harness.py --sha256-ordinary-file \
  /tmp/<parent>/root/../outside /tmp/<parent>/root
```

The helper exited zero and printed:

```text
79aeab3ee479535e3a7c6e4bad68ce02d556740d4c27558df0336de653a64a73
```

`sha256sum` independently returned the same digest for `/tmp/<parent>/outside`. The focused helper
test rejects a directly expressed `/etc/hosts` path but does not try a `..` alias. The disposable
tree was removed after recording.

#### Impact

The callable helper mode does not satisfy its documented and mandatory “reject paths outside the
ordinary root” contract. Its no-follow descriptor checks protect the file it eventually opens but
do not restore root containment after the lexical escape.

The live wrapper is not escaped by this reproducer: its resolver requires one exact path equal to
`<fresh-child>/bin/slhdsa_acvp_parser`, writes that exact path to a bound record, and invokes the
helper without `.` or `..`. The defect is therefore limited to the general helper/path-scope
boundary and future reuse, which warrants LOW severity.

#### Requested repair

Reject any non-canonical lexical root or input and any `.` or `..` path component before walking.
Require a nonempty proper relative path whose components cannot leave the root. Prefer opening the
root directory once and traversing each accepted relative component with descriptor-relative
no-follow operations, retaining the existing final path/fd identity and stable SHA-256 checks.
Add exact sibling escape, nested parent escape, redundant-component, and symlink-alias negatives to
the live helper CLI suite.

## Verdict rationale

R11 fixes the r10 reusable-build weakness, uses a genuinely fresh root for the accepted executable,
computes cryptographic current-file digests, restores default Lake configuration, and passes every
nominal authority, parser, build, policy, provenance, hygiene, and report gate. No issue was found
in default restoration, exact stdout/status handling, current executable SHA-256 binding, or the
core coherent-cache regression.

However, production validation accepts non-ordinary current module/C/object/sidecar artifacts that
the acceptance record says are mandatory, and the SHA-256 helper accepts a `..` path outside its
declared root. The protocol permits no finding at any severity. S01 r11 therefore **FAILS**
independent review. F-044 through F-052 remain pending, S01 remains blocked, and S02 must not start.
No implementation repair, administrative promotion, commit, or PR was made.
