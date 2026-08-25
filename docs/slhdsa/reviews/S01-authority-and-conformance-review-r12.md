# S01 independent re-review r12 — current artifact and canonical path enforcement

Verdict: **FAIL**

Reviewer: fresh independent reviewer; not an S01 implementer and not a reviewer for r0--r11.

Review date: 2026-08-24.

Baseline: VCVio commit `f1853af40da1efa11a71c2d7011996eebdbf6938` on branch
`codex/sphincsplus-formalization`, plus the uncommitted S01 r12 worktree presented for review.

## Decision summary

The r12 work correctly rejects the r11 current-artifact substitutions and path escape. I reproduced
the exact 24-file current-artifact boundary, all 18 simultaneous substitutions, canonical raw-path
rejections, descriptor-relative no-follow traversal, sidecar-to-trace binding, a genuinely fresh
private build, the exact parser output, configuration restoration, and the full validation gates.

S01 nevertheless fails the mandatory zero-finding threshold. I found two current issues:

1. the descriptor walker leaks the newly opened child descriptor if the post-open `fstat` or
   device/inode identity check fails while opening an absolute root component or an intermediate
   relative directory; and
2. the current assurance-count documentation is internally inconsistent. Six SHA CLI cases are a
   subset of the current 20 path/shared/CLI group, but the session document presents both as if
   they were separate categories and also adds a nominal case. That list sums to 218, not the
   claimed 211. The normative validation document separately retains the obsolete r10 total of 55.

These are S01-R12-001 and S01-R12-002 below. I made no repair. F-053/F-054 therefore remain
remediated pending review rather than accepted, S01 remains open, and S02 remains blocked.

## Frozen state, scope, and immutable inputs

The initial and final branch were `codex/sphincsplus-formalization`; HEAD was and remained
`f1853af40da1efa11a71c2d7011996eebdbf6938`. The presented status was:

```text
 M lakefile.lean
?? HashSigTest/SLHDSA/ACVP/
?? docs/slhdsa/
?? scripts/slhdsa/
```

There was no staged diff, no `HashSig/**` diff, no S02 implementation, and no review commit or PR.
The review used `/tmp` for disposable probes and builds. The only repository file changed by this
reviewer is this r12 review artifact.

I read `prompt.md`, the applicable root `AGENTS.md`, the current S01 plans, sessions, matrices,
findings, scope, source ledger, assumptions, TCB, validation, README and report, and every immutable
r0--r11 review. Every predecessor retained its FAIL verdict and exact hash:

```text
r0   ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76
r1   9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec
r2   3a8e5afe4d1b17c0b29febd18f993442f41e4f3137a994badce7d54946420ad8
r3   bb84cb7380c9a5a1aa0c78018898389a7d1ac436dfa39caa987f170670542662
r4   3a334dfe161d1475a48e44385fdd114615897d8416bf8026d15dcc2dddaa3c89
r5   03ae3b07aee41ddf90a30ee42edd388b2c3921c42f8a27807180262b4397ca97
r6   8f4f477ce19484a20bf1af6af4acce2bb10707bbab9c88e803593ef6ff797d22
r7   fd8f9483e973ebca7388080e9218aa3c9b9d5857722a60bc42e5458de89941aa
r8   a09fc3b7fffacb2e83f69f968c5b2c4ba81b91cee3258e5848fea1734735dd9d
r9   52db8de84cf122c066fa4dd2928dd4d93c99f45754d95681cbfe7ed2610759fa
r10  cccabc4e95357055838ae8052f00f6d372ca8a29185d408dee81d916c5a138c1
r11  e9f459db757e8f584fed113bd42b0df947c1660b74bc7202b0957d9ba98690ff
```

R11 was exactly 22,427 bytes and 434 lines. This r12 file was still the unassigned PENDING
template before review, with SHA-256
`18ff24f56956a3534758062dc822c37f862b549e47faf38374957007fef3b277`, 7,759 bytes,
and 143 lines.

The frozen implementation and evidence pins I checked were:

```text
lakefile.lean                                             ed17f54b243bed2ed6db5e4ab5f3a83e29ca5c3dcaeabd7f714eff01ce3e5f8f
scripts/slhdsa/check-harness.py                           c196e58ee2b258e6c2aba02b69869816e79c60333eca9fe92d9fdde57a232ac5
scripts/slhdsa/validate.sh                                6cf9fd1bdefa272ab29a9b20ab2f53af77d8ec9a0b7d6a60cfd7fb4429ed9916
docs/slhdsa/reference-manifest.json                       40dd804d6a3916e81cbfc787a09d0e38de27345c5f3817626d6f492b95e65e03
docs/slhdsa/matrices/declarations.jsonl                   83165d2d46c4adc710bd33da9a5eca74432da92c843641734643095daea9d00a
HashSigTest/SLHDSA/ACVP/StrictJson.lean                    20f9aff3f5339e54d7fc5e148fadb0e37d8f4b4bd816938f0a81b4cf7b087089
HashSigTest/SLHDSA/ACVP/Schema.lean                        3ccab70a3ff8e2e6f39cc09e4b2296fad035267b4def0e6c8bb002062f5733a0
HashSigTest/SLHDSA/ACVP/ParserTests.lean                   1a56fd4fef9880a464583749d27e14840b2f48afc81fe007db473bb167585cd5
```

The three Lean sources were respectively 2,849/114, 18,619/417, and 12,290/205 bytes/lines.
The lakefile was 17,087 bytes/380 lines and the declaration matrix 12,938 bytes. The current
assumptions and TCB files also retained their presented hashes
`1b35c230fcaffe63d73aa68e7d9afb44120dfa834879e6f010183fbc80892196` and
`da21c7f9425a4252cf37d09a60386451279c0d284ff9dd51070258ead8cb892d`.

## Authority, provenance, and conformance scope

Both committed-only and optional-checkout provenance checks passed. The optional checkouts were
clean at ACVP-Server commit `975de31eb83d87039ec88934fdc47d8c312b892d` and protocol commit
`892fd14710f3a7edbea230d0aecc5511e0257f8e`. The independent result retained nine committed
artifacts, all fifteen server artifacts, keyGen 12 groups/120 tests, sigGen 72/624, sigVer 36/504
split into 72 positive and 432 negative results, and the 144-cell/24-positive pre-hash matrix.

The source classifications, exact citations, license/provenance records, projection checks,
parameter matrix, source ledger, declaration inventory, policy audit, imported assumptions, and
scope boundaries remained consistent with those pinned sources. This is still test-only strict
parser/schema-format evidence, not an SLH-DSA functional implementation or security proof. I found
no current authority, provenance, licensing, schema, API, declaration, axiom, or scope defect beyond
the count-documentation issue reported below.

## Canonical paths and descriptor traversal

I inspected and exercised the production raw-path parser and the shared filesystem functions, both
through their internal interfaces and through the exact CLI. The raw parser rejects before `Path`
normalization. It accepts only one exact absolute spelling and rejects relative paths, `.` and `..`
components, duplicate separators, trailing separators, and double-leading-slash spellings such as
`//tmp/...`. The shared relation requires distinct absolute root and file paths and a nonempty
proper relative component list.

The Linux walker anchors absolute traversal at `/`. It uses no-follow metadata, directory-relative
opens with `O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC`, and device/inode comparison for every root and
relative directory component. It opens final inputs relative to the retained parent descriptor
with `O_NOFOLLOW`, requires an ordinary file, compares path and opened identity, and checks
device/inode/size/mtime before and after reads. Final-file identity mismatch and stable-read error
paths close their owned descriptors. Exclusive output creation is likewise parent-descriptor
relative, ordinary-file constrained, and no-follow.

My disposable `/tmp/s01_r12_path_probe.py` exercised:

- canonical SHA success and exact output;
- exact sibling and nested-parent escapes, root equality, and direct outside paths;
- relative input/root and all input/root dot, parent, duplicate-separator, trailing-separator, and
  double-leading-separator spellings;
- missing paths, directories, FIFO and device/special entries;
- inside and outside final symlinks, intermediate symlinks, and root-component symlinks;
- final-file, root-component, intermediate-directory and read-time path/fd identity replacement;
- existing output, final output symlink, and intermediate output symlink.

All acceptance and rejection results were correct. A socket entry could not be created under the
review sandbox, but FIFO and device types were independently covered and the production active-tree
suite covers sockets. The replacement cases exposed the descriptor leak in S01-R12-001.

## Exact current-artifact evidence

The production manifest is exactly three modules (`ParserTests`, `Schema`, and `StrictJson`) times
these eight unique paths:

```text
lib/lean/<module>.olean
lib/lean/<module>.olean.hash
lib/lean/<module>.trace
ir/<module>.c
ir/<module>.c.hash
ir/<module>.c.o.export
ir/<module>.c.o.export.hash
ir/<module>.c.o.export.trace
```

All 24 paths are required as ordinary no-symlink paths below the initially absent fresh child
before trace consumption. Trace and sidecar reads reopen the exact paths through the same no-follow
layer. Each sidecar is exactly 16 lowercase hexadecimal bytes with no LF. Module `.olean.hash`
binds to trace `o[0]`; `.c.hash` binds to trace `c`; and export-object `.hash` binds to both the
object trace output and the executable-link input. The trace schema requires the first `o` entry to
be the exact current `.olean`; subsequent entries may only be `.olean.server` or `.olean.private`,
so a wrong first/list element cannot satisfy the check.

My independent `/tmp/s01_r12_artifact_probe.py` checked the exact 24 unique paths and reproduced:

- the exact 18 simultaneous r11 substitutions for all three modules, once with inside symlinks and
  once with outside symlinks;
- representative missing and FIFO entries;
- a manifest-parent alias;
- wrong-first and second-ordinary-`.olean` trace ambiguity attempts; and
- uppercase, LF-terminated, short, and correctly sized but mismatched sidecars.

Every mutation rejected, restoration succeeded, and nominal validation passed afterward. This
independently closes the specific S01-R11-001 acceptance path.

A private resolver run used an initially absent child under `/tmp/slhdsa-r12-review.q9PxjX`. It
performed a real 16-action build and validated the current artifact before parser execution. The
old replacement sentinel remained absent. The resolved binary was the one canonical fresh binary,
and its SHA-256 agreed before and after execution.

The fresh tree also contains `.ilean`, `.ir`, `.olean.server`, `.olean.private`, setup files, the
binary response file, compiler-generated stubs, and native/static support inputs. I inspected the
response file and executable link trace. These are generated or consumed inside the explicitly
trusted Lake/Lean/compiler and external-dependency boundary; they are not independently claimed as
current three-module evidence. The documentation excludes rather than claims them. I found no
additional artifact outside the declared narrow evidence manifest that invalidates the stated
source-to-executable evidence.

## Assurance-count audit

I read the executable test construction instead of accepting its printed `211 total` label. The
checker prints this partition:

```text
8 + 21 + 4 + 9 + 20 + 2 + 130 + 2 + 2 + 5 + 5 + 3 = 211
```

The current 20 path/shared/CLI group is exactly two direct shared sibling/nested escape checks plus
an 18-element live CLI rejection tuple. Those 18 include the six previously described SHA CLI
cases. The six are therefore a subset of 20, not a disjoint category.

The current S01 session document instead claims all 211 and separately lists 9 SHA output/binding,
6 SHA CLI, 2 output, 2 WrongSrc, 2 stale, 5 fresh, 5 query, 3 replacement, 20
canonical/shared/CLI, 130 artifact, and one nominal case, in addition to the 8, 21 and 4 groups.
That apparent partition sums to 218. The current validation document also says the build-input suite
rejects 55 cases, the old r10 total, without marking the statement historical. This is
S01-R12-002.

## Runtime, retained regressions, and full gates

The direct parser output was exactly 154 bytes and three LF-terminated lines, with SHA-256
`0e726bc3320786f915215b02e692d124c82a9ec056ad40780b6e68fc8c0c8c07`. It reported 16 positive,
52 negative, and 68 total checks. Status was zero and stderr was empty.

I reproduced the r7--r11 quote, source-directory, argument, Wrong.Root, both WrongSrc,
translated-selector, stale-build, default-configuration, coherent-cache, fresh-build, SHA-256,
stdout/status/stderr, and output-file cases. The exact wrapper passes only canonical absolute paths,
uses exclusive ordinary 65-byte expected/before/after digest records, captures stdout directly in
an ordinary file while leaving stderr visible, retains the command status, and performs the
post-execution digest check even on command failure. The fresh private configuration was restored;
the later default Lake query returned
`/home/alh/SPHINCS/VCV-io/.lake/build/bin/slhdsa_acvp_parser`. Wrapper cleanup completed.

I serialized the heavy commands. All of the following gates passed:

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

The elaborated dependency probe resolved eight public/root names and rejected all thirteen private
or nonexistent probes. `lake build HashSigTest` completed 2,743 jobs. The complete wrapper completed
3,007 repository, 2,744 HashSig, and 2,743 HashSigTest jobs, performed the genuine 16-action fresh
build, passed both configuration audits, reported 31 exact policy findings and 680 constants, and
passed the exact-axiom, compiled initializer, update-lib, extern/interop, and KAT gates. Its only
warnings were the documented inherited `sorry` and native-stub warnings. `update-lib.sh` reported
`No update necessary` for all nine libraries.

Python AST compilation, Bash syntax, duplicate-rejecting parsing of all 12 JSON files and JSONL,
no-follow hygiene and debris checks, `git diff --check`, the empty staged diff, and the explicit
empty `HashSig/**` diff passed. The active S01 tree contained no symlink or special entry.

TeX built a six-page, 285,174-byte PDF in `/tmp`. `pdftotext` confirmed F-053/F-054, the exact
three-by-eight manifest, descriptor-relative traversal, the sequential/no-concurrent-writer and TCB
limits, r12 PENDING prestate, and S02 blocked. There were only inherited minor overfull-box
warnings.

Passing gates do not override either current finding under the mandatory zero-finding rule.

## Prior finding disposition

The frozen sources and the retained regression suite preserve the previously reviewed repairs from
r0--r10. For the two r11 findings specifically:

- **S01-R11-001 / F-053:** functionally reproduced as repaired. Both exact 18-path simultaneous
  inside and outside substitutions now reject before executable runtime, as do missing, special,
  alias, and sidecar/trace mismatch cases.
- **S01-R11-002 / F-054:** functionally reproduced as repaired. The exact sibling
  `root/../outside` spelling and nested variants reject before normalization, and canonical shared
  traversal does not escape the supplied root.

Because this independent review found new issues, F-053/F-054 must not be promoted from
`REMEDIATED-PENDING-REVIEW` to accepted. F-044--F-054 remain pending with S01. This review does not
self-certify implementation changes.

## Findings

### S01-R12-001 — LOW — newly opened directory descriptors leak on identity-check errors

**Evidence.** In `open_absolute_directory_fd`, the code opens a root component into `child`, calls
`os.fstat(child)`, and requires the opened identity to match the preceding no-follow metadata. Only
after those operations does it close the previous descriptor and assign `descriptor = child`. The
outer exception handler owns and closes only `descriptor`. If `fstat(child)` raises or the identity
requirement fails, the new `child` is never closed.

`open_ordinary_file_under` has the same ownership transition for each intermediate relative
directory. Its exception handler closes the optional final-file descriptor and the old
`parent_descriptor`, but not the newly opened `child` when post-open `fstat` or identity validation
fails before ownership transfer. The final-file path does not have this leak; it assigns its file
descriptor before validation and the exception handler closes it.

I reproduced both leaking paths synchronously without relying on an uncontrolled race. The probe
replaced the target after no-follow metadata and during the corresponding `os.open`, once for an
absolute root component and once for an intermediate relative component. Production correctly
rejected both identity changes, but `/proc/self/fd` showed exactly one new open descriptor after
each call:

```text
independent canonical/descriptor probe: PASS
confirmed leaked child fds: root=[4], relative=[3]
```

I manually closed the probe descriptors before continuing. Repeating either error would accumulate
one descriptor per attempt.

**Impact.** This does not make the walker follow or accept a symlink, and it does not affect the
normal one-shot controlled run. Repeated local identity-change or post-open `fstat` errors can,
however, exhaust the process descriptor limit and turn a fail-closed check into denial of service or
misleading later filesystem errors. It fails the required descriptor lifecycle and error-path
review.

**Required repair.** Give every successful `os.open` immediate exception-safe ownership. Close the
new child on every `fstat` or validation failure and transfer ownership only after validation. Add
repeatable root-component and relative-intermediate identity-replacement tests, including a forced
post-open `fstat` error, that compare the process descriptor set before and after every rejection.

### S01-R12-002 — LOW — current assurance-count documentation double-counts cases

**Evidence.** The executable checker defines the current 20 path/shared/CLI cases as two direct
shared escape checks plus 18 live CLI rejection cases. The six old SHA CLI cases occur inside that
18-element tuple. They are not six additional cases. The checker's printed category arithmetic
sums to 211.

The current session record presents the six SHA CLI cases and the 20 canonical/shared/CLI cases as
separate peers, then adds a nominal case. Its stated peer categories sum to 218 while the same text
claims 211. `docs/slhdsa/validation.md` separately retains `The build-input suite rejects 55 cases`,
which is the r10 count and is presented as current normative validation rather than history. The
r10 55 and r11 67 statements inside immutable historical reviews remain correct for those revisions
and are not findings.

**Impact.** The executed mutations passed, but a reader cannot reconcile the current documented
assurance total with the executable grouping. The ambiguity weakens auditability and violates the
review requirement for precise count accounting.

**Required repair.** Publish one exact current partition aligned with the checker, explicitly state
that the six SHA CLI cases are included in the 20 group, and state consistently whether nominal
success cases contribute to the named total. Replace or clearly historicize the stale 55-case
statement in the validation document. Add a documentation consistency assertion that derives these
numbers from the executable group lengths instead of repeating hand-maintained totals.

## Final decision

The r12 implementation materially repairs both r11 findings and all broad technical gates pass.
The shared descriptor lifecycle defect and the irreconcilable current assurance counts are still
real current issues. Under S01's mandatory zero-finding threshold, the only possible verdict is
**FAIL**.

No implementation, administrative record, predecessor review, commit, or PR was changed by this
review. S02 must not start.
