# S01 independent re-review r13 — descriptor ownership and assurance accounting

Verdict: **FAIL**

Reviewer: fresh independent S01 r13 software-QA reviewer; not the S01 implementer and not a
reviewer for r0 through r12.

Review date: 2026-08-25.

Reviewed tree: VCVio commit `f1853af40da1efa11a71c2d7011996eebdbf6938` on branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r13 worktree.

Independence statement: I did not design, implement, or repair S01. I read the governing prompt,
repository instructions, current/session documents, and immutable r0--r12 reviews; inspected and
executed the frozen result; and confined independent mutations, builds, and fault injection to
`/tmp`. This verdict is my only repository edit. I made no commit or PR.

## Decision summary

R13 fixes the two exact r12 reproductions. Newly opened directory children are owned immediately,
and the four production-level root/relative identity and `fstat` cases repeat sixteen failures
without changing the exact process descriptor map. The checker executes and reconciles the exact
215-case partition instead of relying on prose or constants alone. Every authority, provenance,
parser, fresh-build, artifact, runtime, documentation, syntax, hygiene, build, and report gate also
passed.

Two low-severity exception/cleanup defects nevertheless violate the review's zero-finding rule:

1. **S01-R13-001 (LOW):** when the private pre-`fstat` fault-injection hook raises an unexpected
   exception such as `RuntimeError`, `_open_validated_directory_child` closes the new child, but
   each caller's typed outer handler is bypassed and its retained parent descriptor leaks. Sixteen
   root-chain calls leaked sixteen descriptors; the same relative-intermediate loop did likewise.
   The hook is absent from normal CLI invocation, which limits production impact, but r13 explicitly
   requires hook/all-exception ownership and treats any leak as a finding.
2. **S01-R13-002 (LOW):** `validate.sh` restores Lake's persistent default build configuration only
   on its success path. Any failure after the `-KbuildDir` query but before the restoration line
   runs the EXIT cleanup and deletes the temporary root while leaving Lake configured to that path.
   An ordinary later Lake query then recreates and uses the stale `/tmp` output until an explicit
   no-override audit repairs the state.

Passing nominal gates cannot offset either finding. S01 r13 fails; S01 remains blocked and S02 must
not start.

## Frozen state, scope, and immutable history

Before reviewer authorship, the worktree was exactly:

```text
branch  codex/sphincsplus-formalization
HEAD    f1853af40da1efa11a71c2d7011996eebdbf6938
status  M lakefile.lean
        ?? HashSigTest/SLHDSA/ACVP/
        ?? docs/slhdsa/
        ?? scripts/slhdsa/
```

The tracked diff is limited to the root-package configurable `buildDir` and the
`slhdsa_acvp_parser` target in `lakefile.lean`. All untracked work is under the three declared S01
roots. Explicit tracked/untracked and `git diff -- HashSig` checks found no `HashSig/**` change, no
S02 construction/security work, and no unauthorized path.

The r13 checklist was one canonical `PENDING` before authorship: 7,030 bytes, 124 lines, SHA-256
`0879a2cfe29b01a16906dad1d2370fd98fbe96d687a3933b9d0c25f64d8ae09c`. Every predecessor retained
one canonical `FAIL` and its exact immutable pin:

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
| r11 | 22,427 | 434 | `e9f459db757e8f584fed113bd42b0df947c1660b74bc7202b0957d9ba98690ff` |
| r12 | 20,025 | 347 | `74277bebc85879dd563e8e6ef5c2b733d85ff6794d093bcaf5644699eed2c90f` |

The frozen Lean sources also reproduced exactly:

| Source | Bytes | SHA-256 |
|---|---:|---|
| `StrictJson.lean` | 2,849 | `20f9aff3f5339e54d7fc5e148fadb0e37d8f4b4bd816938f0a81b4cf7b087089` |
| `Schema.lean` | 18,619 | `3ccab70a3ff8e2e6f39cc09e4b2296fad035267b4def0e6c8bb002062f5733a0` |
| `ParserTests.lean` | 12,290 | `1a56fd4fef9880a464583749d27e14840b2f48afc81fe007db473bb167585cd5` |

`lakefile.lean` remained 17,087 bytes with SHA-256
`ed17f54b243bed2ed6db5e4ab5f3a83e29ca5c3dcaeabd7f714eff01ce3e5f8f`. The declarations matrix
remained 12,938 bytes with SHA-256
`83165d2d46c4adc710bd33da9a5eca74432da92c843641734643095daea9d00a`.

## Descriptor ownership audit

I followed ownership line by line through `_open_validated_directory_child`,
`open_absolute_directory_fd`, `open_ordinary_file_under`, final ordinary-file acquisition, stable
reads, SHA-256 reads, fresh-root checks, incremental sidecars, and exclusive output creation.

The normal r13 paths are correct:

- `os.open` assigns the new child before the hook, `fstat`, type, and device/inode checks;
- `_open_validated_directory_child` catches every pre-transfer `BaseException`, closes that child,
  and re-raises;
- a successful transfer sets the old-owner variable to `-1`, closes the old parent once, and only
  then installs the validated child as the current owner;
- ordinary final-file `open`/`fstat` and validation failures close both file and parent;
- stable read/hash `finally` blocks close their retained file and parent descriptors;
- fresh-root before/after, canonical sidecar reads, and exclusive output use the same no-follow
  ownership discipline.

Independent production-level fault injection selected only the exact post-open child and retained
two unrelated live descriptors. Root-chain device/inode mismatch, root-chain `fstat` `OSError`,
relative-intermediate device/inode mismatch, and relative-intermediate `fstat` `OSError` each
rejected sixteen of sixteen calls. Before/after `/proc/self/fd` maps compared descriptor number,
device, inode, and mode and were byte-for-byte equal; both unrelated sentinels remained live. The
built-in version used one sentinel and produced the same result during the genuine focused run.

I also injected failures before `open`, at descriptor-relative `stat`, at final-file `open` and
`fstat`, and inspected close/transfer behavior. Ordinary `OSError` and `CheckFailure` paths clean up
as intended. A Linux `close` error is not safely retryable because release may already have
occurred; the pre-release `descriptor = -1` discipline avoids closing a reused number, and a
close-then-raise simulation did not double-close. These facts do not cover the unexpected-hook
exception in S01-R13-001.

## Executed 215-case partition

The checker owns one mapping and computes `PARSER_FOCUSED_TOTAL` with `sum`. The genuine fresh
resolver run compared its observed category dictionary with that exact mapping before printing:

focused-parser-partition: legacy=8; source-object-link=21; imports=4; sha-output-binding=9; path-cli=20; output-types=2; artifacts=130; wrong-srcdir=2; stale=2; fresh-root=5; query-output=5; replacement-cache=3; descriptor-lifecycle=4; total=215; sha-cli-is-subset-of-path-cli=6; nominal-success-excluded=true

Independent source accounting matched the live execution:

- artifact cases are one exact r11 18-path simultaneous substitution, 24 paths times five
  missing/inside-link/outside-link/FIFO/alias states, and nine sidecar-token mismatches:
  `1 + 24*5 + 9 = 130`;
- source/object/link cases are three modules times three source mutations, one generated-C
  mutation, and three executable-link mutations: `3*(3+1+3) = 21`;
- import cases are two relationships times wrong/missing: four;
- path CLI cases are two shared direct escape checks plus eighteen actual subprocess rejections:
  twenty. The six historical SHA CLI cases are a subset of those twenty, not another addend;
- the four lifecycle cases genuinely execute sixteen iterations each but count as four conceptual
  cases; and nominal successful SHA resolution executes as a gate but is not counted.

All nine required active documentation surfaces contained exactly the one canonical line above.
The active non-immutable tree contained no stale `55`, `67`, `211`, or `218` focused total and no
obsolete current-Lake-hash wording. Independent semantic mutations changed one category while
preserving total 215, added the SHA subset as a separate addend, counted nominal success, changed
the declared total, and appended a historical total to the active session. Every mutation rejected.

## Retained r0--r12 evidence

The current authority records remain exact and narrowly stated. The genuine sibling FIPS 205 PDF
is 1,055,752 bytes with SHA-256
`8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d`; the separate canonical
profile contains all twelve Table-2 parameter rows and exact Section 10/11 API, OID, randomness,
other-prehash, and primitive-grammar records. SP 800-230 is separately recorded as a non-normative
Initial Public Draft with six proposed sets and a strict `2^24` signatures/key cap. ACVP-Server
v1.1.0.38 remains only a server-format compatibility pin; v1.1.0.43 and protocol draft `-01` are the
current evidence pins.

Offline and optional-checkout provenance reproduced nine committed artifacts, fifteen server
artifacts, the protocol root/sections/composite, exact LF projections and license, and full-suite
counts `12/120`, `72/624`, and `36/504 (+72/-432)`. The pre-hash matrix remains 144 cells with
exactly 24 positive sample cells. Documentation consistently calls these artifacts sample JSON,
not approved vectors, a certificate, implementation conformance, construction evidence, or security
evidence. COV-005 remains missing/S10/pending; F-015/F-016/F-018 remain open.

The frozen source grammar rejects comments, malformed state, command quotations, metaprogramming,
private-name moves, false-root `main`, and `Does.Not.Exist`; the external elaborated probe resolves
eight public/root names and rejects thirteen private/false names. Lake's literal parser remains
defense in depth. The authoritative `lake -R translate-config toml` record rejects Wrong.Root,
target/package WrongSrc, source selectors, aliases, argument selectors, wrong/missing/duplicate
targets, and malformed translation output.

The accepted fresh-build path starts with an absent child under a mode-700 private parent and uses
`lake -R -H --no-cache -KbuildDir=...`. The genuine run built sixteen actions. It required the exact
three-source chain, three-by-eight 24-file current manifest, nine token-bound sidecars, generated-C/
object/link relations, and the two direct import relationships. All 24 paths rejected missing,
inside/outside symlink, FIFO, and manifest alias states. The exact r11 simultaneous substitution,
r12 canonical-path aliases, both WrongSrc projects, stale configuration, coherent cached state,
wrong query records, and initially non-absent roots all rejected.

The wrapper resolves one canonical ordinary executable, transports its exact path and SHA-256 in
exclusive files, hashes through a stable no-follow descriptor before and after execution, executes
that path with no second target lookup, preserves visible stderr and process status, and compares
stdout as an exact 154-byte file. Direct execution produced exactly 16 positive, 52 negative, and
68 total checks. Missing output, extra nonblank output, one or several terminal blank lines, actual
smoke output, and an exact-output nonzero producer rejected. Successful full validation restored
the default path to `/home/alh/SPHINCS/VCV-io/.lake/build/bin/slhdsa_acvp_parser` and removed its
temporary roots. The separate abnormal-exit restoration defect is S01-R13-002.

## Commands and report evidence

All required commands ran serially and passed on the frozen pre-verdict tree:

```text
python3 -B scripts/slhdsa/check-harness.py
  PASS: source/Lake/authority/profile/matrix/filesystem mutations

./scripts/slhdsa/validate.sh --docs-only
  PASS

python3 -B scripts/slhdsa/check-acvp-provenance.py
  PASS: 9 committed; 15 server; 12/120, 72/624, 36/504 (+72/-432); 144/24

SLHDSA_ACVP_SERVER_ROOT=/tmp/slhdsa-s01-acvp-server \
SLHDSA_ACVP_PROTOCOL_ROOT=/tmp/slhdsa-s01-acvp-protocol \
  python3 -B scripts/slhdsa/check-acvp-provenance.py
  PASS: server 975de31eb83d87039ec88934fdc47d8c312b892d; protocol
        892fd14710f3a7edbea230d0aecc5511e0257f8e

lake exe slhdsa_acvp_parser
  PASS: exact 16/52/68 records

lake build HashSigTest
  PASS: 2743 jobs

python3 -B scripts/slhdsa/check-harness.py --elaborated-s01-dependencies
  PASS: 8 resolved; 13 rejected; Does.Not.Exist rejected

./scripts/update-lib.sh
  PASS: No update necessary for all nine libraries

./scripts/slhdsa/validate.sh
  PASS: 3007/2744/2743 jobs; genuine 16-action fresh build; exact 215 partition;
        parser 16/52/68; policy 31 findings/680 constants; compiled IR; update-lib;
        extern/interop isolation; SHA2 and C13 KATs
```

Python AST and Bash syntax checks passed. Duplicate-aware parsing accepted all 12 JSON files and
all 14 records in the declarations JSONL. Independent no-follow-style inspection covered 73 active
ordinary files and found no symlink, special entry, missing LF, terminal blank line, non-excluded
trailing whitespace, tab, bytecode, cache directory, or debris. `git diff --check`, exact scope, and
the explicit empty `HashSig/**` diff passed.

`latexmk` produced a six-page, 319,860-byte PDF under
`/tmp/slhdsa-s01-r13-review-tex.WgiC3C`. Final citations resolved; only minor overfull/underfull
boxes remained. `pdftotext` confirmed F-055/F-056, descriptor language, the exact 215 partition,
r13 pending prestate, and S02 blocked.

The administrative prestate honestly recorded r0--r12 `FAIL`, F-055/F-056 and all retained repairs
as remediated pending independent review, r13 `PENDING`, no self-certification, and S02 blocked.
Those records must not be promoted after this failing verdict.

## Findings

### S01-R13-001 — LOW — unexpected hook exceptions leak the retained parent descriptor

`_open_validated_directory_child` correctly closes the newly opened child on any `BaseException`.
However, `open_absolute_directory_fd` and `open_ordinary_file_under` wrap their traversal with
`except (OSError, CheckFailure)`. If the private `_pre_child_fstat` or
`_pre_relative_child_fstat` hook raises `RuntimeError`, the helper closes its child and re-raises,
but the caller's typed handler is bypassed. Its still-owned current parent is never closed.

I reproduced this against the production functions under `/tmp`. Each action retained an unrelated
`/dev/null` sentinel, captured exact `/proc/self/fd` device/inode/mode maps, and called the relevant
traversal sixteen times:

```text
root hook RuntimeError:
  failures=16; before != after; added fds=[5,6,...,20]; sentinel live

relative-intermediate hook RuntimeError:
  failures=16; before != after; added fds=[5,6,...,20]; sentinel live
```

I closed the leaked descriptors between the two independent loops. By contrast, the intended
identity and `OSError` `fstat` cases left exact maps unchanged. The private hooks are used only by
the disposable lifecycle tests and default to `None` in production CLI modes, so this does not let
an ordinary parser invocation leak a descriptor. It is still a confirmed ownership defect in the
reviewed function boundary, directly contradicts the r13 hook/all-exception and "any leak" review
condition, and can weaken future fault-injection coverage.

Repair both caller scopes with ownership cleanup that runs for every `BaseException` while
re-raising it unchanged. Keep the newly opened child owned until validation succeeds, close it if
transfer fails, close the prior parent exactly once on successful transfer, and never retry a Linux
`close` whose release status is ambiguous. Add root and relative lifecycle cases whose hook itself
raises `RuntimeError` (and, separately, whose selected `fstat` raises an unexpected exception),
repeat each sixteen times, and require exact descriptor maps plus unrelated sentinels unchanged.

### S01-R13-002 — LOW — abnormal wrapper exits leave Lake bound to the deleted temporary build root

`validate.sh` installs an EXIT cleanup that removes the parser and fixture temporary directories.
The fresh resolver then invokes Lake with `-KbuildDir=<temporary-child>`, which persistently updates
the elaborated root-package configuration. The no-override `--audit-s01-lake-config` restoration is
only at line 243, after successful path, runtime, stdout, and post-execution SHA-256 checks. A
nonzero parser, output mismatch, hash mismatch, resolver failure after Lake reconfiguration, or
other `set -e` exit before that line runs directory cleanup but not configuration restoration.

I reproduced the exact state transition in a disposable three-module project using the production
fresh resolver. After its fresh query, I modeled an abnormal EXIT cleanup by deleting the private
parent and deliberately skipped the success-only default audit. An ordinary, non-`-R`, non-override
query returned status zero and rebuilt at the stale path:

```text
fresh selected:
  /tmp/r13-restore-dh_7jttd/private/fresh-root-build/bin/slhdsa_acvp_parser

ordinary query after modeled abort/cleanup:
  status 0
  "/tmp/r13-restore-dh_7jttd/private/fresh-root-build/bin/slhdsa_acvp_parser"

ordinary query after explicit default audit:
  status 0
  "/tmp/r13-restore-dh_7jttd/.lake/build/bin/slhdsa_acvp_parser"
```

Thus the successful wrapper is clean, but its failure path leaves persistent repository state
pointing outside the worktree and to a directory the trap just removed. A later ordinary Lake
command can recreate and use that location. The gate does not falsely accept a parser on the
successful path, so severity is LOW; the defect concerns deterministic failure cleanup and later
build integrity.

Set an `override_active` flag immediately before the command that can apply `-KbuildDir`, not only
after that command succeeds. Install cleanup immediately after `mktemp`. In the EXIT handler,
capture the original `$?`, restore the no-override default configuration whenever the flag is set,
and do so before removing the temporary root. Preserve the original nonzero status; if the original
status was zero, a restoration failure must make the wrapper fail. Report restoration/cleanup
failures without accidentally replacing an already meaningful nonzero parser status. Clear the
flag only after confirmed restoration.

Independent Bash probes confirmed that EXIT runs for explicit exit, `set -e`, and SIGTERM while
preserving statuses 7, 1, and 143, respectively. SIGKILL (status 137) cannot run shell cleanup and
is an unavoidable residual boundary that should be documented. A naive restoration command under
`set -e` changed an original status 7 to 1, so status preservation needs an explicit implementation.
Add failure-path regressions after the override for resolver output, parser status/stdout, and
post-hash failures; each must leave an ordinary no-override query at `.lake/build` and remove the
temporary path.

## Prior-finding disposition and final decision

R13 repairs S01-R12-001/F-055 for the four intended `CheckFailure`/`OSError` lifecycle cases and
repairs S01-R12-002/F-056 with one executed, semantically checked 215-case partition. Every r0--r11
authority, source-selection, parser, fresh-build, canonical-path, artifact, hash, runtime, and scope
repair also passed its retained regression evidence.

S01-R13-001 exposes a narrower unexpected-hook exception outside the four claimed passing cases;
S01-R13-002 exposes abnormal wrapper cleanup not covered by the successful restoration test. These
are new findings, not reasons to reopen the correctness of the nominal r12 repairs. No third finding
was confirmed.

The independent acceptance threshold is zero findings. Final verdict: **FAIL**. Preserve r0--r13 as
immutable failure evidence, perform a scoped repair, and require a brand-new independent review.
S01 remains blocked; S02 must not start.
