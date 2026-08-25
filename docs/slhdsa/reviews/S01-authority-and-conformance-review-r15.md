# S01 independent re-review r15 — bounded descriptor ownership inventory

Verdict: **FAIL**

Reviewer: fresh independent S01 r15 software-assurance reviewer; not the S01 implementer and not a
reviewer for r0 through r14.

Review date: 2026-08-25.

Reviewed tree: VCVio commit `f1853af40da1efa11a71c2d7011996eebdbf6938` on branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r15 worktree.

Independence and write-scope statement: I did not design, implement, or repair S01/r15. I read the
governing prompt, plan, review protocol, S01 session history, immutable r14 verdict, and frozen r15
implementation before fault injection. Every probe was read-only or confined to automatically
removed `/tmp` state. This verdict is my only repository edit. I made no commit and opened no pull
request.

## Decision summary

R15 substantially repairs F-059. Every current literal production acquisition has a visible owner,
`take()` marks that owner unowned before a fallible close or transfer, and the only current literal
`os.close` call is in `_close_owned_descriptors`. Safe built-in first, middle, last, and simultaneous
close failures attempt every owner and use the first cleanup error as the nominal cause. The old
directory-chain transfer preserves a forced same-number `/dev/null` reuse and closes its new child
exactly once in 32 independent repetitions. The retained r14 EXIT cleanup also passes all seven
state-machine cases and independent removal-failure tests.

Two low-severity defects nevertheless prevent a zero-finding PASS:

1. F-060's type-only evidence repair is incomplete. Python permits an exception class's `__name__`
   to be a `str` subclass. The helper accepts that object with `isinstance`, then interpolates it in
   an unguarded f-string. A hostile `__format__` therefore masks the exact active exception; on the
   nominal path it replaces the promised deterministic `CheckFailure` and loses its first-error
   cause. Both outcomes reproduced 32/32 times.
2. The AST inventory recognizes only literal `os.close`, `os.open`, and `os.dup` calls and only the
   immediate syntactic parent of acquisitions. It accepts assigned aliases, `getattr`, imported
   aliases, discarded temporary owners, `.take()` followed by discard, and rebinding of the owner
   constructor. It therefore does not enforce the claimed sole-close/immediate-meaningful-owner
   regression policy. Current production callers were manually audited and contain no alias, but
   the normal inventory would silently accept a future regression in exactly the ownership surface
   it claims to guard.

These are S01-R15-001 and S01-R15-002. Both reproduced paths remain fail-closed in the tested
process: the first changes diagnostic exception identity, and the second is a regression-control
defect rather than a hidden current production close. Severity is LOW for each. They still violate
the explicit r15 contract and the zero-issue acceptance rule. S01 r15 fails; S01 is not accepted and
S02 must remain blocked.

## Frozen state and immutable history

Before reviewer authorship, branch, base, and status were exactly:

```text
branch  codex/sphincsplus-formalization
HEAD    f1853af40da1efa11a71c2d7011996eebdbf6938
status  M lakefile.lean
        ?? HashSigTest/SLHDSA/ACVP/
        ?? docs/slhdsa/
        ?? scripts/slhdsa/
```

The pre-authorship r15 checklist was exactly 7,691 bytes, 124 lines, and SHA-256
`89d13ad5127ce002d9bb7e9f60372324f3c811fb2effb3ecaccca0080392cd2a` with one canonical
`PENDING`. R14 remained exactly 19,084 bytes, 330 lines, SHA-256
`347281880d2221e2e5e8386aa8898baee389e7d62cf50adb12031b8db0ae15f8`, and one canonical
`FAIL`. Every earlier S01 review also reproduced its immutable failure pin and exactly one
canonical `FAIL`:

| Review | SHA-256 |
|---|---|
| r0 | `ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76` |
| r1 | `9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec` |
| r2 | `3a8e5afe4d1b17c0b29febd18f993442f41e4f3137a994badce7d54946420ad8` |
| r3 | `bb84cb7380c9a5a1aa0c78018898389a7d1ac436dfa39caa987f170670542662` |
| r4 | `3a334dfe161d1475a48e44385fdd114615897d8416bf8026d15dcc2dddaa3c89` |
| r5 | `03ae3b07aee41ddf90a30ee42edd388b2c3921c42f8a27807180262b4397ca97` |
| r6 | `8f4f477ce19484a20bf1af6af4acce2bb10707bbab9c88e803593ef6ff797d22` |
| r7 | `fd8f9483e973ebca7388080e9218aa3c9b9d5857722a60bc42e5458de89941aa` |
| r8 | `a09fc3b7fffacb2e83f69f968c5b2c4ba81b91cee3258e5848fea1734735dd9d` |
| r9 | `52db8de84cf122c066fa4dd2928dd4d93c99f45754d95681cbfe7ed2610759fa` |
| r10 | `cccabc4e95357055838ae8052f00f6d372ca8a29185d408dee81d916c5a138c1` |
| r11 | `e9f459db757e8f584fed113bd42b0df947c1660b74bc7202b0957d9ba98690ff` |
| r12 | `74277bebc85879dd563e8e6ef5c2b733d85ff6794d093bcaf5644699eed2c90f` |
| r13 | `104ac10c67ea471f772efd3e0319df5ce99db9b0e7fc0859a2a700564112fd21` |
| r14 | `347281880d2221e2e5e8386aa8898baee389e7d62cf50adb12031b8db0ae15f8` |

The supplied frozen implementation pins all matched before review:

| Artifact | SHA-256 | Size/lines where pinned |
|---|---|---|
| `scripts/slhdsa/check-harness.py` | `d7b137ca25ce9d58948d4d13355bc4c23ebe7db47fd408b8195477459f1aa47a` | 275,527 B / 5,364 |
| `scripts/slhdsa/validate.sh` | `1b9d89cf9d48b2c16ed72f00aaa7515b66e56f9fd05674e92238a7f17fa868e2` | 15,615 B / 417 |
| `lakefile.lean` | `ed17f54b243bed2ed6db5e4ab5f3a83e29ca5c3dcaeabd7f714eff01ce3e5f8f` | 17,087 B / 380 |
| `StrictJson.lean` | `20f9aff3f5339e54d7fc5e148fadb0e37d8f4b4bd816938f0a81b4cf7b087089` | 2,849 B / 114 |
| `Schema.lean` | `3ccab70a3ff8e2e6f39cc09e4b2296fad035267b4def0e6c8bb002062f5733a0` | 18,619 B / 417 |
| `ParserTests.lean` | `1a56fd4fef9880a464583749d27e14840b2f48afc81fe007db473bb167585cd5` | 12,290 B / 205 |
| `matrices/assumptions.csv` | `b202031f48ee4d17d4eb0fd79935cfa11833ecbe76db4b008ad991bb977562a1` | 3,433 B / 13 |
| `matrices/tcb.csv` | `848e217ae1aa71b78707d3fe670e5e4421cfcbfb3f1b068515df186edf2f54f8` | 4,578 B / 14 |

No `HashSig/**` path is modified. The tracked change remains confined to `lakefile.lean`; the only
untracked roots remain `HashSigTest/SLHDSA/ACVP/`, `docs/slhdsa/`, and `scripts/slhdsa/`. I found no
S02 construction/security work and no unauthorized path.

## F-059 repair and current ownership inventory

### Literal production acquisitions and transfers

I independently parsed every literal `os.open`, `os.dup`, and `os.close` call and then reviewed its
semantics rather than treating AST shape as ownership evidence. Excluding seven acquisitions inside
the focused fault-test implementation, the current production acquisition inventory is:

| Function | Operation | Ownership/transfer |
|---|---|---|
| `_open_root_descriptor` | `os.open` | immediately assigned to a local owner; `take()` only on successful return |
| `_open_directory_at` | `os.open` | immediately assigned to a local owner; `take()` only on successful return |
| `_scan_directory_descriptor` | directory `os.open` | child owner spans validation and recursive scan |
| `_scan_directory_descriptor` | file `os.open` | child owner spans validation and read |
| `_open_directory_chain` | `os.dup` | current owner exists before any child operation |
| `_open_validated_directory_child` | `os.open` | child owner exists before hook and `fstat` |
| `open_absolute_directory_fd` | root `os.open` | root owner exists before traversal |
| `open_ordinary_file_under` | file `os.open` | file and retained-parent owners remain distinct |
| `validate_fresh_build_root_after` | child `os.open` | initialized sentinel owner is replaced immediately |
| `write_new_gate_record` | output `os.open` | output and retained-parent owners remain distinct |

The only literal `os.close` call is line 616 in `_close_owned_descriptors`. The production call graph
contains no import, assignment, `getattr`, or callable alias of `open`, `dup`, or `close`. No two
current owner objects contain the same live integer: children are acquired while their parents are
live, every returned integer is taken from its old owner before being wrapped by the caller, and
every multi-owner cleanup list contains distinct concurrently live acquisitions. Thus the current
caller invariant excludes aliases, although S01-R15-002 shows that it is not enforced by the
claimed static gate.

The owner helper marks a nonnegative descriptor `-1` before calling the fallible close. A duplicate
reference to the same owner object therefore does not retry a consumed integer. A separately
constructed owner for an already closed integer produces a nominal `CheckFailure` caused by
`EBADF`; with an active exception, that cleanup failure is suppressed and noted without replacing
the active object. These focused cases passed.

### Independent F-059 fault injection

For the old chain I patched only the selected duplicated parent. The injected close called the real
close, opened `/dev/null` to force the exact integer's immediate reuse, and then raised
`OSError(5)`. Across 32 repetitions, production `_open_directory_chain`:

```text
production-chain-forced-reuse:
  32/32 reused fd remained live
  32/32 newly opened directory child closed exactly once
  exact /proc/self/fd identity map unchanged
  two unrelated sentinels unchanged
```

For direct helper cleanup, independent three-owner cases injected a close-after-real failure at the
first, middle, last, and all three positions. Every case attempted all three owners, marked every
owner unowned, and raised one deterministic `CheckFailure` with the first injected error as cause.
A duplicate reference to one owner was skipped after its first `take()`; a forced reused descriptor
remained live. Base `add_note` failure caused by a custom active exception's `__notes__` rejection
was suppressed and the exact original object/arguments/traceback survived 32/32 times. A hostile
metaclass `__name__` property that raised also fell back to the literal `BaseException` evidence and
preserved the original 32/32 times.

These results confirm the core F-059 non-retry/attempt-all repair for the paths sampled before the
new finding. Because S01-R15-001 made PASS impossible, I did not continue through all fifteen
embedded production families or run the genuine fresh-build resolver that invokes them. Nominal
implementer evidence cannot substitute for the interrupted independent suite.

## Finding S01-R15-001 — LOW — hostile type-name formatting still masks cleanup outcomes

### Root cause

`_close_owned_descriptors` attempts to obtain a safe exception type name with:

```text
object.__getattribute__(type(error), "__name__")
isinstance(type_name, str)
```

The guarded block catches a metaclass property/getattribute failure, but Python permits assigning a
`str` subclass as a class's `__name__`. A nonempty subclass passes `isinstance` and the truth test.
The helper then leaves the guarded block and constructs `evidence` with an f-string. That operation
dynamically calls the subclass's `__format__`, which can raise. Evidence construction occurs before
the active-exception `BaseException.add_note` try/catch and before nominal `CheckFailure` creation.

This does not invoke the cleanup exception instance's `__str__` or `__repr__`; it is a different
hostile-dispatch route through the supposedly sanitized type-name object. It directly violates the
r15 requirement to attack hostile metaclass/type-name access and the F-060 claim that cleanup
evidence is type-only and cannot mask the original.

### Independent reproduction

I defined an `OSError` subclass and assigned its `__name__` to a nonempty `str` subclass whose
`__bool__` returned true and whose `__format__`, `__str__`, and `__repr__` raised. For each selected
owner, the patched close called the real `os.close` first and then raised that cleanup exception.

With an already active, distinct `RuntimeError`, three owners all closed and became unowned, but
the observed exception was `HostileFormat("hostile type-name __format__ invoked")`, not the exact
active object. On the nominal two-owner path, the same hostile format exception emerged instead of
`CheckFailure`, and `__cause__` was `None` rather than the first cleanup error. Repeated results were:

```text
hostile-type-name:
  active original masked = 32/32
  nominal deterministic CheckFailure replaced = 32/32
  exact /proc/self/fd identity map unchanged
  two unrelated sentinels unchanged
```

The exact-fd-map result bounds the defect: every owner was attempted and no descriptor leaked in
this reproducer. Safe built-in simultaneous errors, a directly raising metaclass property, and a
failing base-note write all passed separately. The defect is specifically the accepted `str`
subclass's later unguarded formatting.

### Impact, severity, and repair

The tested paths still fail nonzero and do not accept a malformed artifact, so severity is LOW.
They lose the precise diagnostic and cause/traceback contract that r15 explicitly promises; the
active exception can again be masked, so F-060 is not repaired.

At minimum, accept a type name only when `type(type_name) is str`, not merely `isinstance`, and use a
literal fallback for every subclass or failure. More robustly, construct the complete evidence
inside a no-mask guard with a constant fallback, validate that internal labels are exact built-in
strings, and test a hostile `str`-subclass class name on both active and nominal paths. The active
test must require exact object/type/arguments/traceback; the nominal test must require exact stable
evidence and the first cleanup error as cause after all owners are attempted.

## Finding S01-R15-002 — LOW — the AST gate accepts alias and meaningless-owner bypasses

### Root cause and accepted mutations

`validate_raw_close_inventory` recognizes only calls whose callee AST is literally an `Attribute`
named `close`, `open`, or `dup` on a `Name` literally equal to `os`. For acquisitions, it checks only
that the immediate AST parent is a call whose callee name is literally `_OwnedDescriptor`. It does
not resolve imports, assignments, `getattr`, call targets, symbol rebinding, owner retention, or
`take()` consumption.

Against the exact frozen checker source, the production gate accepted all nine independently added
mutations below:

```text
assigned-close:                  ACCEPT
getattr-close:                   ACCEPT
from-os-import-close:            ACCEPT
assigned-open:                   ACCEPT
getattr-open:                    ACCEPT
from-os-import-open:             ACCEPT
wrapped-then-discarded-open:      ACCEPT
wrapped-take-then-discarded-open: ACCEPT
rebound-_OwnedDescriptor:         ACCEPT
```

The existing self-tests rejected literal `os.close(fd)`, literal unowned `os.open(...)`, and literal
unowned `os.dup(...)`, matching the implementation but not the broader assurance claim. An owner
temporary that is discarded without cleanup is a real leak if the new path executes; syntactic
wrapping alone is not meaningful ownership. Assigned/imported/getattr close calls can reintroduce
the direct or sequential close patterns from F-059 while the inventory continues to report exactly
one permitted literal helper call.

The limitation is observable inside the current file: focused fault injection deliberately stores
`os.close` in `real_close` aliases. Those uses are test-only and appropriate, but the AST pass does
not establish that distinction; it simply ignores every alias call. The present production call
graph has no such hidden call because I audited it manually, not because the gate proves absence.

### Alias behavior and impact

A duplicate reference to the same owner object is safe because the first `take()` changes the
shared object to `-1`. Two distinct owner objects holding one integer are not safe: after the first
close really released the integer and forced a `/dev/null` reuse, the second owner closed the reused
unrelated descriptor. Current production acquisition/transfer paths do not construct such aliases,
but neither the helper nor the AST policy rejects the invariant violation. The mandatory review
instruction required aliases to be gated/documented rather than silently assumed.

This is LOW because no hidden alias/raw-close path exists in the frozen production source and the
defect is in fail-closed regression assurance. It nevertheless makes the stated owner inventory
non-enforcing, which is material in a harness specifically introduced to prevent recurrence of
F-059.

Repair should make the policy semantic enough for its exact scope: reject assignment/import/getattr
aliases for `open`/`dup`/`close`; forbid rebinding the owner/helper names; exact-register permitted
production and test acquisition/close sites by enclosing scope and structural role; and add
mutations for each bypass above. Runtime cleanup should also detect distinct live owners with the
same integer before any close, mark aliases unowned, close each unique integer at most once, and
preserve an active exception or produce deterministic nominal invariant evidence. The current
literal-bypass self-tests must remain.

## Focused mapping and retained r14 cleanup

The source has one `PARSER_FOCUSED_CASE_COUNTS` mapping and computes its total with `sum`. It contains
fifteen textual `repeated_ownership_case` invocations corresponding to the declared families. The
arithmetic is coherent, the six SHA CLI cases remain a subset of `path-cli=20`, nominal success is
excluded, and the exact current line appears once in each of the nine declared active surfaces:

focused-parser-partition: legacy=8; source-object-link=21; imports=4; sha-output-binding=9; path-cli=20; output-types=2; artifacts=130; wrong-srcdir=2; stale=2; fresh-root=5; query-output=5; replacement-cache=3; descriptor-lifecycle=6; descriptor-ownership=15; total=232; sha-cli-is-subset-of-path-cli=6; nominal-success-excluded=true

All r0-r14 history exclusions are exact path/hash entries. I found no active stale 215/217/230
total in the declared current surfaces. Because review stopped at S01-R15-001, the 232 cases were
not independently observed at runtime; source arithmetic and implementer evidence do not change
that explicit interruption.

I sourced the exact r14 cleanup state machine from the frozen wrapper in a clean Bash process. The
seven cases passed:

```text
explicit exit 7                 -> 7
errexit                         -> 1
SIGTERM                         -> 143
initiating 7 + restore failure  -> 7
success + restore failure       -> 1
normal success                  -> 0
representative resolve failure  -> 23
```

An independent `rm` status-71 injection confirmed that restoration completed while the probe root
still existed. Initiating status 7 remained 7; an initially successful body became status 1; failed
removal roots were then removed by the outer probe. The handler removes its EXIT trap before exit,
so it does not recurse. A direct configuration audit passed, and ordinary Lake query resolved:

```text
/home/alh/SPHINCS/VCV-io/.lake/build/bin/slhdsa_acvp_parser
```

SIGKILL is accurately excluded because a shell cannot execute an EXIT trap after SIGKILL. I found
no new Bash cleanup issue.

## Authority, profile, and administrative disposition review

The immutable review hashes and session record consistently describe r0-r14 as failed and retain
their findings. The current canonical documents still classify the ACVP-Server files as sample JSON
with `isSample = true`, not a validation certificate or independent FIPS-approved vector set.
Parser output remains explicitly parser/schema-format evidence only, not implementation-conformance,
construction, certificate, or security evidence. The six-set `SP800-230-IPD-6SET` profile remains
separate from `LEGACY-SHA2-128-24`.

F-015, F-016, and F-018 remain open. F-044 through F-060 remain
`REMEDIATED-PENDING-REVIEW`; this failed review cannot promote any of them. COV-005 remains
`missing`, owned by S10, and `pending`, with issue #469 and the 24-of-144 positive-cell limitation
visible. S02 remains blocked everywhere checked. No authority, conformance, or successor-session
claim can be accepted from r15.

## Commands and stop-rule evidence

The following focused commands completed before authorship:

```text
pwd; git branch --show-current; git rev-parse HEAD; git status --short
sha256sum / wc -c -l for all supplied pins and r0-r15
grep exact canonical verdicts for r0-r14
  PASS: branch/base/status, all pins, sizes, and immutable FAIL verdicts reproduced

AST extraction of every os.open/os.dup/os.close call and enclosing function
manual acquisition/transfer/cleanup audit
  PASS for the current literal production call graph

independent close-helper Python fault injection
  PASS: safe first/middle/last/all failures; all three owners attempted; first cause retained
  PASS: BaseException.add_note failure, raising metaclass property, duplicate same-owner object,
        invalid/already-closed descriptor behavior
  FAIL: hostile str-subclass type name masked active and nominal outcomes 32/32
  OBSERVED: distinct aliased owner objects closed a forced reused descriptor

independent AST source mutations
  FAIL: nine alias/discard/rebinding bypasses accepted
  PASS: three existing literal bypass forms rejected

independent production-chain forced-reuse probe
  PASS: 32 repetitions; reused fd live; new child closed once; exact fd map; two sentinels

bash exact cleanup state-machine extraction
  PASS: seven cases, including TERM/143 and restore failures
bash independent rm-status-71 injection
  PASS: status preservation/failure and restore-before-remove ordering

python3 -B scripts/slhdsa/check-harness.py --audit-s01-lake-config
lake -J query slhdsa_acvp_parser:exe
  PASS: default configuration restored and exact worktree executable resolved

git diff --check
git diff -- HashSig
git status --short -- HashSig
  PASS: whitespace diff; empty HashSig diff/status
```

After S01-R15-001 was established, I obeyed the stop rule. I did not run the genuine fresh private
parser build/focused 232-case resolver, normal checker/docs-only wrapper, offline or checkout-backed
provenance, direct 154-byte parser, 8/13/`Does.Not.Exist` Lean probe, update-lib, repository/HashSig/
HashSigTest builds, full wrapper, PolicyAudit/IR/isolation/KAT gates, syntax/duplicate-aware JSON/
JSONL/hygiene suites, or TeX/pdftotext. CPU-heavy nominal results cannot change a zero-finding
verdict after a confirmed issue. No `/tmp` evidence is retained; the Python temporary directory and
Bash probe roots were removed.

## Acceptance consequence

R15 has two confirmed findings and therefore cannot be accepted. The next implementation iteration
must preserve r0 through r15 byte-for-byte, record both findings in the canonical register/matrices,
repair the type-name evidence boundary and the alias/meaningful-owner inventory, rerun all focused
and full gates on the exact final tree, and obtain another brand-new independent zero-finding
review. Until then S01 remains incomplete and S02 remains blocked.
