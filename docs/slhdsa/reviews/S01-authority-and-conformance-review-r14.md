# S01 independent re-review r14 — all-exception ownership and unconditional restore

Verdict: **FAIL**

Reviewer: fresh independent S01 r14 software-assurance reviewer; not the S01 implementer and not a
reviewer for r0 through r13.

Review date: 2026-08-25.

Reviewed tree: VCVio commit `f1853af40da1efa11a71c2d7011996eebdbf6938` on branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r14 worktree.

Independence and write-scope statement: I did not design, implement, or repair S01. I read the
governing prompt and repository instructions, inspected the frozen implementation, reproduced the
two r13 defects independently, and attacked their repairs with separate fault injection. I stopped
the CPU-heavy nominal gates as soon as a new independently reproduced issue made a zero-finding
PASS impossible. All probes were read-only or confined to automatically removed `/tmp`
directories. This verdict is my only repository edit. I made no commit and opened no pull request.

## Decision summary

Both repairs named by r14 work in their intended narrow cases:

- root-chain and relative-intermediate hook `RuntimeError`, identity mismatch, and post-open
  `fstat` failure preserve the original exception and leave exact descriptor identity maps and two
  unrelated sentinels unchanged; and
- the wrapper's EXIT state machine restores before removal, preserves initiating statuses 7, 1,
  and 143, preserves an initiating nonzero when restore/removal also fails, fails a successful
  body when cleanup fails, prevents recursive EXIT handling, and leaves the ordinary Lake query at
  `.lake/build/bin/slhdsa_acvp_parser`. SIGKILL is accurately excluded.

R14 nevertheless does not establish the claimed all-exception ownership discipline. The repaired
directory traversal is only one of two descriptor implementations in the production checker, and
several retained consumers still close two owners sequentially. A close operation that releases
its descriptor and then reports an error can therefore mask the original validation exception,
skip and leak a retained parent, or cause the older directory-chain handler to retry a consumed
descriptor number. My direct production-code probes reproduced all three outcomes, including an
unrelated reused `/dev/null` descriptor being closed and a newly opened child being leaked.

This is one systemic low-severity ownership/cleanup finding, S01-R14-001. The checker still exits
nonzero in the reproduced paths, which limits the immediate effect to diagnostic corruption,
resource loss, and possible interference with other descriptors rather than false acceptance.
It nonetheless violates the explicit r14 no-masking/no-retry/no-unrelated-close contract and the
zero-finding acceptance rule. S01 r14 fails; S01 is not accepted and S02 must remain blocked.

## Frozen state and immutable history

Before reviewer authorship, the branch, base, and status were exactly:

```text
branch  codex/sphincsplus-formalization
HEAD    f1853af40da1efa11a71c2d7011996eebdbf6938
status  M lakefile.lean
        ?? HashSigTest/SLHDSA/ACVP/
        ?? docs/slhdsa/
        ?? scripts/slhdsa/
```

The pre-authorship r14 checklist was one canonical `PENDING` artifact: 6,866 bytes, 115 lines,
SHA-256 `243f5d311857213b510db3687e0a89035194db4bfb5c1e148e1860c6d81ff803`.
R13 remained exactly 20,771 bytes, 347 lines, and SHA-256
`104ac10c67ea471f772efd3e0319df5ce99db9b0e7fc0859a2a700564112fd21`.
Every earlier S01 review also reproduced its immutable failure pin:

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

The supplied implementation pins all matched before review:

| Artifact | SHA-256 |
|---|---|
| `scripts/slhdsa/check-harness.py` | `a9f0b42b437649ba8d6156bf9dbe81a9aa14fe04c89a4e829aa8aa9948c68413` |
| `scripts/slhdsa/validate.sh` | `1b9d89cf9d48b2c16ed72f00aaa7515b66e56f9fd05674e92238a7f17fa868e2` |
| `lakefile.lean` | `ed17f54b243bed2ed6db5e4ab5f3a83e29ca5c3dcaeabd7f714eff01ce3e5f8f` |
| `StrictJson.lean` | `20f9aff3f5339e54d7fc5e148fadb0e37d8f4b4bd816938f0a81b4cf7b087089` |
| `Schema.lean` | `3ccab70a3ff8e2e6f39cc09e4b2296fad035267b4def0e6c8bb002062f5733a0` |
| `ParserTests.lean` | `1a56fd4fef9880a464583749d27e14840b2f48afc81fe007db473bb167585cd5` |
| `matrices/assumptions.csv` | `8cf474f5a126a6e7be925dcf7c942cbf39463a12211bda49e20e792fbe3f58f4` |
| `matrices/tcb.csv` | `46058a4b2a519cc0639a9d3cd487401e9911b2529c4158e0382b3ead8a75d319` |

No `HashSig/**` path is modified. The tracked change remains confined to `lakefile.lean`; the only
untracked roots remain `HashSigTest/SLHDSA/ACVP/`, `docs/slhdsa/`, and `scripts/slhdsa/`. I found no
S02 construction/security work and no unauthorized path.

## R13 finding reproduction and repair audit

### S01-R13-001 / F-057 — narrow traversal repair passes

I followed ownership through `_open_validated_directory_child`,
`open_absolute_directory_fd`, and `open_ordinary_file_under`. A child is owned immediately after
`os.open`. The helper catches every `BaseException`, closes the child without retrying it, suppresses
only cleanup failure while the original exception is active, and re-raises the original. Each
caller keeps the retained parent as its owner until the helper returns. At transfer, it saves the
old owner, marks the caller variable `-1`, attempts the old close once, closes the separately owned
child if that close raises, and otherwise installs the child as the new owner. The outer
`BaseException` handler closes whichever caller owner remains without masking the initiating
exception.

Two independent probes used two live `/dev/null` sentinels and compared complete
`/proc/self/fd` maps as `(fd, st_dev, st_ino, st_mode)`:

```text
independent RuntimeError lifecycle:
  PASS (root and relative cases x32; exact fd identity maps; 2 sentinels)

independent identity/fstat lifecycle:
  PASS (root/relative identity and fstat cases x32; exact fd identity maps; 2 sentinels)
```

The hook exceptions retained their exact messages. The identity probe altered only the selected
post-open child's inode record; the `fstat` probe raised only for that child. No descriptor
accumulated and neither sentinel changed identity.

The code defines one `PARSER_FOCUSED_CASE_COUNTS` mapping, computes its total with `sum`, records
every completed category, and requires exact dictionary equality. The arithmetic and current
documentation are internally coherent:

focused-parser-partition: legacy=8; source-object-link=21; imports=4; sha-output-binding=9; path-cli=20; output-types=2; artifacts=130; wrong-srcdir=2; stale=2; fresh-root=5; query-output=5; replacement-cache=3; descriptor-lifecycle=6; total=217; sha-cli-is-subset-of-path-cli=6; nominal-success-excluded=true

The exact line appears once in each of the nine declared active documentation surfaces; immutable
historical reviews are excluded by exact path and pin. The six lifecycle entries genuinely
represent root/relative identity, `fstat`, and hook-runtime cases. S01-R14-001 is not an arithmetic
double-count: it shows that those six cases do not cover the other production descriptor owners
to which the r14 all-exception language applies.

### S01-R13-002 / F-058 — EXIT cleanup repair passes the tested state machine

The actual Bash function captures `$?` as its first command, removes the EXIT trap, disables
errexit for cleanup, and tests an override-active flag. The production flag is set on the line
immediately before the possibly mutating resolve command. Restoration occurs while
`parser_gate_root` is still an ordinary directory; only a successful restore clears the flag.
Temporary roots are removed afterward. An initiating nonzero is returned ahead of any cleanup
status; an initially successful body returns failure if restore or removal fails. Removing the trap
before the handler's final `exit` prevents recursion. `set -u` accesses in the handler use defaults
where state may be absent.

I sourced the exact function/self-test lines from the frozen wrapper in a clean Bash process. The
seven genuine cases reported:

```text
SLH-DSA parser override cleanup self-tests: PASS
  explicit 7; errexit 1; SIGTERM 143; exit 7 + restore failure;
  success + restore failure; normal success; resolve failure 23
```

I separately replaced only `rm` in child scopes with a status-71 failure. An initiating 7 remained
7; an initially successful body returned 1; restoration markers proved that restoration succeeded
while each probe root still existed, and the failed-removal roots remained for the outer probe to
remove. A no-override audit passed, and an ordinary `lake -J query slhdsa_acvp_parser:exe` resolved
exactly `/home/alh/SPHINCS/VCV-io/.lake/build/bin/slhdsa_acvp_parser`. The self-test modes are
assigned inside the wrapper and cannot be selected by its CLI or inherited environment. SIGKILL
cannot run a shell EXIT trap and is described only as that unavoidable limitation.

I found no separate Bash cleanup finding.

## Finding

### S01-R14-001 — LOW — descriptor cleanup is inconsistent and can mask, leak, or retry a consumed fd

**Affected production paths.** R14 repaired the new parser path walker but did not migrate the
older active-tree walker or all consumers of `open_ordinary_file_under`:

1. In the active-tree walker, `_open_root_descriptor` and `_open_directory_at` directly close in a
   `BaseException` handler; recursive directory and file scans directly close in `finally`; and
   the top-level scan/load scopes directly close their roots. Any close error can replace the
   original identity/read/hygiene error.
2. `_open_directory_chain` is more serious. It obtains `child`, executes `os.close(current)`, and
   only then assigns `current = child`. If the close releases `current` and reports an error, the
   outer handler calls `os.close(current)` again. The new child is not owned by the handler. Thus
   the child leaks; the second close either masks the first with `EBADF` or can close an unrelated
   object if that descriptor number was reused.
3. `require_ordinary_file_under`, `read_ordinary_file_under`, and `sha256_ordinary_file` close the
   file descriptor and retained parent in two sequential statements. `write_new_gate_record` does
   the same in its `finally`. A close-after-release error from the first statement prevents the
   second statement from running. The retained parent leaks, and a body exception is replaced.
   Current artifact checks use `require_ordinary_file_under`; trace and incremental-sidecar reads
   use `read_ordinary_file_under`; executable attestation uses the SHA path; the exclusive path/hash
   record outputs use the writer. This is therefore one shared production defect, not dead code.
4. `validate_fresh_build_root_before` and `validate_fresh_build_root_after` use direct finalizer
   closes. The nested `after` form still reaches the parent close, so my probe found no leak there,
   but a child close error replaced the original validation exception and was then reclassified as
   a different `CheckFailure`.

**Independent reproductions.** All fault injection acted on the production functions, selected
only exact descriptors, called the real `os.close` first, and then raised `OSError(5)` to model the
important Linux condition in which a descriptor number is consumed even though close reports an
error. Cleanup never retried a probe descriptor after the run; leaked descriptors were identified
by exact identity map and closed explicitly before leaving `/tmp`.

For the read consumer, `os.read` first raised
`RuntimeError("original-read-runtime")`. The file close then really released that file and raised.
The observed exception was the close `OSError`, not the runtime error, and the parent was still
live. Repeating the production call sixteen times produced:

```text
repeated downstream close failure:
  original RuntimeError masked 16/16
  leaked retained parents = [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
  two unrelated sentinels remained live
```

The exclusive output probe independently produced close `OSError` in place of its original write
`RuntimeError`, leaked retained parent fd 4, and left its unrelated sentinel live. Code inspection
shows the SHA and sidecar paths have the identical read-finalizer structure.

For `_open_directory_chain`, the injected first close really released its current owner, then
opened `/dev/null` to force immediate reuse of that exact descriptor number before raising. The
outer handler's retry closed the reused `/dev/null` descriptor and left the newly opened directory
child live:

```text
observed initiating close error: OSError(5, "independent close-after-release")
reused fd: 4; unrelated reused descriptor live afterward: false
leaked child descriptors: [5]
```

For the fresh-root `after` validator, selected-child `fstat` raised
`RuntimeError("original-fresh-runtime")`; child close released and raised; the parent was eventually
closed, but the externally observed error was instead:

```text
CheckFailure: S01: Lake did not create the fresh build root:
  [Errno 5] fresh-close-after-release
cause: OSError; original RuntimeError masked; exact fd map otherwise preserved
```

**Impact and severity.** The reproduced paths remain fail-closed at process level, so I found no
route from this defect to acceptance of malformed authority data, artifacts, or parser output.
Severity is therefore LOW. Nevertheless, repeated failures can exhaust descriptors, diagnostic
causes can be lost, and the old chain can interfere with an unrelated reused descriptor. Those are
the exact classes r14 says it prevents. Nominal successful gates cannot discharge an untested
exception-ownership contract.

**Required repair.** Use one explicit, non-retrying ownership discipline across both descriptor
implementations and every consumer:

- after acquisition, track each owner independently; mark an fd variable unowned before any
  fallible release and never retry that number;
- while an original exception is active, attempt every still-owned close exactly once, retain the
  original exception, and record/suppress only cleanup failures;
- on nominal cleanup, still attempt every owned close and then raise a deterministic
  `CheckFailure` if any close reported failure, without skipping later owners;
- refactor `_open_directory_chain` so the returned child is owned before the old parent close and
  the exception path can close the child without retrying the consumed parent;
- apply the same helper/pair cleanup to active-tree scans, current-artifact requirement/read/hash,
  fresh-root checks, sidecar reads, and exclusive output records; and
- add production-level close-after-release tests for the chain with forced fd reuse, read/SHA/output
  with an already active unexpected exception, nominal two-owner cleanup, and fresh-root masking.
  Repeat leak-sensitive cases, preserve exact fd identity maps and unrelated sentinels, and update
  the one mechanically enforced focused partition and all active documentation to the actual new
  case count.

Do not weaken the current r14 root/relative tests; they correctly catch the original r13 defect.

## Commands and bounded evidence

The following pre-finding and focused commands completed successfully:

```text
git status --short --branch
git rev-parse HEAD
sha256sum <all supplied pins and S01 r0-r13 reviews>
wc -c -l <r13> <r14-pre-authorship>
  PASS: branch/base/status and all exact pins/counts reproduced

python3 -B scripts/slhdsa/check-harness.py
  PASS: exact sorry allowlist; Lake mapping; 23 source/token/static-Lake,
        9 selector-source, 13 translated-Lake; authority/profile/matrix/filesystem mutations

independent Python production-function descriptor probes
  PASS: intended root/relative repair (2 RuntimeError + 4 identity/fstat cases, each x32)
  REPRODUCED: read parent leak/masking x16; output parent leak/masking;
              active-chain child leak and unrelated reused-fd close;
              fresh-root original-exception masking

bash -c '<source exact validate.sh cleanup functions and seven cases>'
  PASS: seven cleanup cases; SIGKILL accurately excluded

bash -c '<same functions; inject rm status 71>'
  PASS: initiating 7 preserved; initially successful body failed 1;
        restoration preceded failed removal

python3 -B scripts/slhdsa/check-harness.py --audit-s01-lake-config
  PASS

lake -J query slhdsa_acvp_parser:exe
  "/home/alh/SPHINCS/VCV-io/.lake/build/bin/slhdsa_acvp_parser"

git diff --check
  PASS

git diff -- HashSig
git status --short -- HashSig
  empty
```

After S01-R14-001 was reproduced, I intentionally did not run `lake build`, `lake build HashSig`,
`lake build HashSigTest`, the fresh private parser build, direct parser runtime, PolicyAudit/IR,
isolation/KAT, TeX, or the full `validate.sh`. The governing zero-finding rule makes those
CPU-heavy nominal results incapable of changing this verdict, and the orchestrator explicitly
requested that heavy gates stop on the first confirmed issue. The ordinary harness preflight did
still validate the pinned authority/profile/matrix corpus, frozen administrative state, immutable
history, syntax, active-tree hygiene, and docs-only semantic mutations before the independent
fault injection found the defect.

No `/tmp` evidence is retained: Python `TemporaryDirectory` scopes and Bash probe roots were
removed after descriptor identities were recorded. Final reviewer handoff must retain the same
branch/base and declared status shape, with this r14 verdict as the only new repository content.

## Acceptance consequence

R14 has one confirmed finding and therefore cannot be accepted. F-057 and F-058 pass their narrow
repair reproductions, but their administrative acceptance must not be integrated from a failed
review. Record S01-R14-001 in the next repair iteration, preserve r0 through r14 byte-for-byte,
rerun all focused and full gates on the final repaired tree, and obtain another brand-new
zero-finding independent review. Until then S01 remains incomplete and S02 remains blocked.
