# S01 independent re-review r16 — exception-safe alias-aware descriptor inventory

Verdict: **PASS**

Reviewer: fresh independent S01 r16 software-assurance reviewer; not the S01 implementer and not a
reviewer for r0 through r15.

Review date: 2026-08-25.

Reviewed tree: VCVio commit `f1853af40da1efa11a71c2d7011996eebdbf6938` on branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r16 worktree.

Independence and write-scope statement: I did not design, implement, or repair S01/r16. I read the
governing prompt, `AGENTS.md`, contribution guidance, accepted S00 r9 review, complete S01 session,
review protocol, current implementation, and every immutable S01 failure r0 through r15. I began
from source, diff, pins, and generated inventories rather than relying on the implementer narrative.
Every independent probe was read-only or confined to removed `/tmp` state. This verdict is my only
repository edit. I made no commit and opened no pull request.

## Decision summary

R16 repairs both r15 findings. Cleanup evidence now depends only on fixed builtin strings and
builtin integer counts. It never consults a cleanup exception's instance, class, name, metaclass,
attribute, representation, string conversion, or truth value. All live owners are preflighted and
made unowned before the first close, equal descriptor integers are grouped, and every unique
integer is attempted at most once. An active exception remains the exact original even when close,
type-name behavior, or base-note storage is hostile. Nominal aliases and close failures produce one
stable `CheckFailure` only after every unique descriptor was attempted, retaining the first close
object solely as `__cause__`.

The static descriptor policy also matches its deliberately narrow claim. It exact-registers the
current source's descriptor references, owner constructions and annotations, transfers, cleanup
consumers, test-only aliases, and every direct `os` load. It rejects the r15 bypasses and the full
30-mutation suite. It does not claim to prove arbitrary Python semantics or reflection, and this
review does not enlarge that boundary.

A separate cumulative audit found no correctness, authority, evidence-integrity, or materially
harmful design regression introduced by the sixteen repair rounds. The harness is large and
refactor-sensitive, but its complexity is isolated from `HashSig/**`, its current claims are
bounded, and its relevant branches executed under the independent gates below. The correct
maintenance decision is to retain and freeze this accepted S01 result, not bootstrap another branch
from the original base. Details and guardrails are recorded below.

Reviewer findings: **none**. R16 passes independent review. S01 may be accepted by the orchestrator;
S02 remains blocked until that acceptance and the corresponding administrative integration.

## Frozen state, scope, and immutable history

Before reviewer authorship, the tree was exactly:

```text
branch  codex/sphincsplus-formalization
HEAD    f1853af40da1efa11a71c2d7011996eebdbf6938
status  M lakefile.lean
        ?? HashSigTest/SLHDSA/ACVP/
        ?? docs/slhdsa/
        ?? scripts/slhdsa/
```

The only tracked change is seven added `lakefile.lean` lines: three lines make the root package's
build directory selectable through the checked Lake configuration, and four define the ACVP parser
executable. Every untracked path is below the three declared S01 roots. Explicit tracked/untracked,
staged, and `git diff -- HashSig` checks found no `HashSig/**` change, no S02 construction/security
source, and no unauthorized root.

The pre-authorship r16 checklist was exactly 8,957 bytes, 138 lines, and SHA-256
`5efb00229fb52882e665cf51bd03643ecd0c6f7816467b0856819967bf3b24b8`, with one canonical
`PENDING`. R15 remained exactly 23,018 bytes, 397 lines, SHA-256
`f153f6bddad34a669ef40d8095c0512d4c07b4e29384cebb60bfa9764d788734`, and one canonical
`FAIL`. Every predecessor reproduced its immutable hash and one canonical `FAIL`:

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
| r15 | `f153f6bddad34a669ef40d8095c0512d4c07b4e29384cebb60bfa9764d788734` |

The supplied frozen implementation pins also matched before review:

| Artifact | SHA-256 | Size/lines where relevant |
|---|---|---:|
| `scripts/slhdsa/check-harness.py` | `c70856b91d5080e13b688102592384f3d1c57e9f542dc947aa1e3799a1be84b8` | 328,411 B / 6,280 |
| `scripts/slhdsa/validate.sh` | `1b9d89cf9d48b2c16ed72f00aaa7515b66e56f9fd05674e92238a7f17fa868e2` | 15,615 B / 417 |
| `lakefile.lean` | `ed17f54b243bed2ed6db5e4ab5f3a83e29ca5c3dcaeabd7f714eff01ce3e5f8f` | 17,087 B / 380 |
| `StrictJson.lean` | `20f9aff3f5339e54d7fc5e148fadb0e37d8f4b4bd816938f0a81b4cf7b087089` | 2,849 B / 114 |
| `Schema.lean` | `3ccab70a3ff8e2e6f39cc09e4b2296fad035267b4def0e6c8bb002062f5733a0` | 18,619 B / 417 |
| `ParserTests.lean` | `1a56fd4fef9880a464583749d27e14840b2f48afc81fe007db473bb167585cd5` | 12,290 B / 205 |
| `matrices/assumptions.csv` | `f62161b131a73dab915f08557f0d6c37971a6857ee60bd4f9f38239c32db3804` | 3,472 B / 13 |
| `matrices/tcb.csv` | `ef2556fed1d15f66c0567fe609c4a6cd0e32d3ecf48c0f9f583c065ba382284b` | 4,614 B / 14 |

The other six canonical matrix pins matched the exact registered path/size/hash set. No generated
Python/TeX debris was present in the active roots after review.

## Cumulative regression and design audit

### Current assurance value and isolation

The complete S01 result remains test support and evidence infrastructure, not proof code:

- `HashSigTest/SLHDSA/ACVP/**` contains the strict parser, typed sample schema, executable tests,
  pinned sample fixtures, and provenance records. It imports Lean JSON support and its own ACVP
  modules, not `HashSig` construction or security declarations.
- `scripts/slhdsa/**` contains the accepted S00 semantic policy audit, S01 provenance checker,
  wrapper, and the monolithic harness. Its executable checks observe the proof tree but add no
  declarations to `HashSig`.
- `docs/slhdsa/**` contains the authority ledger, exact profiles, matrices, decisions, findings,
  report, session state, and immutable review evidence.
- The only repository-wide configuration coupling is the seven-line Lake change described above.
  Ordinary builds keep `Lake.defaultBuildDir`; the temporary override is used only by the checked
  fresh-parser path and is restored on the tested normal/error/signal exits.

The independently executed full gate confirms that this isolation is real: the repository,
`HashSig`, and `HashSigTest` build separately; the authoritative HashSig audit still reports the
exact accepted S00 environment; and `git diff -- HashSig` remains empty.

### Ownership and exception design

R16 leaves one small runtime abstraction rather than parallel cleanup implementations.
`_OwnedDescriptor.take` marks an integer unowned before any fallible release or transfer.
`_close_owned_descriptors` preflights the complete list, deduplicates descriptor integers, attempts
all unique closes, and makes active and nominal disposition explicit. Every current production
acquisition and cleanup consumer was manually traced in addition to the static inventory. I found
no duplicated direct-close path, retry-after-consumption path, hidden current alias, skipped owner,
or exception-derived evidence path.

The exact behavior independently reproduced for close failures at the first, middle, last, and all
positions; same-owner repetition; legitimate `dup` integers; hostile active/nominal evidence;
raising type-name metaclasses; rejecting base-note storage; and active/nominal distinct-owner
aliases with forced same-number reuse. Owner state, exception/cause identity, sentinels, and
descriptor maps agreed with the stated contract.

### Static policy proportionality and confidence boundary

The AST registry is substantial: it records 221 `os` loads, 52 owner constructions, eight `take`
roles, 52 cleanup-helper consumers, 10 production acquisitions/one production close, 14 test
acquisitions, and 18 test captures/calls. That makes the checker intentionally sensitive to
refactoring. It is not, however, used as a proof of general Python behavior. The current docs call
it an exact policy for the frozen source grammar, enumerate the banned forms, and explicitly deny a
claim against arbitrary reflection. Manual/AI semantic review remains part of the assurance model.

I searched for contradictory or duplicated mechanisms, unreachable assurance paths, false
confidence language, and weakened original guarantees. The same production validator used by the
normal gate runs the 30 mutation sources; the genuine fresh resolver executes the descriptor fault
families and reconciles the observed category map; the full wrapper then consumes the exact fresh
binary. The retained S00 semantic Lean audit, S01 authority/provenance checks, parser execution, and
descriptor policy cover different boundaries rather than claiming to substitute for one another.
No current load-bearing check was shown unreachable or semantically dead.

Two minor cleanup opportunities are non-blocking observations, not findings: the now count-only
cleanup helper retains an unused `cleanup_label` parameter, and `ruff --no-cache` reports one unused
test-local `real_fstat` assignment. Neither value participates in a claim, branch, resource
lifecycle, exception outcome, or accepted evidence. Removing them later would be ordinary polish,
not an acceptance repair.

### Salvage versus fresh bootstrap

**Decision: retain and freeze the current S01 branch; do not bootstrap again from the original
base.** Concrete evidence favors salvage:

1. The complexity is isolated to documentation, test support, and scripts; no `HashSig/**` Lean
   source changed.
2. The valuable assets are independently reproduced: primary-source pins, exact profiles,
   provenance, sample-schema parser, parser runtime, S00 semantic audit, and complete build gates.
3. The current high-risk cleanup and build-integrity paths have direct fault-injection coverage and
   bounded claims. No present correctness or evidence-integrity counterexample remains.
4. Rebootstrapping would discard reviewed assets and repeat authority/provenance work while leaving
   the same need for a parser target, source pins, TCB accounting, and semantic Lean audit. No
   demonstrated current defect would be cured merely by moving those assets to a new branch.

The guardrail is to freeze the descriptor/AST machinery after S01. Later Lean sessions should not
ratchet new reviewer insights into this syntax registry unless an actual regression changes the
frozen descriptor boundary. Deterministic gates should continue to cover stable objective facts;
AI reviewers should judge theorem meaning, architecture, specification fidelity, maintainability,
and other semantic questions. Later session acceptance should center on the Lean deliverables, and
must not reopen accepted S01 infrastructure without concrete affected-scope evidence.

If future concrete evidence ever makes a clean bootstrap preferable, the minimum proven assets to
carry are the source ledger/reference manifest, exact FIPS/IPD profiles, licensed ACVP fixtures and
provenance checker, the three frozen Lean ACVP parser modules and small Lake target, the S00
elaborated `HashSig` policy audit, and the explicit assumption/TCB boundaries. A clean bootstrap
could leave behind the monolithic historical mutation accounting, exact AST registry, and active
administrative pin machinery, replacing them only with checks justified by its narrower threat
model. That is a contingency boundary, not the recommendation for this accepted tree.

## R15 finding dispositions

### S01-R15-001 / F-061 — repaired

`_close_owned_descriptors` stores cleanup objects only in a failure list. It computes evidence from
`len(failures)`, `len(unique_descriptors)`, and the builtin integer alias counter. The constructed
note/messages contain only fixed literals and those counts. There is no access to an exception
instance, type, `__name__`, metaclass, attribute, string, representation, format hook, or truth
value. On nominal failure, only `failures[0]` is used as the cause object.

With an active exception, `BaseException.add_note(active_exception, note)` is called explicitly in
a `BaseException` guard. No subclass override is dispatched, and failure in the base note storage
is suppressed. Independent 32-repetition probes used hostile `__str__`/`__repr__`, a nonempty
hostile `str` subclass installed as class `__name__`, a raising metaclass, and rejecting base-note
storage. Active cleanup preserved the exact original object/type/args/traceback; nominal cleanup
preserved stable `CheckFailure` evidence and the exact first cause. F-061 is repaired.

### S01-R15-002 / F-062 — repaired

Runtime preflight takes every live owner before the first close. Equal integer values increment the
alias count and contribute one unique close. Active alias/close anomalies attempt all unique
descriptors, add constant/count-only evidence best-effort, and preserve the exact original. Nominal
aliasing attempts all unique descriptors and raises one deterministic invariant `CheckFailure`; an
associated close failure remains the first cause.

Independent active and nominal distinct-owner probes repeated 32 times. Each selected close called
the real close, opened `/dev/null` at the exact released integer, and then raised. The replacement
remained live, every original owner ended at `-1`, two unrelated sentinels and the exact fd map were
unchanged after explicit replacement cleanup, and the unique integer was never retried. A repeated
reference to the same owner caused one close; two distinct `dup` integers caused two closes.

The static policy independently rejected the exact r15 nine assigned/`getattr`/from-import,
discard, take-discard, and constructor-rebinding counterexamples plus additional dup, module,
container, dynamic-import, attribute-map, and declaration-kind mutations. The normal gate executed
the complete 30-mutation suite, including changed `take`, cleanup consumer, and registered
`real_close`/`real_dup` roles. Manual inspection confirmed the exact current inventories and the
bounded documentation claim. F-062 is repaired.

## Focused accounting and retained authority/parser evidence

The checker owns one category map, computes its total, observes every conceptual case during the
fresh resolver, and compares the actual dictionary for equality. The independently executed result
was exactly:

focused-parser-partition: legacy=8; source-object-link=21; imports=4; sha-output-binding=9; path-cli=20; output-types=2; artifacts=130; wrong-srcdir=2; stale=2; fresh-root=5; query-output=5; replacement-cache=3; descriptor-lifecycle=6; descriptor-ownership=17; total=234; sha-cli-is-subset-of-path-cli=6; nominal-success-excluded=true

The two added conceptual cases are active and nominal distinct-owner aliases. Strengthening hostile
families to 32 repetitions does not double-count conceptual cases. The normal docs gate rejects a
changed partition, a separately added SHA subset, and stale active totals.

Retained S01 evidence also reproduced:

- exact final FIPS 205 authority/local PDF and twelve parameter/API rows;
- distinct six-set non-normative `SP800-230-IPD-6SET` and one-set
  `LEGACY-SHA2-128-24` identities, with the deprecated ID confined to exact immutable history;
- ACVP-Server `975de31eb83d87039ec88934fdc47d8c312b892d`, protocol
  `892fd14710f3a7edbea230d0aecc5511e0257f8e`, all 15 GenVal pins, protocol records,
  license/projection provenance, and optional checkout regeneration;
- keyGen 12/120, sigGen 72/624, sigVer 36/504 split 72 positive/432 negative, and exactly 24 of
  144 external pre-hash positive cells;
- `isSample = true` and schema-format-only language. The files are not called certificates,
  approved vectors, implementation conformance, construction evidence, or security evidence;
- COV-005 remains missing/S10/pending, and F-015, F-016, and F-018 remain open; and
- the fresh parser gate begins with an absent private root, requires the exact 24-file current
  manifest and canonical no-follow paths, executes the bound binary at its exact path, checks its
  SHA-256 before/after, byte-compares stdout, and restores the Lake override under the seven tested
  wrapper states. SIGKILL and the sequential no-concurrent-writer assumption remain explicit.

## Independent commands and evidence

The following completed successfully on the frozen pre-verdict tree:

```text
python3 -B scripts/slhdsa/check-harness.py
  PASS: 30 semantic AST mutations; exact sorry allowlist; source/Lake/authority/profile/
        matrix/filesystem mutations

./scripts/slhdsa/validate.sh --docs-only
  PASS: normal harness plus offline provenance

SLHDSA_ACVP_SERVER_ROOT=/tmp/slhdsa-s01-acvp-server \
SLHDSA_ACVP_PROTOCOL_ROOT=/tmp/slhdsa-s01-acvp-protocol \
  python3 -B scripts/slhdsa/check-acvp-provenance.py
  PASS: both exact checkouts, artifacts, projections, counts, and protocol composite

independent Python F-061/F-062 probes
  PASS: hostile evidence/raising metaclass/rejecting base note; exact active identity/traceback;
        first/middle/last/all nominal causes; same owner/dup integers; active/nominal aliases;
        32 repetitions for hostile and alias families with exact descriptor maps

independent scoped-AST mutations
  PASS: exact r15 nine plus extended assigned/getattr/import/module/container/dynamic/declaration
        counterexamples rejected

lake exe slhdsa_acvp_parser
  PASS: exactly 154 bytes/3 LF records; SHA-256
        0e726bc985fa93c02e34c66d79b5b3a52947cecd93e0803a611a9be3ab581c07;
        16 positive, 52 negative, 68 total

./scripts/slhdsa/validate.sh
  PASS: 3,007-job repository build; 2,744-job HashSig build; 2,743-job HashSigTest build;
        8-public/13-private/Does.Not.Exist dependency probe; seven wrapper cleanup cases;
        genuine 16-action no-cache parser build; exact 234-case partition; exact parser runtime;
        elaborated policy and compiled IR fixture; update-lib; extern/interop isolation;
        SHA2-128-24 and C13 KATs

./scripts/update-lib.sh
git diff --exit-code -- HashSig
git diff --check
  PASS: no generated update, no HashSig diff, and clean tracked whitespace diff

Python/Lean/Bash syntax; duplicate-aware JSON/JSONL; active-scope no-follow/hygiene/debris;
review/source/matrix pins; and final scope checks
  PASS

latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/slhdsa-s01-r16-independent-tex slhdsa-formalization-audit.tex
  PASS: seven pages, 322,218 bytes; only minor box warnings

pdftotext /tmp/slhdsa-s01-r16-independent-tex/slhdsa-formalization-audit.pdf -
  PASS: rendered F-061/F-062, transitive root main, descriptor-ownership 17/total 234,
        r16 pending prestate, and S02 blocked
```

The full policy audit's deliberate historical `sorry` fixtures emitted their known warnings and
then produced the exact 31 findings. The live HashSig environment retained only the three standard
axioms plus the one explicitly open security `sorryAx`; no new axiom, `unsafe`, `extern`, runtime
override, initializer, or linter suppression was introduced by S01.

## Final decision

No blocking finding was confirmed in either review phase. F-061 and F-062 are repaired, all earlier
S01 repairs retain their required evidence, the cumulative design remains bounded and isolated,
and the accepted assets should be frozen rather than expanded into a general Python verifier.

Final verdict: **PASS**. This artifact replaces only the r16 pending checklist. Historical r0
through r15 failures remain immutable. The orchestrator may now accept S01 and perform the narrow
administrative status integration before starting S02.
