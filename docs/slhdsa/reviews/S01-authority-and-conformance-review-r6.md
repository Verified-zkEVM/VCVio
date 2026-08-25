# S01 adversarial re-review r6 — declaration dependency accounting

Verdict: **FAIL**

Reviewer: fresh independent S01 r6 adversarial review sub-agent; not an S01 implementer or any
prior S01 reviewer

Reviewed commit/tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r6 tree

Date: 2026-08-24

Independence statement: I did not design, implement, or repair S01 and did not conduct r0 through
r5. The implementation remained frozen. All mutations, Lean probes, and generated report output
were confined to `/tmp`; this artifact is my only repository edit. I made no commit or PR.

## Verdict summary

The live DECL-011 through DECL-014 rows now describe the actual call graph accurately. Their current
public roots resolve, their private source declarations are private at the recorded lines, root
`main` resolves while both previously used qualified spellings do not, and the current Lake target
maps to the parser module. The old qualified-main, bare-private, nonexistent-private, false-line,
wrong-direction, wrong-target-token, and path-escape mutations were rejected.

That accurate live snapshot is not enough for the r6 acceptance claim. Three current defects remain:

1. **S01-R6-001 (MEDIUM):** the claimed semantic declaration/source-anchor validator is not
   declaration-aware. It accepts a nonexistent `lean-public` name, a private anchor located wholly
   inside a Lean block comment, and a `main` nested under a newly opened namespace. Each accepted
   mutation can pass the normal docs gate while contradicting the token's documented semantics.
2. **S01-R6-002 (MEDIUM):** the Lake-root check searches raw text and accepts the expected stanza
   inside a block comment. A valid four-target root permutation passed docs-only validation and made
   all three runtime commands used by `validate.sh` exit successfully without executing the ACVP
   parser at any of them. The wrapper checks only exit status, not the required 16/52/68 output.
3. **S01-R6-003 (LOW):** the canonical TeX report contains a literal tab followed by
   `exttt{main}` instead of `\texttt{main}`. The report compiles, but its PDF visibly says
   `extttmain`.

The zero-finding acceptance rule is unconditional. S01 r6 therefore fails, F-044 cannot be promoted
to fixed, S01 remains blocked, and S02 must not start.

## Completed checklist

- [x] Recomputed r0 through r5 hashes, verified each has exactly one canonical `FAIL`, and preserved
  r5 at SHA-256 `03ae3b07aee41ddf90a30ee42edd388b2c3921c42f8a27807180262b4397ca97`.
- [x] Verified this r6 artifact had exactly one canonical `PENDING` and SHA-256
  `e8af9c0da766d5d8e93f4654f65e10c8f041b12d861d87b087a20898f467d1fd` before authorship.
- [x] Confirmed branch, HEAD, status, allowed r6 paths, no `HashSig/**` change, no S02 work, and no
  r6 change to StrictJson, Schema, or ParserTests relative to the frozen r5 review base.
- [x] Confirmed F-044 was `REMEDIATED-PENDING-REVIEW`, F-015/F-016 remained `OPEN`, COV-005 was
  `missing`/S10/`pending`, r6 was pending, and S02 was blocked before this verdict.
- [x] Audited DECL-011 through DECL-014 line by line against the actual Lean call graph, direction
  semantics, source paths, names, lines, visibility, root `main`, private `runAll`, and Lake target.
- [x] Ran independent external Lean probes for all recorded public Lean dependencies and safe roots,
  root `main`, all three formerly public private helpers, and both nonexistent qualified-main names.
- [x] Audited exact row matching, token class/direction checks, source/root/Lake anchors, matrix pins,
  and path allowlists; ran every required mutation and additional comment/namespace/Lake bypasses.
- [x] Confirmed the typed-token documentation is explicitly scoped to DECL-011 through DECL-014 and
  does not extend a resolution/completeness claim to DECL-001 through DECL-010. F-018/TCB-009 remain.
- [x] Reran the focused harness, real-reference docs-only gate, optional checkout-backed provenance,
  parser 16+52=68 gate, complete full validation, update-lib, syntax, hygiene, debris, diff, scope,
  and TeX gates.
- [x] Re-evaluated S01-R5-001 and the r5-passed authority, provenance, schema/API, traversal, matrix,
  identity, assurance, and administrative surfaces. No ACVP Lean source regression was introduced.

## Frozen tree and immutable review history

The live review state before authorship was:

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

The sole tracked diff is the four-line `slhdsa_acvp_parser` target. Untracked files remain confined
to the three declared S01 roots. Separate tracked and untracked queries returned no `HashSig/**`
path and no proposed S02 source directory. No construction, implementation-conformance, or security
claim was added.

The immutable S01 review measurements are:

```text
ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76  r0  FAIL
9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec  r1  FAIL
3a8e5afe4d1b17c0b29febd18f993442f41e4f3137a994badce7d54946420ad8  r2  FAIL
bb84cb7380c9a5a1aa0c78018898389a7d1ac436dfa39caa987f170670542662  r3  FAIL
3a334dfe161d1475a48e44385fdd114615897d8416bf8026d15dcc2dddaa3c89  r4  FAIL
03ae3b07aee41ddf90a30ee42edd388b2c3921c42f8a27807180262b4397ca97  r5  FAIL
```

Every file contained exactly one canonical verdict. Before replacement, r6 was 3,573 bytes, 58
lines, and contained exactly one canonical `PENDING`.

The three ACVP Lean sources are byte-identical to the r5 review's frozen mutation base:

```text
20f9aff3f5339e54d7fc5e148fadb0e37d8f4b4bd816938f0a81b4cf7b087089  StrictJson.lean
3ccab70a3ff8e2e6f39cc09e4b2296fad035267b4def0e6c8bb002062f5733a0  Schema.lean
1a56fd4fef9880a464583749d27e14840b2f48afc81fe007db473bb167585cd5  ParserTests.lean
```

Thus the r6 implementation delta is limited to the declaration matrix, checker, review/admin
surfaces, and corresponding matrix pins. The r5 authority/schema/traversal implementation was not
silently changed.

## Exact declaration and call-graph audit

### DECL-011 — `SLHDSA.Test.ACVP.parameterSets`

The public definition spans Schema lines 59--72. Its immediate named public dependency is
`SLHDSA.Test.ACVP.ParamInfo`; the array literal constructs that type. The only source occurrence
consuming `parameterSets` is private `parameterByName` at line 187, whose body uses it at line 188.
The repaired reverse token therefore correctly replaces the old transitive `parsePromptJson` entry:

```text
direct:  lean-public|SLHDSA.Test.ACVP.ParamInfo
reverse: source-private-direct|HashSigTest/SLHDSA/ACVP/Schema.lean|parameterByName|187
```

### DECL-012 — `SLHDSA.Test.ACVP.parseAndValidate`

The public definition spans Schema lines 401--405. Its three immediate named callees are public
`parsePrompt` (line 322), public `parseResults` (line 366), and private `validatePair` (line 377).
ParserTests' private `runPositive` (line 97, call at line 100) and `runNegative` (line 113, calls at
159, 161, 172--180, 190, and 193) are its immediate reverse consumers.

Root `main` is not an immediate caller. It calls private `runAll` at line 205; `runAll` calls
`runPositive` and `runNegative` at lines 198--199. The `root-entry-transitive` token therefore has
the right direction and transitive label.

### DECL-013 — root `main`

Namespace `SLHDSA.Test.ACVP.ParserTests` closes at line 202. The live declaration at line 205 is the
root-level public `main : IO Unit`, and its immediate callee is private `runAll` at line 197. The
current Lake configuration defines `slhdsa_acvp_parser` with root module
`HashSigTest.SLHDSA.ACVP.ParserTests`. The live row correctly uses:

```text
direct:  source-private-direct|HashSigTest/SLHDSA/ACVP/ParserTests.lean|runAll|197
reverse: lake-exe-direct|slhdsa_acvp_parser
```

### DECL-014 — `SLHDSA.Test.ACVP.parseWrappedPair`

The public definition spans Schema lines 408--415. Its immediate named callees are exactly public
`StrictJson.parse` plus private `asObject` (136), `requireKeys` (123), `field` (131),
`parsePromptJson` (312), `parseResultsJson` (356), and `validatePair` (377). Private `nestedPair`
(line 37, call at 48) and private `runNegative` (line 113, calls at 145--157) are immediate reverse
consumers. Root `main` is again transitive through `runAll` and those test-suite functions.

Repository-wide source searches found no omitted occurrence of any of these four inventoried names.
The row order, edge order, direct/transitive labels, paths, and live line numbers are accurate.

### Independent Lean visibility probes

An external module importing ParserTests resolved every public dependency/root used by these rows:

```text
SLHDSA.Test.ACVP.ParamInfo : Type
SLHDSA.Test.ACVP.parameterSets : Array SLHDSA.Test.ACVP.ParamInfo
SLHDSA.Test.ACVP.StrictJson.parse : String -> Except String Lean.Json
SLHDSA.Test.ACVP.parsePrompt : String -> Except String Prompt
SLHDSA.Test.ACVP.parseResults : String -> Except String Results
SLHDSA.Test.ACVP.parseAndValidate : String -> String -> Except String (Prompt × Results)
SLHDSA.Test.ACVP.parseWrappedPair : String -> Except String (Prompt × Results)
main : IO Unit
```

A separate expected-failure probe reported `Unknown identifier` for each of:

```text
SLHDSA.Test.ACVP.parsePromptJson
SLHDSA.Test.ACVP.parseResultsJson
SLHDSA.Test.ACVP.validatePair
HashSigTest.SLHDSA.ACVP.ParserTests.main
SLHDSA.Test.ACVP.ParserTests.main
```

This confirms the current public/private/root visibility and reproduces the precise r5 mismatch.

## Exact pins, expected rejections, and additional bypasses

The live exact matrix corpus is:

| Matrix | Bytes | SHA-256 |
|---|---:|---|
| `assumptions.csv` | 2,687 | `b9773bfe245e2c94ab75a2697d47eeef71d5a6148e44bcefa6c0e9f97232e1d0` |
| `coverage.csv` | 3,602 | `0b82e0b42197a332b35b228a1ad3b641d92411c7ba5345e8179ceba68962928c` |
| `decisions.csv` | 1,368 | `12d0615301f5bf5e9829a0f976da94a043855e1d544cc7b4c11f7fc98d9129ac` |
| `declarations.jsonl` | 12,938 | `83165d2d46c4adc710bd33da9a5eca74432da92c843641734643095daea9d00a` |
| `fips205-profile.json` | 5,059 | `c833c36b33951e3b76fcf344e282cb26a37317f115b425eb776dfcdc1a23eeb5` |
| `proof-obligations.csv` | 3,368 | `3a043967b04a1b153cce40d472170d6d754b6f531d4ee618825d52cd79901314` |
| `sp800-230-ipd-profile.json` | 1,504 | `77ee7c4f0e872f2f2f31c830a14f4d90d63c55d260a0f3aaa3ac0e4aec92d26e` |
| `tcb.csv` | 3,397 | `7c86d31c8cb27075de58431a7bfade7dae26a569accd1dbd04ee7caf22cd2752` |

In separate disposable complete trees, the normal docs gate rejected the old qualified main, bare
private helper, nonexistent private helper, false private line, root token in direct direction, and
wrong Lake token. Exact-row matching was the first reported reason. Independent direct calls to the
token validator also rejected those semantic cases. Relative `..`, absolute source paths, root-path
escape, and negative lines were rejected by the exact path/name/line allowlists.

Those successes do not cover the following accepted mutations.

### Nonexistent public declaration

The semantic token validator returned success for:

```text
lean-public|Does.Not.Exist
```

It checks only a dotted-name regular expression and that the final component is not in a hard-coded
private-name set. Lean independently reported:

```text
Unknown identifier `Does.Not.Exist`
```

After changing the disposable DECL-012 row, the checker's duplicate expected literal, and the
documented declarations byte pin consistently, the normal docs-only gate passed. This distinguishes
the exact-row/pin check from semantic name resolution: the duplicated expectation can agree with a
nonexistent declaration.

### Private source anchor inside a comment

In a disposable Schema, a block comment was opened at the end of line 376, leaving the exact raw
line `private def validatePair ...` wholly commented on line 377. The actual equivalent private
definition was placed on line 378 without changing line count or public declaration spans. The
mutated Schema elaborated successfully, but the token validator still certified line 377 and the
normal docs-only gate passed. The raw per-line regular expression is not comment-aware and therefore
does not establish that its alleged declaration exists at the anchor.

### Namespace-shifted root

In a disposable ParserTests, the blank line 203 was replaced by `namespace Fake`; line 202 still
contained the expected earlier `end SLHDSA.Test.ACVP.ParserTests`, and line 205 still began
`def main`. The token validator and normal docs-only gate passed. Lean established the contradiction:

```text
Fake.main : IO Unit
Unknown identifier `main`
```

Looking for a nearby prior `end` cannot prove current namespace depth or root visibility.

### Comment-shadowed Lake mapping and runtime substitution

The expected parser target stanza was placed inside a block comment while active executable roots
were permuted as follows:

```text
slhdsa_acvp_parser -> HashSigTest.SLHDSA.C13KAT
slhdsa_c13_kat     -> HashSigTest.SLHDSA.Sha2KAT
slhdsa_kat         -> VCVioTest.Smoke
smoke_test         -> HashSigTest.SLHDSA.ACVP.ParserTests
```

This is a valid one-to-one Lake configuration. The raw regex found the commented expected stanza,
and docs-only validation passed. Running the three exact runtime commands used by the full wrapper
then produced, respectively:

```text
lake exe slhdsa_acvp_parser  -> SLH-DSA-C13 KAT: PASS
lake exe slhdsa_kat          -> VCVio smoke test OK
lake exe slhdsa_c13_kat      -> SLH-DSA-SHA2-128-24 KAT: PASS
```

All exited zero and none emitted or executed the ACVP parser's 16/52/68 gate. ParserTests remained
only the root of `smoke_test`, which `validate.sh` does not execute. Static inspection of
`validate.sh` confirms it does not validate the required output from any `lake exe` invocation.
After this disposable test, all three live targets were rerun under the real configuration and
restored to their correct outputs.

## Authority, provenance, parser, and complete gates

Both optional upstream checkouts were available and clean. Their identities reproduced as:

```text
/tmp/slhdsa-s01-acvp-server
  HEAD 975de31eb83d87039ec88934fdc47d8c312b892d
  exact tag v1.1.0.43
  clean

/tmp/slhdsa-s01-acvp-protocol
  HEAD 892fd14710f3a7edbea230d0aecc5511e0257f8e
  clean
```

With `SLHDSA_ACVP_SERVER_ROOT` and `SLHDSA_ACVP_PROTOCOL_ROOT` set, the independent provenance gate
verified all nine committed artifacts, all fifteen server artifacts, protocol root/sections/
composite, exact full-suite counts `12/120`, `72/624`, `36/504 (+72/-432)`, and the `144/24`
coverage projection. Offline provenance also passed.

The live parser command produced exactly:

```text
SLH-DSA ACVP parser positive suite: PASS (16 cases)
SLH-DSA ACVP parser negative suite: PASS (52 cases)
SLH-DSA ACVP parser runtime gate: PASS (68 cases)
```

The live gates completed:

```text
python3 -B scripts/slhdsa/check-harness.py
  PASS; five built-in dependency mutations reported rejected

SLHDSA_REFERENCE_ROOT=/home/alh/SPHINCS ./scripts/slhdsa/validate.sh --docs-only
  PASS; 18 local references; authority/profile/scope/matrix/walker mutations; provenance

SLHDSA_REFERENCE_ROOT=/home/alh/SPHINCS ./scripts/slhdsa/validate.sh
  PASS; repository 3,007 jobs; HashSig 2,744; HashSigTest 2,743; parser 68;
  elaborated policy/compiled-IR fixture; generated umbrella; isolation; both KATs

./scripts/update-lib.sh
  PASS; all nine generated surfaces reported “No update necessary”
```

The full build emitted only the already documented baseline `sorry` and absent-native-backend stub
warnings. The policy audit reproduced 31 exact historical findings, four raw current-state surfaces,
seven compiler helpers, 680 owned constants, the exact standard axiom union plus the one confined
`sorryAx`, and no initializer execution.

Independent syntax checks parsed all Python via `ast`, all 16 JSON files with duplicate rejection,
all 14 JSONL rows, and every Bash script. `git diff --check` passed. Active-scope debris scans found
no `__pycache__`, `.pyc`, or `.pyo`. Status/scope scans found no unauthorized path or `HashSig/**`
change. The only non-immutable active tab was the report defect in S01-R6-003; the only trailing
whitespace findings were the two already hash-locked S00-r5 lines excluded by the production gate.

The report compiled from `docs/slhdsa/report` into `/tmp/slhdsa-s01-r6-review-tex` with BibTeX and
resolved citations. It produced a five-page, 282,004-byte PDF. Minor overfull-box warnings remain.
`pdftotext` independently exposed the malformed r6 phrase as `transitive root extttmain`.

## Administrative and assurance audit

Before authorship, README, plan, session index/record, review index, report, findings, and matrix
notes consistently recorded r0--r5 `FAIL`, r6 `PENDING`, and S02 blocked. F-044 was
`REMEDIATED-PENDING-REVIEW`; F-015 and F-016 were `OPEN`; COV-005 was
`missing`/required/S10/`pending`; ASM-011 and TCB-006 remained pending/schema-only; TCB-009 and F-018
continued to disclose the incomplete manual inventory.

The documentation explicitly limits the typed convention to DECL-011--DECL-014 and says the older
manual strings receive no global external-resolution guarantee. That scope statement is accurate.
The narrower prose that the checker requires actual declaration/source/root identities and the Lake
mapping is not supported because of S01-R6-001 and S01-R6-002. I found no new conformance,
certificate, construction, or security overclaim.

## Prior-finding disposition

S01-R5-001 identified wrong current dependency identities. The current rows replace private names
with source-logical tokens, replace the nonexistent qualified executable with root `main`, correct
DECL-011's immediate reverse consumer, and enumerate the actual immediate/transitive edges. The
live data portion of the repair is therefore correct.

The repair also claims exact semantic enforcement of those identities. That portion is not complete:
nonexistent public declarations, commented private anchors, namespace-shifted roots, and
comment-shadowed Lake mappings are accepted. F-044 must remain remediated-pending rather than fixed.

The r5 reviewer completed and passed every r0--r4 repaired authority, FIPS profile, profile-identity,
matrix, descriptor-walker, parser API, wrapper, provenance, quantitative, license, sample-state,
hygiene, build, and TeX surface other than its declaration-inventory finding. R6 leaves all ACVP
Lean sources unchanged, and I reran the complete live gates and optional provenance. I found no
regression on those r5-passed surfaces. That absence of regression does not waive the new r6
findings.

## Findings

### S01-R6-001 — MEDIUM — dependency tokens do not semantically validate Lean declarations or source anchors

`validate_s01_dependency_token` validates `lean-public` with a dotted-name regex and a private-name
denylist; it never asks Lean whether the declaration exists or is public. Private and root anchors
use raw line regexes without Lean comment or namespace state. Consequently, it accepted all three
independent counterexamples documented above: `lean-public|Does.Not.Exist`, a private declaration
line wholly inside a block comment, and a `main` nested below `namespace Fake`. The docs-only gate
also accepted complete disposable trees containing each counterexample.

This directly contradicts `validation.md`'s statement that `lean-public` is a public Lean callee and
that the checker requires the declaration at the exact private/root source anchor. Exact row
hard-coding and a byte pin only show agreement with the duplicate expectation in the same checker;
they do not prove the expectation denotes a Lean declaration.

Severity is MEDIUM because these rows are test-only and the manual inventory remains disclosed, but
the r6 repair exists specifically to make dependency identities non-misleading and fail closed.
Repair should derive or probe public names in an elaborated Lean environment and use a
comment/namespace-aware source representation (or elaborated declaration metadata) for private and
root anchors. Counterexamples must exercise that semantic layer independently of exact row literals.

### S01-R6-002 — MEDIUM — comment-shadowed Lake roots can silently replace the required parser runtime gate

The `lake-exe-direct` validator applies one raw multiline regex to `lakefile.lean`. It does not remove
comments or inspect Lake's elaborated configuration. The full wrapper later checks only command exit
status. The valid four-root permutation above passed docs-only validation and made every named
runtime command used by the wrapper succeed while the ACVP parser executable was never run.

This contradicts the documented claim that the checker requires the exact Lake root mapping and
undermines the fail-closed 16/52/68 runtime gate. Severity is MEDIUM because it concerns a test-only
schema gate rather than construction/security code, but it permits a green full validation without
the claimed parser execution. Repair should inspect the elaborated Lake target mapping or a
comment-aware exact configuration and should assert the parser command's exact structured result,
not merely exit zero.

### S01-R6-003 — LOW — the report's r6 `main` notation is malformed

`docs/slhdsa/report/slhdsa-formalization-audit.tex:163` contains a literal tab followed by
`exttt{main}`. TeX treats this as ordinary text rather than the intended `\texttt{main}` command.
The PDF consequently renders `transitive root extttmain`. This is a small presentation defect, but
the canonical report is a required deliverable and r6 introduced the malformed statement. Replace
the tab/text with the valid TeX command and include tabs in active report hygiene.

## Verdict rationale

The current dependency rows themselves repair the specific wrong names reported by r5, all current
Lean visibility/call-graph facts are correct, and every live authority, provenance, parser, build,
policy, KAT, syntax, hygiene, and TeX gate completed. No ACVP Lean or construction/security source
changed in r6.

However, the new validator can certify nonexistent or relocated Lean declarations, its Lake check
can be comment-shadowed so the full gate omits the parser runtime, and the report contains a visible
TeX defect. Under the mandatory zero-finding threshold, S01 r6 **FAILS** independent review. S01
remains blocked and S02 must not start. No implementation repair, commit, or PR was made.
