# S01 adversarial re-review r7 — semantic dependency and runtime gates

Verdict: **FAIL**

Reviewer: fresh independent S01 r7 adversarial review sub-agent; not an S01 implementer or any
prior S01 reviewer

Reviewed commit/tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r7 tree

Date: 2026-08-24

Independence statement: I did not design, implement, or repair S01 and did not conduct r0 through
r6. The implementation remained frozen. Disposable mutations, generated output, and Lean/Lake
probes were confined to `/tmp` or stdin; this artifact is my only repository edit. I made no commit
or PR.

## Verdict summary

The live declaration rows and call graph are accurate. The new checker rejects ordinary comments,
strings, malformed lexical/scope state, the r6 `Fake.main` and commented-private cases, and the r6
comment-shadowed four-root permutation. After the test build, all eight inventory-derived public or
root names resolve and all thirteen private or false names are rejected externally. The live Lake
mapping is correct, the parser prints the intended 16/52/68 records, full validation passes, and the
report now renders `transitive root main` correctly.

Two current defects nevertheless violate the r7 acceptance claims:

1. **S01-R7-001 (MEDIUM):** the shared lexer does not track Lean command syntax quotations. The
   source extractor certified an unexpanded quoted `private def` as an active source declaration.
   The Lake parser likewise certified an unexpanded quoted expected target while a macro registered
   a different active root. A disposable wrong root spoofed the three expected records and passed
   the exact-output helper without executing ParserTests.
2. **S01-R7-002 (LOW):** Bash command substitution removes all trailing newline characters. An
   executable producing the three expected records plus extra terminal blank lines is normalized
   to the expected string and accepted, contrary to the stated no-extra-line check.

The zero-finding rule is unconditional. S01 r7 therefore fails, F-045/F-046 cannot be accepted,
F-047 alone is repaired, and S02 must remain blocked.

## Completed checklist

- [x] Recomputed r0 through r6 hashes, required exactly one canonical `FAIL` in every artifact, and
  preserved r6 at 22,677 bytes, 429 lines, SHA-256
  `8f4f477ce19484a20bf1af6af4acce2bb10707bbab9c88e803593ef6ff797d22`.
- [x] Verified this artifact was 4,918 bytes, 78 lines, contained exactly one canonical `PENDING`,
  and had SHA-256 `1e70229340564af3071a9deb0c0e07fa0422162d394190b4f63cf93dce64e55d`
  before authorship.
- [x] Confirmed branch, HEAD, status, allowed r7 paths, no `HashSig/**` change, no S02 work, and no
  ACVP Lean source change relative to the immutable r6 source hashes.
- [x] Confirmed F-044 through F-047 were `REMEDIATED-PENDING-REVIEW`, F-015/F-016 remained `OPEN`,
  COV-005 remained `missing`/S10/`pending`, r7 was pending, and S02 was blocked.
- [x] Audited DECL-011 through DECL-014 and the current call graph, typed directions, source lines,
  visibility, root `main`, private `runAll`, and the live Lake target.
- [x] Audited the lexer and declaration/namespace/mutual state logic line by line on all three exact
  source pins; tested comments, all string classes, malformed lexical state, nested/named/unnamed
  scope cases, underflow, unclosed state, duplicates, unsupported commands, and modifier variants.
- [x] Built HashSigTest and independently derived the current eight public/root and thirteen
  private/false external probe names. All exact public names resolved, all exact private/false names
  failed, and the dynamic `Does.Not.Exist` public substitution failed elaboration.
- [x] Tested false path/name/line/direction, source-pin drift, ordinary block-comment relocation,
  balanced and nested namespace shifts, and exact-row-independent token calls. Tested the command-
  quotation counterexample that remains accepted.
- [x] Audited active Lake parsing and tested comments, ordinary/raw strings, missing/wrong/duplicate/
  ambiguous/incomplete/non-immediate roots, duplicate target names, malformed lexical state, the
  exact r6 four-root permutation, and a valid macro/quotation counterexample.
- [x] Audited `validate.sh` status, stdout, and stderr behavior; tested the expected value, C13,
  smoke, extra nonblank, missing, nonzero-exit, successful swapped/spoofing executable, and trailing-
  blank cases. Inspected stale-build behavior in the disposable project.
- [x] Confirmed the actual TeX `\texttt{main}` command, no live internal tab, independent tab
  rejection, immutable review preservation, five-page report compilation, and exact PDF text.
- [x] Ran focused harness, real-sibling docs-only, clean checkout-backed provenance, parser direct,
  complete full validation, explicit update-lib, syntax/JSON/JSONL/Bash, whitespace/tab/debris/scope/
  diff, exact source/matrix/review pins, and TeX gates.
- [x] Re-evaluated the r5/r6 findings and the authority, provenance, schema/API, descriptor-walker,
  identity, quantitative, assurance, hygiene, build, and report surfaces passed by r5/r6.

## Frozen tree and immutable review history

The live state before authorship was:

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

The sole tracked change remained the four-line parser executable target. The untracked paths were
confined to the three allowed S01 roots. Separate tracked and untracked queries found no
`HashSig/**` path. No construction, implementation-conformance, certificate, or security claim was
introduced.

The immutable S01 review chain reproduced exactly:

```text
ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76  r0  FAIL
9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec  r1  FAIL
3a8e5afe4d1b17c0b29febd18f993442f41e4f3137a994badce7d54946420ad8  r2  FAIL
bb84cb7380c9a5a1aa0c78018898389a7d1ac436dfa39caa987f170670542662  r3  FAIL
3a334dfe161d1475a48e44385fdd114615897d8416bf8026d15dcc2dddaa3c89  r4  FAIL
03ae3b07aee41ddf90a30ee42edd388b2c3921c42f8a27807180262b4397ca97  r5  FAIL
8f4f477ce19484a20bf1af6af4acce2bb10707bbab9c88e803593ef6ff797d22  r6  FAIL
```

Every file contained exactly one canonical verdict. The frozen ACVP Lean sources remained:

```text
20f9aff3f5339e54d7fc5e148fadb0e37d8f4b4bd816938f0a81b4cf7b087089  StrictJson.lean
3ccab70a3ff8e2e6f39cc09e4b2296fad035267b4def0e6c8bb002062f5733a0  Schema.lean
1a56fd4fef9880a464583749d27e14840b2f48afc81fe007db473bb167585cd5  ParserTests.lean
```

## Current declaration and call-graph audit

The extractor reports exactly one active declaration for every current typed dependency:

- `ParamInfo` is a public structure at Schema line 41; `parameterSets` is a public definition at
  line 59, and its only immediate named reverse consumer is private `parameterByName` at line 187.
- `parseAndValidate` is public at line 401. Its immediate callees are public `parsePrompt` (322),
  public `parseResults` (366), and private `validatePair` (377). Private `runPositive` (ParserTests
  97) and `runNegative` (113) consume it; root `main` is correctly labelled transitive.
- Root `main` is one public definition in the empty namespace at ParserTests line 205. It calls
  private `runAll` at line 197. The active `slhdsa_acvp_parser` target currently selects
  `HashSigTest.SLHDSA.ACVP.ParserTests`.
- `parseWrappedPair` is public at Schema line 408. Its immediate named callees are public
  `StrictJson.parse` (StrictJson 111) and private `asObject` (136), `requireKeys` (123), `field`
  (131), `parsePromptJson` (312), `parseResultsJson` (356), and `validatePair` (377). Private
  `nestedPair` (ParserTests 37) and `runNegative` (113) consume it; root `main` is transitive.

Repository-wide occurrence searches confirmed those immediate relationships and found no omitted
current consumer among these four rows. The current data therefore fixes S01-R5-001 and is not
itself misleading.

### Independent source-state mutations

The source parser rejected 23 independent negative cases: unterminated block comment, quoted string,
raw string, and character literal; scope underflow; unclosed namespace and mutual; mismatched named
end; unnamed namespace end; duplicate declaration; malformed namespace/mutual commands; ordinary
commented private relocation; balanced `Fake.main`, nested `A.B.main`, and dotted `A.B.main`; false
path, private name, private line, root/Lake direction; and `Does.Not.Exist`. Comment, ordinary-string,
and raw-string declaration text stayed hidden. `private partial def` and `partial def` were
classified private/public as intended; an unsupported explicit-public variant failed closed. A
one-byte source change disagreed with the exact source pin.

The normal focused checker independently reported all sixteen built-in source/token/Lake mutations
rejected. These successes exercise semantic functions directly rather than merely the exact row or
matrix byte pins.

### External elaborated visibility probe

After `lake build HashSigTest` completed 2,743 jobs, the inventory-derived public set was exactly:

```text
SLHDSA.Test.ACVP.ParamInfo
SLHDSA.Test.ACVP.StrictJson.parse
SLHDSA.Test.ACVP.parameterSets
SLHDSA.Test.ACVP.parseAndValidate
SLHDSA.Test.ACVP.parsePrompt
SLHDSA.Test.ACVP.parseResults
SLHDSA.Test.ACVP.parseWrappedPair
main
```

All eight resolved in an external module. The private/false set contained the eleven exact private
source spellings plus `HashSigTest.SLHDSA.ACVP.ParserTests.main` and
`SLHDSA.Test.ACVP.ParserTests.main`; all thirteen produced exact unknown-identifier failures. The
inventory-driven mode also substituted `Does.Not.Exist` into the public probe and rejected it at
elaboration. This independently confirms the current public/private facts.

## S01-R7-001 reproduction: command quotations are treated as active syntax

### Private source anchor

The lexer removes comments and strings but emits punctuation and every token inside Lean syntax
quotations. The declaration extractor groups tokens only by line and does not track quotation or
parenthesis context. This valid synthetic source therefore produced a `ghost` private-def record at
line 2 even though the quoted command was never expanded and the active declaration was opaque:

```lean
macro "unusedAnchor" : command => `(
private def ghost : Nat := 1)
private opaque ghost : Nat := 2
```

Lean elaborated it and reported `ghost : Nat`; the extractor reported
`LeanSourceDeclaration(... line=2, visibility='private', keyword='def')`.

I then applied the same construction to a disposable complete Schema source: the line-377 anchor
was an unexpanded quoted `private def validatePair`, and the actual callable implementation was a
line-378 `private opaque validatePair` with the original body. The full mutated Schema elaborated
successfully from stdin. Nevertheless,
`validate_s01_dependency_token(...|validatePair|377)` returned success and reported the quoted line
as the active private definition. Because both declarations are private externally, the r7 external
negative probe would not distinguish the quoted anchor from the actual opaque declaration. Updating
the source byte pin consistently would therefore preserve a misleading anchor.

This is not an exact-row failure: the live dependency token and line stayed unchanged, and the
semantic source-token validator itself accepted the counterexample.

### Lake target and parser-runtime substitution

The same lexer-based Lake parser has the same quotation blind spot. In the disposable project
`/tmp/slhdsa-r7-lake-quote-8ktcfJ`, a hygienic macro accepted the target, field, and root as
antiquotations and registered the actual target:

```lean
macro "wrongTarget" n:identOrStr field:ident r:term : command =>
  `(lean_exe $n where $field := $r)
wrongTarget slhdsa_acvp_parser root `Wrong.Root
```

A different, never-invoked macro contained the expected text with `lean_exe` and `root` beginning
their own lines inside a command quotation. `parse_lake_executable_roots` ignored the actual macro
invocation and returned:

```text
{'slhdsa_acvp_parser': 'HashSigTest.SLHDSA.ACVP.ParserTests'}
```

`validate_lake_parser_mapping` accepted it. Lake itself built `Wrong.Root` and the executable first
printed `WRONG ROOT EXECUTED`, proving the semantic disagreement. After the disposable wrong root
was changed to print the three expected 16/52/68 records, Lake again built and executed Wrong.Root,
and the wrapper's exact string comparison returned success:

```text
SLH-DSA ACVP parser positive suite: PASS (16 cases)
SLH-DSA ACVP parser negative suite: PASS (52 cases)
SLH-DSA ACVP parser runtime gate: PASS (68 cases)
WRONG-ROOT-SPOOF: EXACT-OUTPUT-GATE-ACCEPTED
```

Thus the combined static mapping and output checks can green without executing ParserTests. This is
a valid Lake configuration, not malformed text; the build log shows `Built Wrong.Root` and a newly
built `slhdsa_acvp_parser:exe`, so it is not a stale-binary artifact.

The parser did correctly reject fourteen ordinary Lake mutations: block/line-commented, ordinary-
string, and raw-string mappings; missing/wrong/duplicate target; duplicate root; incomplete or
non-immediate mapping; extra root token; and malformed block-comment, quoted-string, and raw-string
state. The exact r6 four-root permutation now parses as parser-to-C13 and is rejected. Those cases
do not cover active command expansion versus unexpanded quoted command syntax.

## S01-R7-002 reproduction: trailing blank output is normalized away

The live executable's raw stdout is 154 bytes and three newline-terminated lines. The captured
expected shell string is 153 bytes because command substitution removes the final LF. C13, smoke,
an extra nonblank line, and a missing line were independently rejected. A nonzero subprocess was
also rejected while its stderr remained visible, matching the wrapper's intended status/stderr
behavior.

However, command substitution removes *all* trailing newline characters, not exactly the ordinary
final one. This direct reproduction used the wrapper's expected value and equality semantics:

```text
producer bytes: 156
captured bytes: 153
expected bytes: 153
TRAILING-BLANK-MUTATION: ACCEPTED
```

The producer printed the expected string followed by three LF bytes: the normal third-line
terminator plus two additional blank-line terminators. `actual="$(producer)"` normalized all three
away, so `[[ "$actual" == "$expected_parser_stdout" ]]` succeeded. One or any number of terminal
blank records can therefore pass despite the documented exact-three-lines/no-extra-line rule. The
helper's in-memory extra-nonblank self-test does not exercise capture normalization.

## Authority, provenance, parser, and complete regression gates

Both optional upstream checkouts were present and clean:

```text
/tmp/slhdsa-s01-acvp-server
  HEAD 975de31eb83d87039ec88934fdc47d8c312b892d
  exact tag v1.1.0.43

/tmp/slhdsa-s01-acvp-protocol
  HEAD 892fd14710f3a7edbea230d0aecc5511e0257f8e
```

Real-sibling docs-only validation and checkout-backed provenance both passed. The latter verified
all nine committed artifacts, all fifteen server artifacts, protocol source/composite evidence,
full-suite counts `12/120`, `72/624`, and `36/504 (+72/-432)`, plus 144 pre-hash cells with 24
positive cells. Offline provenance also passed.

The direct parser output was exactly 16 positive, 52 negative, and 68 total cases. Complete
checkout-backed `validate.sh` passed:

```text
repository build       3,007 jobs
HashSig build          2,744 jobs
HashSigTest build      2,743 jobs
dependency probe       8 public/root resolved; 13 private/false rejected
parser runtime         16 + 52 = 68
policy fixtures        31 exact historical findings
HashSig inventory      680 owned constants; exact standard union plus confined sorryAx
compiled IR fixture    ordinary and IR surfaces rejected; sentinel absent
generated umbrella     no update necessary
isolation and KATs     passed
```

The warnings were the documented repository `sorry` warnings and absent-native-backend stubs.
Running `./scripts/update-lib.sh` explicitly afterwards reported “No update necessary” for all nine
generated surfaces.

Independent syntax checks parsed both Python files, thirteen duplicate-aware JSON files, all
fourteen JSONL rows, and every Bash script. `git diff --check` passed. A separate scan covered 67
active files under all three S01 roots and found no missing final LF, terminal blank line, internal
tab, non-excluded trailing whitespace, symlink/special entry, Python bytecode, or `__pycache__`.
Tracked and untracked scope queries again found no `HashSig/**` change.

The exact matrix pins after all tests were:

| Matrix | SHA-256 |
|---|---|
| `assumptions.csv` | `17741a24d719d95f879761cc32813837e61c48dc511ddd85e2c0e15501aa5de4` |
| `coverage.csv` | `0b82e0b42197a332b35b228a1ad3b641d92411c7ba5345e8179ceba68962928c` |
| `decisions.csv` | `12d0615301f5bf5e9829a0f976da94a043855e1d544cc7b4c11f7fc98d9129ac` |
| `declarations.jsonl` | `83165d2d46c4adc710bd33da9a5eca74432da92c843641734643095daea9d00a` |
| `fips205-profile.json` | `c833c36b33951e3b76fcf344e282cb26a37317f115b425eb776dfcdc1a23eeb5` |
| `proof-obligations.csv` | `3a043967b04a1b153cce40d472170d6d754b6f531d4ee618825d52cd79901314` |
| `sp800-230-ipd-profile.json` | `77ee7c4f0e872f2f2f31c830a14f4d90d63c55d260a0f3aaa3ac0e4aec92d26e` |
| `tcb.csv` | `086bc8e1afaa0b4f7a77a2fe8bdb5a40666fbf55bd3f019b707c6e7e84976e7d` |

## Report and administrative audit

The canonical TeX line contains the actual `\texttt{main}` command and no internal tab. A focused
tab mutation was rejected by active-scope hygiene. Every immutable review retained its exact hash.
Building with `latexmk` from `docs/slhdsa/report` into
`/tmp/slhdsa-s01-r7-independent-tex` produced a five-page, 282,640-byte PDF with resolved
bibliography and only minor overfull-box warnings. `pdftotext` contains `transitive root main` and
contains no `extttmain` variant. S01-R6-003 is therefore fully repaired.

Before authorship, README, plan, session records, review index, report, findings, and matrices
consistently recorded r0 through r6 as failed, r7 pending, and S02 blocked. F-044 through F-047 were
pending review; F-015/F-016 remained open; COV-005 remained missing/S10/pending. TCB-009 and F-018
continued to disclose the incomplete manual inventory. I found no new construction, conformance,
certificate, or security overclaim. The narrower semantic-source/Lake and exact-output claims are
incorrect for the counterexamples above.

## Prior-finding disposition

S01-R5-001's live-data defect is repaired: the current rows use accurate typed identities and the
current call graph is exact. S01-R6-001 is only partially repaired. Ordinary comments, malformed
state, namespaces, nonexistent public names, and external visibility are handled, but an unexpanded
command quotation can still stand in for a claimed active private declaration while the actual
helper has another declaration kind and line. F-045 must remain pending.

S01-R6-002 is also only partially repaired. The exact r6 comment-shadow permutation and ordinary
wrong-output cases are rejected, but command quotation/macro expansion can make the static Lake
result disagree with the active target; a wrong target printing the expected records then passes.
Trailing blank records also survive command-substitution normalization. F-046 must remain pending.

S01-R6-003 is repaired: source, tab hygiene, TeX build, and extracted PDF text all pass.

The r5 reviewer passed every other repaired authority, FIPS-profile, identity, matrix,
descriptor-walker, parser API, provenance, quantitative, license, sample-state, hygiene, build, and
TeX surface. R7 leaves the ACVP sources unchanged, and I reran all corresponding current gates. I
found no regression on those surfaces. That does not waive the two r7 findings.

## Findings

### S01-R7-001 — MEDIUM — command quotations bypass both claimed active-source and active-Lake semantics

`lex_lean` is comment/string-aware but not syntax-quotation-aware. The declaration and Lake parsers
then interpret selected tokens at the start of a line as active commands without asking whether the
tokens occur under an unexpanded `` `( ... ) `` quotation. This caused two validated semantic
false positives: an unexpanded quoted private definition was certified as the exact active source
anchor, and an unexpanded quoted expected Lake stanza was certified while macro expansion
registered `Wrong.Root`.

The Lake case composes with the wrapper: the wrong executable printed the expected 16/52/68 text
and passed, so the complete relevant gate can omit ParserTests execution. Severity is MEDIUM because
this is test-only assurance and does not affect construction/security code, but it recreates the
substitute-executable failure that r7 claims to close and makes private inventory anchors misleading
after a consistent pin update.

Repair should use elaborated declaration metadata for private anchors and the elaborated Lake target
configuration for executable roots, or conservatively reject every unsupported quotation/macro
surface before making semantic claims. Add the exact unexpanded-private/active-opaque and
unexpanded-expected/active-macro-root mutations. The runtime gate should be tied to the verified
active target rather than treating spoofable text as independent proof of module identity.

### S01-R7-002 — LOW — command substitution accepts extra terminal blank lines

`parser_stdout="$(lake exe slhdsa_acvp_parser)"` strips every trailing LF before the helper compares
strings. The reproduced 156-byte output (expected records plus extra terminal blank lines) became
the same 153-byte string as normal output and passed. This directly contradicts the documented
“exactly three records with no extra line” rule, although it cannot by itself replace a non-parser
output with the expected nonblank records. That narrower impact warrants LOW severity.

Repair should capture stdout in a temporary regular file while preserving the subprocess exit code
and visible stderr, then byte-compare it to the three expected records with exactly one final LF.
Add one and multiple terminal blank-line mutations through the real capture path, not only direct
function arguments.

## Verdict rationale

The current declaration facts, current Lake mapping, current external visibility, parser runtime,
authority/provenance corpus, builds, policy audit, KATs, hygiene, and report all pass. The report-tab
finding is fixed, and no ACVP or construction/security source changed.

Nevertheless, the repaired semantic gates can certify quoted commands that are not active, a valid
wrong Lake root can spoof the expected runtime text and green the relevant gate, and extra trailing
blank lines evade the claimed exact-output comparison. Under the mandatory zero-issue threshold,
S01 r7 **FAILS** independent review. S01 remains blocked and S02 must not start. No implementation
repair, commit, or PR was made.
