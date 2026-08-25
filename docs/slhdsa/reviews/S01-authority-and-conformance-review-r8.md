# S01 adversarial re-review r8 — quotation-safe target and byte-exact runtime gates

Verdict: **FAIL**

Reviewer: fresh independent S01 r8 review sub-agent; not an S01 implementer or any prior S01
reviewer

Reviewed tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r8 tree

Date: 2026-08-24

Independence statement: I did not design, implement, or repair S01 and did not conduct r0 through
r7. The implementation remained frozen. All independent mutation projects and generated output
were confined to `/tmp`; this artifact is my only repository edit. I made no commit or PR.

## Verdict summary

R8 repairs the two exact r7 examples. The frozen-source checker rejects active command quotations
and the configured metaprogramming command families before making declaration claims. The exact
quoted line-377 private-definition/active line-378 private-opaque mutation elaborates, but its
quoted source anchor is rejected. Lake's translated configuration exposes `Wrong.Root` in the exact
r7 macro project, and the authoritative validator rejects it. The live parser emits exactly three
LF-terminated records, 154 bytes total; byte comparison rejects missing, reordered, duplicated,
space-altered, NUL-extended, nonblank-extended, nonterminated, and terminal-blank variants.

One current configuration-provenance defect nevertheless remains. The translated Lake validator
requires the executable name and root module but does not constrain the executable's effective
source directory. A disposable project retained the expected root name while selecting
`WrongSrc`; Lake consequently compiled the alternate file under that directory rather than the
pinned repository `ParserTests.lean`. The alternate program emitted the exact expected 154 bytes,
so both the configuration check and runtime byte check accepted it. This is finding S01-R8-001.

The acceptance threshold is zero findings. S01 r8 therefore fails, F-048/F-049 cannot yet be
accepted as a complete repair, S01 remains blocked, and S02 must not start.

## Frozen state and immutable history

Before reviewer authorship, the branch was `codex/sphincsplus-formalization` at
`f1853af40da1efa11a71c2d7011996eebdbf6938`. Status contained only the four-line tracked
`lakefile.lean` executable addition and untracked files below `HashSigTest/SLHDSA/ACVP/**`,
`docs/slhdsa/**`, and `scripts/slhdsa/**`. Separate status and diff queries found no `HashSig/**`
source change and no S02 work.

The r8 checklist was 5,537 bytes, 85 lines, had SHA-256
`725b7ff7fc59bf0756496795af122ed8b51c3911fdd0a50e5bf069c2f2035a16`, and contained exactly one
canonical `PENDING` before authorship. The immutable S01 review chain reproduced exactly, with one
canonical `FAIL` in every file:

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

R7 remained exactly 23,261 bytes and 413 lines. The three ACVP Lean sources remained frozen:

| Source | SHA-256 |
|---|---|
| `StrictJson.lean` | `20f9aff3f5339e54d7fc5e148fadb0e37d8f4b4bd816938f0a81b4cf7b087089` |
| `Schema.lean` | `3ccab70a3ff8e2e6f39cc09e4b2296fad035267b4def0e6c8bb002062f5733a0` |
| `ParserTests.lean` | `1a56fd4fef9880a464583749d27e14840b2f48afc81fe007db473bb167585cd5` |

The exact eight-file matrix path set and byte pins passed the normal harness. In particular,
`declarations.jsonl` remained 12,938 bytes with SHA-256
`83165d2d46c4adc710bd33da9a5eca74432da92c843641734643095daea9d00a`; no construction,
implementation-conformance, certificate, or security claim was added.

Administrative inspection before authorship found r0 through r7 `FAIL`, r8 `PENDING`, F-044
through F-049 `REMEDIATED-PENDING-REVIEW`, F-015/F-016 and F-018 still open, COV-005 still
missing/S10/pending, and S02 blocked. No S01 self-certification was present.

## Completed independent checks

### Source declarations and visibility

The focused normal checker passed and reported 23 rejected source/token/static-Lake mutations and
five rejected translated-Lake mutations. Independent probes additionally established:

- comments, documentation comments, ordinary strings, and raw strings do not create declarations;
- ordinary root and namespaced private declarations retain the expected namespace and visibility;
- multiline, nested, and unclosed backtick-parenthesis quotations fail closed;
- `macro`, `macro_rules`, `syntax`, `syntax_rules`, `elab`, `elab_rules`, `command_elab`,
  `term_elab`, `run_cmd`, and `run_tac` families fail closed, including a qualified `elab` leaf;
- the complete r7 Schema mutation has the quoted private definition at line 377 and active private
  opaque implementation at line 378, elaborates successfully, and is rejected by the source layer.

`lake build HashSigTest` passed with 2,743 jobs. The post-build external probe resolved the exact
eight public/root names, rejected the exact thirteen private/false names, and rejected the dynamic
`Does.Not.Exist` substitution.

### Lake translation

An independent translation of the live project used an initially absent file under `/tmp`. It
produced an ordinary 1,502-byte TOML file whose unique parser entry mapped
`slhdsa_acvp_parser` to `HashSigTest.SLHDSA.ACVP.ParserTests`. Local Lake help confirms that `-R`
re-elaborates configuration rather than trusting configuration oleans.

The exact r7 disposable macro project translated the active root as `Wrong.Root`. The literal
defense-in-depth parser still observed the unused quoted expected stanza, while the translated-data
validator correctly rejected the actual root. Independent translation-function probes rejected
nonzero command status, timeout, missing output, directory output, symlink output, invalid TOML,
missing/wrong-type executable arrays, non-table entries, missing/non-string names or roots, wrong
root, and duplicate names. A Lake project with a duplicate executable name failed during
configuration elaboration. A target with Lake's default omitted root translated without a root and
was rejected. A stale executable built from `Wrong.Root` was rebuilt from the newly translated
expected root after the configuration changed.

These successes do not cover the effective-source-directory mismatch in S01-R8-001.

### Parser runtime bytes

Direct runtime produced exactly these measurements:

- 154 bytes;
- three records and three LF bytes;
- SHA-256 `0e726bc985fa93c02e34c66d79b5b3a52947cecd93e0803a611a9be3ab581c07`;
- positive 16, negative 52, and total 68.

The independent expected file was byte-identical. Direct byte comparison rejected one and multiple
extra terminal blank lines, no final LF, extra nonblank data, leading or trailing spaces, a terminal
NUL, a missing line, reordered lines, and a duplicated line. A nonzero producer was rejected even
when it wrote all 154 expected bytes, while stderr remained separate and observable for a
successful producer. Static inspection confirmed that parser stdout is redirected directly to an
ordinary file inside one `mktemp` directory, never stored in a shell variable, and that one EXIT
cleanup covers both the parser and later policy-fixture temporary roots.

### Authority, schema, and ordinary hygiene regression

The real-sibling docs-only gate passed. It verified 18 local reference-manifest entries under
`/home/alh/SPHINCS`, all exact authority/profile/source/matrix records, the descriptor-relative
active-tree checks, and the complete normal mutation groups. Offline provenance passed for nine
committed artifacts, fifteen pinned server artifacts, exact full-suite counts 12/120, 72/624, and
36/504 split 72 positive/432 negative, and 144 pre-hash cells with 24 positive cells.

Manual reassessment found the authority distinctions, exact twelve-set FIPS profile, six-set
non-normative IPD profile, one-set legacy profile, sample-only qualification, NIST notice,
final-LF normalization, strict duplicate-preserving parser, typed schema boundaries, declaration
rows, COV-005 limitation, findings, TCB, and report language consistent with the previously
reproduced r5/r6/r7 dispositions. Active status contained no symlink, special entry, Python debris,
or unauthorized path in the normal harness result.

After the confirmed blocking finding, the reviewer was directed to finish this artifact without
starting further tests. Checkout-backed optional provenance, complete full validation, explicit
update-lib, and TeX recompilation are therefore not represented as independent r8 reviewer passes;
the implementer's recorded results for them do not change this verdict.

## Prior-finding dispositions

The exact r7 quotation example is repaired by the conservative frozen-source grammar. The exact r7
`Wrong.Root` macro example is repaired by translated configuration, and terminal newline
normalization is repaired by ordinary-file capture and comparison. The live current tree and the
focused reproductions for those examples passed.

R8 nevertheless does not establish that the module name in translated configuration selects the
byte-pinned repository module. The source-directory field can redirect that same module name to an
alternate file. Consequently F-048's configuration/runtime-source portion remains incomplete even
though its exact `Wrong.Root` reproducer is fixed. F-049's exact terminal-LF repair passed every
completed independent probe but cannot be administratively accepted while S01 as a whole fails.

All r0--r6 repairs previously reproduced by the exhaustive r5/r6/r7 reviews remain unchanged at
their frozen source and matrix pins. This review found no separate regression in those current
surfaces, but the S01 findings remain pending until a future zero-finding review.

## Finding

### S01-R8-001 — MEDIUM — translated executable validation does not bind the effective source directory

`validate_translated_lake_data` inspects each translated executable's `name` and `root`, requires
unique names, and requires the expected parser root. It does not validate the executable-level
`srcDir`, the package-level inherited source directory, or another field that can alter which file
supplies the named root module.

The independent project at `/tmp/s01-r8-lake-srcdir-bypass` contained:

- a package configuration with the expected executable name and expected root module, plus target
  source directory `WrongSrc`;
- a repository-relative `HashSigTest/SLHDSA/ACVP/ParserTests.lean` whose output was deliberately
  distinguishable;
- an alternate `WrongSrc/HashSigTest/SLHDSA/ACVP/ParserTests.lean` that emitted the three expected
  records.

Lake's translated parser record was exactly the expected name and root plus
`srcDir = "WrongSrc"`. Both production configuration validators accepted that record. Lake then
built the named module from `WrongSrc` and ran it, producing exactly 154 bytes with the expected
SHA-256 and 16/52/68 records. The production-equivalent file comparator accepted those bytes. A
second disposable project confirmed that a package-level inherited `srcDir` has the same source-
selection effect while the executable record itself still contains only the accepted name/root.

The impact is a build-target provenance mismatch. The normal source pin and declaration checks can
inspect the repository `ParserTests.lean`, while the runtime target compiles a different file with
the same module name. Exact stdout verifies behavior of the selected executable but cannot identify
which file was compiled. Therefore the current combined gate does not justify its claim that the
pinned parser module supplied the accepted runtime result.

Repair must fail closed over the effective source selection, not only the target name. At minimum,
validate both package-level and executable-level source-directory fields against the repository
root and reject an unexpected override. Prefer additionally checking Lake's resolved build input or
trace so the parser module's actual source path and bytes equal the pinned
`HashSigTest/SLHDSA/ACVP/ParserTests.lean`. Add the exact `WrongSrc` target-level case and the
package-inherited case as regression tests, each using the expected module name and expected runtime
records. After repair, rerun every full and optional gate and assign another fresh independent
reviewer.

## Verdict rationale

R8 materially improves source-quotation handling and output-byte fidelity. The exact r7 examples,
live parser counts, source visibility, normal authority/provenance checks, and completed focused
mutations all reproduce as described.

However, translated configuration currently proves only the logical root name, not the source file
that supplies that root. The disposable source-directory case was accepted end to end while the
pinned parser file was not compiled. Under the mandatory zero-issue threshold, S01 r8 **FAILS**.
S01 remains blocked and S02 must not start. No implementation repair, administrative promotion,
commit, or PR was made.
