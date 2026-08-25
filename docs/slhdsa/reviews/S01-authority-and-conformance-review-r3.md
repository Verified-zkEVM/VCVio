# S01 adversarial re-review r3 — authority and pinned conformance anchors

Verdict: **FAIL**

Reviewer: independent S01 r3 authority/conformance review sub-agent; not an S00/S01 implementer or
an S01 r0/r1/r2 reviewer

Reviewed commit/tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r3 tree

Date: 2026-08-24

Independence statement: I did not design, implement, or repair S01, and I did not perform S01 r0,
r1, or r2. The implementation remained frozen. All probes, mutation trees, derived data, and TeX
output were confined to `/tmp/slhdsa-r3-review.spmjro`; this verdict is my only repository edit.

## Required checks

- [x] Immutable S01 r0/r1/r2 reviews remain byte-identical and canonically `FAIL`.
- [x] The repair remains within S01 scope and changes no `HashSig/**` construction/security file.
- [x] Literal deprecated-ID and whitespace scanning covers ordinary files under the complete
  documented S01 test scope, including files outside the ACVP subtree.
- [x] The two r2 outer-scope deprecated-ID mutations and new-file terminal-blank-line mutation reject.
- [ ] The recursive scan covers every permitted filesystem entry and the current-ID occurrence
  policy cannot be bypassed syntactically; see S01-R3-002.
- [x] The exact 33-line/15-path current-ID manifest rejects duplicate/extra literal occurrences,
  same-line contradictions, exact line changes, and the r2 two-ID Schema reproducer.
- [x] The complete COV-014 contradiction and missing/duplicate/field mutations of every named S01
  row reject.
- [ ] Extra conflicting S01-relevant profile rows reject; see S01-R3-003.
- [x] Parser tests are currently described only as parser/schema-format validation evidence, not as
  implementation-conformance, construction, or security evidence; COV-005 remains missing/S10.
- [x] The old parser assurance phrase rejects and the exact qualified replacement is required.
- [x] The report says six-profile matrix and agrees with the six exact canonical scope rows; a
  six-to-five mutation rejects.
- [x] F-036/F-037 and all administrative surfaces record r2 FAIL, r3 PENDING, and S02 blocked.
- [ ] All controlling FIPS profile metadata and normative API prose are exact-record validated; see
  S01-R3-001.
- [x] Existing provenance, parser runtime, build, ordinary hygiene, and report gates pass.

## Frozen state and history

Before writing this verdict:

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

The tracked diff is only the four-line `slhdsa_acvp_parser` declaration in `lakefile.lean`. All
untracked S01 implementation paths are under the three declared S01 roots. There is no change under
`HashSig/**`; the documented 22-file source manifest reproduced as
`d6b782daf07d6cbd4a9a3542361ff22176db139d14e98911abe512a9546101b7`.

The r3 artifact had exactly one canonical `PENDING` verdict before authorship. The immutable S01
failures remain exact, each with one `FAIL` verdict:

```text
ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76  r0
9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec  r1
3a8e5afe4d1b17c0b29febd18f993442f41e4f3137a994badce7d54946420ad8  r2
```

No historical review or finding was rewritten.

## Prior-finding dispositions

| Prior finding | Independent r3 disposition |
|---|---|
| S01-R0-001 | **The cited manifest defects remain repaired, but a separate controlling FIPS profile is not fail-closed.** Exact reference-manifest FIPS/server/protocol/compatibility/SP records and the SP profile reject prior mutations. `fips205-profile.json` accepts false authority and normative randomness text; see S01-R3-001. |
| S01-R0-002 | **Literal current content and exact r2 reproducers are repaired; the scope guard remains bypassable.** The two identities are currently distinct. Split/constructed spellings and directory symlinks escape the scanner; see S01-R3-002. |
| S01-R0-003 | **Repaired.** The pinned draft is `draft-livelsberger-acvp-slh-dsa-01`, dated 25 June 2024, and bibliography/gates agree. |
| S01-R0-004 | **The four JSON EOF defects and ordinary-file coverage are repaired, but unsupported filesystem entries are omitted.** Current regular files are clean; directory and broken symlinks pass; see S01-R3-002. |
| S01-R1-001 | **The exact reference-manifest FIPS record is repaired; the FIPS profile artifact is not complete-record checked.** Genuine sibling bytes reproduce, but false profile authority/API text passes; see S01-R3-001. |
| S01-R1-002 | **Exact scope and literal active associations are repaired.** All 33 registered lines are correct and literal additions reject. Syntactic reconstruction still passes; see S01-R3-002. |
| S01-R2-001 | **Every exact r2 reproducer rejects, but the broader repair is incomplete.** Outer existing/new deprecated IDs, terminal blank, exact Schema contradiction, and COV-014 triple contradiction reject. Symlink/syntactic bypasses and an extra conflicting FIPS conformance row pass; see S01-R3-002/003. |
| S01-R2-002 | **Current assurance language and count are repaired.** ParserTests has the schema-only qualification, COV-005 is missing/S10/pending, and the report has six profiles. ASM-011 says future conformance evidence and explicitly denies current implementation-conformance evidence, so it is not misleading in context. The matrix gate can accept a new contradictory current conformance row; see S01-R3-003. |

The zero-finding rule therefore does not permit acceptance.

## Authority, provenance, and sample reproduction

Independent byte/PDF-text reproduction gave:

```text
FIPS 205: 1055752 bytes
8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d
Published: August 13, 2024

SP 800-230 IPD: 282069 bytes, 12 pages
62d092f787a1f79260454bf332b642ff3b5b73dbcce2678a133a1406065e452e
Initial Public Draft; public-comment period begins 2026-04-13
```

FIPS Table 2 independently yielded the six paired SHA2/SHAKE tuples
`(n,h,d,h',a,k,lg_w,m,category,pk,sk,sig)`:

```text
128s (16,63,7,9,12,14,4,30,1,32,64,7856)
128f (16,66,22,3,6,33,4,34,1,32,64,17088)
192s (24,63,7,9,14,17,4,39,3,48,96,16224)
192f (24,66,22,3,8,33,4,42,3,48,96,35664)
256s (32,64,8,8,14,22,4,47,5,64,128,29792)
256f (32,68,17,4,9,35,4,49,5,64,128,49856)
```

The 255-byte context limit and pinned mode/randomness/OID/grammar evidence also reproduced. The IPD
yielded the six separate SHA2/SHAKE category 1/3/5 rows:

```text
128-24 (16,22,1,22,24,6,2,21,1,32,3856)
192-24 (24,21,1,21,25,9,3,32,3,48,7752)
256-24 (32,21,1,21,25,12,2,41,5,64,14944)
```

Its cap is exactly `2^24` signatures/key. It remains a non-normative Initial Public Draft, not a
FIPS Table-2 profile or general-use approval claim.

The optional checkouts were clean and exact:

```text
ACVP-Server     975de31eb83d87039ec88934fdc47d8c312b892d  v1.1.0.43
ACVP protocol   892fd14710f3a7edbea230d0aecc5511e0257f8e
```

Official GitHub API results on 2026-08-24 showed issue #469 open and PR #471 open/unmerged; the PR
still says sample JSON was not regenerated. Direct tag references gave v1.1.0.43 =
`975de31eb83d87039ec88934fdc47d8c312b892d` and v1.1.0.38 =
`85f8742965b2691862079172982683757d8d91db`. The latter is only a server-format boundary.

An independent strict-JSON/hash derivation, not importing either production checker, verified all
15 server artifact size/hash records, the 2,258-byte protocol root hash
`d9c7088a6bb0531b2a5ab65104f467a7abe0e5ffc4d22f8ec1b7b90978d7d061`, all 15 section records,
and composite `bc38ec528afcaa7f6a8155fd75a7612166203c789a540c0ac42e860a04c40a54`.
It also verified the complete NIST notice/acknowledgement/modification notice, each five normalized
copy equals upstream plus exactly one LF, and both bounded projections regenerate at:

```text
sigGen (19,157),(20,164),(31,271),(55,469),(56,476),(67,583)
sigVer (19,253),(19,256),(19,257),(19,258),(20,268),(31,422)
```

The independent full prompt/result join reproduced:

```text
keyGen 12/120; sigGen 72/624; sigVer 36/504 = 72 positive + 432 negative
```

The exact ordered 12-by-12 matrix has 144 cells and 24 positive external/preHash cases. Every set
has two positives/ten gaps; SHA3-224 and SHAKE-128 have none. The committed cells equal the
independent derivation. Negative cases are not used as OID/digest-binding evidence.

These accurate current bytes do not cure S01-R3-001's fail-closed profile gap.

## Parser and current assurance language

Manual inspection confirmed `StrictJson.lean` is a small Lean 4.32.2 JSON-parser adaptation. Local
upstream source confirms Gabriel Ebner/Marc Huisinga attribution; the adaptation retains it and adds
Nicolas Consigny's dated modification attribution. Recursive helpers are private, decoded keys are
checked before insertion at every depth, and EOF is required.

The schema enforces exact keys/discriminants, positive globally unique IDs, nonempty groups/tests,
exact joins, twelve parameter rows, seed/key/signature widths, 1..8192-byte messages, 0..255-byte
external contexts, conditional interface/mode fields, deterministic randomness, and twelve ACVP
hash names. SigVer accepts only exact and plus/minus-one sample lengths and requires exact width for
a positive result. No new `sorry`, axiom, unsafe/extern, initializer, runtime override, or
production HashSig import was found.

The native suite passed 16 positive and 47 negative cases. A separate probe accepted an 8,192-byte
message and rejected zero/8,193-byte messages, object/array trailing commas, a deep
escaped-equivalent duplicate, and trailing junk.

Current `conformance evidence` occurrences are future target language, historical r2 text, or
explicitly schema-only. The canonical surfaces say:

```text
ParserTests: parser/schema-format validation evidence only; not implementation-conformance,
             construction, or security evidence
COV-005: missing / required / S10 / pending
ASM-011: Schema and future conformance evidence; note explicitly denies current implementation-
         conformance, construction, or security evidence
```

Restoring the old unqualified parser phrase failed the normal gate for the intended reason.
Changing the report's exact `six-profile` sentence to `five-profile` also failed; `scope.md` parses
to exactly six ordered rows.

## Occurrence, matrix, and filesystem evidence

Independent scanning, excluding only the three hash-locked S01 failures, found:

```text
33 normalized current-ID lines / 15 paths
20 six-set-ID occurrences / 19 legacy-ID occurrences
```

The exact r2 mutations gave:

```text
deprecated ID appended to outer Sha2KAT.lean                    FAIL
deprecated ID in a new outer file                               FAIL
terminal blank in a new outer file                              FAIL
exact contradictory two-ID Schema comment                      FAIL
COV-014 claim/evidence/notes triple contradiction               FAIL
old parser assurance phrase                                    FAIL
report six-to-five count                                       FAIL
```

Direct production-validator probes changed every field or removed each of COV-005/009/010/014,
PO-014, ASM-007/011, D-001/002, and TCB-006: all 120 mutations rejected. A duplicate and missing
COV-005 also failed through the normal on-disk gate. The accepted mutations below show these
positive results are incomplete.

## Nominal gates

All nominal commands passed on the frozen pre-authorship tree:

```text
offline provenance
  PASS: 9 committed; 15 server; 12/120,72/624,36/504(+72/-432); 144/24
optional server/protocol provenance
  PASS: exact artifacts, copies, projections, counts, protocol composite
lake build HashSigTest
  PASS: 2743 jobs
lake exe slhdsa_acvp_parser
  PASS: 16 + 47 = 63
./scripts/update-lib.sh
  PASS: no update necessary
./scripts/slhdsa/validate.sh --docs-only
  PASS
./scripts/slhdsa/validate.sh
  PASS: 3007-job repo, 2744-job HashSig, 2743-job HashSigTest, parser, semantic policy,
        ordinary/IR fixture, umbrella, isolation, and both KATs
strict JSON/JSONL; Python compile; Bash syntax; direct UTF-8/whitespace; git diff --check;
scope; 22-file HashSig composite
  PASS: 63 active regular files; only exact immutable S00 r5 hard breaks excluded
latexmk to /tmp
  PASS: five-page PDF; minor overfull boxes only
```

Warnings are the documented native stubs and inherited/admitted proofs; none is introduced by S01.
Administrative surfaces honestly record r0/r1/r2 FAIL, F-030..F-037 remediated pending review, r3
PENDING before this verdict, F-015/F-016 OPEN, COV-005 missing/S10/pending, and S02 blocked. Current
public data is sample JSON, not approved vectors, a certificate, or implementation conformance.

## Findings

### S01-R3-001 — HIGH — the normative FIPS profile artifact is not complete-record validated

`fips205-profile.json` controls Table 2 and Sections 10/11. `check_fips_profile()` validates rows,
selected API fields, OIDs, and grammars, but not profile `authority`, exact top/API key sets,
`randomness`, or `other_prehashes`. The provenance checker does not read it.

In two isolated exact trees I changed only this profile:

```text
authority: FIPS 205 final, Table 2, Sections 10 and 11 -> untrusted draft

randomness: hedged n-byte addrnd; deterministic PK.seed opt_rand
         -> deterministic all-zero opt_rand; hedged signing unsupported
```

For both:

```text
SLHDSA_REFERENCE_ROOT=/home/alh/SPHINCS ./scripts/slhdsa/validate.sh --docs-only
SLH-DSA harness check: PASS
SLH-DSA ACVP provenance: PASS (...)
SLH-DSA docs-only validation: PASS
```

The genuine sibling FIPS PDF was present and hash-verified. This is an unchecked normative
profile/classification surface, not absent evidence. The exact reference-manifest FIPS record does
not make contradictory fields in the separate canonical profile safe.

### S01-R3-002 — MEDIUM — recursive scope and current-ID guards have filesystem/syntactic bypasses

`load_active_s01_files()` uses `Path.rglob("*")` and keeps only `path.is_file()`. It neither rejects
unsupported entries nor descends into a directory symlink; a broken symlink is silently omitted.
I added a directory symlink under `HashSigTest/SLHDSA/` to a target whose file contained the exact
deprecated ID. The normal gate passed. A separate broken `ignored-note.md` symlink also passed.

The exact-line manifest can also be bypassed by reconstructing identities across lines or string
fragments. Both additions compiled with Lean and passed the normal docs gate:

```text
-- SP800-230-IPD-
-- 6SET is the single current-code set; LEGACY-SHA2-128-
-- 24 is the six-set profile.

private def contradictoryProfile :=
  "SP800-230-IPD-" ++ "6SET is the single current-code set; LEGACY-SHA2-128-" ++
  "24 is the six-set profile"
```

The ledger disclaims general natural-language understanding, but r3 explicitly requires split,
newline, path-alias, and syntactic bypass testing. These examples construct the exact identities;
they do not require a general prose classifier. Literal current content is correct, but the claimed
fail-closed scope/association policy is incomplete.

### S01-R3-003 — MEDIUM — an extra contradictory FIPS conformance row passes

The named rows and extra six-set/legacy rows are gated. Another S01-relevant `FIPS205-12`
conformance row is not. I appended this schema-valid unique row in an isolated tree:

```text
COV-015,FIPS205-12,conformance,Parser suite proves full ACVP implementation conformance,
NIST ACVP,FIPS205 revision,HashSigTest/SLHDSA/ACVP/,covered,required,Parser runtime PASS,
S01,pending,Complete implementation conformance established
```

The normal docs gate passed completely. COV-005 remained byte-identical, missing, S10-owned, and
pending, so the same matrix contained opposite claims. This is exactly an extra conflicting
S01-relevant profile row and violates the complete structured-row/no-conformance-overclaim guard.

## Verdict rationale

R3 fixes every literal r2 reproducer. Current authority bytes, license, projections, counts, 24
positive cells, parser behavior, schema-only language, six-profile count, ordinary-file hygiene,
builds, and report reproduce. ASM-011 is adequately future-qualified, and no current
construction/security/conformance claim was found.

However, the normal gate accepts false normative FIPS-profile authority/API text, omits symlinked
or broken entries and syntactically reconstructed identities, and accepts a row claiming current
implementation conformance while COV-005 remains missing. The protocol permits no findings. S01 r3
therefore **FAILS** independent review, and S02 must not start. No repair was made.
