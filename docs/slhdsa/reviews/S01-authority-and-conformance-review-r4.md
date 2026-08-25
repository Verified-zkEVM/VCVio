# S01 adversarial re-review r4 — authority and pinned conformance anchors

Verdict: **FAIL**

Reviewer: independent S01 r4 authority/conformance review sub-agent; not an S01 implementer or an
S01 r0/r1/r2/r3 reviewer

Reviewed commit/tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r4 tree

Date: 2026-08-24

Independence statement: I did not design, implement, or repair S01, and I did not perform S01 r0,
r1, r2, or r3. The implementation remained frozen. All probes and disposable copies were confined
to `/tmp/slhdsa-r4-review.GUdc7N`; this verdict is my only repository edit.

## Required-check status

- [x] The branch, HEAD, tracked/untracked scope, and absence of a `HashSig/**` source change were
  independently confirmed.
- [x] Immutable S01 r0/r1/r2/r3 reviews remain byte-identical, canonically `FAIL`, and have the
  four handoff hashes. The r4 artifact was canonically `PENDING` before reviewer authorship.
- [x] The genuine sibling FIPS 205 PDF hash/size and the separate 5,059-byte canonical profile pin
  were independently reproduced. The profile's complete structured content was compared with the
  PDF's Table 2 and Sections 10/11.
- [ ] The planned independent on-disk FIPS-profile mutation suite was not completed before the
  review run was interrupted. Static inspection confirmed complete-record checks and built-in
  non-tautological mutations, but that is not recorded as completed end-to-end reproduction.
- [x] The exact eight-file matrix path, size, and SHA-256 set was independently enumerated and
  matched the checker constants.
- [ ] The planned independent on-disk matrix mutation suite was not completed before interruption.
- [x] The active-tree enumerator and its five built-in filesystem cases were inspected. Its stable
  symlink/special-entry checks are present, but an independent pathname-replacement probe found the
  local consistency defect S01-R4-001.
- [ ] Independent completion of every requested static linked-root/file/directory/broken-link/FIFO
  case was preempted. This does not negate the stronger confirmed pathname-replacement failure.
- [ ] Independent recomputation of the full literal-line manifest and normalized 20/19/1 counts,
  and every requested reconstruction mutation, was not completed before interruption. Code
  inspection confirmed the intended ASCII-alphanumeric normalization and exact historical
  exclusions.
- [x] The native 63-case parser suite and additional adversarial parser/schema probes passed for
  the production string-to-pair path. Two low-severity public API boundary issues were reproduced;
  see S01-R4-002 and S01-R4-003.
- [ ] Offline/optional provenance, the full build/validation stack, independent quantitative ACVP
  reproduction, comprehensive hygiene, and TeX were not rerun by this reviewer before interruption.
  Earlier implementer and historical-review results were read but are not represented here as
  independent r4 execution.
- [x] Administrative inspection before authorship found r0-r3 `FAIL`, r4 `PENDING`, S02 blocked,
  F-015/F-016 open, COV-005 missing/S10/pending, and no accepted construction, security, certificate,
  or implementation-conformance claim.

The verdict rule is zero findings. The incomplete checks cannot be treated as passes, and the
confirmed findings independently require failure.

## Frozen state and immutable history

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

The tracked diff is only the four-line `slhdsa_acvp_parser` executable declaration in
`lakefile.lean`. All untracked work is under the three declared S01 roots, and a separate status
query found no `HashSig/**` change. No S02 construction work is present.

The four immutable S01 failure artifacts reproduced exactly, each with one canonical `FAIL`:

```text
ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76  r0
9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec  r1
3a8e5afe4d1b17c0b29febd18f993442f41e4f3137a994badce7d54946420ad8  r2
bb84cb7380c9a5a1aa0c78018898389a7d1ac436dfa39caa987f170670542662  r3
```

The r4 checklist had one canonical `PENDING` verdict and SHA-256
`bc76d5a2c042c29cb7aa8e7e20a5e2c69366a24d4bfa1bbe6e5ff683cf48a785` before authorship.

## Independently reproduced authority and pin evidence

The genuine sibling authority and separate canonical profile measured:

```text
8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d
  /home/alh/SPHINCS/NIST.FIPS.205.pdf
1055752 bytes; PDF title: Stateless Hash-Based Digital Signature Standard; 61 pages

c833c36b33951e3b76fcf344e282cb26a37317f115b425eb776dfcdc1a23eeb5
  docs/slhdsa/matrices/fips205-profile.json
5059 bytes
```

Independent PDF text extraction reproduced all twelve ordered SHA2/SHAKE Table-2 rows, their
`n,h,d,h',a,k,lg_w,m`, category, public-key and signature sizes, the derived `4n` private-key size,
the 255-byte context bound, domain bytes and message grammars, the four displayed DER OIDs and
digest/category records, the other-approved-prehash rule, deterministic/hedged `opt_rand`
semantics, and all three exact SHAKE/SHA2 primitive grammar groups. The profile object matches this
evidence. Inspection found that r4 now requires exact top-level/API keys, authority, ordered rows,
OIDs, other-prehash text, randomness text, and primitive grammars, in addition to the raw byte pin.

The complete current matrix directory independently measured:

```text
assumptions.csv             2687  df234fee0acfe6b6d8750b46c8e424160948f2b6535f2dd249870987a3751f96
coverage.csv                3602  0b82e0b42197a332b35b228a1ad3b641d92411c7ba5345e8179ceba68962928c
decisions.csv               1368  12d0615301f5bf5e9829a0f976da94a043855e1d544cc7b4c11f7fc98d9129ac
declarations.jsonl         10970  9ce891e5712e0076f46aa446cb9cbb98893af3426483a055cdf7a823e8a337ea
fips205-profile.json        5059  c833c36b33951e3b76fcf344e282cb26a37317f115b425eb776dfcdc1a23eeb5
proof-obligations.csv       3368  3a043967b04a1b153cce40d472170d6d754b6f531d4ee618825d52cd79901314
sp800-230-ipd-profile.json  1504  77ee7c4f0e872f2f2f31c830a14f4d90d63c55d260a0f3aaa3ac0e4aec92d26e
tcb.csv                     3304  e9ba30d6280551573423d1da8b9e5127f75d48b929e4d78962aeeedd2365bdee
```

These are exactly the eight paths and pins embedded in `S01_MATRIX_PINS`. The comments accurately
say a future accepted session may deliberately update the pins; they do not claim a permanent
freeze.

## Parser/schema evidence

An independent helper, which made no repository edit, ran the native parser executable:

```text
lake exe slhdsa_acvp_parser
positive PASS (16); negative PASS (47); runtime PASS (63)
```

Additional runtime probes rejected literal/escaped-equivalent duplicates at top level, nested
objects, and objects inside arrays; trailing values/junk, trailing commas, and unterminated nesting;
zero- and 8,193-byte messages; sigVer signatures two bytes short/long; and forbidden conditional
fields. They accepted valid deep nesting, an 8,192-byte message, internal sigVer's exact fields,
and the pinned sigVer exact/one-byte-short/one-byte-long cases. Inspection also confirmed exact
keys/types/discriminants, positive and global ID uniqueness in both parsers, exact prompt/result
joins in the production path, all twelve rows/hash enums, exact widths, context 0..255, and the
interface/mode/determinism/randomness conditions.

The production `parseAndValidate` string path is protected by `StrictJson.parse` and by both typed
parsers. The lower-level public APIs have the narrower defects recorded below.

## Prior-finding dispositions

| Prior finding | Independent r4 disposition |
|---|---|
| S01-R0-001 | Current complete-record and profile validation code covers the cited authority fields. Independent end-to-end mutation completion was interrupted, so this review does not upgrade the inspection to an executed PASS. |
| S01-R0-002 | Current identifiers are distinct and the exact scope records remain present. Full independent r4 reconstruction-mutation completion was interrupted. |
| S01-R0-003 | The current bibliography/profile material retains the pinned 25 June 2024 `-01` identity on inspection. |
| S01-R0-004 | Current ordinary files inspected were clean and the scanner covers the broad test-support root. The stronger traversal consistency claim remains defective under pathname replacement; see S01-R4-001. |
| S01-R1-001 | Complete reference-manifest FIPS record and genuine sibling PDF checks remain present; the separate FIPS profile now also has complete structure and bytes pinned. |
| S01-R1-002 | Exact scope and registered literal associations remain present; independent completion of all reconstruction mutations was interrupted. |
| S01-R2-001 | The r4 code broadens ordinary-file coverage and exact-pins the whole matrix corpus, but its active-tree read is not identity-stable; see S01-R4-001. |
| S01-R2-002 | Current parser language is schema-format-only and COV-005 remains missing/S10. The two lower-level public API descriptions/preconditions remain too broad; see S01-R4-002/003. |
| S01-R3-001 | The canonical FIPS profile is now byte-pinned and complete-record checked; its current contents independently match the genuine PDF evidence. |
| S01-R3-002 | Static syntactic reconstruction and stable symlink cases are materially addressed, but the no-follow traversal can follow a replaced queued directory pathname; see S01-R4-001. |
| S01-R3-003 | The exact eight-file matrix corpus is now path/byte-pinned in addition to selected semantic checks. Independent end-to-end matrix mutations were interrupted. |

## Findings

### S01-R4-001 — MEDIUM — the active-tree read is not stable against local pathname replacement

`scan_regular_tree_no_follow()` first obtains no-follow metadata for a directory entry, stores a
`Path` in `pending`, and later calls `os.scandir(directory)` on that pathname. It does not retain an
open directory descriptor or compare the opened directory's device/inode identity with the object
that was checked. A directory may therefore be replaced between its `lstat` and later scan. The file
path similarly has no checked-versus-opened device/inode equality, although `O_NOFOLLOW` does reject
a symlink that is already present at `open` time.

This was reproduced against the real production function in a disposable local tree. The scan root
contained a real `zz-victim/` directory and several large sparse regular files. A local thread waited
until traversal was underway, renamed that directory, and installed a symlink at the queued
pathname to a different directory outside the scan root:

```python
def swap_directory():
    time.sleep(0.01)
    os.rename(root / "zz-victim", root / "saved-victim")
    os.symlink(external, root / "zz-victim")

threading.Thread(target=swap_directory).start()
files = scan_regular_tree_no_follow(root)
```

The external directory contained `outside.txt` with a unique marker. The exact result was:

```text
ACCEPTED external_read=True keys=[..., 'zz-victim/outside.txt']
```

The result was reproduced twice. This is a local repository-integrity/consistency defect: a path
validated as one directory was later opened as a different object, and outside content was read and
accepted. It directly contradicts `validation.md`'s unqualified statement that the no-follow
walker rejects linked roots/directories “before reading” and TCB-006's claim that this scanner is
the mitigation for path aliases. The five stable-entry self-tests do not exercise the interval
between metadata validation and the later pathname open, so they cannot detect this failure.

### S01-R4-002 — LOW — public parsed-JSON entry points do not retain the advertised duplicate-key boundary

`parsePromptJson` and `parseResultsJson` are public and documented as strict parsing entry points for
an already parsed `Lean.Json`. Duplicate-key rejection exists only in the string entry points that
invoke `StrictJson.parse`; ordinary `Lean.Json.parse` has already overwritten duplicate object
keys. An independent probe supplied a source with an invalid first `vsId` followed by a valid
duplicate. `parsePrompt source` rejected it, while:

```text
Lean.Json.parse source >>= parsePromptJson
ACCEPTED
```

The production `parseAndValidate` path is safe, and a JSON value cannot itself preserve the lost
source occurrence. The issue is the public API/assurance boundary: the lower-level function's
“strict” description does not state that duplicate-key assurance requires provenance from
`StrictJson.parse` rather than an arbitrary `Lean.Json` producer.

### S01-R4-003 — LOW — public `validatePair` assumes uniqueness that its bijection contract does not state

`validatePair` is public and its documentation claims exact prompt/result `(tgId,tcId)` bijection.
The function relies on parser-established positive/unique ID invariants instead of checking them.
An independent direct-construction probe built a prompt and result value containing duplicate
`tcId` records on both sides; the exact result was:

```text
#eval validatePair duplicatePrompt duplicateResults
Except.ok ()
```

`parseAndValidate` remains safe because both parsers establish uniqueness before calling this
function. The defect is nevertheless real for the public typed validator: without a documented
precondition or an invariant-carrying input type, it accepts values that do not satisfy its
unqualified exact-bijection contract.

## Verdict rationale

The current FIPS profile and eight matrix pins materially repair r3's static authority and
structured-row findings, and the production string parser path passed its runtime/adversarial
probes. However, the active-tree enumerator can validate one directory object and later follow the
same pathname to a different outside directory, while its canonical documentation says links and
aliases are rejected before reading. Two public parser/schema APIs also expose weaker contracts
than their descriptions imply. In addition, the interrupted reproduction items above cannot be
silently counted as passes.

The acceptance rule permits no finding. S01 r4 therefore **FAILS** independent review. S02 must not
start. No implementation repair was made.
