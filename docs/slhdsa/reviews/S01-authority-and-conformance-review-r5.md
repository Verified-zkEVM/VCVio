# S01 adversarial re-review r5 — authority and pinned conformance anchors

Verdict: **FAIL**

Reviewer: independent S01 r5 authority/conformance review sub-agent; not an S01 implementer or an
S01 r0/r1/r2/r3/r4 reviewer

Reviewed commit/tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r5 tree

Date: 2026-08-24

Independence statement: I did not design, implement, or repair S01, and I did not perform any of
the five prior S01 reviews. The implementation remained frozen. Disposable copies, independent
probes, extracted PDFs, and TeX output were confined to `/tmp`; this verdict is my only repository
edit. I made no commit or PR.

## Required-check status

Every interrupted r4 item and every new r5 item was completed. A checked item records execution or
inspection, not acceptance; the declaration-inventory inspection produced S01-R5-001.

- [x] Confirmed branch, HEAD, status, allowed S01 paths, the four-line `lakefile.lean` executable
  addition, no `HashSig/**` source change, and no S02 work.
- [x] Recomputed the exact r0 through r4 artifact hashes and verified one canonical `FAIL` in each.
  The r5 artifact had one canonical `PENDING` and SHA-256
  `75f4c6258fa5d75064f97249e6a1146e628c185324a3ab1c789faa8ee2f2657a` before authorship.
- [x] Independently reproduced the genuine FIPS PDF and distinct 5,059-byte canonical profile,
  compared every pinned authority/API/randomness/parameter/OID/grammar field to the PDF, and ran
  focused authority, randomness, key-width, other-prehash, API, order, OID, grammar, and raw-byte
  mutations in disposable copies. All were rejected.
- [x] Enumerated all eight matrix paths, sizes, and hashes, and rejected added coverage/decision/TCB
  rows, removal, an unregistered file, a field edit, terminal whitespace, and a symlink replacement.
- [x] Recomputed the complete active-tree literal manifest and normalized `20/19/1` identity
  counts. Split, comment-delimited, quoted, operator-spaced, case-folded, duplicated, and new-file
  reconstructions were all rejected.
- [x] Reran offline and optional checkout-backed provenance, independently derived all ACVP
  counts/joins/projections and the exact 24 positive prehash cells, ran native parser tests and
  additional probes, built `HashSigTest`, ran update-lib, docs and full validation, and completed
  syntax, hygiene, diff, and TeX checks.
- [x] Inspected the Linux descriptor-relative walker from repository-root anchoring through every
  active root and child. Metadata/open identity, relative enumeration/read/recurse, no-follow
  behavior, fail-closed runtime support, and descriptor cleanup were verified.
- [x] Reproduced stable real, root/file/directory/broken symlink, FIFO, deterministic root/file/
  directory replacement, and the exact r4 concurrent local-directory replacement cases. No
  outside or replacement bytes were returned.
- [x] Inspected the Lean API and verified that `parsePromptJson`, `parseResultsJson`, and
  `validatePair` are private, while the four public roots accept source strings and preserve strict
  duplicate rejection. External-module private-name probes failed to resolve as required.
- [x] Verified `parseWrappedPair` strict-parses the complete wrapper before projection, enforces the
  exact two wrapper keys, privately validates both members and their join, and rejects literal,
  escaped-equivalent, and nested duplicates plus unknown/missing wrapper keys.
- [x] Checked schema conditions, source spans, visibility, declaration dependencies, matrix pins,
  and assurance prose against the narrowed API. Spans and public-root visibility match; dependency
  accounting does not, as recorded in S01-R5-001.
- [x] Re-evaluated every prior S01 finding and disposition and the authority/server/protocol/SP/
  sample/license/LF/bibliography/current-issue/PR evidence. No prior defect was reproduced in its
  repaired surface.
- [x] Confirmed the administrative pre-verdict state: r0–r4 `FAIL`; F-030 through F-043
  `REMEDIATED-PENDING-REVIEW`; r5 `PENDING`; F-015/F-016 `OPEN`; COV-005 missing/S10/pending; S02
  blocked; and the r4 interruption accurately recorded.

The acceptance rule is zero findings. S01-R5-001 therefore requires `FAIL` even though every
required check is complete.

## Frozen state and immutable review history

The review environment was Linux 6.18.7 x86-64, Python 3.12.3, Lake 5.0.0, and Lean 4.32.2
(`f3b06c705e6c85f5314019d5d3baab0fec5b580c`). Before authorship:

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

The tracked diff was exactly four added lines defining `slhdsa_acvp_parser`; the untracked content
was confined to the three declared S01 roots. Separate status and diff queries found no
`HashSig/**` change and no S02 construction. The immutable reviews measured:

```text
ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76  r0  FAIL
9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec  r1  FAIL
3a8e5afe4d1b17c0b29febd18f993442f41e4f3137a994badce7d54946420ad8  r2  FAIL
bb84cb7380c9a5a1aa0c78018898389a7d1ac436dfa39caa987f170670542662  r3  FAIL
3a334dfe161d1475a48e44385fdd114615897d8416bf8026d15dcc2dddaa3c89  r4  FAIL
```

Each contained exactly one canonical verdict. The r5 checklist was `PENDING` throughout all gates;
only this independent artifact changes it.

## FIPS 205 and SP 800-230 authority reproduction

The genuine sibling FIPS publication and independent canonical profile measured:

```text
8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d
  /home/alh/SPHINCS/NIST.FIPS.205.pdf
1055752 bytes; title “Stateless Hash-Based Digital Signature Standard”; 61 pages

c833c36b33951e3b76fcf344e282cb26a37317f115b425eb776dfcdc1a23eeb5
  docs/slhdsa/matrices/fips205-profile.json
5059 bytes
```

Independent PDF text extraction and visual/table comparison reproduced the ordered twelve SHA2/
SHAKE Table-2 rows. The six distinct numeric tuples below each occur once for SHA2 and once for
SHAKE; tuple columns are `n,h,d,h',a,k,lg_w,m,pk,sk,sig`:

```text
128s  16,63, 7,9,12,14,4,30,32, 64, 7856
128f  16,66,22,3, 6,33,4,34,32, 64,17088
192s  24,63, 7,9,14,17,4,39,48, 96,16224
192f  24,66,22,3, 8,33,4,42,48, 96,35664
256s  32,64, 8,8,14,22,4,47,64,128,29792
256f  32,68,17,4, 9,35,4,49,64,128,49856
```

The derived private-key width is exactly `4n`; categories are 1/3/5; context is at most 255
bytes. Sections 10 and 11 also matched the pure and prehash domain bytes and `M'` grammars, the
other-approved-prehash rule, deterministic versus hedged `opt_rand`, and every Hmsg/PRF/PRFmsg/F/H/
Tl grammar in the three SHAKE, SHA2-n16, and SHA2-n24/n32 records. The four displayed OIDs and DER
encodings independently matched: SHA-256 `2.16.840.1.101.3.4.2.1` /
`0609608648016503040201`, SHA-512 `.3` / `0609608648016503040203`, SHAKE128 `.11` /
`060960864801650304020B`, and SHAKE256 `.12` / `060960864801650304020C`.

The separate SP authority reproduced as:

```text
62d092f787a1f79260454bf332b642ff3b5b73dbcce2678a133a1406065e452e
  /tmp/NIST.SP.800-230.ipd.pdf
282069 bytes; 12 pages; Initial Public Draft; 2026-04-13
```

Its six Table-1 SHA2/SHAKE limited-signature rows and strict `2^24 = 16,777,216` signatures/key
cap match the 1,504-byte profile pin. The material consistently calls it an Initial Public Draft,
not final FIPS authority, and does not claim six-set implementation coverage.

### Independent disposable authority mutations

I copied the frozen tree to `/tmp/s01-r5-mutation-base.Q5th55`, retained a disposable `.git`
worktree pointer so revision checks remained meaningful, and invoked the normal docs gate with
`SLHDSA_REFERENCE_ROOT=/home/alh/SPHINCS`. The result log was
`/tmp/s01-r5-mutation-results.txt`. Every focused mutation was rejected:

```text
FIPS authority / randomness / secret-key width / other-prehash rule        REJECT
pure API grammar / parameter row order / OID / primitive grammar           REJECT
raw byte plus whitespace/EOF change                                        REJECT
```

The first eight failed the exact profile pin; the raw-byte change failed comprehensive byte/
whitespace validation. The production gate additionally ran ten structured FIPS-profile mutation
self-tests, which deliberately recompute bytes after changing records; their rejection shows that
the semantic checks are not tautological aliases of the fixed hash.

## Exact matrix corpus, identities, and mutation resistance

Independent `wc -c` and `sha256sum` produced exactly the eight registered matrix objects:

| Path under `docs/slhdsa/matrices/` | Bytes | SHA-256 |
|---|---:|---|
| `assumptions.csv` | 2,687 | `00ab7ccf58fc3bf19ca6ef64db780c94cb0b8ae5ef8c48a9bff34a65546decf2` |
| `coverage.csv` | 3,602 | `0b82e0b42197a332b35b228a1ad3b641d92411c7ba5345e8179ceba68962928c` |
| `decisions.csv` | 1,368 | `12d0615301f5bf5e9829a0f976da94a043855e1d544cc7b4c11f7fc98d9129ac` |
| `declarations.jsonl` | 12,003 | `5356ccd5fccf2ae17de383bfba0e8fe4239b0e91b97b340df459fd20a9a0d558` |
| `fips205-profile.json` | 5,059 | `c833c36b33951e3b76fcf344e282cb26a37317f115b425eb776dfcdc1a23eeb5` |
| `proof-obligations.csv` | 3,368 | `3a043967b04a1b153cce40d472170d6d754b6f531d4ee618825d52cd79901314` |
| `sp800-230-ipd-profile.json` | 1,504 | `77ee7c4f0e872f2f2f31c830a14f4d90d63c55d260a0f3aaa3ac0e4aec92d26e` |
| `tcb.csv` | 3,318 | `c933215696262709bab409ce27173e88132badcb73802f30e5ade052833c8abe` |

The exact path set is enforced in addition to the pins. Disposable additions to coverage,
decisions, and TCB, removal of `decisions.csv`, addition of a ninth matrix file, an assumptions
field edit, a terminal blank line in proof obligations, and replacement of TCB by a symlink were
all rejected by the normal docs gate for the expected path/pin/hygiene/no-follow reason.

I independently enumerated every literal current-identity association over `docs/slhdsa`,
`scripts/slhdsa`, and the whole `HashSigTest/SLHDSA` test-support root, excluding only the exact
hash-locked r0–r4 review files. The per-file counts below are
`deprecated / SP800-230-IPD-6SET / LEGACY-SHA2-128-24`:

| Active file | Counts |
|---|---:|
| `HashSigTest/SLHDSA/ACVP/fixtures/provenance.json` | `0 / 1 / 0` |
| `docs/slhdsa/decisions.md` | `0 / 1 / 1` |
| `docs/slhdsa/findings.md` | `1 / 1 / 1` |
| `docs/slhdsa/matrices/assumptions.csv` | `0 / 0 / 1` |
| `docs/slhdsa/matrices/coverage.csv` | `0 / 1 / 2` |
| `docs/slhdsa/matrices/decisions.csv` | `0 / 1 / 1` |
| `docs/slhdsa/matrices/proof-obligations.csv` | `0 / 0 / 1` |
| `docs/slhdsa/matrices/sp800-230-ipd-profile.json` | `0 / 1 / 1` |
| `docs/slhdsa/reference-manifest.json` | `0 / 1 / 0` |
| `docs/slhdsa/report/slhdsa-formalization-audit.tex` | `0 / 2 / 2` |
| `docs/slhdsa/scope.md` | `0 / 2 / 1` |
| `docs/slhdsa/sessions/S01-authority-and-conformance.md` | `0 / 2 / 2` |
| `docs/slhdsa/source-ledger.md` | `0 / 1 / 1` |
| `scripts/slhdsa/check-acvp-provenance.py` | `0 / 1 / 1` |
| `scripts/slhdsa/check-harness.py` | `0 / 5 / 4` |
| **Totals** | **`1 / 20 / 19`** |

ASCII-alphanumeric normalization, lowercasing, and overlapping counting independently produced
the same `1/20/19` totals, so no identity is reconstructed without a registered literal. The sole
deprecated occurrence is the exact historical F-031 row. Independent split, comment delimiter,
string quote/concatenation, operator spacing, case folding, duplicate literal, and reconstructed
identity in a new outer test-support file were all rejected.

## Source provenance, samples, license, and current upstream state

The local ACVP-Server checkout was clean at exact tag `v1.1.0.43`, commit
`975de31eb83d87039ec88934fdc47d8c312b892d`; the protocol checkout was clean at
`892fd14710f3a7edbea230d0aecc5511e0257f8e`, with root document
`draft-livelsberger-acvp-slh-dsa-01` and `revdate: 2024-06-25`. The 2,258-byte root hash is
`d9c7088a6bb0531b2a5ab65104f467a7abe0e5ffc4d22f8ec1b7b90978d7d061`; an independent ordered
root-plus-15-section manifest yielded composite
`bc38ec528afcaa7f6a8155fd75a7612166203c789a540c0ac42e860a04c40a54`.

The 15 section pins, in the composite's `LC_ALL=C` order, were:

```text
03-supported.adoc                         287  d92d036162464cda211b458ef214de0cfac49642cd6a51ba6df9cb5e0bdf6355
04-testtypes.adoc                        4788  4528cb13bd80da55cac571723c0aa7e4729f401b1c97b583d1c5e9099908c570
05-capabilities.adoc                      800  b9d0ca1b5c773a056d1837373ee212f9f155367dedbad7d83f32f090952dd605
05-slh-dsa-keygen-capabilities.adoc      1638  09568244b74d1b6fe2250544526859be669b38222357b3bc24f891d880b1bc12
05-slh-dsa-siggen-capabilities.adoc      3690  644b863cfb3fedca6db12f2deaa70074c1e4c9f710a9bf615227f9d44d2cffb7
05-slh-dsa-sigver-capabilities.adoc      3396  24c235b4b3d7e4b3db79207f2416c33c9c942da40035976789ad534f4f89fafd
06-slh-dsa-keygen-test-vectors.adoc      2581  8001e6b79a3b446bab0d42876c494031327e85f04646c21712c8fc34988fe966
06-slh-dsa-siggen-test-vectors.adoc      4692  d07f8c3291d7787b118c8804294258549723342a57b1290fb923e49333c6ea15
06-slh-dsa-sigver-test-vectors.adoc      5095  08740e1b04d5de7124b05a99f3b9ebdfbb93231ff3a126f4f5316755a0702bfd
06-test-vectors.adoc                     1527  acede1bd43f0c9230fe42c550660855c5d26121dbb1c755e5e16f63017d7cf4e
07-responses.adoc                        1204  f47fc9df4269faa50b0e7afabe13aabd487db0a648e2fc0fb086994122f5ee5a
07-slh-dsa-keygen-responses.adoc         1099  e83fdda88d9691f8eff65c5827ac43fe666751e69f57f74c9dd39a246f228283
07-slh-dsa-siggen-responses.adoc         1035  f858107c8fa775bb14f7824016de4e55d276c341a06b952a8b43b6ea438a643e
07-slh-dsa-sigver-responses.adoc         1046  786247baefdb39a3c014b6542a9e93c4ddc3a9f49194e49615c4174089e1a52e
98-references.adoc                       1092  b127d1e0d713365b797b12fe167e693c1a113641fd56d2084ded37adf8cf8042
```

The exact 15 ACVP-Server artifacts were independently enumerated:

| Mode/artifact | Bytes | SHA-256 |
|---|---:|---|
| keyGen registration | 438 | `dfbf8116cb108209bc8fe539ec460dcda7036336ff460e4b0d9cf55c464fca08` |
| keyGen prompt | 32,454 | `bce170976f257ee3dfc8c54ea46722ccb553539847daa6d8048f0216cc28b51c` |
| keyGen internal projection | 75,294 | `d7c53a1b6450087047b57aae83a5a51a0ac89ecdb23ebe071e83fbb69ae9d920` |
| keyGen expected results | 45,192 | `f35f74b6676d6b369c87e88c36698f28c14d5929d31e507d910288c69258afee` |
| keyGen validation | 6,792 | `df6726b334e4ab0ce0b48f716a423bd2b4366cea589d2878ff3023ba11494da9` |
| sigGen registration | 1,776 | `f7db21f297028ae806a07b482a7bad73e49c8df2bf0dec492786c1313ba9fa72` |
| sigGen prompt | 5,512,830 | `afa673eacdf0aec53512a159159b7632684adfcd0d88f8640a7f6f5796aacdc8` |
| sigGen internal projection | 38,178,342 | `62b42e7c27fda5de8a94aba2943ae413b59b6ea08141f3bc035b1eceae235dba` |
| sigGen expected results | 32,595,492 | `71e8e0f7e4b0cfd1747314299204d9d4d50968d200a4ae873921eaa7aabeaad1` |
| sigGen validation | 35,520 | `4b3e13ff387d2b491b94a60f78b09d7c0d568154061773cb6d8faf6b28b448fc` |
| sigVer registration | 1,730 | `afe3475e0e0f2680daf0f6b908832e8f0649f2dc6909b5df6be78802f09e5dde` |
| sigVer prompt | 30,513,796 | `4e7beb1233e47baa0acdd36417c66c45811aa40a4e32ffdb1a35d93b13b289fb` |
| sigVer internal projection | 30,731,848 | `a013fc2104f4ed4799d96d51141f65b965969b2cf10646626a021b6d456ce792` |
| sigVer expected results | 39,216 | `259f5e2a0665de0adc0fefa45b5db3a2a6ed13c3c44d14bdaf64a80aee12c687` |
| sigVer validation | 28,680 | `83335f44c1b91d90258da79e398eb7370e06b1eb2dd94279da01fffba64a54ee` |

Offline provenance passed over nine committed artifacts. Optional provenance with both local
checkouts passed the exact 15 server artifacts, protocol root/sections/composite, and all fixture
projections. A copied-tree mutation from release `v1.1.0.43` to `.42` was rejected by the exact pin.
The older `v1.1.0.38` boundary is separately pinned to commit
`85f8742965b2691862079172982683757d8d91db` and is described only as server-format compatibility.

Current primary-source checks found ACVP-Server issue #469 open and PR #471 open, unmerged, and
explicitly not regenerating the sample JSON. The official `v1.1.0.43` release identifies the
975de31 commit and production date 2026-08-12. These states agree with the documentation; samples
are never described as certificates, approved vectors, or implementation-conformance evidence.

`NOTICE-NIST.txt` independently matched the complete three-paragraph NIST license after normalized
comparison and records the exact source/release/commit, acknowledgement, and modification nature.
The five vendored objects match upstream bytes plus exactly one final LF:

```text
keyGen registration 438 -> 439       sigGen registration 1776 -> 1777
sigVer registration 1730 -> 1731     keyGen prompt 32454 -> 32455
keyGen expected 45192 -> 45193
```

The documentation correctly describes this LF normalization rather than falsely calling those
five files byte-identical.

## Descriptor-relative active-tree traversal

I inspected `scripts/slhdsa/check-harness.py` from platform preconditions through root opening,
component traversal, child reads, recursion, and cleanup. It fails closed unless running on Linux
POSIX with `O_DIRECTORY`, `O_NOFOLLOW`, descriptor-relative stat/open, and descriptor `scandir`
support. It performs no weaker pathname fallback.

The repository root is first no-follow metadata-checked, then opened with
`O_DIRECTORY|O_NOFOLLOW`, and the opened `fstat` type/device/inode must equal the checked object.
Each active-root component is opened relative to its held parent descriptor and similarly matched.
Directories are enumerated using `os.scandir(parent_fd)`; each child is no-follow statted and
opened relative to that same held parent, then `fstat`-matched by type, `st_dev`, and `st_ino`.
Files are read from the held file descriptor. Directories recurse through the held child
descriptor: no checked child pathname is queued or reopened. `try/finally` paths close all owned
descriptors, including replacements in the component-chain opener.

The independent production-function probe `/tmp/s01-r5-walker-probe.py` reported:

```text
ACCEPT stable-real-tree exact bytes
REJECT stable-file-symlink
REJECT stable-directory-symlink
REJECT stable-broken-symlink
REJECT stable-root-symlink
REJECT stable-fifo
REJECT deterministic-directory-replacement
NO outside bytes read in deterministic directory replacement
REJECT deterministic-file-replacement
NO replacement bytes read in deterministic file replacement
REJECT deterministic-root-replacement
REJECT r4-concurrent-local-directory-replacement
NO result/outside bytes returned in concurrent r4 scenario
REJECT unsupported-runtime
FD cleanup PASS 4->4
```

The concurrent r4 reproduction used 12 large sparse ordinary files, delayed 0.01 seconds, renamed
`zz-victim`, and installed an external-directory symlink at that local name. Unlike r4, the repaired
walker rejected it and returned neither a result nor the outside marker. The deterministic file
case replaced a checked file with a different regular inode and rejected it before replacement
bytes were read. I found no remaining pathname/descriptor consistency or lifetime gap.

## Strict JSON, typed schema, wrapper provenance, and public API

Static inspection found these intended public source-string roots:

```text
SLHDSA.Test.ACVP.parsePrompt
SLHDSA.Test.ACVP.parseResults
SLHDSA.Test.ACVP.parseAndValidate
SLHDSA.Test.ACVP.parseWrappedPair
```

`parsePromptJson`, `parseResultsJson`, and `validatePair` are `private def`. An external module
resolved all four public names and reported `Unknown identifier` for all three private spellings.
Thus the r4 arbitrary parsed-JSON and directly constructed pair call paths are closed.

`parsePrompt`, `parseResults`, and `parseAndValidate` each retain `StrictJson.parse` before typed
schema validation, so literal, nested, and escaped-equivalent source duplicates cannot be erased by
an ordinary JSON parser first. `parseWrappedPair` strict-parses the complete source, requires
exactly `prompt` and `expectedResults`, privately parses the two values, and privately validates the
pair. The fixture `nestedPair` first strict-parses the complete projection source, only then
extracts/compresses the two objects for `parseWrappedPair`; duplicate provenance is therefore not
discarded before strict parsing.

The native executable ran all `16` positive and `52` negative cases, `68` total. An independent
external runtime probe additionally observed:

```text
OK valid prompt/results/pair/wrapper; OK message 1 and message 8192; OK context 255
REJECT prompt literal duplicate; results escaped duplicate
REJECT wrapper literal/escaped/nested duplicate; wrapper unknown/missing key
REJECT malformed/trailing source; message 0; message 8193; context 256
REJECT prompt/result vsId join and tcId join
```

Manual schema review confirmed exact keys/types/discriminants, positive and globally unique group/
case IDs, nonempty groups/tests, exact prompt/result joins, all 12 parameter names and hash enums,
key/signature widths, message 1–8192 bytes, context at most 255 bytes, internal/external and pure/
prehash conditional fields, deterministic/randomized conditions, and sigVer exact or ±1-byte
prompt cases with positive results restricted to exact signature width. This remains parser/schema-
format evidence only, not conformance, construction, or security evidence.

The four inventory source spans themselves are exact: DECL-011 lines 59–72, DECL-012 lines 401–405,
DECL-013 line 205, and DECL-014 lines 408–415. Public/private visibility in Lean is correct. The
inventory dependency names are not all correct; see S01-R5-001.

## Independent ACVP quantitative reproduction

`/tmp/s01-r5-quantitative.py` used a separate duplicate-detecting JSON loader, not the production
checker. It re-established exact prompt/result global `(tgId,tcId)` bijections and produced:

```text
keyGen: 12 groups / 120 tests
sigGen: 72 groups / 624 tests
sigVer: 36 groups / 504 tests; 72 positive / 432 negative

sigGen external preHash: deterministic 144, randomized 144
sigGen external pure:    deterministic  84, randomized  84
sigGen internal:         deterministic  84, randomized  84
```

The external-prehash universe is exactly 144 parameter/hash cells. Exactly 24 are positive—two per
parameter set—and ten cells are missing per set; SHA3-224 and SHAKE-128 have zero positives. The
24 independently derived `(parameterSet,hashAlg) -> (tgId,tcId)` cells are:

```text
SHA2-128f:  SHA2-256 (2,25);       SHA3-384 (2,19)
SHA2-128s:  SHA2-512 (20,268);     SHAKE-256 (20,271)
SHA2-192f:  SHA2-512 (4,52);       SHA2-512/224 (4,53)
SHA2-192s:  SHA2-256 (22,307);     SHA2-512/256 (22,302)
SHA2-256f:  SHA2-224 (6,72);       SHA2-384 (6,84)
SHA2-256s:  SHA2-512 (24,331);     SHA3-384 (24,328)
SHAKE-128f: SHA2-512/256 (8,111);  SHA3-512 (8,107)
SHAKE-128s: SHA2-512/224 (26,351); SHA2-512/256 (26,364)
SHAKE-192f: SHA3-384 (10,139);     SHA3-512 (10,129)
SHAKE-192s: SHA3-256 (28,386);     SHA3-384 (28,388)
SHAKE-256f: SHA2-224 (12,167);     SHA2-256 (12,168)
SHAKE-256s: SHA2-512/256 (30,417); SHA3-256 (30,412)
```

The sigGen and sigVer committed slice prompts/results were independently re-derived from the pinned
upstream sources in upstream order and matched exactly. Negative sigVer cases were not counted as
positive OID/digest coverage.

## Gates and hygiene

The following commands completed successfully while r5 was still `PENDING`:

```text
python3 -B scripts/slhdsa/check-acvp-provenance.py
  PASS: 9 committed artifacts; 15 server artifacts; counts/projections; 144/24; 8 mutations

ACVP_SERVER_ROOT=/tmp/slhdsa-s01-acvp-server \
ACVP_PROTOCOL_ROOT=/tmp/slhdsa-s01-acvp-protocol \
python3 -B scripts/slhdsa/check-acvp-provenance.py
  PASS: exact server checkout, protocol root/15 sections/composite, counts and projections

lake exe slhdsa_acvp_parser
  positive PASS (16); negative PASS (52); runtime PASS (68)

lake build HashSigTest
  PASS (2,743 jobs)

./scripts/update-lib.sh
  PASS; all nine generated import surfaces reported “No update necessary”

SLHDSA_REFERENCE_ROOT=/home/alh/SPHINCS ./scripts/slhdsa/validate.sh --docs-only
  PASS; 18 local references; authority/profile/scope/matrix/walker mutation self-tests;
  provenance PASS

SLHDSA_REFERENCE_ROOT=/home/alh/SPHINCS ./scripts/slhdsa/validate.sh
  PASS; repository 3,007 jobs; HashSig 2,744; HashSigTest 2,743; parser 68;
  PolicyAudit and compiled-IR ordinary/exact rejection; update-lib; isolation; KATs
```

The full build emitted only the documented unrelated baseline sorries and native-stub warnings.
Independent syntax checks parsed every JSON/JSONL object, Python compilation succeeded without
leaving bytecode, and every shell script passed `bash -n`. A scan found no `__pycache__`, `.pyc`,
`.pyo`, prohibited new ACVP Lean source token, or unauthorized path. Exact active-tree whitespace
passed with only the two immutable S00-r5 hard-break exclusions; `git diff --check` passed.

The production docs gate reported its own non-tautological self-test summary:

```text
S01 authority/profile mutation self-tests PASS
  (6 authority, 10 FIPS-profile, 13 scope/active/claim,
   6 matrix corruptions, 8 filesystem/replacement cases rejected)
```

Finally:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/slhdsa-s01-r5-review-tex docs/slhdsa/report/slhdsa-formalization-audit.tex
```

completed with resolved references and produced a five-page, 281,560-byte PDF. Only minor overfull
box warnings remained.

## Prior-finding dispositions

The cited reproducer for each prior finding is repaired in the frozen r5 implementation. Because
r5 has a new finding and fails, these observations do not administratively accept S01 or promote
F-030 through F-043 beyond `REMEDIATED-PENDING-REVIEW`.

| Prior finding | Independent r5 disposition |
|---|---|
| S01-R0-001 | Repaired surface reproduced: exact authority/server/protocol/SP records and focused corrupt-authority/status/commit/profile mutations fail closed. |
| S01-R0-002 | Repaired surface reproduced: six-set draft and one-set legacy identities are distinct, exact-manifested, normalized-counted, and reconstruction mutations reject. |
| S01-R0-003 | Repaired surface reproduced: bibliography and pinned protocol root use 25 June 2024 for `draft-livelsberger-acvp-slh-dsa-01`. |
| S01-R0-004 | Repaired surface reproduced: active-tree LF/whitespace hygiene and exact upstream-plus-one-LF records pass; ordinary diff is supplemented by the comprehensive scan. |
| S01-R1-001 | Repaired surface reproduced: genuine FIPS PDF identity is checked separately from a complete exact canonical authority/profile record. |
| S01-R1-002 | Repaired surface reproduced: exact scope rows, full active-tree associations, and reconflation/reconstruction mutations fail closed. |
| S01-R2-001 | Repaired surface reproduced: the entire outer `HashSigTest/SLHDSA` support root is descriptor-scanned and the exact occurrence manifest rejects additions and contradictions. |
| S01-R2-002 | Repaired surface reproduced: assurance text says parser/schema-format only, the report counts six profiles, and COV-005 remains missing/S10/pending. |
| S01-R3-001 | Repaired surface reproduced: FIPS profile bytes and complete authority/API/randomness/prehash/order/OID/grammar semantics are pinned and mutation-tested. |
| S01-R3-002 | Repaired surface reproduced: descriptor-relative no-follow scanning rejects stable and replacement links/special entries, and normalized reconstruction checks reject nonliteral identities. |
| S01-R3-003 | Repaired surface reproduced: the exact eight-path/size/hash matrix corpus rejects extra rows, removed/new files, field/whitespace changes, and link replacements. |
| S01-R4-001 | Repaired surface reproduced: repository/root/child descriptors remain anchored; deterministic and concurrent replacements reject without returning outside or replacement bytes. |
| S01-R4-002 | Repaired surface reproduced: parsed-JSON helpers are private; only strict duplicate-safe string roots are public, including the exact wrapper root. |
| S01-R4-003 | Repaired surface reproduced: typed `validatePair` is private and documents its parser-established invariant boundary; direct external construction cannot call it. |

## Administrative and assurance consistency

Before this verdict, README, plan, session, report, findings, and review index consistently recorded
r0–r4 as `FAIL`, r5 as `PENDING`, and S02 as blocked. F-030 through F-043 were exactly
`REMEDIATED-PENDING-REVIEW`; F-015 and F-016 remained `OPEN`; COV-005 remained
`missing / required / S10 / pending`. The r4 artifact accurately listed the work interrupted before
its findings and the r5 checklist required all of it to be rerun.

TCB-006 and the r4 traversal repair were exercised above. TCB-009 identifies the manual/bootstrap
inventory as a review risk. ASM-011 is explicitly future/schema-only and pending. The six profile
rows, SP draft/FIPS distinction, license normalization, sample qualification, issue/PR state, and
ACVP coverage gaps are internally consistent. I found no accepted conformance, certificate,
construction, or security overclaim and no second current defect.

## Finding

### S01-R5-001 — LOW — the manual declaration inventory records nonexistent or ambiguous dependency names

`docs/slhdsa/matrices/declarations.jsonl` is explicitly `bootstrap-manual`, and its own DECL-013
correctly records the executable declaration as the unqualified public name `main` at
`HashSigTest/SLHDSA/ACVP/ParserTests.lean:205`. The source closes namespace
`SLHDSA.Test.ACVP.ParserTests` on line 202 before defining that root. Nevertheless:

- DECL-012 (`SLHDSA.Test.ACVP.parseAndValidate`) and DECL-014
  (`SLHDSA.Test.ACVP.parseWrappedPair`) both record reverse dependency
  `HashSigTest.SLHDSA.ACVP.ParserTests.main`.
- DECL-011 records reverse dependency `SLHDSA.Test.ACVP.parsePromptJson`.
- DECL-012 records direct dependency `SLHDSA.Test.ACVP.validatePair`.
- DECL-014 records direct dependencies `SLHDSA.Test.ACVP.parsePromptJson`,
  `SLHDSA.Test.ACVP.parseResultsJson`, and `SLHDSA.Test.ACVP.validatePair`.

An external Lean module established the mismatch directly:

```text
#check main
main : IO Unit

#check HashSigTest.SLHDSA.ACVP.ParserTests.main
Unknown identifier `HashSigTest.SLHDSA.ACVP.ParserTests.main`

#check SLHDSA.Test.ACVP.parsePromptJson
#check SLHDSA.Test.ACVP.parseResultsJson
#check SLHDSA.Test.ACVP.validatePair
Unknown identifier for each private spelling
```

The helper privacy is the desired r5 API repair, and the public runtime boundary is safe. The defect
is inventory identity/accounting: two reverse-dependency entries name a declaration that does not
exist, while multiple dependency entries present private source spellings as if they were stable
resolvable names, without a private/source-logical qualifier or the actual private declaration
identity. This conflicts with the required declaration-dependency/public-API inventory check and
can mislead later manual dependency review.

Severity is LOW because this bootstrap inventory is non-load-bearing, already covered by TCB-009,
and neither the Lean API nor any construction/security result depends on these strings. It is still
a real current issue, and the review protocol permits no issue at any severity. No repair was made.

## Verdict rationale

The r5 repair closes every reproduced r0–r4 authority, scope, matrix, traversal, and public-parser
defect. All formerly interrupted r4 executions, new descriptor-replacement cases, private-name and
wrapper checks, quantitative derivations, full gates, hygiene, and TeX completed. I found no path
escape, duplicate-provenance loss, schema gap, pin mismatch, or assurance overclaim.

However, the frozen manual declaration inventory contains nonexistent and ambiguous dependency
identities. The zero-finding acceptance rule is unconditional. S01 r5 therefore **FAILS** independent
review. S01 remains blocked and S02 must not start. No implementation repair, commit, or PR was
made.
