# S01 — authority and pinned conformance anchors

Status: reviews r0/r1/r2/r3/r4/r5/r6/r7/r8/r9/r10/r11/r12/r13/r14/r15 failed; independent r16 PASS; S01 accepted; S02 eligible

## Inputs and scope

- Accepted predecessor: S00 independent re-review r9 PASS.
- Repository baseline: `f1853af40da1efa11a71c2d7011996eebdbf6938` on
  `codex/sphincsplus-formalization`.
- Allowed implementation scope: `HashSigTest/SLHDSA/**`, `scripts/slhdsa/**`, and
  `docs/slhdsa/**`, plus the minimal `lakefile.lean` executable target required for native parser
  runtime (imported parser definitions are unavailable to `lean --run`).
- No `HashSig/**` construction or security declaration changed. No conformance or certificate claim
  is made by parsing NIST sample JSON.

## Deliverables

- Final FIPS 205, ACVP protocol, ACVP-Server release, sample-JSON, issue, and SP 800-230 IPD pins.
- Exact FIPS 205 twelve-set parameter/API table retained as the normative construction anchor.
- Three JSON-value-exact registrations and JSON-value-exact keyGen prompt/expected sample files,
  each with its recorded single final-LF normalization, plus bounded,
  reproducible sigGen/sigVer projections and the complete 144-cell pre-hash coverage projection.
- Strict Lean JSON/schema parser and runtime positive/negative suite.
- Deterministic offline provenance checker with optional full-checkout verification.
- NIST software notice and explicit projection/change notice.

The ACVP-Server files are public **sample JSON** with `isSample = true`; they are neither a NIST
validation certificate nor an independent set of FIPS-approved vectors. Issue #469 remains open.

`SP800-230-IPD-6SET` is only the six-set non-normative authority/profile and
`LEGACY-SHA2-128-24` is only the one-set current-code subprofile.

## Quantitative evidence

At ACVP-Server commit `975de31eb83d87039ec88934fdc47d8c312b892d`:

- keyGen: 12 groups and 120 tests;
- sigGen: 72 groups and 624 tests;
- sigVer: 36 groups and 504 tests, split into 72 positive and 432 negative cases;
- external pre-hash sigVer: exactly 24 of 144 `(parameterSet, hashAlg)` cells have a positive case;
- every parameter set lacks at least ten positive hash cells; SHA3-224 and SHAKE-128 lack a positive
  case globally.

Negative cases do not demonstrate correct OID/digest binding. Open ACVP-Server PR #471 does not
regenerate the public sample JSON, so it does not change this measurement.

## Validation evidence

The following gates are required before review; their final outputs are recorded at handoff:

```text
python3 -B scripts/slhdsa/check-acvp-provenance.py
lake exe slhdsa_acvp_parser
lake build HashSigTest
./scripts/update-lib.sh
./scripts/slhdsa/validate.sh --docs-only
./scripts/slhdsa/validate.sh
(cd docs/slhdsa/report && latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/slhdsa-s01-tex slhdsa-formalization-audit.tex)
git diff --check
```

Implementer command results are evidence for the reviewer, not self-certification.

Observed initial-implementation results on 2026-08-24:

- offline provenance: PASS for 9 committed artifacts, 15 pinned server artifacts, full-suite counts,
  and the 144/24 coverage matrix;
- optional provenance with both pinned local checkouts: PASS, including projection regeneration,
  authoritative full-file counts, the protocol root, 15 sections, and composite;
- native parser runtime: PASS for 16 positive and 47 fail-closed negative cases;
- `lake build HashSigTest`: PASS, 2,743 jobs;
- `update-lib.sh`: PASS, no update necessary;
- docs-only validation and full validation: PASS;
- TeX: PASS, five-page PDF under `/tmp/slhdsa-s01-tex`, with minor overfull-box warnings only;
- `git diff --check` and the S01 scope/hygiene review: PASS.

Repair iteration r1 validation on 2026-08-24:

- normal offline provenance: PASS, including four self-contained corrupt-metadata mutations rejected;
- harness metadata gate: PASS, including two independently expressed corrupt-metadata mutations
  rejected;
- optional provenance with the exact pinned server and protocol checkouts: PASS, including full-suite
  count derivation and projection regeneration;
- native parser runtime: PASS for 16 positive and 47 fail-closed negative cases;
- `lake build HashSigTest`: PASS, 2,743 jobs;
- `update-lib.sh`: PASS, no update necessary;
- docs-only validation and full validation: PASS;
- JSON/JSONL parsing and shell syntax checks: PASS;
- TeX: PASS, five-page PDF under `/tmp/slhdsa-s01-r1-tex`, with minor overfull-box warnings only;
- `git diff --check` plus direct tracked-and-untracked S01 whitespace/scope/hygiene review: PASS;
- immutable r0 review SHA-256 remained
  `ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76`.

Repair iteration r2 validation on 2026-08-24:

- normal docs gate with the real sibling bundle: PASS; local FIPS bytes verified separately, six
  metadata and two scope corruptions rejected;
- offline provenance: PASS; eight authority/provenance corruptions rejected;
- optional provenance with both exact pinned checkouts: PASS, including full-suite count derivation
  and projection regeneration;
- active profile scan: PASS; deprecated-ID occurrences are confined to hash-locked r0/r1 history
  and the exact F-031 description;
- native parser runtime: PASS for 16 positive and 47 fail-closed negative cases;
- `lake build HashSigTest`: PASS, 2,743 jobs;
- `update-lib.sh`: PASS, no update necessary;
- docs-only validation and full validation: PASS;
- JSON/JSONL parsing, Bash syntax, comprehensive whitespace/scope/hygiene, and
  `git diff --check`: PASS;
- TeX: PASS, five-page PDF under `/tmp/slhdsa-s01-r2-tex`, with minor overfull-box warnings only;
- immutable r0/r1 review SHA-256 values remained
  `ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76` and
  `9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec`.

Repair iteration r3 validation on 2026-08-24:

- normal docs gate with the real sibling bundle: PASS; six metadata and nine
  scope/active/claim corruptions rejected;
- the nine cases include both prior scope mutations and every r2 reproducer: deprecated identity in
  an existing outer test, deprecated identity in a new outer file, a new-file terminal blank line,
  contradictory current IDs in Schema, contradictory COV-014 claim/evidence/notes, the old parser
  assurance phrase, and report six-to-five miscount;
- offline provenance: PASS with eight mutations rejected; optional exact server/protocol checkout
  verification also PASS;
- exact occurrence manifest and complete S01-relevant matrix records: PASS across all canonical
  document, script, and full test-support roots;
- native parser runtime: PASS for 16 positive and 47 fail-closed negative cases;
- `lake build HashSigTest`: PASS, 2,743 jobs;
- `update-lib.sh`: PASS, no update necessary;
- docs-only validation and full validation: PASS;
- JSON/JSONL parsing, Bash syntax, comprehensive tracked/untracked whitespace/scope/hygiene, and
  `git diff --check`: PASS;
- TeX: PASS, five-page PDF under `/tmp/slhdsa-s01-r3-tex`, with minor overfull-box warnings only;
- immutable r0/r1/r2 review SHA-256 values remained
  `ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76`,
  `9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec`, and
  `3a8e5afe4d1b17c0b29febd18f993442f41e4f3137a994badce7d54946420ad8`.

Repair iteration r4 design and handoff on 2026-08-24:

- the canonical FIPS profile is checked by exact byte size/SHA-256 and exact structured top/API,
  authority, randomness, other-prehash, ordered Table-2/OID, and primitive-grammar records;
- a no-follow `lstat`/`scandir` walker covers all three active roots, rejects linked roots,
  file/directory/broken symlinks and unsupported entries before reading, and exercises five actual
  disposable-filesystem negative cases;
- normalized ASCII-alphanumeric identity counts must equal the exact registered literal occurrence
  manifest, including a single exact historical deprecated occurrence; split comments, string
  concatenations, and shorter-fragment reconstructions are negative cases;
- the exact eight-file canonical matrix path set and every artifact's bytes are pinned in addition
  to the existing structured semantic checks; future sessions must deliberately update and review
  pins when canonical matrices change;
- F-038/F-039/F-040 record the immutable r3 findings as remediated pending review. These controls
  and their implementer-run gates are evidence for review, not S01 acceptance.

Repair iteration r4 validation on 2026-08-24:

- real-sibling docs-only gate: PASS; six authority, ten complete FIPS-profile, thirteen
  scope/active/claim, six complete-matrix, and five actual filesystem-entry corruptions rejected;
- offline provenance: PASS with eight mutations rejected; optional exact server/protocol checkout
  verification: PASS, including authoritative counts, projection regeneration, root/section hashes,
  and protocol composite;
- native parser runtime: PASS for 16 positive and 47 fail-closed negative cases;
- `lake build HashSigTest`: PASS, 2,743 jobs; `update-lib.sh`: PASS, no update necessary;
- full validation: PASS, including elaborated policy, compiled initializer, isolation, and both KATs;
- JSON/JSONL, Python, and Bash syntax: PASS; separate real-directory and broken-symlink
  reproductions rejected; comprehensive tracked/untracked whitespace/scope/hygiene and
  `git diff --check`: PASS;
- TeX: PASS, five-page PDF under `/tmp/slhdsa-s01-r4-tex`, with minor inherited overfull-box
  warnings only;
- immutable r0/r1/r2/r3 review SHA-256 values remained
  `ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76`,
  `9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec`,
  `3a8e5afe4d1b17c0b29febd18f993442f41e4f3137a994badce7d54946420ad8`, and
  `bb84cb7380c9a5a1aa0c78018898389a7d1ac436dfa39caa987f170670542662`.

Repair iteration r5 design and handoff on 2026-08-24:

- Linux descriptor-relative traversal anchors the opened repository, opens active-root components
  and children relative to held parent descriptors, and compares no-follow metadata with opened
  device/inode/type before reading or recursion; unsupported platforms fail closed;
- deterministic pre-open hooks exercise root replacement, the exact r4 external-directory symlink
  replacement, and regular-file replacement, alongside stable root/file/directory/broken links and
  FIFO rejection; replacement contents are never returned;
- parsed-JSON prompt/results helpers and typed pair validation are private and explicitly consume
  parser-established invariants; public prompt/results, two-source pair, and exact-wrapper roots all
  accept source strings and retain duplicate-key rejection;
- wrapper runtime negatives cover duplicate literal, escaped-equivalent, and nested keys plus
  unknown/missing keys. The runtime corpus is now 16 positive and 52 negative cases;
- declaration accounting and matrix byte pins include the new public wrapper root. F-041/F-042/F-043
  record the r4 findings as remediated pending review, not fixed.

Repair iteration r5 validation on 2026-08-24:

- real-sibling docs gate: PASS; 35 authority/FIPS/scope/matrix mutations and eight stable/replacement
  filesystem cases rejected, for 43 harness negatives total;
- offline provenance: PASS with eight mutations rejected; optional exact server/protocol checkout
  verification: PASS, including authoritative counts, projection regeneration, root/section hashes,
  and protocol composite;
- native parser runtime: PASS for 16 positive and 52 fail-closed negative cases; an external Lean
  probe confirmed all three private helper names are unresolvable;
- `lake build HashSigTest`: PASS, 2,743 jobs; `update-lib.sh`: PASS, no update necessary;
- full validation: PASS, including elaborated policy, compiled initializer, isolation, and both KATs;
- JSON/JSONL, Python, and Bash syntax, comprehensive tracked/untracked whitespace/scope/hygiene,
  generated-debris scan, and `git diff --check`: PASS;
- TeX: PASS, five-page PDF under `/tmp/slhdsa-s01-r5-tex`, with minor inherited overfull-box
  warnings only;
- immutable r0/r1/r2/r3/r4 review SHA-256 values remained
  `ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76`,
  `9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec`,
  `3a8e5afe4d1b17c0b29febd18f993442f41e4f3137a994badce7d54946420ad8`,
  `bb84cb7380c9a5a1aa0c78018898389a7d1ac436dfa39caa987f170670542662`, and
  `3a334dfe161d1475a48e44385fdd114615897d8416bf8026d15dcc2dddaa3c89`.

Repair iteration r6 validation on 2026-08-24:

- focused harness and real-sibling docs-only validation: PASS; the five new token-level semantic
  mutations were rejected independently of exact-row matching, alongside the existing 43 harness
  negatives and eight provenance mutations;
- native parser runtime: unchanged PASS for 16 positive and 52 fail-closed negative cases;
- full validation: PASS, including 3,007-job repository build, 2,744-job HashSig build, 2,743-job
  HashSigTest build, elaborated policy/compiled fixtures, isolation checks, and both KATs;
- explicit `update-lib.sh`: PASS with no update necessary; Python, JSON/JSONL, and Bash syntax,
  comprehensive tracked/untracked active-scope whitespace/hygiene, generated-debris checks,
  `git diff --check`, and an empty `HashSig/**` diff: PASS;
- TeX: PASS, five-page PDF under `/tmp/slhdsa-s01-r6-tex`, with inherited overfull-box warnings
  only;
- immutable r0/r1/r2/r3/r4/r5 review SHA-256 values remained
  `ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76`,
  `9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec`,
  `3a8e5afe4d1b17c0b29febd18f993442f41e4f3137a994badce7d54946420ad8`,
  `bb84cb7380c9a5a1aa0c78018898389a7d1ac436dfa39caa987f170670542662`,
  `3a334dfe161d1475a48e44385fdd114615897d8416bf8026d15dcc2dddaa3c89`, and
  `03ae3b07aee41ddf90a30ee42edd388b2c3921c42f8a27807180262b4397ca97`.

Repair iteration r7 validation on 2026-08-24:

- the focused normal checker and real-sibling docs-only gate: PASS; the active-source parser found
  4, 44, and 19 declarations in the exact-pinned StrictJson, Schema, and ParserTests sources while
  tracking their actual namespace and mutual-command state;
- all grouped harness mutations were rejected: 16 declaration/source/Lake cases, including the r6
  block-comment four-root Lake permutation; six authority, ten complete-profile, fourteen
  scope/active/claim, six complete-matrix, and eight filesystem cases;
- the post-build inventory-driven external Lean probe: PASS; all eight public/root names resolved,
  all eleven private spellings and both false qualified-main spellings remained unresolved, and a
  dynamically substituted `Does.Not.Exist` public token failed elaboration;
- offline provenance: PASS with eight mutations rejected; optional exact server/protocol checkout
  verification: PASS, including authoritative counts, projection regeneration, root/section hashes,
  and protocol composite;
- native parser runtime and the full wrapper: PASS for exactly 16 positive, 52 fail-closed negative,
  and 68 total cases. Four stdout mutations were rejected, including the output from a successful
  execution of the wrong smoke-test executable;
- full validation: PASS, including 3,007-job repository build, 2,744-job HashSig build, 2,743-job
  HashSigTest build, elaborated policy/compiled fixtures, isolation checks, and both KATs;
- explicit `update-lib.sh`: PASS with no update necessary; Python, JSON/JSONL, and Bash syntax,
  comprehensive tracked/untracked active-scope whitespace/tab/hygiene, generated-debris checks,
  `git diff --check`, and an empty `HashSig/**` diff: PASS;
- TeX: PASS, five-page PDF under `/tmp/slhdsa-s01-r7-tex`; `pdftotext` confirms the rendered
  phrase `transitive root main`, with only inherited overfull-box warnings;
- immutable r0/r1/r2/r3/r4/r5/r6 review SHA-256 values remained
  `ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76`,
  `9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec`,
  `3a8e5afe4d1b17c0b29febd18f993442f41e4f3137a994badce7d54946420ad8`,
  `bb84cb7380c9a5a1aa0c78018898389a7d1ac436dfa39caa987f170670542662`,
  `3a334dfe161d1475a48e44385fdd114615897d8416bf8026d15dcc2dddaa3c89`,
  `03ae3b07aee41ddf90a30ee42edd388b2c3921c42f8a27807180262b4397ca97`, and
  `8f4f477ce19484a20bf1af6af4acce2bb10707bbab9c88e803593ef6ff797d22`.

Repair iteration r8 validation on 2026-08-24:

- the focused normal checker and real-sibling docs-only gate: PASS; the live actual Lake
  configuration translated to the exact parser root, and 23 source/token/static-Lake plus five
  translated-Lake mutations were rejected, including the exact r7 macro/quotation project;
- the complete quoted line-377 private-def/active line-378 private-opaque Schema mutation elaborated
  successfully in `/tmp`, while the source semantic layer rejected its quoted anchor; nested,
  malformed, and active metaprogramming variants were also rejected;
- optional exact server/protocol checkout provenance: PASS at commits
  `975de31eb83d87039ec88934fdc47d8c312b892d` and
  `892fd14710f3a7edbea230d0aecc5511e0257f8e`, including authoritative counts, projection
  regeneration, root/section hashes, and protocol composite;
- direct native parser stdout was exactly 154 bytes and three LF-terminated records: 16 positive,
  52 fail-closed negative, and 68 total cases;
- the file comparator rejected six byte mutations, including one and multiple extra terminal blank
  lines; the actual capture path rejected a successful smoke executable and a nonzero producer;
- `lake build HashSigTest`: PASS, 2,743 jobs; the external probe again resolved eight public/root
  names, rejected thirteen private/false names, and rejected `Does.Not.Exist`;
- full validation: PASS, including 3,007-job repository build, 2,744-job HashSig build, 2,743-job
  HashSigTest build, actual-config re-audit immediately before parser execution, elaborated policy,
  compiled initializer, isolation checks, and both KATs;
- explicit `update-lib.sh`: PASS with no update necessary; Python, duplicate-aware JSON/JSONL, and
  Bash syntax, comprehensive tracked/untracked whitespace/tab/hygiene, generated-debris checks,
  `git diff --check`, and an empty `HashSig/**` diff: PASS;
- TeX: PASS, six-page 283,394-byte PDF under `/tmp/slhdsa-s01-r8-tex`; `pdftotext` confirms
  `transitive root main`, the r8 disposition, and no `exttt` variant;
- implementer-created standalone mutation/translation files under `/tmp` were removed; wrapper
  temporary parser/policy directories were removed by its single EXIT cleanup;
- immutable r0/r1/r2/r3/r4/r5/r6/r7 review SHA-256 values remained
  `ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76`,
  `9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec`,
  `3a8e5afe4d1b17c0b29febd18f993442f41e4f3137a994badce7d54946420ad8`,
  `bb84cb7380c9a5a1aa0c78018898389a7d1ac436dfa39caa987f170670542662`,
  `3a334dfe161d1475a48e44385fdd114615897d8416bf8026d15dcc2dddaa3c89`,
  `03ae3b07aee41ddf90a30ee42edd388b2c3921c42f8a27807180262b4397ca97`,
  `8f4f477ce19484a20bf1af6af4acce2bb10707bbab9c88e803593ef6ff797d22`, and
  `fd8f9483e973ebca7388080e9218aa3c9b9d5857722a60bc42e5458de89941aa`.

Repair iteration r9 final-tree validation on 2026-08-24:

- normal harness and real-sibling docs-only: PASS; 23 source/token/static-Lake, nine selector-source,
  and thirteen translated-Lake mutations were rejected, including the r7 wrong-root project, both
  r8 source-directory levels, all tested path aliases, and package Lean-argument selectors;
- structured actual-build-input gate: PASS; Lake `-R -H -J query` resolved the exact worktree
  executable and current non-synthetic traces bound the frozen ParserTests source through generated
  C and its export object to that binary. Eight structured/JSON, two symlink/special-output, two
  exact `WrongSrc`, and two stale-transition cases were rejected;
- offline and optional pinned checkout-backed provenance: PASS; the server/protocol checkouts at the
  exact recorded commits reproduced the full-suite counts, projections, root/section hashes, and
  protocol composite;
- direct native parser and exact attested-binary wrapper execution: PASS, exactly 154 bytes and
  three LF-terminated records with 16 positive, 52 fail-closed negative, and 68 total cases;
- `lake build HashSigTest`: PASS, 2,743 jobs; the external probe resolved eight public/root names,
  rejected thirteen private/false names, and rejected the dynamic nonexistent-public mutation;
- full validation: PASS, including 3,007-job repository, 2,744-job HashSig, and 2,743-job
  HashSigTest builds; elaborated policy and compiled initializer fixtures; isolation checks; and
  both KATs. Baseline warnings remained the inherited sorries and absent optional native submodules;
- explicit `update-lib.sh`: PASS with no update necessary; Python and Bash syntax, duplicate-aware
  parsing of thirteen JSON/JSONL files, comprehensive active-scope hygiene, `git diff --check`, and
  an empty `HashSig/**` diff: PASS;
- TeX: PASS, six-page 283,724-byte PDF under `/tmp/slhdsa-s01-r9-tex`; `pdftotext` confirms
  `transitive root main`, the F-050 r9 disposition, and that S01 r9 remains pending;
- implementer debug translations, retained source-selection probe, and Python bytecode scratch under
  `/tmp` were removed. Wrapper temporary parser/policy roots were removed by its EXIT cleanup;
- immutable r8 remained exactly 13,492 bytes, 220 lines, SHA-256
  `a09fc3b7fffacb2e83f69f968c5b2c4ba81b91cee3258e5848fea1734735dd9d`. The r9 PENDING handoff was
  10,309 bytes, 162 lines, SHA-256
  `629d1b6360ab694f9cd73278ad45c7d8d8dfaa4e7ee4373baf663927385649f3`.

Baseline warnings remain visible: the accepted `HashSig/SLHDSA/Security.lean` admission and unrelated
repository admissions are unchanged, and absent native submodules use the repository's documented
empty-stub behavior. Neither warning is S01 evidence.

## S00 acceptance propagation

Independent r9 accepted the exact S00 semantic policy, baseline completeness evidence, controlled
inventory explanation, and related harness/TCB rows. S01 administratively propagates that verdict to
the corresponding canonical findings and S00-owned matrix evidence. This is not an S01 review and
does not discharge any open construction, security, conformance, or external-vector obligation.

## Review handoff

Independent review r0 at `reviews/S01-authority-and-conformance-review.md` is an immutable `FAIL`.
It reported four findings: incomplete fail-closed authority metadata, conflated draft/current-code
profile identities, the incorrect Internet-Draft bibliography year, and whitespace validation that
missed four untracked JSON terminal blank lines.

Repair iteration r1 hard-pins the coupled metadata in both normal gates and adds four in-process
negative mutations; separates `SP800-230-IPD-6SET` from `LEGACY-SHA2-128-24`; corrects and gates the
25 June 2024 draft identity; and checks whitespace directly across active tracked and untracked S01
files. The only exclusions are the two byte-preserved Markdown hard-break lines in immutable S00 r5.

Independent review r1 at `reviews/S01-authority-and-conformance-review-r1.md` is also an immutable
`FAIL`. It found that the FIPS 205 publication date and authority classification were not checked,
and that canonical scope/profile separation was correct in prose but could regress without failing
the normal gate.

Repair iteration r2 compares complete exact records for final FIPS 205, current ACVP-Server, its
compatibility boundary, the current protocol, and the SP IPD/profile while preserving separate local
PDF byte verification. It rejects false FIPS date/authority and analogous record mutations. It also
parses exact unique scope rows, rejects both reconflation mutations, scans all active documentation
for the deprecated identifier under a hash-bound historical allowlist, and gates the current
associations across the ledger, report, matrices, JSON, decisions, session, and scope.

Independent review r2 at `reviews/S01-authority-and-conformance-review-r2.md` is an immutable
`FAIL`. It found that the outer test-support scope and additional current-ID contradictions escaped
the scanner, canonical matrix rows were only partially checked, parser/schema tests overstated their
assurance role, and the report miscounted six profile rows as five.

Repair iteration r3 expands active-file and whitespace coverage to all of
`HashSigTest/SLHDSA/**`, exact-registers every legitimate current-ID path/normalized-line occurrence,
requires complete records for every relevant matrix row, and adds the seven concrete r2 mutations.
It qualifies parser results as parser/schema-format evidence only and gates the report's six-profile
count against the exact six-row scope table. This syntactic occurrence/record policy makes no claim
to infer arbitrary semantics from prose that contains neither registered identity.

Independent review r3 at `reviews/S01-authority-and-conformance-review-r3.md` is an immutable
`FAIL`. It found incomplete canonical FIPS-profile validation, symlink/special-entry and syntactic
identity-reconstruction bypasses, and acceptance of extra contradictory matrix rows.

Repair iteration r4 exact-pins and completely validates the canonical FIPS profile, replaces the
recursive scan with a no-follow regular-file walker plus real filesystem self-tests, reconciles
normalized reconstructed identities against the literal manifest, and byte-pins the exact current
matrix corpus in addition to semantic checks. It adds focused isolated mutations for every r3
reproducer and does not broaden claims beyond syntactic identity and pinned structured data.

Independent review r4 at `reviews/S01-authority-and-conformance-review-r4.md` is an immutable
`FAIL`. It reproduced a directory pathname-replacement escape and two public parser-invariant
boundary defects. Its independent on-disk FIPS/matrix mutations, stable filesystem/reconstruction
suite, provenance, complete build/validation, quantitative checks, hygiene, and TeX were interrupted
and remain explicitly mandatory for the r5 reviewer.

Repair iteration r5 replaces pathname queuing with Linux descriptor-relative device/inode/type
checks from an anchored repository descriptor and adds deterministic root/directory/file replacement
tests. It makes the three invariant-dependent helpers private, exposes a strict exact-wrapper string
root, and routes projection tests through that safe API. This is an implementer disposition only.

Independent review r5 at `reviews/S01-authority-and-conformance-review-r5.md` is an immutable
`FAIL`. It accepted the parser API-boundary repair and reported one low-severity declaration-
inventory defect: three rows used private source spellings as if they were externally resolvable
Lean declarations and used a nonexistent qualified spelling for the executable entrypoint.

Repair iteration r6 leaves every Lean source unchanged. It gives DECL-011 through DECL-014 exact
typed dependency tokens: public Lean declarations, immediate private source anchors, the transitive
root-level `main`, and the direct Lake executable are distinct classes. Private tokens carry exact
repository path/name/line anchors; root and Lake token classes are direction-restricted. The audit
also corrects DECL-011 to its immediate `parameterByName` consumer and DECL-013 to its immediate
private `runAll` callee. The normal checker requires each exact edge set and source keyword and
rejects the former qualified-main spelling, a bare private helper, and a nonexistent private helper.
Two additional semantic mutations exercise root-token direction and a false private source line;
all five invoke the token validator directly rather than failing first on exact-row equality.
This scoped repair does not claim that the legacy bootstrap rows are resolvable or that the manual
inventory is complete; F-018 remains open.

Independent review r6 at `reviews/S01-authority-and-conformance-review-r6.md` is an immutable
`FAIL`. It confirmed the corrected call graph but found three defects: source tokens could resolve
commented or namespace-shifted text, raw Lake matching could be comment-shadowed while successful
substitute executables escaped the wrapper, and a literal report tab rendered `extttmain`.

Repair iteration r7 keeps the call graph and every Lean source frozen. The normal docs gate
byte-pins and comment/namespace-parses the three ACVP Lean sources, source-resolves exact public,
private, and root declarations, and parses unique active Lake executable mappings. After the
HashSigTest build, the full wrapper derives current public/root names from the inventory and checks
them from an external Lean module; it also requires every private spelling and both false qualified
root spellings to remain unresolved. A dynamic nonexistent-public mutation exercises that
elaborated layer independently of the row literals. The parser runtime wrapper now captures and
requires exactly the three 16/52/68 stdout records, with successful KAT/smoke and extra/missing
output mutations. The report uses the real TeX command for `main`, and active internal tabs fail
hygiene. F-045/F-046/F-047 record these dispositions as pending review, not fixed. The typed checks
remain limited to the four S01 test rows; F-018 and TCB-009 still disclose manual-inventory
incompleteness.

Independent review r7 at `reviews/S01-authority-and-conformance-review-r7.md` is an immutable
`FAIL`. It confirmed the current call graph, external visibility, live literal Lake stanza, report
repair, parser counts, and all earlier authority/provenance gates. It found that unexpanded command
quotations could impersonate active private declarations and Lake mappings, and that Bash command
substitution erased extra terminal blank lines before stdout comparison.

Repair iteration r8 leaves the ACVP Lean sources and call graph frozen. Source-logical checking now
uses an intentionally narrow quotation-free/metaprogramming-free grammar before extracting
declarations. Lake's re-elaborated disposable TOML, rather than literal source parsing, controls the
executable-root claim and rejects the exact r7 macro project whose active root is `Wrong.Root`.
Immediately before runtime, the wrapper repeats that audit and captures stdout in an ordinary file;
an exact 154-byte file comparison preserves all terminal LFs and the executable status. F-048/F-049
record these implementer dispositions as pending review. F-044--F-047 remain pending until S01 as a
whole is independently accepted, and F-018 continues to disclose manual-inventory incompleteness.

Independent review r8 at `reviews/S01-authority-and-conformance-review-r8.md` is an immutable
`FAIL`. It confirmed the quotation/translated-root and byte-file repairs but demonstrated both
target-level and inherited package-level `srcDir` redirection: alternate source bytes under the same
module name emitted the exact accepted 154-byte output.

Repair iteration r9 keeps the three ACVP Lean sources and their API frozen. The docs/configuration
gate requires absent package `srcDir`, `moreLeanArgs`, and `weakLeanArgs`, plus an exact parser target
containing only the expected name/root. It reconstructs both r8 `WrongSrc` builds and the r7
`Wrong.Root` case. Immediately before runtime, the full wrapper invokes Lake with `-R -H -J query`,
strictly parses the current non-synthetic JSON traces, requires the exact frozen source path and
SHA-256, follows structured hashes through generated C and the ParserTests export object into the
queried executable, checks ordinary non-symlink paths and the executable hash file, and executes
that exact resolved binary. Eight structured/JSON, two output-type, two `WrongSrc`, and two stale-
transition mutations exercise this layer. F-050 records the r8 finding as remediated pending review;
F-044--F-049 remain pending until S01 acceptance, and F-018 remains open.

Independent review r9 at `reviews/S01-authority-and-conformance-review-r9.md` is an immutable
`FAIL`. It confirmed the source-selector and ParserTests trace repair but found that the executable
trace token and adjacent `.hash` were metadata-to-metadata evidence: the gate did not compute a
hash from the current executable file. It also observed that Schema and StrictJson were not
followed through the structured trace chain.

Repair iteration r10 leaves `HashSig/**` and the three ACVP Lean sources frozen. Its historical
byte-pinned helper ran the then-selected toolchain hash API, with exactly
one ordinary non-symlink input and one canonical hash record. The resolver requires trace, sidecar,
and current executable hashes to agree. The wrapper carries the resolved path and expected hash in
ordinary files, hashes immediately before and after execution, preserves stderr/status, and retains
the exact 154-byte stdout comparison. The structured trace gate now follows ParserTests, Schema,
and StrictJson from exact frozen sources through generated C/export objects into the executable and
requires their two direct import-artifact relationships. The then-current focused partition included the
exact same-output executable replacement, a different-output replacement, helper output/status,
all three module chains, both imports, prior WrongSrc/stale cases, and file types. F-051 records the
r9 defect as remediated pending review; F-044--F-050 remain pending until S01 acceptance.

The before/after checks are sequential, not atomic. They assume no concurrent writer modifies the
binary between checks; a post-execution mismatch is detected only after execution. The installed
Lake/Lean toolchain remains trusted. These limitations are recorded in ASM-012 and TCB-013 and do
not turn parser/schema-format runtime evidence into implementation-conformance evidence.

Repair iteration r10 validation on 2026-08-24:

- historical r10 current-byte/build-input suite: PASS for its then-current partition (eight legacy trace/JSON,
  21 three-module source/C/object/link, four direct imports, eight helper/hash, five live helper CLI,
  two output types, both WrongSrc levels, both stale transitions, and three executable-replacement/
  current-byte cases). The exact same-output 154-byte replacement was distinguished by Lake's
  current-file hash and rejected before sentinel execution;
- normal harness and real-sibling docs-only wrapper: PASS with the existing 23 source/token/static-
  Lake, nine selector-source, thirteen translated-Lake, six authority, ten FIPS-profile, fourteen
  scope/active/claim, six matrix, and eight filesystem/replacement mutations;
- offline and optional exact-checkout provenance: PASS; both `/tmp/slhdsa-s01-acvp-server` and
  `/tmp/slhdsa-s01-acvp-protocol` reproduced the pinned commits, full-suite counts, projections,
  source hashes, and protocol composite;
- direct parser and attested wrapper execution: PASS at exactly 154 bytes and three LF-terminated
  records, with 16 positive, 52 fail-closed negative, and 68 total cases. The shell rejected six
  stdout-file mutations, a successful wrong executable, a nonzero producer, and four before/after
  hash-file mutations;
- `lake build HashSigTest`: PASS, 2,743 jobs. The external probe resolved eight public/root names,
  rejected thirteen private/false names, and rejected the dynamic nonexistent-public mutation;
- complete validation: PASS with 3,007-job repository, 2,744-job HashSig, and 2,743-job HashSigTest
  builds; elaborated policy and compiled initializer fixtures; extern/interop isolation; and both
  KATs. Only the inherited sorry and absent optional native-submodule warnings remained;
- explicit `update-lib.sh`: PASS with no update necessary. Python/Bash syntax, duplicate-aware
  parsing of twelve JSON and one JSONL files, active-scope symlink/special/debris checks,
  `git diff --check`, and an empty `HashSig/**` diff: PASS;
- TeX from `docs/slhdsa/report` to `/tmp/slhdsa-s01-r10-tex`: PASS, six pages and 284,883 bytes.
  `pdftotext` confirms F-051, the historical hash helper, the no-concurrent-writer limitation, and
  that S01 r10 remains pending;
- whole `lakefile.lean`: 17,413 bytes, SHA-256
  `d7c91f35fe23c276335327ab00c8119eafd88a306bb6a27ae82b96ad6dbdde0e`; its exact hash-script suffix:
  603 bytes, SHA-256 `fc859c45e415af2340b4c2b0f796d11ab042d9fc2dd3387647426386bf89fd0e`;
- current matrix pin changes are limited to assumptions (3,113 bytes,
  `1654bc508c663991af5ed82b94145aa040e0eab4f13e024a1134a4ca5b5337e8`) and TCB (4,059 bytes,
  `f0b81b729f83484ccc3902e00c38fb0ef7f7320e0e1c8520eb5c90556bcabc98`); the other six exact pins
  remain unchanged;
- immutable r9 remains 14,161 bytes, 231 lines, SHA-256
  `52db8de84cf122c066fa4dd2928dd4d93c99f45754d95681cbfe7ed2610759fa`. The r10 PENDING handoff is
  7,585 bytes, 124 lines, SHA-256
  `f3ed05df575faa3d9ca71734a1bfa6465d60e0e74c4a665be7bc84c1316522f8`;
- branch `codex/sphincsplus-formalization`, HEAD
  `f1853af40da1efa11a71c2d7011996eebdbf6938`; no commit or PR. Disposable debug projects and direct
  parser stdout were removed; test-suite temporary roots were removed by their own cleanup.

Independent review r10 at `reviews/S01-authority-and-conformance-review-r10.md` is an immutable
`FAIL`. It confirmed the current-byte, exact-output, three-module, and import checks but demonstrated
that a reusable root-package build and its records could be changed coherently to describe an
unrelated exact-output executable. It also found that Lake's 16-hex build token was not a
cryptographic executable identity. This is F-052.

Repair iteration r11 leaves `HashSig/**` and all three frozen ACVP Lean sources unchanged. The
byte-pinned package configuration consumes a checked `buildDir` setting while ordinary builds retain
Lake's default. The parser wrapper creates a mode-700 temporary parent and designates one exact
initially absent child, then invokes Lake with `-R -H --no-cache` and that build-directory override.
It requires the resolved executable and every root-package generated C file, object, trace, and
sidecar for ParserTests, Schema, and StrictJson to be ordinary non-symlink files inside that child.
The exact source inputs remain the canonical frozen worktree files; external dependency artifacts
remain a disclosed TCB input. The records are not claimed to authenticate themselves: their
relevance comes from being generated in the initially empty private output during the accepted
invocation by the trusted installed Lake/Lean/compiler.

The r10 Lake hash script is removed. The checker instead opens the exact fresh executable with
`O_NOFOLLOW`, verifies path/fd identity, streams current bytes through Python SHA-256, and rejects an
identity, size, or modification-time change across the read. The wrapper binds the resolved path
and expected SHA-256 in ordinary exclusive files, recomputes immediately before and unconditionally
after exact-path execution, and preserves the executable's stderr/status and exact 154-byte stdout
comparison. These checks remain sequential and assume no concurrent writer; they do not claim an
atomic replacement barrier or implementation conformance.

The historical focused r11 suite passed its then-current partition: eight legacy structured/JSON, 21 three-module
source/object/link, four import, nine SHA-256 output/binding, six SHA-256 CLI, two output-type, two
WrongSrc, two stale-transition, five fresh-root, five query-output, and three replacement/cache
cases. The exact r10 coherent reusable-default-build reproducer accepts internally consistent
replacement records under the historical metadata-only predicate, while the accepted gate ignores
that default state, creates a separate fresh canonical executable, verifies it has no replacement
sentinel, and executes it at exactly 16/52/68 cases.

Repair iteration r11 validation on 2026-08-24:

- `python3 -B scripts/slhdsa/check-harness.py` and
  `./scripts/slhdsa/validate.sh --docs-only`: PASS. The normal harness retained 23 source/token/
  static-Lake, nine selector-source, thirteen translated-Lake, six authority, ten FIPS-profile,
  fourteen scope/active/claim, six matrix, and eight filesystem/replacement negative groups;
- offline and exact-checkout provenance: PASS. With `/tmp/slhdsa-s01-acvp-server` and
  `/tmp/slhdsa-s01-acvp-protocol`, the checker reproduced the pinned revisions, all 15 artifacts,
  full-suite counts, projections, root source, and protocol composite;
- `lake exe slhdsa_acvp_parser`: PASS with exactly 154 bytes, SHA-256
  `0e726bc985fa93c02e34c66d79b5b3a52947cecd93e0803a611a9be3ab581c07`, and the three
  LF-terminated 16-positive/52-negative/68-total records;
- `lake build HashSigTest`: PASS, 2,743 jobs. The external dependency probe resolved eight
  public/root names, rejected thirteen private/false names, and rejected `Does.Not.Exist`;
- the first complete wrapper run exposed that Lake retained the disposable `buildDir` in its
  elaborated package configuration after the bound parser gate, so the subsequent policy audit
  could not locate default `HashSig` oleans. The repair now requires a second translated-config
  audit after the post-execution SHA-256 to restore the byte-pinned default configuration; a direct
  restored-config policy audit and the subsequent complete wrapper rerun both pass;
- `./scripts/slhdsa/validate.sh`: PASS after that integration repair, including 3,007-job repository,
  2,744-job HashSig, and 2,743-job HashSigTest builds; the fresh 16-action parser build; all
  then-current focused fresh-build mutations; exact 16/52/68 runtime; both configuration audits; elaborated
  source policy and compiled initializer fixture; extern/interop isolation; and both KATs. Only the
  inherited sorry and absent optional native-submodule warnings remain;
- `./scripts/update-lib.sh`: PASS with no update necessary. Python and Bash syntax, duplicate-aware
  parsing of twelve JSON files and one JSONL file, active tracked/untracked hygiene, `git diff
  --check`, debris checks, and an empty `HashSig/**` diff: PASS;
- TeX compilation to `/tmp/slhdsa-s01-r11-tex-SeJhRe`: PASS, six pages and 284,735 bytes.
  `pdftotext` confirms F-052, fresh output, SHA-256, r11 pending, and S02 blocked;
- the frozen ACVP source SHA-256 values remain `20f9aff3...7089` (StrictJson),
  `3ccab70a...33a0` (Schema), and `1a56fd4f...5cd5` (ParserTests). `lakefile.lean` is 17,087
  bytes/380 lines with SHA-256 `ed17f54b243bed2ed6db5e4ab5f3a83e29ca5c3dcaeabd7f714eff01ce3e5f8f`;
- matrix changes are limited to assumptions (3,121 bytes,
  `861b7aeec6bfcdf3773fa25908fc729f1887b972cbd7057dcd207a5a8d89cb1a`) and TCB (4,129
  bytes, `e23aefab388904004a155391e5d5b97836c6bab6a57682a92fc30cf705abb7ce`); the other six
  current matrix pins remain unchanged;
- immutable r10 remains 15,852 bytes/258 lines with SHA-256
  `cccabc4e95357055838ae8052f00f6d372ca8a29185d408dee81d916c5a138c1`. The r11 PENDING
  artifact is 8,682 bytes/140 lines with SHA-256
  `db242f3b7b40a8f1a50206ecdfaa92d7dd82c56e0b6484b45d0d0930dab8ab28`; and
- branch `codex/sphincsplus-formalization`, HEAD
  `f1853af40da1efa11a71c2d7011996eebdbf6938`; no commit or PR. The focused suites and wrapper
  removed their temporary roots. TeX output remains only in the named `/tmp` directory for
  inspection and is not repository state.

Independent review r11 at `reviews/S01-authority-and-conformance-review-r11.md` is an immutable
`FAIL`. It confirmed the private fresh build, coherent-cache exclusion, exact executable SHA-256,
default restoration, and nominal gates. It then replaced 18 current module/C/object/sidecar paths
with symlinks that the resolver did not inspect, and demonstrated that `root/../outside` escaped the
standalone SHA-256 helper's lexical containment. These are F-053 and F-054.

Repair iteration r12 leaves `HashSig/**`, the three frozen ACVP Lean sources, and the Lake target
unchanged. It defines one exact eight-path current artifact manifest for each of ParserTests,
Schema, and StrictJson: `.olean`, its sidecar, module trace, generated C, its sidecar, export object,
its sidecar, and object trace. All 24 files are opened ordinary/no-follow under the fresh child. The
module, C, and export-object sidecars must be exact 16-hex records equal to the structured `o[0]`,
`c`, and object/link tokens. `.ilean`, `.ir`, `.olean.server`, `.olean.private`, setup, server, and
other private-support outputs are outside the consumed/claimed evidence set.

Raw CLI paths now reject every non-canonical absolute spelling before Path construction. Shared
functions require a distinct non-root absolute root/file pair and one nonempty proper relative path
without dot/parent components. The Linux walker anchors at `/` and uses descriptor-relative
no-follow directory and file opens with device/inode checks at every component; stable reads retain
both file and parent descriptors for the final device/inode/size/mtime comparison. Exclusive gate
records use the same parent-descriptor boundary.

The historical focused r12 resolver passed its then-current cases. New coverage was the exact 18-symlink reproducer, 96
missing/inside-symlink/outside-symlink/FIFO cases over all 24 manifest paths, 24 manifest-alias
cases, nine sidecar-token mismatches, and twenty canonical-path/shared/CLI cases. All mutations are
confined to the fresh `/tmp` root, restored before return, and validated again before the exact
fresh executable path and SHA-256 are released.

Repair iteration r12 validation on 2026-08-24:

- `python3 -B scripts/slhdsa/check-harness.py` and
  `./scripts/slhdsa/validate.sh --docs-only`: PASS. The historical focused fresh-build resolver passed
  cases: eight legacy structured/JSON, 21 three-module source/object/link, four import, nine
  SHA-256 output/binding, six SHA-256 CLI, two output-type, two WrongSrc, two stale-transition,
  five fresh-root, five query-output, three replacement/cache, twenty canonical-path/shared/CLI,
  130 current-artifact path/type/metadata, and one nominal resolution case;
- offline and exact-checkout provenance: PASS. With `/tmp/slhdsa-s01-acvp-server` and
  `/tmp/slhdsa-s01-acvp-protocol`, the checker reproduced the pinned revisions, all 15 artifacts,
  full-suite counts, projections, root source, and protocol composite;
- direct `lake exe slhdsa_acvp_parser`: PASS with exactly 154 bytes, SHA-256
  `0e726bc985fa93c02e34c66d79b5b3a52947cecd93e0803a611a9be3ab581c07`, and the three
  LF-terminated 16-positive/52-negative/68-total records;
- `lake build HashSigTest`: PASS, 2,743 jobs. The external dependency probe resolved eight
  public/root names, rejected thirteen private/false names, and rejected `Does.Not.Exist`;
- `./scripts/slhdsa/validate.sh`: PASS, including 3,007-job repository, 2,744-job HashSig, and
  2,743-job HashSigTest builds; the fresh parser build; all then-current focused cases; exact 16/52/68
  runtime; translated configuration and fresh artifact validation; elaborated source policy and
  compiled initializer fixture; extern/interop isolation; and both KATs. Only the inherited sorry
  and absent optional native-submodule warnings remain;
- `./scripts/update-lib.sh`: PASS with no update necessary. Python and Bash syntax, duplicate-aware
  parsing of twelve JSON files and one JSONL file, active tracked/untracked whitespace/tab/hygiene,
  `git diff --check`, debris checks, and an empty `HashSig/**` diff: PASS;
- TeX compilation to `/tmp/slhdsa-s01-r12-tex-ViYjpw`: PASS, six pages and 285,174 bytes.
  `pdftotext` confirms F-053/F-054, the 24-file manifest, descriptor-relative traversal, r12
  pending, and S02 blocked;
- the frozen ACVP source SHA-256 values remain `20f9aff3...7089` (StrictJson),
  `3ccab70a...33a0` (Schema), and `1a56fd4f...5cd5` (ParserTests). `lakefile.lean` remains 17,087
  bytes/380 lines with SHA-256 `ed17f54b243bed2ed6db5e4ab5f3a83e29ca5c3dcaeabd7f714eff01ce3e5f8f`;
- matrix changes are limited to assumptions (3,199 bytes,
  `1b35c230fcaffe63d73aa68e7d9afb44120dfa834879e6f010183fbc80892196`) and TCB (4,281
  bytes, `da21c7f9425a4252cf37d09a60386451279c0d284ff9dd51070258ead8cb892d`); the other six current
  matrix pins remain unchanged;
- immutable r11 remains 22,427 bytes/434 lines with SHA-256
  `e9f459db757e8f584fed113bd42b0df947c1660b74bc7202b0957d9ba98690ff`. The r12 PENDING
  artifact is 7,759 bytes/143 lines with SHA-256
  `18ff24f56956a3534758062dc822c37f862b549e47faf38374957007fef3b277`; and
- branch `codex/sphincsplus-formalization`, HEAD
  `f1853af40da1efa11a71c2d7011996eebdbf6938`; no commit or PR. The focused suites and wrapper
  removed their temporary roots. TeX output remains only in the named `/tmp` directory for
  inspection and is not repository state.

Independent review r12 at `reviews/S01-authority-and-conformance-review-r12.md` is an immutable
`FAIL`. It confirmed the canonical path and 24-file current-artifact repairs but found that a newly
opened directory child leaked when its post-open `fstat` or identity check failed. It also found
that active count prose double-counted the SHA CLI subset and retained historical totals. These are
F-055 and F-056.

Repair iteration r13 immediately owns every opened directory child and closes it on typed
pre-transfer validation exceptions. Root-chain and relative-intermediate identity and `fstat`
failures each run sixteen times under `/tmp`; exact `/proc/self/fd` identity maps and an unrelated
sentinel remain unchanged. The checker observes one centralized category mapping and rejects any
arithmetic, subset, nominal, or active-document disagreement. The six SHA CLI cases are included in
the path/CLI category and nominal successful resolution is excluded.

focused-parser-partition: legacy=8; source-object-link=21; imports=4; sha-output-binding=9; path-cli=20; output-types=2; artifacts=130; wrong-srcdir=2; stale=2; fresh-root=5; query-output=5; replacement-cache=3; descriptor-lifecycle=6; descriptor-ownership=17; total=234; sha-cli-is-subset-of-path-cli=6; nominal-success-excluded=true

Repair iteration r13 validation on 2026-08-25:

- the direct focused resolver performs a genuine 16-action build and passes its then-current
  mutation partition. The current r14 suite has six descriptor-lifecycle cases, each repeating
  sixteen failures with an exact `/proc/self/fd` identity map and unrelated sentinel unchanged;
- `python3 -B scripts/slhdsa/check-harness.py` and
  `./scripts/slhdsa/validate.sh --docs-only`: PASS. The normal checker also rejects the semantic
  double-counted-subset mutation and an appended stale active-document total;
- offline and optional exact-checkout provenance: PASS. The optional server and protocol roots
  reproduce their pinned commits, artifacts, suite counts, projections, root source, and composite;
- direct `lake exe slhdsa_acvp_parser`: PASS with exactly 154 bytes, three lines, SHA-256
  `0e726bc985fa93c02e34c66d79b5b3a52947cecd93e0803a611a9be3ab581c07`, and exact
  16-positive/52-negative/68-total records;
- `lake build HashSigTest`: PASS, 2,743 jobs. The external dependency probe resolves eight
  public/root names, rejects thirteen private/false names, and rejects `Does.Not.Exist`;
- `./scripts/slhdsa/validate.sh`: PASS, including 3,007-job repository, 2,744-job HashSig, and
  2,743-job HashSigTest builds; fresh parser build and all focused cases; exact parser runtime;
  configuration audits; elaborated policy and compiled initializer fixture; extern/interop
  isolation; and both KATs. Only inherited sorry and absent optional native-submodule warnings
  remain;
- `./scripts/update-lib.sh`: PASS with no update necessary. Python/Bash syntax, duplicate-aware
  parsing of twelve JSON files and one JSONL file, active tracked/untracked whitespace/tab/hygiene,
  `git diff --check`, debris checks, and an empty `HashSig/**` diff: PASS;
- TeX compilation to `/tmp/slhdsa-s01-r13-tex-Vic6MY`: PASS, six pages and 319,860 bytes.
  `pdftotext` confirmed F-055/F-056, the exact focused partition and total, the then-pending r13
  pre-review state, and S02 blocked;
- immutable r12 remains 20,025 bytes/347 lines with SHA-256
  `74277bebc85879dd563e8e6ef5c2b733d85ff6794d093bcaf5644699eed2c90f`. The r13 pre-review
  PENDING artifact was 7,030 bytes/124 lines with SHA-256
  `0879a2cfe29b01a16906dad1d2370fd98fbe96d687a3933b9d0c25f64d8ae09c`;
- checker SHA-256 is `302b84182aa0bd42b6409dc63b152276a7973553cbb9695497bbb0e51df345e1`.
  `validate.sh` remains `6cf9fd1b...9916`; `lakefile.lean` remains 17,087 bytes/380 lines and
  `ed17f54b...5f8f`. Frozen StrictJson/Schema/ParserTests remain `20f9aff3...7089`,
  `3ccab70a...33a0`, and `1a56fd4f...5cd5`;
- matrix changes are limited to assumptions (3,243 bytes,
  `1d60fedecc19ebdedee525791cc603211e8d84fcd4ae5256eeed354c31871d27`) and TCB (4,341
  bytes, `3a44ddfca30839fd02d0d34aef57bf3f855ef607448c7f7abec2470e375957f2`); the other six
  matrix pins remain unchanged; and
- branch `codex/sphincsplus-formalization`, HEAD
  `f1853af40da1efa11a71c2d7011996eebdbf6938`; no commit or PR. The focused build and direct parser
  output are disposable `/tmp` state. The exact-final-tree docs/full gates are rerun after this
  final evidence edit before the tree is frozen.

Independent review r13 at `reviews/S01-authority-and-conformance-review-r13.md` is an immutable
`FAIL`. It confirmed F-055/F-056 but found that an unexpected hook exception bypassed typed outer
cleanup and retained a parent descriptor (F-057), and that the temporary Lake build-directory
override was restored only on explicit success (F-058).

Repair iteration r14 closes a retained traversal parent for every propagated `BaseException`, while
preserving the original exception and suppressing cleanup-only close errors. Root-chain and
relative-intermediate unexpected hook `RuntimeError` cases join the four prior lifecycle cases;
each of all six repeats sixteen times with an exact unchanged `/proc/self/fd` identity map and an
unrelated live sentinel. The current mechanically derived partition appears above.

The full wrapper arms a private override-active flag immediately before the possibly mutating
resolver. Its non-recursive EXIT trap captures the initiating status first, disables errexit,
restores the default Lake configuration while the temp root still exists, and only then removes
temporary roots. It preserves an initiating nonzero status; a restore failure turns an otherwise
successful run into failure. Seven direct state-machine regressions cover explicit exit 7, errexit,
SIGTERM/143, initiating failure plus restore failure, success plus restore failure, normal success,
and representative resolve failure. SIGKILL cannot execute a shell EXIT trap.

Focused r14 evidence on 2026-08-25:

- the direct genuine fresh resolver/build suite passed its then-current mechanically observed cases,
  including 96 unexpected-exception lifecycle iterations across root and relative traversal;
- the extracted production wrapper cleanup state machine passes all seven cleanup regressions;
- immutable r13 remains 20,771 bytes/347 lines with SHA-256
  `104ac10c67ea471f772efd3e0319df5ce99db9b0e7fc0859a2a700564112fd21`;
- `python3 -B scripts/slhdsa/check-harness.py` and
  `./scripts/slhdsa/validate.sh --docs-only`: PASS, including administrative, exact matrix-pin,
  whitespace/type, authority, and offline provenance checks;
- optional checkout-backed provenance using `/tmp/slhdsa-s01-acvp-server` and
  `/tmp/slhdsa-s01-acvp-protocol`: PASS, reproducing all exact pinned artifacts/counts/projections;
- direct parser runtime: PASS with exactly 154 bytes, three lines, SHA-256
  `0e726bc985fa93c02e34c66d79b5b3a52947cecd93e0803a611a9be3ab581c07`, and exact
  16-positive/52-negative/68-total records;
- `lake build HashSigTest`: PASS, 2,743 jobs. The external dependency probe resolves eight
  public/root names, rejects thirteen private/false names, and rejects `Does.Not.Exist`;
- `./scripts/slhdsa/validate.sh`: PASS, including 3,007-job repository, 2,744-job HashSig, and
  2,743-job HashSigTest builds; the seven cleanup regressions; fresh parser build and all focused
  cases; exact parser runtime; configuration audits; elaborated policy and compiled initializer
  fixture; extern/interop isolation; and both KATs. Only inherited `sorry` and absent optional
  native-submodule warnings remain;
- `./scripts/update-lib.sh`: PASS with no update necessary. Python and Bash syntax, duplicate-aware
  parsing of twelve JSON files and fourteen JSONL records, `git diff --check`, and an empty
  `HashSig/**` diff: PASS;
- TeX compilation to `/tmp/slhdsa-s01-r14-tex`: PASS, six pages and 320,326 bytes. `pdftotext`
  confirmed F-057/F-058, the then-current focused partition, the SIGKILL limitation, r14 pre-review
  pending, and S02
  blocked;
- checker SHA-256 is `a9f0b42b437649ba8d6156bf9dbe81a9aa14fe04c89a4e829aa8aa9948c68413`;
  `validate.sh` is `1b9d89cf9d48b2c16ed72f00aaa7515b66e56f9fd05674e92238a7f17fa868e2`;
  `lakefile.lean` remains `ed17f54b243bed2ed6db5e4ab5f3a83e29ca5c3dcaeabd7f714eff01ce3e5f8f`.
  Frozen StrictJson/Schema/ParserTests remain `20f9aff3...7089`, `3ccab70a...33a0`, and
  `1a56fd4f...5cd5`;
- matrix changes are limited to assumptions (3,317 bytes,
  `8cf474f5a126a6e7be925dcf7c942cbf39463a12211bda49e20e792fbe3f58f4`) and TCB (4,491 bytes,
  `46058a4b2a519cc0639a9d3cd487401e9911b2529c4158e0382b3ead8a75d319`); the other six current
  matrix pins remain unchanged; and
- branch `codex/sphincsplus-formalization`, HEAD
  `f1853af40da1efa11a71c2d7011996eebdbf6938`; no commit or PR. The exact-final-tree docs/full gates
  are rerun after this final evidence edit before the tree is frozen.

Independent review r14 at `reviews/S01-authority-and-conformance-review-r14.md` is an immutable
`FAIL`. It confirmed F-057/F-058, but found direct and sequential close paths in the older
active-tree walker and retained parser consumers. A close-after-real-then-raise fault could mask an
active exception, skip and leak a later owner, or retry a consumed integer after forced reuse. This
is F-059.

Repair iteration r15 defines one `_OwnedDescriptor` for every bounded production acquisition and
one `_close_owned_descriptors` helper as the sole raw `os.close` site. `take()` marks the local
owner unowned before the close. Cleanup with an active exception attempts every still-owned close
once, records cleanup failures through the explicit `BaseException.add_note` implementation, and
rethrows the exact original object. Cleanup evidence uses internal labels and exception type names;
it never invokes a cleanup exception's dynamic string or representation methods. Nominal cleanup
attempts every owner and raises one deterministic `CheckFailure` with stable labels and the first
cleanup failure as cause. An AST inventory gate rejects any extra raw close call.

The older root/directory/recursive scanner and chain, `load_active_s01_files`, both modern traversal
functions, ordinary-file require/read/SHA consumers, fresh-root before/after validators, and
exclusive record output all use this discipline. Fifteen production close-after-release families
repeat sixteen times with two unrelated sentinels and exact `/proc/self/fd` identity maps. The old
chain additionally forces same-number `/dev/null` reuse and proves the reused descriptor remains
live while the newly opened child closes exactly once. The two root-found pre-review F-060 families
use an active `RuntimeError` whose overridden `add_note` raises and a cleanup error whose string and
representation methods raise; they prove base-note dispatch, safe deterministic nominal evidence,
exact original preservation, and cleanup of every owner.

Focused r15 evidence on 2026-08-25:

- a genuine fresh 16-action parser build and resolver passed the then-current r15 focused cases;
- descriptor-lifecycle remains six conceptual cases, and descriptor-ownership adds fifteen
  conceptual families with sixteen repetitions apiece;
- the raw-close AST guard reports exactly one production call inside the owner helper and rejects a
  disposable added direct-close function;
- both hostile-dispatch families repeat sixteen times with exact unchanged descriptor maps and two
  sentinels: the active custom `RuntimeError` retains the base-added safe note without invoking its
  override, while the nominal hostile cleanup retains the exact cause and deterministic type-only
  `CheckFailure` after attempting both owners;
- immutable r14 remains 19,084 bytes/330 lines with SHA-256
  `347281880d2221e2e5e8386aa8898baee389e7d62cf50adb12031b8db0ae15f8`;
- `python3 -B scripts/slhdsa/check-harness.py` and
  `./scripts/slhdsa/validate.sh --docs-only`: PASS, including the then-current r15 partition,
  administrative and matrix-pin checks, whitespace/type scans, authority checks, and offline
  provenance;
- optional checkout-backed provenance using `/tmp/slhdsa-s01-acvp-server` and
  `/tmp/slhdsa-s01-acvp-protocol`: PASS, reproducing the pinned artifacts, counts, and projections;
- direct parser runtime: PASS with exactly 154 bytes, three lines, SHA-256
  `0e726bc985fa93c02e34c66d79b5b3a52947cecd93e0803a611a9be3ab581c07`, and exact
  16-positive/52-negative/68-total records;
- `lake build HashSigTest`: PASS, 2,743 jobs. The external dependency probe resolves eight
  public/root names, rejects thirteen private/false names, and rejects `Does.Not.Exist`;
- `./scripts/slhdsa/validate.sh`: PASS, including 3,007-job repository, 2,744-job HashSig, and
  2,743-job HashSigTest builds; the seven Bash cleanup regressions; fresh parser build and all r15
  focused cases; exact parser runtime; configuration audits; elaborated policy and compiled
  initializer fixture; extern/interop isolation; and both KATs. Only inherited `sorry` and absent
  optional native-submodule warnings remain;
- `./scripts/update-lib.sh`: PASS with no update necessary. Python and Bash syntax,
  duplicate-aware parsing of the twelve S01 JSON files and fourteen JSONL records,
  `git diff --check`, type/debris scans, and an empty `HashSig/**` diff: PASS;
- TeX compilation to `/tmp/slhdsa-s01-r15-hostile-tex`: PASS, six pages and 320,974 bytes.
  `pdftotext` confirmed F-059/F-060, the then-current r15 partition, r15 pending, and S02
  blocked;
- checker SHA-256 is `d7b137ca25ce9d58948d4d13355bc4c23ebe7db47fd408b8195477459f1aa47a`;
  `validate.sh` is `1b9d89cf9d48b2c16ed72f00aaa7515b66e56f9fd05674e92238a7f17fa868e2`;
  `lakefile.lean` remains `ed17f54b243bed2ed6db5e4ab5f3a83e29ca5c3dcaeabd7f714eff01ce3e5f8f`.
  Frozen StrictJson/Schema/ParserTests remain `20f9aff3...7089`, `3ccab70a...33a0`, and
  `1a56fd4f...5cd5`;
- matrix changes are limited to assumptions (3,433 bytes,
  `b202031f48ee4d17d4eb0fd79935cfa11833ecbe76db4b008ad991bb977562a1`) and TCB (4,578 bytes,
  `848e217ae1aa71b78707d3fe670e5e4421cfcbfb3f1b068515df186edf2f54f8`); the other six current
  matrix pins remain unchanged; and
- branch `codex/sphincsplus-formalization`, HEAD
  `f1853af40da1efa11a71c2d7011996eebdbf6938`; no commit or PR. The exact-final-tree docs/full gates
  are rerun after this final post-authorization evidence edit before the tree is frozen.

At the prior r15 handoff, F-059 and root-found pre-review F-060 were
`REMEDIATED-PENDING-REVIEW`, with F-044--F-058 still pending. The then-current r15 checklist was
`PENDING`; it is now the immutable independent r15 `FAIL` described below. S02 remained blocked.

## Repair iteration r16 — hostile evidence removal and alias-aware scoped inventory

Independent r15 at `reviews/S01-authority-and-conformance-review-r15.md` is an immutable `FAIL` at
23,018 bytes/397 lines, SHA-256
`f153f6bddad34a669ef40d8095c0512d4c07b4e29384cebb60bfa9764d788734`. It confirmed the bounded
production owner migration but found two LOW defects. F-061 records that cleanup still formatted a
hostile nonempty `str` subclass stored as an exception class's `__name__`, masking the exact active
original and nominal deterministic failure. F-062 records that the shallow AST scan accepted the
nine independent alias/discard/rebinding mutations and that distinct owner objects holding one
integer could close a forced same-number replacement.

R16 removes all exception-derived cleanup evidence. `_close_owned_descriptors` first preflights the
entire owner list, marks every live owner unowned, groups descriptor integers, and closes every
unique integer at most once. Evidence is made only from fixed builtin strings and builtin integer
counts. With an active exception, explicit `BaseException.add_note` is best effort and cannot
replace the exact original. Nominal close failures retain the exact first cleanup object only as
cause; distinct-owner aliasing produces a deterministic invariant `CheckFailure` after all unique
integers have been attempted. Hostile type-name/base-note and active/nominal forced-reuse alias
families repeat 32 times with exact fd maps and two sentinels. Same-object repetition remains safe,
while distinct descriptors created by `dup` close independently.

The semantic AST policy is intentionally exact and narrow for the frozen checker source. It
enumerates every direct `os.open`/`os.dup`/`os.close` attribute, every `os` load, protected-symbol
declaration/rebinding, all owner constructor/annotation shapes, all eight `take` transfers, all 52
cleanup-helper consumers, and every registered test-only `real_close`/`real_dup` call. The exact
registry contains 10 production acquisitions/one close and 14 test acquisitions/18 captures. It
rejects 30 literal, assigned, imported, `getattr`, dynamic-import/evaluation, module/container alias,
discard, take-discard, rebinding, opposite-declaration, lifecycle-consumer, and test-alias mutations.
This does not claim that arbitrary Python reflection outside the explicitly banned/registered syntax
is impossible.

Focused r16 boundary evidence on 2026-08-25:

- the exact scoped production inventory and all 30 disposable semantic AST mutations pass;
- all 234 mechanically observed focused cases pass against the current parser build, including 17
  descriptor-ownership cases and the unchanged six descriptor-lifecycle cases;
- the hostile active/nominal and distinct-owner active/nominal families repeat 32 times with no fd
  leak, unchanged sentinels, preserved originals/causes, and no replacement-fd retry;
- immutable r15 matches its required hash/size/line count; frozen StrictJson/Schema/ParserTests and
  `lakefile.lean` remain byte-identical; and no `HashSig/**` path is modified;
- checker SHA-256 is `c70856b91d5080e13b688102592384f3d1c57e9f542dc947aa1e3799a1be84b8`;
  assumptions is 3,472 bytes at
  `f62161b131a73dab915f08557f0d6c37971a6857ee60bd4f9f38239c32db3804`; TCB is 4,614 bytes at
  `ef2556fed1d15f66c0567fe609c4a6cd0e32d3ecf48c0f9f583c065ba382284b`; the other six matrix
  pins remain unchanged;
- the r16 PENDING checklist is 8,957 bytes/138 lines at
  `5efb00229fb52882e665cf51bd03643ecd0c6f7816467b0856819967bf3b24b8`;
- the normal checker and docs-only wrapper pass, including the exact 30-case AST policy suite;
  offline provenance passes, and optional pinned checkout provenance verifies both server and
  protocol roots;
- direct parser output is exactly 154 bytes/three lines at SHA-256
  `0e726bc985fa93c02e34c66d79b5b3a52947cecd93e0803a611a9be3ab581c07`, with exact
  16-positive/52-negative/68-total records; `lake build HashSigTest` passes 2,743 jobs, and the
  dependency probe resolves eight public/root names while rejecting thirteen private/false names
  plus `Does.Not.Exist`;
- two serialized full validation runs pass the 3,007/2,744/2,743-job builds, fresh 16-action parser
  build, all 234 focused cases, exact parser runtime, seven shell cleanup regressions, policy audit,
  initializer fixture, isolation checks, and both KATs; `./scripts/update-lib.sh` reports no update;
- duplicate-aware Python/JSON/JSONL and Bash syntax, comprehensive scope/type/debris hygiene,
  `git diff --check`, and an empty `HashSig/**` diff pass; and
- TeX compiles to a seven-page 322218-byte PDF in `/tmp`; extracted text confirms F-061/F-062,
  descriptor ownership 17/total 234, r16 pending, and S02 blocked. The temporary output was removed.

Independent r16 is PASS with no blocking findings. Its immutable artifact is 20,920 bytes/335 lines
at SHA-256 `d044a7601c99101ba2d4ec8190a23142a5479da005aae249d75f36cceffcd465`.
That verdict administratively fixes F-030--F-062, accepts S01, and makes S02 eligible; it does not
discharge COV-005, F-015, F-016, or F-018. The two nonblocking unused-variable observations require
no code churn. The accepted descriptor/AST machinery is retained and frozen, not a bootstrap for
further policy ratcheting: successor sessions center on Lean deliverables and reopen it only for a
concrete regression. No commit or PR was made.
