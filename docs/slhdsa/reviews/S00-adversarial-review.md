# S00 adversarial review

Verdict: **FAIL**

Reviewer: independent sub-agent `s00_harness_review`

Reviewed commit: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938` plus the uncommitted S00
allowlisted tree under `docs/slhdsa/**` and `scripts/slhdsa/**`

Date: 2026-08-24

Independence statement: the reviewer did not implement S00 and made no repository edits. The review
started from the prompt, primary sources, repository state, inventories, validators, and diff.

## Required checks

- [x] Scope/profile matrix prevents normative, abstract-security, legacy, C13, and deployment claims
  from leaking into one another.
- [ ] Every pinned hash/revision and authority classification is reproduced.
- [ ] CCS coefficients, FIPS/round-3 extraction, and EasyCrypt abstraction corrections are checked
  directly against primary sources.
- [x] Every validated current-code defect is represented as an open obligation/finding.
- [x] Session ordering fixes security/oracle architecture before refactors and reductions.
- [x] Each future session has inputs, allowlist, deliverables, gates, review, and re-review stop rule.
- [ ] CSV/JSONL schemas and seed data are internally consistent and do not claim complete extraction.
- [ ] Validators are deterministic, fail closed, and do not mutate the repository.
- [ ] Exact sorry allowlist and prohibited-declaration checks behave on positive and negative tests.
- [x] Baseline runtime/elaboration, `#print axioms`, and report compilation are reproduced.

## Commands and evidence

Reproduced:

- `./scripts/slhdsa/validate.sh --docs-only`: PASS.
- `bash -n scripts/slhdsa/validate.sh`: PASS.
- `./scripts/slhdsa/validate.sh`: PASS; repository build 3007 jobs, HashSig build 2744 jobs,
  generated umbrella, extern/interop isolation, and both regression executables passed.
- Exact `#print axioms` footprints in `validation.md`; the omitted concrete
  `shaPrimitives_perfectlyComplete` root was also checked.
- `latexmk` with output under `/tmp`: clean three-page PDF build.
- Primary PDF/report/prompt hashes, EasyCrypt/VCVio revisions, current ACVP anchors, and issue-469
  state. The undocumented source-tree composite recipe was not reproducible from the ledger alone.
- Negative Lean fixtures showed that admitted and prohibited syntax variants evade the scanner;
  Lean accepted those fixtures.

## Findings and dispositions

1. **CRITICAL — policy validator is not fail-closed.** It misses inline `by sorry`, `admit`,
   modifier/attribute-prefixed axioms and unsafe declarations, multiline extern attributes, and
   multiline linter suppression. It scans only `HashSig/SLHDSA/**` although the stated sorry policy
   covers `HashSig/**`; an evading sorry is misreported as monotone removal. The PENDING substring
   check both accepts conflicting verdict text and prevents a legitimate PASS from validating.
2. **HIGH — security/source corrections are incomplete.** Record that the original CCS full tight
   proof was invalidated at the WOTS step and cannot be proof authority without the later repair;
   preserve Appendix A's nuanced FORS changes and separate WOTS checksum-shift correction; state
   that EasyCrypt mechanizes classical probabilistic games, not quantum/QROM semantics or lifting.
3. **HIGH — target specification is not exact enough to validate later sessions.** Add all Table-2
   tuples/sizes; exact pure/pre-hash message grammars, OIDs, digest lengths, and allowed hashes; and
   exact SHA2/SHAKE primitive input grammars.
4. **MEDIUM — declaration inventory coordinates are false.** Multiple end columns exceed the source
   line or end on blank lines. Validate both coordinates and strengthen bootstrap consistency.
5. **MEDIUM — provenance is ambiguous.** Document the composite source-hash recipe and make the
   sibling-reference root/locators explicit and reproducible.
6. **MEDIUM — saved proof evidence is incomplete.** Add the concrete completed load-bearing root to
   the exact `#print axioms` record.
7. **MEDIUM — decision state is contradictory.** The current gate requires maintainer acceptance of
   scope decisions, while D-001 through D-005 already say `ACCEPTED` without an approver or recorded
   acceptance artifact. Use a status that distinguishes an orchestrator proposal from owner approval.
8. **LOW — generated Python bytecode pollutes the tree.** Remove it and prevent recurrence.

Every finding remains open. The repaired session requires independent review in
`S00-adversarial-review-r1.md`; this failed artifact is retained unchanged.

## Verdict rationale

Executable baselines and several corrections were sound, but the critical scanner holes permit the
admitted/unsafe changes the harness claims to reject. False inventory coordinates and missing
target/source detail also prevent a reliable pre-formalization contract. S00 fails; S01 is blocked.
