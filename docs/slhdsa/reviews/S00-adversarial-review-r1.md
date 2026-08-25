# S00 adversarial review — re-review 1

Verdict: **FAIL**

Reviewer: independent sub-agent `s00_harness_r1_review`

Reviewed commit/tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938` plus the repaired,
uncommitted S00 allowlisted tree

Date: 2026-08-24

Independence statement: the reviewer did not implement S00 or its first repair and made no edits.

## Required checks

- [x] Every finding in `S00-adversarial-review.md` has an evidence-backed disposition in the repaired
  session tree.
- [ ] Adversarial fixtures reject every admitted, axiom, unsafe, extern, and linter-bypass form
  while accepting the unchanged allowlisted source.
- [x] Verdict transitions are unambiguous and an accepted PASS remains validatable.
- [x] Source corrections and exact normative target tables/grammars match primary sources.
- [x] Every ledger locator/hash recipe and declaration source coordinate is reproducible.
- [x] Exact axiom footprints include every completed load-bearing bootstrap root.
- [x] Full validation, report compilation, tree hygiene, and traceability pass.

## Commands and evidence

The reviewer reproduced the repaired gates and then compiled two negative fixtures with
`lake env lean`, inspecting their declarations/axiom footprints. No repository file was modified.

## Prior-finding dispositions

The original eight findings were repaired in the reviewed tree: source/specification/decision/proof
records were corrected and reproduced; spans and provenance passed; full validation and report
compilation passed; bytecode debris was absent. This does not override the two new findings below.

## New findings

1. **CRITICAL — interpolated-string admission bypass.** The lexer handled only `s!"..."`.
   Valid `m!"{(by sorry : String)}"` elaborated with a warning and `sorryAx`, while the scanner
   skipped its body. Scan interpolation for every identifier-prefixed interpolator, with fixtures.
2. **HIGH — partial definition bypass.** A valid recursive `partial def` elaborated as an opaque
   partial/runtime definition but was not rejected because it lacks the literal `unsafe` modifier.
   Reject and test partial definitions as part of the unsafe/runtime policy.

## Verdict rationale

Both counterexamples violate the claimed fail-closed policy. S00 r1 fails; S01 remains blocked. The
repair must receive a fresh independent r2 review.
