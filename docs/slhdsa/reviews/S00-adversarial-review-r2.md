# S00 adversarial review — re-review 2

Verdict: **FAIL**

Reviewer: independent sub-agent `s00_harness_r2_review`

Reviewed commit/tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938` plus the r2 repaired,
uncommitted S00 allowlisted tree

Date: 2026-08-24

Independence statement: the reviewer did not implement any S00 revision and made no edits.

## Required checks

- [ ] Every finding in the original review and r1 has an evidence-backed disposition.
- [ ] All identifier-prefixed interpolated strings are conservatively rejected, so no embedded term
  can hide an admission.
- [ ] Partial/unsafe/runtime-override declarations are rejected and covered by fixtures.
- [ ] Admission/axiom/metaprogramming/extern/linter policy remains fail-closed over `HashSig/**`.
- [ ] Source/specification/provenance/span/decision/proof records still reproduce.
- [ ] Docs-only/full validation, report compilation, hygiene, and traceability pass.

## Commands and evidence

The reviewer compiled the four fixtures below with `lake env lean`, ran `#print axioms` where
applicable, and called `policy_findings` on the same source. No repository file was modified.

## Prior-finding dispositions

The earlier `m!"..."` and `partial def` cases were rejected after r1, but qualification,
interpolator token separation, other imported interpolation macros, and a built-in command
metaprogramming surface remained open.

## New findings

1. **CRITICAL — qualified admission bypass:** `_root_.sorryAx False true` compiled with `sorryAx`,
   while the checker returned no finding.
2. **CRITICAL — separated interpolation bypass:** `m! "{(by sorry : String)}"` and newline/comment
   variants compiled with `sorryAx`; the checker required a contiguous prefix.
3. **CRITICAL — other imported interpolators:** `println! "{(by sorry : String)}"` compiled with
   `sorryAx`; the checker recognized only its limited prefix grammar.
4. **CRITICAL — command metaprogramming axiom injection:** built-in `run_cmd` invoking
   `Lean.addDecl (.axiomDecl ...)` injected a kernel axiom and was not prohibited.

## Verdict rationale

The policy remains bypassable by valid Lean. S00 r2 fails; S01 remains blocked. A repaired tree needs
a fresh r3 review.
