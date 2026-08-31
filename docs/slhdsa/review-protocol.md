# Independent adversarial review protocol

## Independence and stop rule

The reviewer must not be the session implementer and must begin from the session inputs, primary
sources, diff, and generated inventories rather than the implementer's narrative. A review is PASS
only when every sampled and load-bearing item has evidence and there are no open issues. Any issue,
including documentation overclaim, is FAIL and blocks all successor sessions.

## Required review actions

1. Reproduce the relevant clean build/runtime commands and distinguish elaboration from execution.
2. Check the diff against the session allowlist and inspect every new axiom, `unsafe`, `extern`,
   `noncomputable`, linter suppression, `sorry`, and TCB change.
3. Review every changed load-bearing declaration in full, its quantifier order, side conditions,
   direct/reverse dependencies, and primary-source correspondence. Search helper dependencies for
   `False`, empty types/targets, impossible hypotheses, arbitrary distributions, and unbounded slack.
4. Run `#print axioms` on all completed load-bearing roots. `sorryAx` must be absent. The S00
   transitive allowlist is exactly `propext`, `Classical.choice`, and `Quot.sound`; these standard
   Lean axioms are recorded, not mislabeled as defects. Any other axiom is rejected, including one
   owned by an external module, unless a later reviewed gate and accepted assumption/TCB row change
   the policy.
5. Confirm vector hashes, licenses, revision, interface/mode, expected result, and positive coverage.
   Existing SHA2-128-24 and C13 KATs are C-reference regression vectors, not FIPS/ACVP conformance.
6. Evaluate every concrete loss/size/count at target parameters and check range/denominator/positivity.
7. Cross-check matrices, report, decisions, and findings against code. A finding is closed only by a
   disposition (`fixed`, `accepted-risk`, `rejected-with-evidence`, or `duplicate`) plus evidence.

## Current allowlist and monotonicity

No `sorry` is now permitted under `HashSig/**`. The S00 allowlist contained only the body of
`SLHDSA.slhdsa_euf_cma_security`; upstream main removed that deferred theorem during B01, so the
monotone allowlist is empty. No path or declaration may re-enter it, and all load-bearing roots
must report zero `sorryAx`.

At S00 no source/user admission constructor, axiom, unsafe/extern/partial declaration, runtime
implementation override, initializer/computed-field entry, or false linter suppression is permitted
under `HashSig/**`. The authoritative full gate audits the elaborated environment and attributes a
declaration to HashSig by its defining module (`HashSig` or `HashSig.*`), not by namespace. It permits
exactly the three standard transitive axioms above; all other self, generated, or externally owned
axiom dependencies fail. It also rejects
unsafe/source-partial constants, extern attributes, regular/builtin initializer entries, and
`implemented_by` overrides. For each imported HashSig module it rejects ordinary and IR
persistent-extension entries in the regular/builtin initializer, extern, and `implemented_by`
registries, even when an entry targets a declaration defined elsewhere. A source lexer checks known
dangerous spellings as defense in depth; it is not a Lean parser and is never used as evidence that
all macro/elaborator routes were recognized.

The persistent-extension review checks that imported ordinary/IR retrieval and current-state fixture
extraction feed the same surface-labelled mapper. The S00 raw fixture covers all four ordinary
attribute families. A separate compiled fixture uses an externally defined command to generate a
regular initializer from victim source containing no prohibited token. Reviewers must confirm a
programmatic meta import with `loadExts := false` exposes its nonempty IR entry through the same
production scanner/mapper, rejects both observed ordinary and IR entries with exact surface
identity, and leaves the side-effect
sentinel absent. The authoritative HashSig audit must use that static import path and must not
source-import HashSig.

The only partial constants accepted by the semantic gate are five exact Lean 4.33.1 compiler
`._unsafe_rec` auxiliaries listed in `validation.md` and `PolicyAudit.lean`. Each must retain the
compiler-recursion name relation, its parent's HashSig defining module, a present safe/non-partial
parent, and no unsafe/extern/init/override/axiom/`sorryAx` surface. The source lexer still rejects the
`partial` and `partial_fixpoint` spellings. Any helper addition/removal/rename fails. A future session may
change that policy only through an accepted decision, TCB row, narrowly scoped tests, an explicit
validator change, and independent reviewer signoff.

## Review artifact

Each review records reviewer/commit/date, scope, commands with runtime/elaboration labels, reviewed
declarations and sources, `#print axioms` output, quantitative evaluations, findings, dispositions,
and one verdict: `PENDING`, `PASS`, or `FAIL`. A failed artifact remains in history; the re-review is
named with `-rN` and links the fixed commit and old findings.
