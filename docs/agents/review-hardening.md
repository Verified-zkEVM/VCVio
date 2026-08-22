# Review Hardening Standard

VCVio changes are reviewed as mathematical and cryptographic library
contributions, not only as branches that compile. A review observation is
resolved only by a hardening commit, a minimized regression, a corrected
interface or statement, a concrete upstream proposal, or removal of content
that should not ship.

## Required Review Passes

Every substantial pull request records four passes:

1. **Migration and CI.** Reconstruct the semantic diff on current `main`, drop
   already-merged dependencies and historical merge commits, and run current
   local and hosted validation.
2. **API and layering.** Audit imports, public declarations, instances,
   notation, module visibility, trusted boundaries, and downstream consumers.
3. **Mathematical and adversarial review.** Try to falsify headline statements
   before following their proofs. Test zero, empty, degenerate, boundary, and
   unrestricted-adversary cases, and check that every premise is jointly
   satisfiable and materially weaker than the conclusion.
4. **Maintenance and claim review.** Check Mathlib conventions, simp normal
   forms, linters, axiom cleanliness, source correspondence, documentation, and
   whether the title and public endpoints say exactly what is formalized.

## Upstream-First Mathematics

Search the pinned Lean core, Mathlib, Batteries, cslib, and PolyFun sources by
statement shape and abstraction before adding generic mathematics. Confirm a
candidate with a small Lean example rather than relying on name similarity.
Use upstream measures, kernels, probability, combinatorics, algebra,
computability, filters, categories, and monad infrastructure where available.

Put genuinely missing reusable mathematics in `ToMathlib` only when it is below
the VCVio framework dependency boundary. Record the upstream search and a
deletion trigger. Polynomial and qualitative interaction/machine structure
belongs in PolyFun; cryptographic games, quantitative policy, and
scheme-specific algebra belong in VCVio or `LatticeCrypto`.

## Hardening Checklist

A merge-ready change must have:

- a focused current-`main` diff and fresh CI;
- minimal imports and preserved Interop/Extern isolation;
- an explicit public API and trust-surface delta;
- ordinary-import consumer canaries for load-bearing public laws;
- committed regressions for every discovered failure or counterexample;
- satisfiable assumptions that do not encode the desired conclusion;
- exact paper/model scope at every headline theorem;
- Mathlib-style names, intrinsic docstrings, lint-clean simp declarations, and
  no blanket linter suppression;
- no new `sorry`, `admit`, unsafe proof shortcut, or unapproved native trust;
- explicit axiom output for headline declarations; and
- a final audit note describing the proof spine checked, attacks attempted,
  hardening added, and remaining boundary.

For probability or security results, distinguish exact identities,
statistical-distance assumptions, computational assumptions, realizability,
and asymptotic/PPT conclusions. Do not silently pass between those layers.

## Concrete Review Artifacts

Load-bearing PRs maintain a compact claim table containing the declaration,
mathematical meaning, premises, paper or source anchor, consumers, axioms, and
negative tests. Counterexamples remain in the test library after a repair so an
invalid formulation cannot return. Proofs should use stable public laws rather
than unfold implementation details across module boundaries.

Large developments are split when independently useful claims can be reviewed,
tested, merged, and reverted separately. Public prose is intrinsic: it records
the theorem and its limitations, not the history of attempts that produced it.
Stable review lessons are folded back into this page; transient campaign status
belongs in pull-request comments or the tracking issue.
