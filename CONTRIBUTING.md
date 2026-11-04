# Contributing to VCVio

Contribute a definition, proof, test, example, or documentation change. These documents give the
context for a contribution:

- [`README.md`](README.md) gives the project overview.
- [`AGENTS.md`](AGENTS.md) describes the repository workflow, the module layering, and proof
  guidance.
- The guides in [`docs/agents/`](docs/agents/) describe each area of the library.
- The [repository ownership map](docs/design/repository-layout.md) gives placement rules and build
  boundaries.

## Before You Start

### Set Up The Build

On a new clone, download the Mathlib cache and build the proof libraries:

```bash
lake exe cache get && lake build
```

`lake build` builds the seven default proof libraries. For work only on the framework,
`lake build VCVio` is faster.

### Check For Overlap

Before you start a formalization, search the open pull requests (PRs) and issues for the same
target:

```bash
gh pr list -R Verified-zkEVM/VCVio --state open --search "<topic or declaration>"
gh issue list -R Verified-zkEVM/VCVio --state open --search "<topic or declaration>"
```

If an open PR covers the same declarations, ask its author whether the work is active. If you open
a PR for the same target, link the earlier PR and explain how your work relates to it.
For work that appears abandoned, you may ask a maintainer whether to proceed.
A maintainer may waive the author-contact step.

### Place The Work

Put a declaration in the library that owns its concept. The
[repository ownership map](docs/design/repository-layout.md) and the module layering in
[`AGENTS.md`](AGENTS.md#module-layering) give the rules. Search VCVio, PolyFun, and Mathlib
before you add a definition. When a Mathlib, core, or Batteries lemma replaces a local one, cite
its row in the [upstream alignment ledger](docs/reading/upstream-alignment.md).

## Validate The Change

Install [uv](https://docs.astral.sh/uv/getting-started/installation/) before the Python checks and the default validation pass.

Do these steps before you request review:

1. After you add, rename, or delete a `.lean` file, run `./scripts/update-lib.sh`. CI fails when
   a regenerated umbrella module differs from the committed one.
2. Run `./scripts/validate.sh`. It runs the fast per-PR CI checks locally, in CI order.
3. Add the flags for the slower passes that the change needs:
   - `--test` builds the test libraries and runs the test executables.
   - `--axioms` runs the axiom and `sorry` sweep. Use it when the change adds or closes a `sorry`,
     or changes proofs.
   - `--lint` runs the Batteries environment linters, as CI does.
   - `--ffi`, together with `--test`, also runs the native ML-KEM, ML-DSA, and Falcon executables.
     This pass is slow.

`./scripts/validate.sh --help` lists every check and flag. [`AGENTS.md`](AGENTS.md#building)
explains the CI build, the caches, and each gate.

For a change to documentation only, run the documentation checks without a Lean build:

```bash
python3 scripts/test-agent-docs.py
python3 scripts/check-agent-docs.py
python3 scripts/extract-doc-fragments.py --check
python3 scripts/check-doc-names.py
```

CI also resolves the declaration names that the guides cite. That check needs a build, so
`./scripts/validate.sh` runs `scripts/check-doc-names.py --resolve` for that purpose.

### Proof Debt And Linters

- Avoid a `sorry` in finished work, unless the change is explicitly meant to preserve partial
  work. To track an open obligation, open a *Proof obligation* issue.
- After you intentionally add or close a `sorry`, run `lake exe axiomsweep --update-baseline`.
  Commit the change to `scripts/axiom_baseline.json`, and explain it in the PR description.
- Keep repository-wide Lean options in `lakefile.lean`. Do not restate `autoImplicit = false`
  with a `set_option` line in a file.
- Do not disable linters locally or globally to make warnings disappear.
  Fix the cause instead of adding `set_option linter.* false`, `set_option weak.linter.* false`, or a repository-level linter suppression.
  [Gotcha 23](docs/agents/gotchas.md#23-do-not-disable-linters-to-silence-warnings)
  gives the one documented exception.
- When you rename or remove a declaration, update every caller in the same PR. Do not add
  deprecated aliases or compatibility wrappers
  ([gotcha 18](docs/agents/gotchas.md#18-full-cutover-no-backward-compatibility-shims)).

### Security Statements

State a security reduction for a named reduction, simulator, or extractor, not for one that only
exists. Adversary types carry no resource bound, and Lean can choose witnesses classically. So
`∃ B, bound ≤ advantage B` holds for every scheme.
[Name the reduction in the theorem statement](docs/agents/crypto.md#name-the-reduction-in-the-theorem-statement)
explains the rule and its alternatives.

## Pull Requests

### Title

Use this format for the PR title:

```text
<type>(<optional scope>): <subject>
```

Use one of these types:

- `feat`: a definition, a formalized result, or a feature
- `fix`: a correction of a defect
- `docs`: documentation
- `refactor`: a change to the organization or the interfaces
- `perf`: a performance improvement
- `test`: tests, test vectors, and examples that act as tests
- `chore`: maintenance
- `ci`: CI workflows and checks

Write a short subject that names the change. Use an imperative phrase, such as "add the CMA-to-NMA
reduction". A noun phrase for the result, such as "the hiding theorem for commitments", is also
correct. Do not use "added" or "adds".

Keep ordinary words lowercase, and keep the capitalization of names such as ML-KEM. Do not end the
subject with a period. Use the scope when it identifies the affected component, such as a library,
a namespace, or a scheme. For a breaking change, put `!` before the colon. For example:

```text
feat(FiatShamir): add the CMA-to-NMA reduction for signatures with aborts
docs(design): describe the generic and algebraic group models
refactor(OracleComp)!: rename the query constructors
```

### Description

Complete the [PR template](.github/PULL_REQUEST_TEMPLATE.md). Keep the description proportional to
the change. Omit a section that does not apply rather than inventing claims for it. Give reviewers
the information that they need to assess the contribution:

- State the problem, the change, and its purpose.
- Identify the headline declarations. For a security theorem, give the notion, the model, the
  assumptions, and the bound.
- Compare each headline statement with its source, and explain the differences in hypotheses,
  conclusions, and scope.
- List each `sorry` that the PR adds or closes, and explain each change to
  `scripts/axiom_baseline.json`.
- Give the validation commands, their results, and the commit that they cover.
- List renamed or removed declarations and the callers that the PR updates.
- Link related issues, the base of a stack, and overlapping work.

Keep the claims in the title and the description consistent with the code and the evidence. A
successful build does not establish fidelity to a source or the absence of `sorry`.

### Size And Stacking

Give each PR one topic. Separate mechanical changes from mathematical changes when a reviewer can
check each one independently.

Use a stack of PRs when a contribution needs several dependent changes. Each PR must build and
pass its validation against its base. Name that base in the description.
If GitHub marks a PR as stacked, use the asynchronous merge API for the merge queue, as the next section describes.

### Checks And The Merge Queue

Before you enqueue a reviewed PR, inspect every check on its current head. Include the lint and
downstream builds, not only the required checks. Resolve each failed or cancelled run. A successful
duplicate run does not clear a cancelled run.

Rerun a cancelled workflow with `gh run rerun RUN_ID`. After you diagnose a retryable failure,
rerun it with `gh run rerun RUN_ID --failed`. Wait for the reruns to finish before you enqueue
the PR.

VCVio's `main` uses the merge queue. A PR that GitHub marks as stacked needs the
[asynchronous merge API](https://docs.github.com/en/rest/pulls/pulls#merge-a-pull-request-asynchronously).
Send `PUT /repos/Verified-zkEVM/VCVio/pulls/NUMBER/merge-async` with `sha` set to the reviewed
head and `merge_action` set to `merge_queue`. Omit the merge-method and commit-message parameters,
because the queue controls them. The ordinary CLI auto-merge path and the GraphQL enqueue
operation reject these stacked PRs.

After the request, check the returned request UUID and the queue entry. Wait for the queue's
checks and the actual merge result before you report a merge.

### Writing

The [writing guide](docs/agents/writing.md) offers advice for documentation, docstrings, comments,
commit messages, PR and issue text, and review comments. Use it to improve clarity and precision.
Leave clear, correct text alone, even if it does not follow a rule or the checker reports it.
The contribution requirements in this document retain their stated force.

Use the [writing workflow](docs/agents/write-technical-prose.md) when you draft or revise that
text. Keep claims, hypotheses, uncertainty, and requirement strength unchanged during a style edit.
The [vocabulary](docs/agents/writing-vocabulary.md) records technical meanings. It does not
prohibit other meanings when their context is clear.

`scripts/check-writing.py` offers optional wording suggestions. It does not establish clarity,
accuracy or STE conformance. CI runs it on changed prose and the PR description, and reports
suggestions as warnings only.

### Tool-Assisted Contributions

You are responsible for content that an AI agent or another tool produces for your contribution:

- Read the headline statements and the full description before you request review.
- Keep temporary plans, handoff notes, and session logs out of the contribution.
- Replace planning codes that a reader cannot find with the maintained source or an explanation.
- Describe the current library in reference documentation. Explain the change in the commit or PR
  description.
- Coordinate concurrent tool runs so that they do not open competing PRs for the same target.

## Attribution And File Headers

Every new Lean file should start with the standard header:

```lean
/-
Copyright (c) CURRENT_YEAR Author Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author Name
-/
```

Replace `CURRENT_YEAR` with the calendar year in which you create the file. Apply this attribution
policy:

1. **New files**: add the standard header with the current year and the names of the credited
   authors.
2. **Routine edits to existing files**: keep the existing header. Do not change the attribution
   only because you edited the file.
3. **Substantial rewrites or replacements**: update the header to show the new authorship when new
   content effectively replaces a file. The same applies when you rename or recreate an old file as
   a genuinely new file. A plain rename does not change the attribution.
4. **Copied or ported material**: a new file can keep substantial content or structure from
   another source. Then keep the required upstream attribution, and add the current credited
   authors as appropriate.
5. **AI assistance**: do not add a separate AI-attribution line. Use the normal header format, and
   list only the names of the credited authors.

If you are not sure, keep the attribution on incremental edits. Change it only when a file is new
or materially replaced.

## Documentation And Docstrings

The [repository ownership map](docs/design/repository-layout.md) gives the placement rules and the
build boundaries for documentation and code.

- Every ordinary Lean source file should have a module docstring `/-! ... -/` near the top.
- Import-only umbrella modules should stay bare. Examples are `VCVio.lean`, `LatticeCrypto.lean`, and
  `Examples.lean`. `lakefile.lean` should stay bare as well.
- Public definitions and major theorems should have a declaration docstring `/-- ... -/`.
- A module docstring should give a concise title and summary, with notation or references when that context helps a reader.
- A declaration docstring should describe what a definition is or what a theorem states, not how it evolved.
- Keep docstrings intrinsic and descriptive. Refer to current definitions when that helps. Do not
  mention removed or renamed declarations, change history, or phrases such as "replaces" or
  "renamed from".
- If a file cites papers, add a references section to the module docstring, or cite the source
  in the surrounding documentation. [`REFERENCES.md`](REFERENCES.md) lists the
  repository's references.

Use this prologue layout for an ordinary Lean source file, with exactly one blank line between the
blocks:

1. The copyright, licence, and authors header.
2. One blank line.
3. `module`.
4. The public and private imports.
5. One blank line.
6. The module docstring.

### Section Headers Within A File

Use Mathlib-style doc-comment section headers, not ASCII banners. For a section break inside a
Lean file, use a one-line docstring header. The documentation generator renders it:

```lean
/-! ## Section title -/
```

For a section with its own paragraph of explanation, use this form:

```lean
/-!
## Section title

Optional paragraph that describes what the section contains.
-/
```

Do not use ASCII banners such as this one:

```lean
-- ============================================================================
-- § Section title
-- ============================================================================
```

An ASCII banner does not appear in the generated documentation, and it divides the file in a way
that the type system does not enforce. The `/-!` form reads as prose and appears in the `doc-gen4`
output. A section that needs a banner usually needs its own `namespace` or its own file.

## Module Scopes

All active Lean libraries and tests use the module system. Put ordinary declarations in a
`public section`, and put tactic and elaborator declarations in a `public meta section`.

Most existing source files use `@[expose] public section` to keep the definitional equalities that
they had before the migration. A new file uses a plain `public section`. Mark a definition
`@[expose]` when unfolding it is part of its intended public API. An executable or runtime
implementation module should use an opaque `public section` when callers do not need to unfold its
definitions.

CI limits the number of broadly exposed files in each library. The
[module-system guide](docs/agents/module-system.md#validation-and-coordinated-rollout) describes
the exposure check and its baseline workflow.

Choose each import form for its purpose:

- `public import` gives a dependency to downstream importers transitively.
- `public meta import` exports a compile-time dependency.
- A plain `import` keeps an implementation dependency private.
- `import all` is for a proof module that deliberately needs the private implementation of an
  imported module.

Do not use the transitional `backward.privateInPublic` or `backward.proofsInPublic` options. Do not
write a cross-package `import all PolyFun.…`. Add a public PolyFun law or API instead.
[`docs/agents/module-system.md`](docs/agents/module-system.md) gives the visibility decision tree
and the long-term boundary between VCVio and PolyFun.

`LatticeCryptoTest.lean` is curated rather than generated, because its executable modules define
colliding root-level `main` declarations. For the same reason, `HashSigTest` has no generated root
umbrella. Build its named executables and modules directly.

## Style Notes

- Keep imports at the top of the file.
- Follow the [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)
  where possible. The capitalization rules are:
  - Terms of a `Prop`, for example proofs and theorem names, use `snake_case`.
  - A `Prop` or a `Type` (or `Sort`) uses `UpperCamelCase`. Examples are inductive types,
    structures, and classes.
  - A function has the name that its return value would have. For example, a function of type
    `A → B → C` has a name for a term of type `C`.
  - All other terms of a `Type` use `lowerCamelCase`.
- Respect the module layering in [`AGENTS.md`](AGENTS.md#module-layering).
- Use `/-! ## Title -/` headers, not ASCII banners, for section breaks in a file.

For probability tactic tests, follow the
[tactic-test conventions](docs/agents/probability.md#normal-forms-and-the-tactic-contract).

### Section Variables

A `variable` line carries an instance assumption only when the theorems in its scope share it.
Lean includes an instance-implicit section variable in every theorem whose statement mentions the
variables that its type refers to. This occurs even when the proof does not use it. The
`unusedSectionVars` linter then requires an `omit [...] in` line. Definitions are not affected,
because Lean removes their unused variables after elaboration.

Put an assumption that a few declarations need on those declarations. For an assumption that a
contiguous block of declarations shares, put a `section` around that block with its own `variable`
line. Reorder declarations when that keeps the file readable.

Do not declare an assumption that another assumption in scope implies. Examples are `[Finite X]`
beside `[SampleableType X]`, `[Fintype X]` beside `[FinEnum X]`, and `[Nonempty X]` beside
`[Inhabited X]`. The proof derives such an assumption, for example with `Fintype.ofFinite` or
`SampleableType.finite`.

Use `omit` for a genuine exception in a section, not as a routine step. A file with more `omit`
lines than `variable` binders needs a different section structure. Omitted variables still take
part in instance search while a statement elaborates. A change to the hypotheses of a definition
also changes the `omit` lists of every file that mentions its types. See gotcha 31 in
[`docs/agents/gotchas.md`](docs/agents/gotchas.md).

## Toolchain And Dependency Bumps

The Lean toolchain and Mathlib move together, and the other pins follow them. Do the steps in this
order, which keeps `lake update` idempotent. The comment above the PolyFun `require` in
`lakefile.lean` explains why.

1. Update `lean-toolchain`, then the Mathlib tag in `lakefile.lean`.
2. Update the `cslib` and `PolyFun` revisions, each to a commit built against that Mathlib.
   Program logic uses the pinned Lean core WP interface through PolyFun.
3. Run `lake update --keep-toolchain`, then `lake exe cache get`.
4. Run `./scripts/validate.sh --lint --test --axioms`. Fix what the new toolchain reports rather
   than silencing it (`docs/agents/gotchas.md` §23).
5. Update `scripts/axiom_baseline.json` only for an intentional change in `sorry` debt.
6. Check each row of the [upstream alignment ledger](docs/reading/upstream-alignment.md) against the
   newly pinned trees. Do not derive the result from a diff against the previous ledger.
7. Update the version mentions in `AGENTS.md` (*Building*) and `docs/agents/gotchas.md` §26.

## Licensing

This project is licensed under Apache 2.0. By contributing, you agree that your contributions are licensed under the same terms.
