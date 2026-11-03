# Writing Workflow

Use this workflow when you draft or revise VCVio documentation, comments, docstrings, commit
messages, PR text, issue text, or review comments. Use it for short comments as well as long guides.
Work on the text that the user requested. A writing review does not authorize unrelated source
changes or publication.

## Read the local requirements

Read the [writing standard](writing.md) and the [vocabulary](writing-vocabulary.md).
Read the relevant section of [CONTRIBUTING.md](../../CONTRIBUTING.md) for the contribution or text
that you prepare. The standard owns the requirements. This workflow explains how to apply them.

Treat existing prose as material to assess, not as a style to preserve. Use STE's writing
principles to correct defects. Keep established identifiers, notation, quotations, and technical
meanings accurate. Consult the official standard when a rule's source or a word's approval matters.
Do not invent a dictionary approval or claim full STE conformance from a checker result.

## Establish the facts

Read the source that the claims in the passage need. A theorem name or a successful build alone
does not establish a mathematical or security claim. Inspect the statement, its hypotheses, and the
relevant proof or axiom evidence. For a security claim, find the notion, the model, the
assumptions, the budgets, the bound, and the named reduction (rule C9).

For a PR description, separate the change, the checks that you ran, and the remaining gaps.
Keep output instructions separate from repository facts. A request for a draft does not establish
a PR's status, approval, or CI result. State those facts only when the source gives them.

For a review comment, identify the affected code or statement and explain the consequence.
For reference documentation, describe the interface or result that exists in the reviewed source.
Do not substitute a session history for that explanation.

If the source does not support a claim, narrow or remove the claim. Preserve uncertainty when the
evidence is incomplete. A prose task does not by itself require a new proof, build, or experiment.

## Draft and revise

Choose procedural or descriptive writing from the passage's purpose. Start with the result,
problem, or action that the reader needs. Develop one topic in each paragraph. Add headings, lists,
and examples when they make the text easier to use.

Revise the text for direct verbs, clear actors and antecedents, consistent terms, and short
sentences. Introduce unfamiliar concepts and notation before you use them. Remove empty praise and
repetition. Keep instructions distinct from explanations and optional advice.

Compare every mathematical rewrite with its source. Keep the hypotheses, quantifiers, negations,
error terms, exceptional cases, and direction of implication. For a security bound, keep the
model, the query budgets, and each term of the bound. Preserve time and requirement strength:
"may have failed" does not mean "failed", and "recommended" does not mean "required".
A shorter expression is useful only when it keeps the intended meaning.

Do not let a writing rule change standard terminology. A rule can conflict with a term or language
pattern that is standard in cryptography research and engineering, computer science, or mathematics.
In that case, keep the standard form and apply the rules to the rest of the passage. Repository
habit alone does not make a wording standard.

Use the vocabulary to resolve ambiguous terms, not to erase valid technical meanings.
"Complete the template" does not claim protocol completeness. "The scheme is hiding" names a
property. A theorem statement and a protocol statement need different qualifiers only when the
context could confuse them.

## Use the checker

Use `scripts/check-writing.py` as an editing aid:

```bash
uv run --no-project --python 3.12 python scripts/check-writing.py path/to/document.md
uv run --no-project --python 3.12 python scripts/check-writing.py --base origin/main
uv run --no-project --python 3.12 python scripts/check-writing.py --stdin description < /tmp/pr-description.md
git log --format=%B origin/main..HEAD | uv run --no-project --python 3.12 python scripts/check-writing.py --stdin commits
```

For changed prose, give the actual review base to `--base`. A stacked PR can have another PR's
branch as its base. Do not assume that every PR targets `main`.

Read each finding before you edit. Counts and grammar patterns are approximations. Correct real
defects, keep accurate technical expressions, and report a recurring checker defect with an
example. Do not rewrite a correct claim only to make the checker quiet.

The checker does not establish clarity, source fidelity, dictionary compliance, or permission to
publish. It reports findings and exits with status 0. The Writing workflow in CI shows the same
findings as warnings. A finding does not fail a PR.

## Read the final text before handoff

Read the complete affected passage after the last edit. Confirm that its structure is useful and
its claims still agree with the source. Check each link or reference that the edit changes.
A good sentence can still be wrong in its paragraph.

Return or save the requested text. Publish it only when the user's instructions authorize that
action. If the task includes a commit or a push, run the validation that the contribution workflow
requires first. Report material evidence gaps without adding a standard disclaimer to every text.
