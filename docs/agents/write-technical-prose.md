# /write-technical-prose

Use this workflow for VCVio documentation, comments, docstrings, commit messages, PR and issue
text, and review comments. Work on the text that the user requested. A prose task does not authorize
publication or unrelated source changes.

1. **Read the source before stating a claim.** [CONTRIBUTING.md](../../CONTRIBUTING.md) owns the
   contribution requirements. Inspect the relevant definitions, hypotheses, proofs and test evidence.
   For a security claim, read its notion, model, assumptions, budgets, bound and named
   reduction. Distinguish the theorem from an example or a test.
2. **Start with what the reader needs.** State the problem, result or action first. Develop one
   topic per paragraph. Use the [writing guide](writing.md) and [vocabulary](writing-vocabulary.md)
   when they help; their advice is not a conformance test.
3. **Revise real problems.** Identify a clarity or accuracy problem before changing a passage.
   Keep established terms, claims, hypotheses, uncertainty and requirement strength. Repository habit
   alone does not justify unclear wording.
4. **Compare complete passages.** Read the old and new paragraphs side by side in context.
   Check that the revision keeps the meaning, conditions and scope, and explain why it is clearer.
   Read the final passage and check changed links or references.
5. **Leave correct text alone.** The checker offers optional suggestions, not a judgment of clarity,
   accuracy or STE conformance. Read each suggestion in context. Do not change clear, correct text
   to silence it. For a PR description, distinguish changes, checks actually run and remaining gaps.

## Use the checker

These commands are optional. For a stacked PR, use its actual review base instead of `origin/main`:

```bash
uv run --no-project --python 3.12 python scripts/check-writing.py --base origin/main
uv run --no-project --python 3.12 python scripts/check-writing.py --stdin description < /tmp/pr-description.md
```

If the task includes a commit or push, run the validation required by CONTRIBUTING first.
