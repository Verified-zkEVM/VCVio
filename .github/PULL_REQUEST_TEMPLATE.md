<!--
Use the title format in CONTRIBUTING.md, "Title".
Follow the mandatory claim rules in docs/agents/writing.md and consider its advisory style guidance.
-->

## Summary

<!-- What changes and why. When a Mathlib, core, or Batteries lemma or idiom replaces a local
one, cite its row in docs/reading/upstream-alignment.md. -->

## Verification

<!-- The commands that you ran locally, and the commit that they cover. Examples are
`lake build <libs> VCVioTest`, `lake exe axiomsweep --check`, `./scripts/update-lib.sh`,
`lake lint -- --env-only`, `lake exe lint-style <libs>`, and
`uv run --no-project --python 3.12 python scripts/check-agent-docs.py`. -->

## Checklist

- [ ] New files have the standard header and a module docstring (`CONTRIBUTING.md`, *Attribution
      And File Headers*). Docstrings are intrinsic, with no change history or "renamed from" wording.
- [ ] New files use a plain `public section` with `@[expose]` on individual declarations
      (*Module Scopes*). If the PR converts a file, it lowers the expose-boundary baseline.
- [ ] `./scripts/update-lib.sh` leaves the umbrella files unchanged. `lake exe axiomsweep --check`
      passes, and `scripts/axiom_baseline.json` is unchanged or the summary explains its diff.
- [ ] No `set_option linter.* false`, no deprecated aliases (`docs/agents/gotchas.md` §18, §23),
      and no native FFI test executables on the PR path.
- [ ] Documentation that the change affects is updated, and `uv run --no-project --python 3.12 python scripts/check-agent-docs.py`
      passes.
- [ ] If a simp, grind, or gcongr set changed, the gate files under `VCVioTest/` gained one-call
      entries. No proof gained a second tactic call outside a dated gap pair. The summary lists
      the line counts of the touched proofs before and after the change.
- [ ] The title follows `CONTRIBUTING.md`. I checked the mandatory claim rules and considered the advisory style guidance.
