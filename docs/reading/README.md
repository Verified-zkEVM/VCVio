# Reading: design records

Longer-form design documents. These are records of investigation and decision, not agent
instructions — for how to *use* the probability layer, see
[`docs/agents/probability.md`](../agents/probability.md).

Each document opens with a status line. A status that calls a document historical marks a dated
record: it keeps the names and facts of its time, and the documentation guard
(`scripts/check-doc-names.py`) does not check its body for retired names. Every other document
describes the present, and the guard checks all of it.

## Probability semantics

Read in this order; each answers a different question.

| # | Document | Status | Question it answers |
|---|---|---|---|
| 1 | [`probability-semantics-landscape.md`](probability-semantics-landscape.md) | Historical evidence survey and decision record | What options were considered, what evidence supported the decision, and which volatile upstream facts were later rechecked? §19 preserves the original verification log; §20 records later disposition. |
| 2 | [`measure-semantics-spike.md`](measure-semantics-spike.md) | Historical implementation record, 2026-08-21 | What happened when the measure-native option was built? Findings and friction, including what it did *not* settle. |
| 3 | [`denotational-probability-semantics.md`](denotational-probability-semantics.md) | Accepted design baseline | Which design was accepted, and what rules govern new work? |
| 4 | [`mathlib-integration-shape.md`](mathlib-integration-shape.md) | Design guidance | What should the resulting statements *look like* so Mathlib's library applies to them? Short- and long-term shape. |

Start at 3 if you only want the current rule. Start at 1 if you want to know why, or to check a
claim before relying on it.

The documents deliberately serve different time horizons. The landscape and spike preserve the
reasoning that led to the decision; the baseline and agent guide state the rules to apply now. Do
not infer current API names or PR status from an old snapshot without checking its later-status
section or the pinned source tree.

## Upstream alignment

| Document | Status | Question it answers |
|---|---|---|
| [`upstream-alignment.md`](upstream-alignment.md) | Living ledger, re-verified at each pin bump | Which of VCVio's general-purpose machinery and tooling does Lean core, Mathlib, Batteries, cslib, or PolyFun already own, and what is the verdict (adopt / keep / upstream / track) for each, with the evidence? Includes a broad reading of the adjacent Mathlib areas and the idioms they suggest. |
| [`internal-duplication.md`](internal-duplication.md) | Living record | Where does VCVio say the same thing twice *inside* the repository (cost layers, invariant predicates, the two Merkle engines, `OracleSpec` operations versus PolyFun's), which spelling is canonical, and what blocks folding the rest? |
| [`api-boundary-campaign.md`](api-boundary-campaign.md) | Historical campaign record, September 2026 | Which public boundaries rely on definitional equality, which instance leaks did the campaign repair, and what consumer evidence and upstream blockers did it record? |
| [`generalized-relation-automation.md`](generalized-relation-automation.md) | Historical investigation record, 2026-09-08 | How do `gcongr`, `grw`, and related tactics apply to VCVio's relations, which registrations simplify current proofs, and which candidates should remain experimental? |
| [`long-proof-audit.md`](long-proof-audit.md) | Historical source audit with compiled experiments, September 2026 | What drives the longest proofs, how much can small automation or shared lemmas remove, and which arguments need deeper refactoring? |
| [`program-logic-performance.md`](program-logic-performance.md) | Historical measurement record, 2026-10-02 | Did the core-WP program logic make the library slower to build, and where does compile time go? Sequential profiled replays of `main` and #821. |

## Keeping these honest

Three conventions, all learned the hard way and worth preserving:

**Record the method, not just the verdict.** §19 of the landscape gives, for each claim, how it was
checked. The failure mode these documents are most exposed to is asserting that upstream provides
something on the strength of a name matching. A name is a hypothesis; the declaration in the pinned
tree is the evidence.

**Cite sources so that the checker can resolve them.** A source location is written `K:path` or
`K:path:line`, where `K` names the tree: `V:` this repository, `M:` Mathlib, `B:` Batteries, `Cs:`
cslib, `P:` PolyFun, `C:` Lean core and Std. `scripts/check-reading-citations.py` (run by
`validate.sh` and the *Agent Docs* workflow) fails on a path that does not exist at the pins or a
line past the end of its file. It does not check that a cited line still says what the text claims,
so whoever adds or moves a citation reads the line it lands on. A location whose target has since
been removed or moved is kept as history without the tree prefix, marked as a snapshot, with its
current disposition beside it.

**Re-check volatile facts at the moment of editing.** Upstream tags, PR statuses, and draft-versus-
open state change faster than the documents that cite them — the PolyFun tag in §19.4 went stale
twice in a single day. Preserve the dated result as history, then add a new dated disposition backed
by the pinned source tree. A fact that was verified last week is not verified today.
