# Reading: design records

Longer-form design documents. These are records of investigation and decision, not agent
instructions — for how to *use* the probability layer, see
[`docs/agents/probability.md`](../agents/probability.md).

## Probability semantics

Read in this order; each answers a different question.

| # | Document | Question it answers |
|---|---|---|
| 1 | [`probability-semantics-landscape.md`](probability-semantics-landscape.md) | What are the options, and what is actually true upstream? The evidence ledger. §19 is its verification log. |
| 2 | `measure-semantics-spike.md` | What happened when one option was built? Findings and friction, including what it did *not* settle. |
| 3 | `denotational-probability-semantics.md` | Which design was accepted, and what is now settled? The baseline for new work. |
| 4 | [`mathlib-integration-shape.md`](mathlib-integration-shape.md) | What should the resulting statements *look like* so Mathlib's library applies to them? Short- and long-term shape. |

Start at 3 if you only want the current rule. Start at 1 if you want to know why, or to check a
claim before relying on it.

Documents 2 and 3 are unlinked above because they are not here yet: they describe the Lean files
of the measure-semantics work and travel with it, so that a reader on `main` is never pointed at a
design whose implementation is absent. 1 and 4 are about upstream and about direction, and hold
whether or not that work lands.

## Keeping these honest

Two conventions, both learned the hard way and worth preserving:

**Record the method, not just the verdict.** §19 of the landscape gives, for each claim, how it was
checked. The failure mode these documents are most exposed to is asserting that upstream provides
something on the strength of a name matching. A name is a hypothesis; the declaration in the pinned
tree is the evidence.

**Re-check volatile facts at the moment of editing.** Upstream tags, PR statuses, and draft-versus-
open state change faster than the documents that cite them — the PolyFun tag in §19.4 went stale
twice in a single day. A fact that was verified last week is not verified.
